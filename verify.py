#!/usr/bin/env python3
"""Build and no-cheat-check exact Lean declarations.

Verification is bound to three reviewed inputs: a module, a declaration, and its
expected Lean type.  A generic successful build is deliberately insufficient.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
import time
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parent
DEFAULT_ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_OUTPUT = {
    "sorryAx": "an admitted proof",
    "declaration uses 'sorry'": "an admitted proof",
    "Lean.ofReduceBool": "compiler-trusted native evaluation",
}
LEAN_NAME_SEGMENT = r"(?:[^\W\d][\w']*|«[^»\r\n\x00-\x1f\x7f]+»)"
LEAN_MODULE_NAME = rf"{LEAN_NAME_SEGMENT}(?:\.{LEAN_NAME_SEGMENT})*"
LEAN_DOTTED_IDENTIFIER = re.compile(rf"{LEAN_MODULE_NAME}\Z")
LEAN_UNIVERSE_IDENTIFIER = re.compile(r"[A-Za-z][A-Za-z0-9_']*\Z")
LEAN_CHAR_LITERAL = re.compile(
    r"'(?:[^'\\\r\n]|\\(?:[abfnrtv\\'\"0]|x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f]+\}))'"
)
MANIFEST_TOP_LEVEL_KEYS = frozenset(
    {
        "version",
        "allowed_axioms",
        "targets",
        "aggregator_only_modules",
        "declaration_exclusions",
        "public_aggregators",
        "reviewed_claim_deltas",
    }
)
MANIFEST_V1_TARGET_KEYS = frozenset(
    {"module", "declaration", "expected_type", "task_id"}
)
MANIFEST_V2_TARGET_KEYS = MANIFEST_V1_TARGET_KEYS | {"universes"}
MANIFEST_CLAIM_KINDS = frozenset({"target", "exclusion", "aggregator"})
MANIFEST_CLAIM_DELTA_KEYS = frozenset(
    {"old_manifest_sha256", "new_manifest_sha256", "old", "new", "reason"}
)
SHA256_HEX = re.compile(r"[0-9a-f]{64}\Z")
IMPORT_COMMAND = re.compile(
    rf"(?<![\w'])\bimport\b[ \t\r\n]+({LEAN_MODULE_NAME})"
)


class VerificationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Target:
    module: str
    declaration: str
    expected_type: str
    task_id: str = ""
    universes: tuple[str, ...] | None = None


@dataclass(frozen=True)
class SourceSnapshot:
    git_head: str
    closure_files: tuple[tuple[str, str], ...]
    modified: tuple[str, ...]
    untracked: tuple[str, ...]
    absent_from_head: tuple[str, ...]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_sha256(value: Any) -> str:
    rendered = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return sha256_bytes(rendered.encode("utf-8"))


def target_serializable(target: Target) -> dict[str, Any]:
    """Return the receipt/marker shape, preserving legacy rows when monomorphic."""
    rendered = {
        "module": target.module,
        "declaration": target.declaration,
        "expected_type": target.expected_type,
        "task_id": target.task_id,
    }
    if target.universes is not None:
        rendered["universes"] = list(target.universes)
    return rendered


def has_control_character(value: str) -> bool:
    """Return whether ``value`` can inject a command or corrupt a receipt line."""
    return any(unicodedata.category(character) == "Cc" for character in value)


def validate_expected_type_syntax(value: str, context: str) -> None:
    """Reject text that can escape the parenthesized exact-type position."""
    pairs = {")": "(", "]": "[", "}": "{"}
    stack: list[str] = []
    in_string = False
    escaped = False
    in_quoted_identifier = False
    identifier_character = lambda c: bool(c) and (c.isalnum() or c in "_'")
    index = 0
    while index < len(value):
        character = value[index]
        if in_string:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            index += 1
            continue
        if in_quoted_identifier:
            if character == "»":
                in_quoted_identifier = False
            index += 1
            continue
        for token in ("--", "/-", "-/"):
            if value.startswith(token, index):
                raise VerificationError(
                    f"{context}: expected_type contains forbidden comment token {token!r}"
                )
        if character == '"':
            in_string = True
        elif character == "«":
            in_quoted_identifier = True
        elif character == "'":
            char_literal = LEAN_CHAR_LITERAL.match(value, index)
            if char_literal is not None:
                index = char_literal.end()
                continue
        if character == "_":
            before = value[index - 1] if index else ""
            after = value[index + 1] if index + 1 < len(value) else ""
            if not identifier_character(before) and not identifier_character(after):
                raise VerificationError(
                    f"{context}: expected_type contains a standalone placeholder"
                )
        if character == "?":
            raise VerificationError(
                f"{context}: expected_type contains an unquoted question mark"
            )
        if character in "([{":
            stack.append(character)
        elif character in pairs:
            if not stack or stack.pop() != pairs[character]:
                raise VerificationError(
                    f"{context}: expected_type has unbalanced delimiters"
                )
        index += 1
    if stack or in_string or in_quoted_identifier or escaped:
        raise VerificationError(f"{context}: expected_type has unbalanced delimiters")


def validate_target(target: Target, context: str) -> None:
    """Validate all text that is interpolated into an audit source or receipt."""
    if not isinstance(target, Target):
        raise VerificationError(f"{context}: target must be a Target")
    fields = {
        "module": target.module,
        "declaration": target.declaration,
        "expected_type": target.expected_type,
        "task_id": target.task_id,
    }
    for field, value in fields.items():
        if not isinstance(value, str):
            raise VerificationError(f"{context}: {field} must be a string")
        if has_control_character(value):
            raise VerificationError(f"{context}: {field} contains a control character")
    if not target.expected_type:
        raise VerificationError(f"{context}: expected_type must not be empty")
    if target.universes is not None:
        validate_expected_type_syntax(target.expected_type, context)
    for field in ("module", "declaration"):
        value = fields[field]
        if not value or LEAN_DOTTED_IDENTIFIER.fullmatch(value) is None:
            raise VerificationError(
                f"{context}: {field} must be a Lean dotted identifier"
            )
    if target.universes is None:
        return
    if not isinstance(target.universes, tuple):
        raise VerificationError(f"{context}: universes must be a tuple")
    for universe in target.universes:
        if not isinstance(universe, str) or has_control_character(universe):
            raise VerificationError(
                f"{context}: universes must contain only strings"
            )
        if (
            not universe
            or LEAN_UNIVERSE_IDENTIFIER.fullmatch(universe) is None
        ):
            raise VerificationError(
                f"{context}: universe must be a Lean identifier: {universe!r}"
            )
    if len(set(target.universes)) != len(target.universes):
        raise VerificationError(f"{context}: universes must not contain duplicates")


def validate_targets(targets: list[Target], context: str) -> None:
    """Validate targets before they can be used as dictionary keys or source text."""
    seen_declarations: set[tuple[str, str]] = set()
    for index, target in enumerate(targets, 1):
        target_context = f"{context}: target {index}"
        validate_target(target, target_context)
        identity = (target.module, target.declaration)
        if identity in seen_declarations:
            raise VerificationError(
                f"{target_context} duplicates declaration {target.declaration} "
                f"in module {target.module}"
            )
        seen_declarations.add(identity)


def validate_manifest_claim_endpoint(value: Any, context: str) -> tuple[str, str, str]:
    """Validate an exact reviewed-claim ledger endpoint."""
    if not isinstance(value, dict) or value.get("kind") not in MANIFEST_CLAIM_KINDS:
        raise VerificationError(f"{context}: claim needs a valid kind")
    kind = value["kind"]
    expected_keys = (
        {"kind", "module"}
        if kind == "aggregator"
        else {"kind", "module", "declaration"}
    )
    if set(value) != expected_keys:
        raise VerificationError(f"{context}: claim needs exact fields")
    module = value["module"]
    if (
        not isinstance(module, str)
        or has_control_character(module)
        or LEAN_DOTTED_IDENTIFIER.fullmatch(module) is None
    ):
        raise VerificationError(f"{context}: claim needs a Lean module name")
    if kind == "aggregator":
        return kind, module, ""
    declaration = value["declaration"]
    if (
        not isinstance(declaration, str)
        or has_control_character(declaration)
        or LEAN_DOTTED_IDENTIFIER.fullmatch(declaration) is None
    ):
        raise VerificationError(f"{context}: claim needs a Lean declaration name")
    return kind, module, declaration


def validate_reviewed_claim_deltas(value: Any, context: str) -> None:
    """Validate current ledger rows; cross-revision append-only checks are CI's job.

    This verifier binds the entire manifest file into provenance, but does not
    consume delta rows to select or alter theorem checks.
    """
    if not isinstance(value, list):
        raise VerificationError(f"{context}: reviewed_claim_deltas must be a list")
    endpoints_by_transition: dict[tuple[str, str], set[tuple[str, str, str]]] = {}
    for index, delta in enumerate(value, 1):
        item_context = f"{context}: reviewed claim delta {index}"
        if not isinstance(delta, dict) or set(delta) != MANIFEST_CLAIM_DELTA_KEYS:
            raise VerificationError(
                f"{item_context}: needs exact transition/old/new/reason fields"
            )
        reason = delta["reason"]
        if not isinstance(reason, str) or not reason.strip():
            raise VerificationError(f"{item_context}: needs rationale")
        hashes: list[str] = []
        for key in ("old_manifest_sha256", "new_manifest_sha256"):
            digest = delta[key]
            if not isinstance(digest, str) or SHA256_HEX.fullmatch(digest) is None:
                raise VerificationError(f"{item_context}: needs {key}")
            hashes.append(digest)
        old = validate_manifest_claim_endpoint(delta["old"], item_context + " old")
        new = (
            validate_manifest_claim_endpoint(delta["new"], item_context + " new")
            if delta["new"] is not None
            else None
        )
        if new == old:
            raise VerificationError(f"{item_context}: no-op claim move is not a removal")
        transition = (hashes[0], hashes[1])
        endpoints = endpoints_by_transition.setdefault(transition, set())
        if old in endpoints or (new is not None and new in endpoints):
            raise VerificationError(
                f"{item_context}: duplicate claim endpoint in transition"
            )
        endpoints.add(old)
        if new is not None:
            endpoints.add(new)


# Repository-locating variables git exports to hooks.  If they leak into Lake's
# nested git calls inside .lake/packages/<dep>, Lake mistakes the dependency
# checkout for the outer repository, deletes and re-clones it, and the clone's
# checkout overwrites the outer index (observed 2026-08-20).  Strip them.
GIT_REPOSITORY_ENV = {
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_COMMON_DIR",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_PREFIX",
    "GIT_NAMESPACE",
}


def lake_environment() -> dict[str, str]:
    return {key: value for key, value in os.environ.items() if key not in GIT_REPOSITORY_ENV}


def audit_temp_directory(root: Path = ROOT) -> Path:
    """Return the private, ignored directory for ephemeral Lean audit sources."""
    lake_directory = root / ".lake"
    directory = lake_directory / "no-cheat-tmp"

    def validate_directory(candidate: Path, resolved_root: Path) -> None:
        if candidate.is_symlink():
            raise VerificationError(
                f"unsafe audit temporary directory is a symlink: {candidate}"
            )
        resolved = candidate.resolve(strict=True)
        try:
            resolved.relative_to(resolved_root)
        except ValueError as exc:
            raise VerificationError(
                f"audit temporary directory escapes repository: {candidate}"
            ) from exc
        metadata = candidate.stat()
        if not stat.S_ISDIR(metadata.st_mode):
            raise VerificationError(f"audit temporary path is not a directory: {candidate}")
        if metadata.st_mode & 0o022:
            raise VerificationError(
                f"audit temporary directory is writable by other users: {candidate}"
            )
        if hasattr(os, "getuid") and metadata.st_uid != os.getuid():
            raise VerificationError(
                f"audit temporary directory has unexpected owner: {candidate}"
            )

    try:
        lake_directory.mkdir(mode=0o700, parents=True, exist_ok=True)
        resolved_root = root.resolve()
        validate_directory(lake_directory, resolved_root)
        directory.mkdir(mode=0o700, exist_ok=True)
        validate_directory(directory, resolved_root)
    except OSError as exc:
        raise VerificationError(f"cannot prepare audit temporary directory {directory}: {exc}") from exc
    return directory


def fsync_directory(directory: Path) -> None:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    descriptor = os.open(directory, flags)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def write_receipt_atomic(receipt_path: Path, rendered: str) -> None:
    """Durably replace a receipt without a predictable temporary-file race."""
    parent = receipt_path.parent
    temporary_path: Path | None = None
    try:
        parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=parent,
            prefix=f".{receipt_path.name}.no-cheat-",
            suffix=".tmp",
            delete=False,
        ) as handle:
            temporary_path = Path(handle.name)
            handle.write(rendered)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_path, receipt_path)
        temporary_path = None
        fsync_directory(parent)
    except OSError as exc:
        raise VerificationError(f"cannot write receipt {receipt_path}: {exc}") from exc
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)


def run(
    command: list[str],
    timeout: int,
    failure_context: Callable[[str], str] | None = None,
) -> tuple[str, float]:
    started = time.monotonic()
    try:
        result = subprocess.run(
            command,
            cwd=ROOT,
            env=lake_environment(),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise VerificationError(
            f"command timed out after {timeout}s: {' '.join(command)}"
        ) from exc
    elapsed = time.monotonic() - started
    if result.returncode != 0:
        context = failure_context(result.stdout) if failure_context else ""
        raise VerificationError(
            f"command failed ({result.returncode}): {' '.join(command)}"
            + (f"\n{context}" if context else "")
            + f"\n{result.stdout}"
        )
    return result.stdout, elapsed


def load_manifest(path: Path) -> tuple[list[Target], set[str], dict[str, Any]]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise VerificationError(f"cannot read manifest {path}: {exc}") from exc
    if not isinstance(raw, dict):
        raise VerificationError(f"{path}: manifest must be a JSON object")
    unexpected_top_level = set(raw) - MANIFEST_TOP_LEVEL_KEYS
    if unexpected_top_level:
        raise VerificationError(
            f"{path}: unsupported top-level key(s): "
            + ", ".join(sorted(unexpected_top_level))
        )
    if type(raw.get("version")) is not int or raw["version"] not in (1, 2):
        raise VerificationError(f"{path}: expected manifest version 1 or 2")
    manifest_version = raw["version"]
    if "targets" not in raw or not isinstance(raw["targets"], list):
        raise VerificationError(f"{path}: targets must be a list")
    # The explicit field is part of the reviewed transition surface: omission
    # must not silently mean the same policy as an intentionally empty list.
    if "allowed_axioms" not in raw:
        raise VerificationError(f"{path}: allowed_axioms must be an explicit list of strings")
    raw_allowed = raw["allowed_axioms"]
    if not isinstance(raw_allowed, list) or any(
        not isinstance(axiom, str) or has_control_character(axiom)
        for axiom in raw_allowed
    ):
        raise VerificationError(f"{path}: allowed_axioms must be a list of strings")
    if len(set(raw_allowed)) != len(raw_allowed):
        raise VerificationError(f"{path}: allowed_axioms must not contain duplicates")
    allowed = set(raw_allowed)
    unsupported = allowed - DEFAULT_ALLOWED_AXIOMS
    if unsupported:
        raise VerificationError(
            f"{path}: cannot allow nonstandard axioms: "
            + ", ".join(sorted(unsupported))
        )
    validate_reviewed_claim_deltas(raw.get("reviewed_claim_deltas", []), str(path))
    targets: list[Target] = []
    for index, item in enumerate(raw["targets"], 1):
        if not isinstance(item, dict):
            raise VerificationError(f"{path}: target {index} must be an object")
        target_keys = (
            MANIFEST_V2_TARGET_KEYS
            if manifest_version == 2
            else MANIFEST_V1_TARGET_KEYS
        )
        unexpected_target_keys = set(item) - target_keys
        if unexpected_target_keys:
            raise VerificationError(
                f"{path}: target {index} has unsupported key(s): "
                + ", ".join(sorted(unexpected_target_keys))
            )
        missing = {
            key for key in ("module", "declaration", "expected_type") if not item.get(key)
        }
        if missing:
            raise VerificationError(
                f"{path}: target {index} lacks {', '.join(sorted(missing))}"
            )
        raw_universes = None
        if manifest_version == 2:
            if "universes" not in item:
                raise VerificationError(
                    f"{path}: target {index}: manifest version 2 requires universes"
                )
            raw_universes = item["universes"]
            if not isinstance(raw_universes, list):
                raise VerificationError(
                    f"{path}: target {index}: universes must be a list of Lean identifiers"
                )
        target = Target(
            module=item["module"],
            declaration=item["declaration"],
            expected_type=item["expected_type"],
            task_id=item.get("task_id", ""),
            universes=(None if raw_universes is None else tuple(raw_universes)),
        )
        validate_target(target, f"{path}: target {index}")
        targets.append(target)
    validate_targets(targets, str(path))
    return targets, allowed, raw


def audit_source(target: Target) -> str:
    if target.universes is None:
        return f"""import {target.module}

set_option autoImplicit false

#check @{target.declaration}

example : {target.expected_type} := by
  exact {target.declaration}

#print axioms {target.declaration}
"""
    reference = explicit_target_reference(target)
    marker = f"_NoCheatSingleAudit.target_{canonical_json_sha256(target_serializable(target))[:16]}"
    leaf = marker.rsplit(".", 1)[1]
    universe_command = (
        f"universe {' '.join(target.universes)}\n" if target.universes else ""
    )
    return f"""import {target.module}
import Lean
import Mathlib.Tactic.RunCmd

set_option autoImplicit false

{universe_arity_guard_source(target.declaration, len(target.universes))}
section
{universe_command}
#check {reference}

namespace _NoCheatSingleAudit
theorem {leaf} : ({target.expected_type}) := by
  exact {reference}
end _NoCheatSingleAudit
end

{universe_arity_guard_source(marker, len(target.universes))}
#print axioms {target.declaration}
"""


def explicit_target_reference(target: Target) -> str:
    """Apply the declaration to the reviewed universe parameters in order."""
    if not target.universes:
        return f"@{target.declaration}"
    return f"@{target.declaration}.{{{', '.join(target.universes)}}}"


def universe_arity_guard_source(declaration: str, expected: int) -> str:
    """Assert the environment's rigid universe-parameter arity for one constant."""
    return "\n".join(
        [
            "run_cmd",
            f"  let info ← Lean.getConstInfo `{declaration}",
            f"  unless info.levelParams.length == {expected} do",
            '    throwError "universe guard: declaration universe arity mismatch"',
        ]
    )


def batch_target_marker(target: Target, index: int) -> str:
    """Return a Lean-safe, unique receipt-to-output identifier for one target."""
    digest = canonical_json_sha256(target_serializable(target))[:16]
    return f"_NoCheatBatchAudit.target_{index}_{digest}"


def batch_target_probe_source(target: Target, marker: str) -> str:
    """The exact per-target segment included in a module's batch audit."""
    leaf = marker.rsplit(".", 1)[1]
    if target.universes is None:
        return "\n".join(
            [
                f"-- verifier target marker: {marker}",
                f"#check @{target.declaration}",
                "",
                "namespace _NoCheatBatchAudit",
                f"theorem {leaf} : {target.expected_type} := by",
                f"  exact {target.declaration}",
                "end _NoCheatBatchAudit",
                "",
                f"#print axioms {marker}",
                "",
            ]
        )
    reference = explicit_target_reference(target)
    lines = [
        f"-- verifier target marker: {marker}",
        universe_arity_guard_source(target.declaration, len(target.universes)),
        "section",
    ]
    if target.universes:
        lines.append(f"universe {' '.join(target.universes)}")
    lines.extend(
        [
            f"#check {reference}",
            "",
            "namespace _NoCheatBatchAudit",
            f"theorem {leaf} : ({target.expected_type}) := by",
            f"  exact {reference}",
            "end _NoCheatBatchAudit",
            "end",
            "",
            universe_arity_guard_source(marker, len(target.universes)),
            "",
            f"#print axioms {marker}",
            "",
        ]
    )
    return "\n".join(lines)


def batch_audit_source(
    module: str, targets: list[Target]
) -> tuple[str, list[range], list[str]]:
    """Render all selected targets for one module in that module's environment.

    A target remains an independent ``#check``/exact-type/axiom probe.  The
    enclosing import is deliberately shared only by targets from the same
    module: importing unrelated modules can change elaboration of unqualified
    names in a reviewed expected type.
    """
    if not targets:
        raise VerificationError(f"cannot render an empty audit batch for {module}")
    if any(target.module != module for target in targets):
        raise VerificationError("audit batch mixes targets from different modules")

    lines = [f"import {module}"]
    if any(target.universes is not None for target in targets):
        lines.append("import Lean")
        lines.append("import Mathlib.Tactic.RunCmd")
    lines.extend(["", "set_option autoImplicit false", ""])
    target_lines: list[range] = []
    markers: list[str] = []
    for index, target in enumerate(targets, 1):
        start = len(lines) + 1
        marker = batch_target_marker(target, index)
        lines.extend(batch_target_probe_source(target, marker).splitlines())
        target_lines.append(range(start, len(lines) + 1))
        markers.append(marker)
    return "\n".join(lines), target_lines, markers


def reject_forbidden_output(output: str) -> None:
    for marker, meaning in FORBIDDEN_OUTPUT.items():
        if marker in output:
            raise VerificationError(f"no-cheat audit found {meaning}: {marker}")


def parse_axioms(output: str, allowed: set[str]) -> list[str]:
    reject_forbidden_output(output)
    blocks = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output, re.S)
    no_axioms = "does not depend on any axioms" in output
    if len(blocks) + int(no_axioms) != 1:
        raise VerificationError(
            "expected exactly one #print axioms result; Lean output was:\n" + output
        )
    found = set()
    if blocks:
        found = {item.strip() for item in blocks[0].split(",") if item.strip()}
    unexpected = found - allowed
    if unexpected:
        raise VerificationError(
            "unexpected axioms: " + ", ".join(sorted(unexpected))
        )
    return sorted(found)


def parse_batch_axioms(
    output: str, targets: list[Target], markers: list[str], allowed: set[str]
) -> list[list[str]]:
    """Parse target-marker-bound ``#print axioms`` output from a batch.

    Do not infer receipt attribution from the order Lean happened to print
    results.  A changed, duplicated, omitted, or reordered marker means the
    audit transcript cannot prove which result belongs to which target.
    """
    reject_forbidden_output(output)
    if len(markers) != len(targets) or len(set(markers)) != len(markers):
        raise VerificationError("batch audit has invalid target markers")
    result_pattern = re.compile(
        r"(?m)^'?"
        r"(?P<marker>[^'\r\n]+?)'?"
        r"\s+(?:depends on axioms:\s*\[(?P<axioms>[^]]*)\]"
        r"|(?P<no_axioms>does not depend on any axioms))"
    )
    observed = list(result_pattern.finditer(output))
    if len(observed) != len(targets):
        raise VerificationError(
            "expected exactly one #print axioms result for each batch target "
            f"({len(targets)} expected, {len(observed)} marked results found); "
            "Lean output was:\n" + output
        )
    observed_markers = [match.group("marker") for match in observed]
    if len(set(observed_markers)) != len(observed_markers):
        raise VerificationError(
            "duplicate batch target marker(s) in #print axioms output: "
            + ", ".join(
                marker
                for marker in sorted(set(observed_markers))
                if observed_markers.count(marker) > 1
            )
        )
    if observed_markers != markers:
        raise VerificationError(
            "batch target markers do not exactly match the rendered target order; "
            f"expected {markers}, found {observed_markers}"
        )
    results: list[list[str]] = []
    for match in observed:
        found = {
            item.strip()
            for item in (match.group("axioms") or "").split(",")
            if item.strip()
        }
        unexpected = found - allowed
        if unexpected:
            raise VerificationError(
                "unexpected axioms for batch target "
                f"{len(results) + 1} ({targets[len(results)].declaration}): "
                + ", ".join(sorted(unexpected))
            )
        results.append(sorted(found))
    return results


def batch_failure_context(
    output: str,
    audit_path: Path,
    module: str,
    targets: list[Target],
    target_lines: list[range],
) -> str:
    """Attach Lean locations in a failing temporary batch to reviewed targets."""
    locations = {
        int(match.group(1))
        for match in re.finditer(rf"{re.escape(str(audit_path))}:(\d+):\d+:", output)
    }
    affected = [
        (index, target)
        for index, (target, lines) in enumerate(zip(targets, target_lines), 1)
        if any(line in lines for line in locations)
    ]
    if affected:
        rendered = ", ".join(
            f"target {index} ({target.declaration})" for index, target in affected
        )
        return f"batch audit failed in {module}; affected {rendered}"
    rendered = ", ".join(
        f"target {index} ({target.declaration})" for index, target in enumerate(targets, 1)
    )
    return f"batch audit failed in {module}; Lean emitted no mappable location (batch: {rendered})"


def module_source(module: str, root: Path = ROOT) -> Path | None:
    candidate = root / (module.replace(".", "/") + ".lean")
    return candidate if candidate.is_file() else None


def local_module_roots(root: Path = ROOT) -> frozenset[str]:
    """Top-level module names owned by this repository, read from its sources."""
    return frozenset(path.stem for path in root.glob("*.lean"))


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean comments, but not comment markers inside strings."""
    rendered: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index : index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                rendered.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                rendered.extend("  ")
                index += 2
            else:
                rendered.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif in_string:
            char = source[index]
            rendered.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif source[index] == '"':
            in_string = True
            rendered.append(" ")
            index += 1
        elif pair == "/-":
            depth = 1
            rendered.extend("  ")
            index += 2
        elif pair == "--":
            newline = source.find("\n", index)
            if newline == -1:
                rendered.extend(" " * (len(source) - index))
                break
            rendered.extend(" " * (newline - index))
            rendered.append("\n")
            index = newline + 1
        else:
            rendered.append(source[index])
            index += 1
    return "".join(rendered)


def normalize_lean_name(name: str) -> str:
    return re.sub(r"«([^»\r\n]+)»", r"\1", name)


def imported_modules(path: Path) -> list[str]:
    source = strip_lean_comments(path.read_text(encoding="utf-8"))
    return [normalize_lean_name(name) for name in IMPORT_COMMAND.findall(source)]


def local_import_closure(module: str, root: Path = ROOT) -> list[Path]:
    """Return the deterministic local Lean source closure of ``module``."""
    initial = module_source(module, root)
    if initial is None:
        raise VerificationError(f"local target module has no source file: {module}")
    pending = [module]
    seen_modules: set[str] = set()
    sources: set[Path] = set()
    local_roots = local_module_roots(root)
    while pending:
        current = pending.pop()
        if current in seen_modules:
            continue
        seen_modules.add(current)
        path = module_source(current, root)
        if path is None:
            if current.split(".", 1)[0] in local_roots:
                raise VerificationError(
                    f"local import has no source file (stale olean risk): {current}"
                )
            continue
        path = path.resolve()
        sources.add(path)
        pending.extend(imported_modules(path))
    return sorted(sources, key=lambda path: path.relative_to(root).as_posix())


def path_name(path: Path, root: Path = ROOT) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(root.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()


def closure_files(paths: list[Path], root: Path = ROOT) -> tuple[tuple[str, str], ...]:
    return tuple(
        (path_name(path, root), sha256_bytes(path.read_bytes()))
        for path in sorted(paths, key=lambda item: path_name(item, root))
    )


def closure_sha256(files: tuple[tuple[str, str], ...]) -> str:
    payload = "".join(f"{path}\0{digest}\n" for path, digest in files)
    return sha256_bytes(payload.encode("utf-8"))


def git_value(*args: str, root: Path = ROOT) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, text=True, capture_output=True, check=False
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or "git command failed"
        raise VerificationError(f"git {' '.join(args)} failed: {detail}")
    return result.stdout.strip()


def git_head_tree(root: Path = ROOT) -> tuple[str, dict[str, tuple[str, str]]]:
    head = git_value("rev-parse", "--verify", "HEAD^{commit}", root=root)
    if not re.fullmatch(r"[0-9a-fA-F]{40,64}", head):
        raise VerificationError(f"git returned an invalid HEAD object id: {head!r}")
    entries: dict[str, tuple[str, str]] = {}
    listing = git_value("ls-tree", "-r", "--full-tree", head, root=root)
    for line in listing.splitlines():
        try:
            metadata, path = line.split("\t", 1)
            mode, kind, object_id = metadata.split()
        except ValueError as exc:
            raise VerificationError(f"cannot parse git tree entry: {line!r}") from exc
        if kind == "blob":
            entries[path] = (mode, object_id)
    return head, entries


def worktree_blob_identity(path: Path, object_format: str) -> tuple[str, str]:
    try:
        data = path.read_bytes()
        mode_bits = path.stat().st_mode
    except OSError as exc:
        raise VerificationError(f"cannot read verification-bound file {path}: {exc}") from exc
    if not stat.S_ISREG(mode_bits):
        raise VerificationError(f"verification-bound path is not a regular file: {path}")
    mode = "100755" if mode_bits & 0o111 else "100644"
    try:
        digest = hashlib.new(object_format)
    except ValueError as exc:
        raise VerificationError(
            f"unsupported git object format: {object_format!r}"
        ) from exc
    digest.update(f"blob {len(data)}\0".encode("ascii"))
    digest.update(data)
    return mode, digest.hexdigest()


def verification_input_paths(
    manifest_path: Path | None = None,
    root: Path = ROOT,
    verifier_path: Path | None = None,
) -> list[Path]:
    """Files that determine how the Lean source closure is interpreted."""
    paths = [
        verifier_path or Path(__file__).resolve(),
        root / "lean-toolchain",
        root / "lakefile.lean",
        root / "lake-manifest.json",
    ]
    if manifest_path is not None:
        paths.append(manifest_path.resolve())
    missing = [path_name(path, root) for path in paths if not path.is_file()]
    if missing:
        raise VerificationError(
            "missing verification provenance input(s): " + ", ".join(missing)
        )
    return sorted({path.resolve() for path in paths}, key=lambda path: path_name(path, root))


def assert_manifest_matches_loaded(
    manifest_path: Path | None, expected_canonical_sha256: str | None
) -> None:
    if manifest_path is None:
        if expected_canonical_sha256 is not None:
            raise VerificationError("manifest hash supplied without a manifest path")
        return
    try:
        current = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise VerificationError(f"cannot re-read manifest {manifest_path}: {exc}") from exc
    if (
        expected_canonical_sha256 is not None
        and canonical_json_sha256(current) != expected_canonical_sha256
    ):
        raise VerificationError("manifest changed between selection and verification")


def source_snapshot(paths: list[Path], root: Path = ROOT) -> SourceSnapshot:
    files = closure_files(paths, root)
    names = {path for path, _ in files}
    paths_by_name = {path_name(path, root): path for path in paths}
    head, in_head = git_head_tree(root)
    object_format = git_value("rev-parse", "--show-object-format", root=root)
    absent = names - set(in_head)
    modified = {
        name
        for name in names - absent
        if worktree_blob_identity(paths_by_name[name], object_format) != in_head[name]
    }
    untracked = set(
        git_value("ls-files", "--others", "--exclude-standard", root=root).splitlines()
    )
    return SourceSnapshot(
        git_head=head,
        closure_files=files,
        modified=tuple(sorted(modified)),
        untracked=tuple(sorted(names & untracked)),
        absent_from_head=tuple(sorted(absent)),
    )


def require_clean_snapshot(snapshot: SourceSnapshot) -> None:
    problems = []
    if snapshot.modified:
        problems.append("modified: " + ", ".join(snapshot.modified))
    if snapshot.untracked:
        problems.append("untracked: " + ", ".join(snapshot.untracked))
    if snapshot.absent_from_head:
        problems.append("absent from HEAD: " + ", ".join(snapshot.absent_from_head))
    if problems:
        raise VerificationError(
            "promotion requires clean, commit-reproducible verification inputs; "
            + "; ".join(problems)
        )


def assert_snapshot_unchanged(before: SourceSnapshot, after: SourceSnapshot) -> None:
    if before.git_head != after.git_head:
        raise VerificationError(
            f"git HEAD changed during verification: {before.git_head} -> {after.git_head}"
        )
    if before.closure_files != after.closure_files:
        raise VerificationError("verification-bound files changed during verification")
    if (
        before.modified,
        before.untracked,
        before.absent_from_head,
    ) != (
        after.modified,
        after.untracked,
        after.absent_from_head,
    ):
        raise VerificationError("Lean source git state changed during verification")


def verify(
    targets: list[Target],
    allowed: set[str],
    timeout: int,
    require_clean_closure: bool = False,
    manifest_path: Path | None = None,
    manifest_canonical_sha256: str | None = None,
) -> dict[str, Any]:
    if not targets:
        raise VerificationError("no verification targets selected")
    validate_targets(targets, "verify input")

    if manifest_path is not None and manifest_canonical_sha256 is None:
        try:
            manifest_canonical_sha256 = canonical_json_sha256(
                json.loads(manifest_path.read_text(encoding="utf-8"))
            )
        except (OSError, json.JSONDecodeError) as exc:
            raise VerificationError(f"cannot read manifest {manifest_path}: {exc}") from exc

    target_closures = {
        target: local_import_closure(target.module) for target in targets
    }
    union_closure = sorted(
        {path for paths in target_closures.values() for path in paths},
        key=lambda path: path.relative_to(ROOT).as_posix(),
    )
    provenance_paths = verification_input_paths(manifest_path)
    assert_manifest_matches_loaded(manifest_path, manifest_canonical_sha256)
    bound_paths = sorted(
        set(union_closure) | set(provenance_paths), key=lambda path: path_name(path)
    )
    before = source_snapshot(bound_paths)
    if require_clean_closure:
        require_clean_snapshot(before)

    lean_names = {path_name(path) for path in union_closure}
    provenance_names = {path_name(path) for path in provenance_paths}
    lean_before_files = tuple(
        item for item in before.closure_files if item[0] in lean_names
    )
    provenance_before_files = tuple(
        item for item in before.closure_files if item[0] in provenance_names
    )
    before_digests = dict(before.closure_files)

    build_seconds: dict[str, float] = {}
    for module in dict.fromkeys(target.module for target in targets):
        _, elapsed = run(["lake", "build", module], timeout)
        build_seconds[module] = round(elapsed, 3)

    # Receipt compatibility: v3 intentionally replaces v2's per-target
    # ``audit_seconds``/``audit_source_sha256`` fields.  Those values are now
    # correctly scoped under ``audit_batches`` (one Lean process/source per
    # module), along with a hash of the captured Lean transcript; target rows
    # retain target-local evidence and that batch link.
    batch_results: dict[Target, tuple[list[str], str, str]] = {}
    audit_batches: list[dict[str, Any]] = []
    temporary_directory = audit_temp_directory()
    for module in dict.fromkeys(target.module for target in targets):
        module_targets = [target for target in targets if target.module == module]
        source, target_lines, markers = batch_audit_source(module, module_targets)
        with tempfile.NamedTemporaryFile(
            mode="w",
            suffix=".lean",
            prefix="no_cheat_",
            encoding="utf-8",
            dir=temporary_directory,
            delete=False,
        ) as handle:
            handle.write(source)
            audit_path = Path(handle.name)
        try:
            output, elapsed = run(
                ["lake", "env", "lean", str(audit_path)],
                timeout,
                failure_context=lambda output: batch_failure_context(
                    output, audit_path, module, module_targets, target_lines
                ),
            )
        finally:
            audit_path.unlink(missing_ok=True)
        for target, marker, axioms in zip(
            module_targets,
            markers,
            parse_batch_axioms(output, module_targets, markers, allowed),
        ):
            batch_results[target] = (axioms, marker, batch_target_probe_source(target, marker))
        audit_batches.append(
            {
                "module": module,
                "audit_seconds": round(elapsed, 3),
                "audit_source_sha256": sha256_bytes(source.encode()),
                "audit_output_sha256": sha256_bytes(output.encode("utf-8")),
                "target_markers": markers,
            }
        )

    results = []
    for target in targets:
        axioms, marker, target_probe = batch_results[target]
        source_path = module_source(target.module)
        target_names = {path_name(path) for path in target_closures[target]}
        target_files = tuple(
            item for item in lean_before_files if item[0] in target_names
        )
        results.append(
            {
                **target_serializable(target),
                "axioms": axioms,
                "batch_module": target.module,
                "batch_target_marker": marker,
                "target_probe_source_sha256": sha256_bytes(target_probe.encode()),
                "module_source": str(source_path.relative_to(ROOT)) if source_path else None,
                "module_source_sha256": (
                    before_digests[path_name(source_path)] if source_path else None
                ),
                "lean_source_closure_sha256": closure_sha256(target_files),
                "lean_source_closure_files": [
                    {"path": path, "sha256": digest} for path, digest in target_files
                ],
            }
        )

    after_lean_paths = {
        path
        for target in targets
        for path in local_import_closure(target.module)
    }
    assert_manifest_matches_loaded(manifest_path, manifest_canonical_sha256)
    after_provenance_paths = verification_input_paths(manifest_path)
    after = source_snapshot(
        sorted(
            after_lean_paths | set(after_provenance_paths), key=lambda path: path_name(path)
        )
    )
    assert_snapshot_unchanged(before, after)
    commit_reproducible = not (
        before.modified or before.untracked or before.absent_from_head
    )

    return {
        "schema": "lean-no-cheat-receipt-v3",
        "verified": True,
        "repository": str(ROOT),
        "git_head": before.git_head,
        "verification_mode": (
            "commit-reproducible"
            if commit_reproducible
            else "diagnostic-only-dirty-closure"
        ),
        "commit_reproducible": commit_reproducible,
        "require_clean_closure": require_clean_closure,
        "closure_modified_files": sorted(set(before.modified) & lean_names),
        "closure_untracked_files": sorted(set(before.untracked) & lean_names),
        "closure_absent_from_head": sorted(set(before.absent_from_head) & lean_names),
        "lean_source_union_closure_sha256": closure_sha256(lean_before_files),
        "lean_source_union_closure_files": [
            {"path": path, "sha256": digest}
            for path, digest in lean_before_files
        ],
        "verification_inputs_sha256": closure_sha256(provenance_before_files),
        "verification_inputs": [
            {"path": path, "sha256": digest}
            for path, digest in provenance_before_files
        ],
        "verification_input_modified_files": sorted(
            set(before.modified) & provenance_names
        ),
        "verification_input_untracked_files": sorted(
            set(before.untracked) & provenance_names
        ),
        "verification_input_absent_from_head": sorted(
            set(before.absent_from_head) & provenance_names
        ),
        "manifest": (
            {
                "path": path_name(manifest_path),
                "sha256": before_digests[path_name(manifest_path)],
                "canonical_sha256": manifest_canonical_sha256,
            }
            if manifest_path is not None
            else None
        ),
        "allowed_axioms": sorted(allowed),
        "build_seconds": build_seconds,
        "audit_batches": audit_batches,
        "targets": results,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, help="reviewed JSON target manifest")
    parser.add_argument("--module", action="append", help="select manifest module")
    parser.add_argument("--declaration", help="direct-mode declaration")
    parser.add_argument("--expected-type", help="direct-mode exact Lean type")
    parser.add_argument("--receipt", type=Path, help="write JSON receipt atomically")
    parser.add_argument(
        "--require-clean-closure",
        action="store_true",
        help="fail unless the Lean closure, verifier, manifest, and environment are clean",
    )
    parser.add_argument("--timeout", type=int, default=1800, help="seconds per command")
    args = parser.parse_args()

    try:
        manifest_path = None
        manifest_canonical_sha256 = None
        if args.manifest:
            targets, allowed, manifest_raw = load_manifest(args.manifest)
            manifest_path = args.manifest.resolve()
            manifest_canonical_sha256 = canonical_json_sha256(manifest_raw)
            if args.declaration or args.expected_type:
                raise VerificationError(
                    "--declaration/--expected-type cannot be combined with --manifest"
                )
            if args.module:
                selected = set(args.module)
                targets = [target for target in targets if target.module in selected]
                missing = selected - {target.module for target in targets}
                if missing:
                    raise VerificationError(
                        "manifest has no targets for: " + ", ".join(sorted(missing))
                    )
        else:
            if not (args.module and len(args.module) == 1 and args.declaration and args.expected_type):
                raise VerificationError(
                    "direct mode requires one --module, --declaration, and --expected-type"
                )
            targets = [Target(args.module[0], args.declaration, args.expected_type)]
            allowed = DEFAULT_ALLOWED_AXIOMS

        receipt = verify(
            targets,
            allowed,
            args.timeout,
            require_clean_closure=args.require_clean_closure,
            manifest_path=manifest_path,
            manifest_canonical_sha256=manifest_canonical_sha256,
        )
        rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
        if args.receipt:
            write_receipt_atomic(args.receipt, rendered)
        print(rendered, end="")
        return 0
    except VerificationError as exc:
        print(f"verification failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
