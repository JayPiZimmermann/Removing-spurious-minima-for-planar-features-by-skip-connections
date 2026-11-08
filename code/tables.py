"""Aggregate the fixed 512-trial experiment and render its paper tables."""

import csv
import hashlib
import json
import math
import statistics
from pathlib import Path


ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
TRIALS_PATH = RESULTS / "trials.csv"
SUMMARY_PATH = RESULTS / "summary.csv"
TABLES_DIR = ROOT.parent / "paper" / "source" / "tables"
MAIN_TABLE_PATH = TABLES_DIR / "experiments_main.tex"
APPENDIX_TABLE_PATH = TABLES_DIR / "experiments_appendix.tex"
MANIFEST_PATH = RESULTS / "manifest.json"

SETTINGS = (
    (3, 3, 2, "planar"),
    (3, 3, 800, "random"),
    (3, 3, 800, "embedded"),
    (5, 10, 2, "planar"),
    (5, 10, 800, "random"),
    (5, 10, 800, "embedded"),
)
MODELS = ("plain", "joint_skip", "profiled_skip")
MODEL_LABELS = {
    "plain": "Plain",
    "joint_skip": "Joint skip",
    "profiled_skip": "Profiled skip",
}
TRIAL_COUNT = 512
FIT_THRESHOLD = 1e-10
INPUT_FIELDS = (
    "m", "n", "d", "teacher_geometry", "trial", "model", "fit", "relative_loss",
    "closest_teacher_swaps", "angular_distance_radians_per_unit",
    "latent_teacher_hash", "input_hash", "optimizer_success", "optimizer_message",
)
SUMMARY_FIELDS = (
    "m", "n", "d", "teacher_geometry", "model", "trials", "fits",
    "closest_teacher_swaps_median",
    "angular_distance_radians_per_unit_median",
)


def _fail(message: str) -> None:
    raise ValueError(f"Invalid trials.csv: {message}")


def _read_and_validate():
    records = {}
    input_hashes = {}
    teacher_hashes = {}
    expected = {
        (m, n, d, geometry, trial, model)
        for m, n, d, geometry in SETTINGS
        for trial in range(TRIAL_COUNT)
        for model in MODELS
    }

    try:
        stream = TRIALS_PATH.open(newline="", encoding="utf-8")
    except OSError as exc:
        _fail(f"cannot open trials.csv ({exc})")

    with stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != list(INPUT_FIELDS):
            _fail(f"expected columns {list(INPUT_FIELDS)!r}, got {reader.fieldnames!r}")
        for line, row in enumerate(reader, start=2):
            try:
                if None in row or any(value is None for value in row.values()):
                    _fail(f"line {line}: row has missing fields or extra columns")
                m, n, d, trial = (int(row[name]) for name in ("m", "n", "d", "trial"))
                geometry = row["teacher_geometry"]
                model = row["model"]
                key = (m, n, d, geometry, trial, model)
                if key not in expected:
                    _fail(f"line {line}: unexpected experiment key {key!r}")
                if key in records:
                    _fail(f"line {line}: duplicate experiment key {key!r}")

                fit = int(row["fit"])
                optimizer_success = int(row["optimizer_success"])
                if fit not in (0, 1) or optimizer_success not in (0, 1):
                    _fail(f"line {line}: fit and optimizer_success must be 0 or 1")
                loss = float(row["relative_loss"])
                swaps = float(row["closest_teacher_swaps"])
                angle = float(row["angular_distance_radians_per_unit"])
                if not all(math.isfinite(x) for x in (loss, swaps, angle)):
                    _fail(f"line {line}: loss and metrics must be finite")
                if loss < 0 or swaps < 0 or angle < 0:
                    _fail(f"line {line}: loss and metrics must be nonnegative")
                if not swaps.is_integer():
                    _fail(f"line {line}: closest_teacher_swaps must be integral")
                expected_fit = int(loss <= FIT_THRESHOLD)
                if fit != expected_fit:
                    _fail(f"line {line}: fit={fit} disagrees with loss threshold ({expected_fit})")

                input_hash = row["input_hash"]
                teacher_hash = row["latent_teacher_hash"]
                if (len(input_hash) != 64 or len(teacher_hash) != 64
                        or any(c not in "0123456789abcdefABCDEF" for c in input_hash + teacher_hash)):
                    _fail(f"line {line}: hashes must be 64-character hexadecimal strings")
                input_key = (m, n, d, geometry, trial)
                prior_input = input_hashes.setdefault(input_key, input_hash)
                if prior_input != input_hash:
                    _fail(f"line {line}: input_hash differs between model arms for {input_key!r}")
                # Planar (d=2) and embedded (d=800) are paired across ambient
                # dimensions. Random teachers have their own draw and are excluded.
                if geometry in ("planar", "embedded"):
                    teacher_key = (m, n, trial)
                    prior_teacher = teacher_hashes.setdefault(teacher_key, teacher_hash)
                    if prior_teacher != teacher_hash:
                        _fail(f"line {line}: latent_teacher_hash differs across dimensions for {teacher_key!r}")

                records[key] = {
                    "fit": fit,
                    "loss": loss,
                    "swaps": swaps,
                    "angle": angle,
                }
            except (TypeError, ValueError) as exc:
                if isinstance(exc, ValueError) and str(exc).startswith("Invalid trials.csv:"):
                    raise
                _fail(f"line {line}: malformed numeric field ({exc})")

    missing = expected.difference(records)
    if missing:
        _fail(f"missing {len(missing)} expected records; first missing key {min(missing)!r}")
    expected_count = len(SETTINGS) * TRIAL_COUNT * len(MODELS)
    if len(records) != expected_count:
        _fail(f"expected {expected_count} records, found {len(records)}")
    return records


def _summary_rows(records):
    rows = []
    for m, n, d, geometry in SETTINGS:
        for model in MODELS:
            cells = [records[(m, n, d, geometry, trial, model)] for trial in range(TRIAL_COUNT)]
            rows.append({
                "m": m,
                "n": n,
                "d": d,
                "teacher_geometry": geometry,
                "model": model,
                "trials": TRIAL_COUNT,
                "fits": sum(item["fit"] for item in cells),
                "closest_teacher_swaps_median": statistics.median(item["swaps"] for item in cells),
                "angular_distance_radians_per_unit_median": statistics.median(item["angle"] for item in cells),
            })
    return rows


def _latex_metrics(rows, conditions):
    by_key = {(row["m"], row["n"], row["d"], row["teacher_geometry"], row["model"]): row for row in rows}
    lines = [
        f"% Generated from trials.csv; medians use all {TRIAL_COUNT} trials per model, including misses.",
        r"\begin{tabular}{cc l r r r}",
        r"\toprule",
        r"$(m,n)$ & $d$ & Model & Fits & \shortstack{Closest-teacher\\switches} & \shortstack{Angular travel\\(rad/student unit)} \\",
        r"\midrule",
    ]
    groups = ((3, 3), (5, 10))
    for group_index, (m, n) in enumerate(groups):
        if group_index:
            lines.append(r"\midrule")
        for condition_index, (d, geometry, condition_label) in enumerate(conditions):
            if condition_index:
                lines.append(r"\cmidrule(lr){2-6}")
            for model_index, model in enumerate(MODELS):
                row = by_key[(m, n, d, geometry, model)]
                mn_cell = rf"\multirow{{{len(conditions) * len(MODELS)}}}{{*}}{{$({m},{n})$}}" if condition_index == 0 and model_index == 0 else ""
                d_cell = rf"\multirow{{3}}{{*}}{{{condition_label}}}" if model_index == 0 else ""
                lines.append(
                    f"{mn_cell} & {d_cell} & {MODEL_LABELS[model]} & "
                    f"{row['fits']}/{TRIAL_COUNT} & {row['closest_teacher_swaps_median']:g} & "
                    f"{row['angular_distance_radians_per_unit_median']:.2f} " + r"\\"
                )
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    return "\n".join(lines)


def main() -> None:
    records = _read_and_validate()
    rows = _summary_rows(records)
    RESULTS.mkdir(parents=True, exist_ok=True)

    with SUMMARY_PATH.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=SUMMARY_FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    TABLES_DIR.mkdir(parents=True, exist_ok=True)
    main_conditions = ((2, "planar", r"$2$"),
                       (800, "embedded", r"$800,\mathrm{emb}$"))
    appendix_conditions = ((2, "planar", r"$2$"),
                           (800, "random", r"$800$"),
                           (800, "embedded", r"$800,\mathrm{emb}$"))
    MAIN_TABLE_PATH.write_text(_latex_metrics(rows, main_conditions), encoding="utf-8")
    APPENDIX_TABLE_PATH.write_text(_latex_metrics(rows, appendix_conditions), encoding="utf-8")
    if MANIFEST_PATH.exists():
        manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
        manifest["table_source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        manifest["table_input_csv_sha256"] = hashlib.sha256(TRIALS_PATH.read_bytes()).hexdigest()
        MANIFEST_PATH.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
