#!/usr/bin/env python3
"""Regenerate the Lean links of the manuscript from this repository.

The map ``links.json`` next to this script is the machine-readable record of
which Lean declaration backs which paper label: every displayed equation and
named proof step (``equations_and_steps``) and every theorem, proposition,
lemma, and remark (``statements``).  Declarations are addressed by
``(file, namespace, name)``; line numbers are never stored but recomputed from
the Lean sources at the repository root, so the script is rerun whenever the
sources move.

Two blocks of the manuscript are rewritten in place:

* between ``% BEGIN GENERATED LEAN EQUATION LINKS`` and its END marker, one
  ``\\DeclareLeanEquation{label}{file}{line}`` per equation and proof step
  (``lean_equation_links.sty`` turns the equation number, respectively the
  step heading, into a hyperlink);
* between ``% BEGIN GENERATED LEAN NAVIGATION APPENDIX`` and its END marker,
  the appendix "Lean Certificates": the five contributions as Lean source
  (definitions before each theorem statement, proofs replaced by links) and
  the statement-to-Lean table.

Every in-text ``\\leandecl{file}{line}{name}`` / ``\\leanlinkdecl`` pointer
also has its line number refreshed from the declaration name.

It also rewrites EQUATIONS.md at the repository root, the same map as a
Markdown table with GitHub links.

Usage:  python3 paper_tools/gen_lean_links.py [--tex paper/main.tex]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]          # the Lean sources live here
LINKS = Path(__file__).resolve().parent / "links.json"

DECL = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected)\s+)*"
    r"(theorem|lemma|abbrev|def|inductive)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
NS = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
END = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
SEC = re.compile(r"^(?:noncomputable\s+)?section")

CONTRIBUTIONS = [
    ("Main", "Benign loss landscape with linear skips", "thm:headline", 1),
    ("PlainTrap", "Spurious minima at arbitrary overparameterization", "thm:plain-trap", 2),
    ("Confinement", "Learning the teacher subspace", "prop:teacher-span-confinement", 3),
    ("EffectiveWidth", "Effective width", "prop:plain-collision-ceiling", 4),
    ("EmpiricalTransfer", "Transfer to empirical loss", "thm:fixed-radius-bridge", 5),
]

BOILERPLATE_SCOPE = (
    "Explicit canonical contract and its local proof; see the equation table "
    "for any chart, normalization or proof-variant qualifications."
)


# --------------------------------------------------------------------------
# Lean source indexing
# --------------------------------------------------------------------------

_index_cache: dict[str, dict[tuple[str, str], list[int]]] = {}


def lean_lines(file: str) -> list[str]:
    return (ROOT / file).read_text(encoding="utf-8").splitlines()


def decl_index(file: str) -> dict[tuple[str, str], list[int]]:
    """(namespace, name) -> 1-based header lines of every declaration."""
    if file in _index_cache:
        return _index_cache[file]
    out: dict[tuple[str, str], list[int]] = {}
    stack: list[tuple[str, str | None]] = []
    for k, line in enumerate(lean_lines(file)):
        m = NS.match(line)
        if m:
            stack.append(("ns", m.group(1)))
            continue
        if SEC.match(line):
            stack.append(("sec", None))
            continue
        if END.match(line):
            if stack:
                stack.pop()
            continue
        m = DECL.match(line)
        if m:
            ns = ".".join(n for kind, n in stack if kind == "ns" and n)
            out.setdefault((ns, m.group(2)), []).append(k + 1)
    _index_cache[file] = out
    return out


def line_of(link: dict) -> int:
    hits = decl_index(link["file"]).get((link["namespace"], link["decl"]), [])
    if len(hits) != 1:
        raise SystemExit(f"declaration {link} resolves to lines {hits}")
    return hits[0]


def href(link: dict, text: str | None = None) -> str:
    line = line_of(link)
    label = text or (
        tex_escape(link["file"]).replace("\\_", "\\_\\allowbreak{}")
        + f":\\allowbreak{{}}{line}"
    )
    return f"\\href{{\\leanbase/{link['file']}\\#L{line}}}{{{label}}}"


def pointer(file: str, qualified: str, text: str) -> str:
    """An in-text ``\\leanlinkdecl`` with a freshly computed line number."""
    ns, _, name = qualified.rpartition(".")
    line = line_of({"file": file, "namespace": ns, "decl": name})
    return f"\\leanlinkdecl{{{file}}}{{{line}}}{{{qualified}}}{{{text}}}"


def tex_escape(s: str) -> str:
    return s.replace("_", "\\_")


# --------------------------------------------------------------------------
# Lean listings for the five contributions
# --------------------------------------------------------------------------

def definitions_by_section() -> list[dict]:
    """Sections of Overview_definitions.lean: title, prose, code."""
    text = (ROOT / "Overview_definitions.lean").read_text(encoding="utf-8")
    body = text.split("-/", 1)[1]                    # drop the module docstring
    parts = re.split(r"^/-! ## ", body, flags=re.M)
    sections = []
    for part in parts[1:]:
        header, _, rest = part.partition("-/")
        title, _, prose = header.partition("\n")
        blocks = [
            b for b in lean_chunks(rest.splitlines())
            if not re.match(r"^(namespace|end|open)\b", b[0])
        ]
        code = "\n\n".join("\n".join(b) for b in blocks)
        sections.append({"title": title.strip(), "prose": prose.strip(), "code": code})
    return sections


def lean_chunks(lines: list[str]) -> list[list[str]]:
    """Docstring-aware chunks: a `/-- ... -/` comment stays with the
    declaration that follows it, even across blank lines."""
    chunks: list[list[str]] = []
    cur: list[str] = []
    in_doc = False
    for line in lines:
        if in_doc:
            cur.append(line)
            if "-/" in line:
                in_doc = False
            continue
        if line.lstrip().startswith("/--"):
            if cur:
                chunks.append(cur)
            cur = [line]
            in_doc = "-/" not in line
            continue
        if line.strip() == "":
            if cur and not cur[-1].rstrip().endswith("-/"):
                chunks.append(cur)
                cur = []
            continue
        cur.append(line)
    if cur:
        chunks.append(cur)
    return chunks


def theorems() -> dict[str, dict]:
    """Docstring, statement (without proof), and proof of each theorem."""
    lines = lean_lines("Overview_theorems.lean")
    out: dict[str, dict] = {}
    for block in lean_chunks(lines):
        heads = [i for i, l in enumerate(block) if l.startswith("theorem ")]
        if not heads:
            continue
        h = heads[0]
        name = block[h].split()[1]
        doc = block[:h]
        stmt_end = next(
            i for i in range(h, len(block))
            if re.search(r":=(\s+by)?\s*$", block[i])
        )
        statement = block[h:stmt_end + 1]
        statement[-1] = re.sub(r"\s*:=(\s+by)?\s*$", "", statement[-1])
        proof = block[stmt_end + 1:]
        out[name] = {
            "doc": "\n".join(doc),
            "statement": "\n".join(statement),
            "proof": "\n".join(proof),
            "line": lines.index(block[h]) + 1,
        }
    return out


LITERATE_OK = set("ℝℕℤ∀∃∧∨¬→↔↦×‖⟪⟫⟨⟩∑∫⁻¹•∘≤≥≠∈∉⊆πθβγδετ αμσω₀₁₂𝓝ᶠ∞")


def check_literate(code: str, where: str) -> None:
    bad = sorted({c for c in code if ord(c) > 127 and c not in LITERATE_OK})
    if bad:
        raise SystemExit(f"{where}: add literate rules for {' '.join(bad)}")


# Characters outside the Basic Multilingual Plane (four UTF-8 bytes) defeat
# listings' literate table under pdflatex; they go through escapeinside.
ASTRAL = {"𝓝": "(*@$\\mathcal{N}$@*)"}


def listing(code: str, where: str) -> str:
    check_literate(code, where)
    for char, tex in ASTRAL.items():
        code = code.replace(char, tex)
    return "\\begin{lstlisting}[style=lean]\n" + code + "\n\\end{lstlisting}"


def theorems_index() -> dict[str, dict]:
    idx = decl_index("Theorems.lean")
    return {
        name: {"file": "Theorems.lean", "namespace": ns, "decl": name}
        for (ns, name) in idx
        if ns == "PaperLeanFormalization.Theorems"
    }


def contributions_tex(links: dict) -> str:
    sections = definitions_by_section()
    thms = theorems()
    thm_links = theorems_index()
    local_of_entry = {
        row["entry"]["decl"]: row["local"]
        for row in links["statements"]
        if row.get("entry") and row.get("local")
    }
    by_number = {}
    model = None
    for s in sections:
        m = re.match(r"(\d)\.", s["title"])
        if m:
            by_number[int(m.group(1))] = s
        else:
            model = s
    out = []
    out.append("\\subsection{The five contributions in Lean}")
    out.append("\\label{app:lean-contributions}")
    out.append(
        "The five theorems of \\texttt{Overview\\_theorems.lean} are printed "
        "below in the order of \\Cref{sec:contributions}, each preceded by the "
        "definitions from \\texttt{Overview\\_definitions.lean} that its "
        "statement introduces. Every proof in that file is a one-line delegation to "
        "the statement index \\texttt{Theorems.lean}; the listings omit these "
        "proofs and link to them instead. The code is reproduced verbatim, with "
        "Lean's Unicode notation typeset as the editor shows it: "
        "\\lstinline[style=lean]|⟪w i, x⟫_ℝ| is the inner product "
        "$\\ip{w_i}{x}$, \\lstinline[style=lean]|‖x‖| the Euclidean norm, "
        "\\lstinline[style=lean]|Fin n → ℝ| a real vector indexed by "
        "$\\{0,\\dots,n-1\\}$, and \\lstinline[style=lean]|∫ x : Vec d, f x| "
        "the Lebesgue integral over $\\R^d$."
    )
    out.append("")
    out.append("\\subsubsection{The model}")
    out.append(
        "Both features, the Gaussian input law, and the two population losses "
        "\\eqref{eq:q-losses} are fixed once; every contribution is stated in "
        "these terms. Masses are signed real numbers: nonnegativity is an "
        "assumption at a candidate, never a constraint on its neighborhood. "
        "The losses are literal Bochner integrals, whose value is $0$ for a "
        "non-integrable integrand, so a reader should check that their integrands "
        "are integrable: the loss--kernel identity behind "
        "\\Cref{lem:pair-moments} and \\Cref{prop:loss_in_residual} is proved from "
        + pointer("Preliminaries.lean",
                  "PaperLeanFormalization.Preliminaries.gaussian_loss_eq_kernel_energy_of_pair_moment",
                  "a bridge")
        + " that assumes integrability of every feature pair, discharged by "
        + pointer("Preliminaries.lean",
                  "PaperLeanFormalization.Preliminaries.centered_feature_pair_integrable",
                  "\\texttt{centered\\_feature\\_pair\\_integrable}")
        + " and "
        + pointer("Preliminaries.lean",
                  "PaperLeanFormalization.Preliminaries.gaussian_plain_pair_integrable",
                  "\\texttt{gaussian\\_plain\\_pair\\_integrable}")
        + "; the squared centered residual and its product with the linear skip are "
        "integrable by "
        + pointer("Skip.lean", "PaperLeanFormalization.Skip.centered_residual_square_integrable",
                  "\\texttt{centered\\_residual\\_square\\_integrable}")
        + " and "
        + pointer("Skip.lean", "PaperLeanFormalization.Skip.linear_centered_residual_integrable",
                  "\\texttt{linear\\_centered\\_residual\\_integrable}")
        + "; and the strict inequality "
        "$0<\\LR$ in \\Cref{thm:plain-trap} is a Lean-checked witness that the "
        "losses are not identically zero."
    )
    out.append(listing(model["code"], "model"))
    bridges = {
        1: (
            "\\Cref{thm:headline} is the population statement of the paper's title: "
            "with a learned linear skip, a non-negative local minimum of the skip loss "
            "against a positive coplanar teacher network has zero loss whenever the "
            "student network is at least as wide. The skip loss is the only new definition."
        ),
        2: (
            "\\Cref{thm:plain-trap} needs the fixed planar trap teacher network, the planar "
            "direction $e(\\theta)$, and strict local minimality on the unit-direction "
            "parameter space; its three clauses are exactly the theorem's three "
            "conclusions."
        ),
        3: (
            "\\Cref{prop:teacher-span-confinement} holds for both features, so the loss "
            "is selected by the \\lstinline[style=lean]|Model|. The conclusion is "
            "containment of every positive-mass student direction in the teacher span."
        ),
        4: (
            "\\Cref{prop:plain-collision-ceiling} is stated in the plane with directions "
            "\\lstinline[style=lean]|Angle θ| and needs no further definition: a critical "
            "point is a zero of the Fréchet derivative in the mass and angle coordinates, "
            "and oriented directions are counted with period $2\\pi$. "
            "The hypothesis is written with Mathlib's \\lstinline[style=lean]|fderiv|, "
            "which is $0$ at a point of non-differentiability; it is not vacuous here, "
            "because in mass--angle coordinates the plain loss is an affine rescaling of "
            "the finite kernel loss ("
            + pointer("Plain.lean", "PaperLeanFormalization.Plain.plain_loss_eq_excess_div",
                      "\\texttt{plain\\_loss\\_eq\\_excess\\_div}")
            + "), which is globally $C^2$ ("
            + pointer("Plain.lean", "PaperLeanFormalization.Plain.ParameterCalculus.loss_contDiff_two",
                      "\\texttt{loss\\_contDiff\\_two}")
            + "); the hypothesis therefore states that the genuine Fréchet derivative "
            "vanishes, equivalently \\lstinline[style=lean]|HasFDerivAt … 0 (s, θ)|."
        ),
        5: (
            "\\Cref{thm:fixed-radius-bridge} replaces the Gaussian law by a finite dataset. "
            "The definitions fix the empirical loss, the joint parameter distance through the "
            "matching skip, the accuracy condition against the Gaussian functional on "
            "degree-two homogeneous tests, and the fixed-radius minimization hypothesis; the "
            "theorem then produces one tolerance $\\delta$ before the dataset, the labels, "
            "the skips, and the student network are chosen."
        ),
    }
    for name, title, label, number in CONTRIBUTIONS:
        sec = by_number[number]
        thm = thms[name]
        out.append("")
        out.append(f"\\subsubsection{{Contribution {number}: {title}}}")
        out.append(f"\\label{{app:lean-contribution-{number}}}")
        out.append(bridges[number])
        if sec["code"].strip():
            out.append(listing(sec["code"], f"definitions {number}"))
        code = thm["doc"] + "\n" + thm["statement"] if thm["doc"] else thm["statement"]
        out.append(listing(code, f"theorem {name}"))
        refs = []
        for word in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", thm["proof"]):
            if word in thm_links and word not in refs:
                refs.append(word)
        entry_links = []
        for r in refs:
            piece = href(thm_links[r], f"\\texttt{{{tex_escape(r)}}}")
            local = local_of_entry.get(r)
            if local:
                piece += f" (proof: {href(local)})"
            entry_links.append(piece)
        this = href(
            {"file": "Overview_theorems.lean", "namespace": "PaperLeanFormalization.Overview", "decl": name},
            f"\\texttt{{{tex_escape(name)}}}",
        )
        out.append(
            f"\\noindent The proof of {this} applies " + ", ".join(entry_links) + "."
        )
    return "\n".join(out)


# --------------------------------------------------------------------------
# Statement table
# --------------------------------------------------------------------------

def tex_labels(tex: str) -> set[str]:
    return set(re.findall(r"\\label\{([^}]*)\}", tex))


def statements_table(links: dict, tex: str) -> str:  # noqa: C901
    labels = tex_labels(tex)
    rows = []
    for name, title, label, number in CONTRIBUTIONS:
        if label not in labels:
            print(f"  skipping contribution row {label}: no label in tex", file=sys.stderr)
            continue
        entry = {"file": "Overview_theorems.lean", "namespace": "PaperLeanFormalization.Overview", "decl": name}
        rows.append(
            f"Contribution {number}: \\Cref{{{label}}} & {href(entry)} & "
            f"\\Cref{{app:lean-contribution-{number}}} & "
            f"{title}; exact contract of \\Cref{{{label}}}. \\\\"
        )
    for row in links["statements"]:
        present = [l for l in row["labels"] if l in labels]
        if not present:
            print(f"  skipping row {row['labels']}: no label in tex", file=sys.stderr)
            continue
        first = present[0]                    # labels of one environment print once
        same_env = [
            l for l in present[1:]
            if re.search(r"\\label\{" + re.escape(first) + r"\}\s*\n\s*\\label\{" + re.escape(l) + r"\}", tex)
        ]
        item = ", ".join(f"{row['kind']}~\\ref{{{l}}}" for l in present if l not in same_env)
        if row["clause"]:
            item += f"\\newline {row['clause']}"
        entry = href(row["entry"]) if row["entry"] else "---"
        local = href(row["local"]) if row["local"] else "---"
        scope = row["scope"]
        if scope == BOILERPLATE_SCOPE:
            scope = "Exact contract and local proof."
        rows.append(f"{item} & {entry} & {local} & {scope} \\\\")
    head = (
        "\\begingroup\n\\footnotesize\n\\setlength{\\tabcolsep}{3pt}\n"
        "\\renewcommand{\\arraystretch}{1.12}\n"
        "\\begin{longtable}{@{}>{\\raggedright\\arraybackslash}p{0.25\\linewidth}"
        ">{\\raggedright\\arraybackslash}p{0.19\\linewidth}"
        ">{\\raggedright\\arraybackslash}p{0.19\\linewidth}"
        ">{\\raggedright\\arraybackslash}p{0.31\\linewidth}@{}}\n"
        "\\toprule\nPaper statement / clause & Statement in Lean & Proof & Scope \\\\\n"
        "\\midrule\n\\endfirsthead\n\\toprule\n"
        "Paper statement / clause & Statement in Lean & Proof & Scope \\\\\n"
        "\\midrule\n\\endhead\n\\bottomrule\n\\endfoot\n"
    )
    return head + "\n".join(rows) + "\n\\end{longtable}\n\\endgroup"


# --------------------------------------------------------------------------
# Assembly
# --------------------------------------------------------------------------

def equation_links(links: dict, tex: str) -> str:
    labels = tex_labels(tex)
    steps = set(re.findall(r"\\pfstep\{([^}]*)\}", tex))
    lines = []
    for row in links["equations_and_steps"]:
        lab = row["label"]
        if lab not in labels and lab not in steps:
            print(f"  no \\label or \\pfstep for {lab}; link not declared", file=sys.stderr)
            continue
        if not row["source"]:
            continue
        # One link per label: the first listed source is the primary one; a
        # second \DeclareLeanEquation for the label would silently override it.
        if any(l.startswith(f"\\DeclareLeanEquation{{{lab}}}") for l in lines):
            continue
        lines.append(
            f"\\DeclareLeanEquation{{{lab}}}{{{row['source']['file']}}}"
            f"{{{line_of(row['source'])}}}"
        )
    declared = {re.match(r"\\DeclareLeanEquation\{([^}]*)\}", l).group(1) for l in lines}
    for lab in sorted(labels):
        if lab.startswith("eq:") and lab not in declared:
            print(f"  equation {lab} has no Lean link", file=sys.stderr)
    for lab in sorted(steps):
        if lab not in declared:
            print(f"  step {lab} has no Lean link", file=sys.stderr)
    return "\n".join(lines)


def appendix(links: dict, tex: str) -> str:
    parts = [
        "\\section{Lean Certificates}",
        "\\label{app:lean-certificates}",
        "Every theorem, proposition, lemma, displayed equation, and named proof step "
        "of this paper has a counterpart in the Lean~4 development at the root of the "
        "accompanying repository, which compiles against Mathlib~\\citep{mathlib2020} "
        "without admitted proofs; \\texttt{verify.py} there checks the five contribution "
        "theorems against their recorded statement types, and the build certificate "
        "confirms that no paper statement uses an axiom beyond propositional "
        "extensionality, choice, and quotient soundness. Throughout the paper, an "
        "equation number and a step heading are hyperlinks to the Lean declaration "
        "that states, respectively proves, that formula or step; the linked "
        "declaration may state a formula in the generality its proof needs, for "
        "instance without the unit-norm restriction of the display. "
        "The map from paper labels to Lean declarations is shipped as "
        "\\texttt{paper\\_tools/links.json}; this appendix and every equation link "
        "are generated from it by \\texttt{paper\\_tools/gen\\_lean\\_links.py}. "
        "\\Cref{app:lean-contributions} prints the five contribution theorems as "
        "Lean source; \\Cref{app:lean-statements} lists every paper statement with "
        "its Lean contract and proof.",
        "",
        contributions_tex(links),
        "",
        "\\subsection{Statements and proofs}",
        "\\label{app:lean-statements}",
        "The statement column is the paper-facing contract in \\texttt{Theorems.lean}; "
        "the proof column is the chapter declaration it delegates to. Separate rows "
        "distinguish clauses of one statement.",
        "",
        statements_table(links, tex),
    ]
    return "\n".join(parts)


# --------------------------------------------------------------------------
# Markdown navigation (EQUATIONS.md)
# --------------------------------------------------------------------------

def github_ref(link: dict) -> str:
    line = line_of(link)
    return f"[{link['namespace']}.{link['decl']}]({link['file']}#L{line})"


def equations_markdown(links: dict, tex: str) -> str:
    labels = tex_labels(tex)
    steps = set(re.findall(r"\\pfstep\{([^}]*)\}", tex))
    rows = ["| Paper label | Kind | Lean declaration | Scope |", "| --- | --- | --- | --- |"]
    for row in links["equations_and_steps"]:
        lab = row["label"]
        if (lab not in labels and lab not in steps) or not row["source"]:
            continue
        rows.append(f"| `{lab}` | {row['kind']} | {github_ref(row['source'])} | {row['scope']} |")
    srows = ["| Paper statement | Statement in Lean | Proof | Scope |", "| --- | --- | --- | --- |"]
    for row in links["statements"]:
        present = [l for l in row["labels"] if l in labels]
        if not present:
            continue
        item = ", ".join(f"`{l}`" for l in present) + (f" ({row['clause']})" if row["clause"] else "")
        entry = github_ref(row["entry"]) if row["entry"] else "—"
        local = github_ref(row["local"]) if row["local"] else "—"
        srows.append(f"| {row['kind']} {item} | {entry} | {local} | {row['scope']} |")
    return "\n".join([
        "# Manuscript and Lean navigation",
        "",
        "Generated by `paper_tools/gen_lean_links.py` from `paper_tools/links.json`; line",
        "numbers are recomputed from the Lean sources at every run. Each row names the",
        "declaration that states (equations, proof steps) or proves (statements) the",
        "paper item; the scope column records how the Lean statement relates to the",
        "display, for instance when it is proved in greater generality.",
        "",
        "## Equations and named proof steps",
        "",
        *rows,
        "",
        "## Statements and proofs",
        "",
        "The statement column is the paper-facing contract in `Theorems.lean`; the proof",
        "column is the chapter declaration it delegates to.",
        "",
        *srows,
        "",
    ])


POINTER = re.compile(
    r"\\(leandecl|leanlinkdecl)\{(?:paper_lean_formalization/)?([A-Za-z_]+\.lean)\}\{(\d+)\}\{([A-Za-z0-9_'.]+)\}"
)


def refresh_pointers(tex: str) -> str:
    """Recompute the line of every \\leandecl / \\leanlinkdecl from its name."""
    def sub(m: re.Match) -> str:
        macro, file, qualified = m.group(1), m.group(2), m.group(4)
        ns, _, name = qualified.rpartition(".")
        line = line_of({"file": file, "namespace": ns, "decl": name})
        return f"\\{macro}{{{file}}}{{{line}}}{{{qualified}}}"
    new, n = POINTER.subn(sub, tex)
    print(f"refreshed {n} in-text pointers", file=sys.stderr)
    return new


def replace_between(text: str, begin: str, end: str, payload: str) -> str:
    i = text.index(begin) + len(begin)
    j = text.index(end)
    return text[:i] + "\n" + payload + "\n" + text[j:]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex", type=Path, default=ROOT / "paper" / "main.tex",
                        help="manuscript to rewrite in place")
    args = parser.parse_args()
    links = json.loads(LINKS.read_text(encoding="utf-8"))
    tex = args.tex.read_text(encoding="utf-8")
    tex = refresh_pointers(tex)
    tex = replace_between(
        tex, "% BEGIN GENERATED LEAN EQUATION LINKS", "% END GENERATED LEAN EQUATION LINKS",
        equation_links(links, tex),
    )
    tex = replace_between(
        tex, "% BEGIN GENERATED LEAN NAVIGATION APPENDIX", "% END GENERATED LEAN NAVIGATION APPENDIX",
        appendix(links, tex),
    )
    args.tex.write_text(tex, encoding="utf-8")
    print("wrote", args.tex)
    (ROOT / "EQUATIONS.md").write_text(equations_markdown(links, tex), encoding="utf-8")
    print("wrote", ROOT / "EQUATIONS.md")


if __name__ == "__main__":
    main()
