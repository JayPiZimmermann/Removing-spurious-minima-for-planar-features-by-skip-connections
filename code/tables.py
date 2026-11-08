"""Aggregate the fixed 512-trial experiment and render its paper tables."""

import csv
import math
import statistics
from pathlib import Path


ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
TRIALS_PATH = RESULTS / "trials.csv"
SUMMARY_PATH = RESULTS / "summary.csv"
FITS_PATH = RESULTS / "fits.tex"
METRICS_PATH = RESULTS / "metrics.tex"

SETTINGS = ((3, 3, 2), (3, 3, 800), (5, 10, 2), (5, 10, 800))
MODELS = ("plain", "joint_skip", "profiled_skip")
MODEL_LABELS = {
    "plain": "Plain",
    "joint_skip": "Joint skip",
    "profiled_skip": "Profiled skip",
}
TRIAL_COUNT = 512
FIT_THRESHOLD = 1e-10
INPUT_FIELDS = (
    "m", "n", "d", "trial", "model", "fit", "relative_loss",
    "closest_teacher_swaps", "angular_distance_radians_per_unit",
    "latent_teacher_hash", "input_hash", "optimizer_success", "optimizer_message",
)
SUMMARY_FIELDS = (
    "m", "n", "d", "model", "trials", "fits",
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
        (m, n, d, trial, model)
        for m, n, d in SETTINGS
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
                model = row["model"]
                key = (m, n, d, trial, model)
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
                input_key = (m, n, d, trial)
                prior_input = input_hashes.setdefault(input_key, input_hash)
                if prior_input != input_hash:
                    _fail(f"line {line}: input_hash differs between model arms for {input_key!r}")
                # The same latent teacher realization is reused across ambient
                # dimensions for each (m,n,trial) setting.
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
    for m, n, d in SETTINGS:
        for model in MODELS:
            cells = [records[(m, n, d, trial, model)] for trial in range(TRIAL_COUNT)]
            rows.append({
                "m": m,
                "n": n,
                "d": d,
                "model": model,
                "trials": TRIAL_COUNT,
                "fits": sum(item["fit"] for item in cells),
                "closest_teacher_swaps_median": statistics.median(item["swaps"] for item in cells),
                "angular_distance_radians_per_unit_median": statistics.median(item["angle"] for item in cells),
            })
    return rows


def _latex_fits(rows):
    by_key = {(row["m"], row["n"], row["d"], row["model"]): row for row in rows}
    lines = [
        f"% Generated from trials.csv; fit counts use all {TRIAL_COUNT} trials per model.",
        r"\begin{tabular}{rrr rrr}",
        r"\toprule",
        r"$m$ & $n$ & $d$ & Plain & Joint skip & Profiled skip \\",
        r"\midrule",
    ]
    for m, n, d in SETTINGS:
        vals = [by_key[(m, n, d, model)]["fits"] for model in MODELS]
        lines.append(f"{m} & {n} & {d} & " + " & ".join(f"{v}/{TRIAL_COUNT}" for v in vals) + r" \\")
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    return "\n".join(lines)


def _latex_metrics(rows):
    lines = [
        f"% Generated from trials.csv; medians use all {TRIAL_COUNT} trials per model, including misses.",
        r"\begin{tabular}{rrr l r r r}",
        r"\toprule",
        r"$m$ & $n$ & $d$ & Model & Fits & \shortstack{Teacher\\switches} & \shortstack{Angular travel\\(rad/unit)} \\",
        r"\midrule",
    ]
    for row in rows:
        lines.append(
            f"{row['m']} & {row['n']} & {row['d']} & {MODEL_LABELS[row['model']]} & "
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
    FITS_PATH.write_text(_latex_fits(rows), encoding="utf-8")
    METRICS_PATH.write_text(_latex_metrics(rows), encoding="utf-8")


if __name__ == "__main__":
    main()
