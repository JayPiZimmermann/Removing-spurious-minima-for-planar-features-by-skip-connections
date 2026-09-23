#!/usr/bin/env python3
"""Generate the appendix figure of the pull, the push, and the step they add up to.

Fixed configuration, declared below: two unit-mass teachers at angles
beta = (0.2 pi, 0.8 pi) and two unit-mass students at
theta = (0.38 pi, 1.05 pi).
A hypothetical extra student ("probe") of mass 1 is placed at every probe
angle gamma.  Computed directly from the closed forms of the paper
(Section 2, eq. residual-loss-pairing-main / residual-potential-paper):

    Phi_C(t) = cos t * arcsin(cos t) + |sin t|,   Phi_R = Phi_C + (pi/2) cos t,
    pull_q(gamma) = sum_k s_k Phi_q(gamma - beta_k)              (teacher potential)
    push_q(gamma) = -sum_j c_j Phi_q(gamma - theta_j) - Phi_q(0) (negated student
                                                                  potential + self term)
    step_q(gamma) = pull_q(gamma) + push_q(gamma) = -F_q(gamma)  (residual of the
                                                     probe-adjoined configuration)

The probe's descent step is (2 pi) dot(theta) = step_q'(gamma) and
(2 pi) dot(c) = step_q(gamma); the arrows draw both components at one probe
angle, scaled by one common factor, teacher part and student part head to
tail with their sum.  Before drawing, the generator asserts the kernel branch
formulas, periodicities, the floor 1 <= Phi_C <= pi/2, the kernel bridge
Phi_R = Phi_C + (pi/2) cos t, Phi_q'(0) = 0 (the self term has zero angular
derivative), the pointwise identity step = pull + push = -(probe-adjoined
residual) computed two independent ways, the analytic kernel slope against
finite differences, and the exact head-to-tail arrow sum.

Run from the repository root:

    python3 paper_tools/figures/pull_push_step/generate_pull_push_step.py
"""
from __future__ import annotations

import hashlib
import json
import math
import platform
import subprocess
from pathlib import Path
from typing import Callable, Sequence

import cairo

HERE = Path(__file__).resolve().parent
OUTPUT_PDF = HERE / "pull_push_step.pdf"
OUTPUT_METADATA = HERE / "pull_push_step.metadata.json"
PDF_VERSION = cairo.PDF_VERSION_1_5
PDF_HEADER = b"%PDF-1.5"

WIDTH = 396.0
HEIGHT = 212.0
DATA_LINE_WIDTH = 1.05
AXIS_LINE_WIDTH = 0.65
GRID_LINE_WIDTH = 0.45
GUIDE_LINE_WIDTH = 0.50
ARROW_LINE_WIDTH = 1.05
PULL_DASH: tuple[float, ...] = ()
PUSH_DASH = (5.0, 2.1)
STEP_DASH = (4.2, 1.6, 1.0, 1.6)
TEACHER_VERTICAL_DASH = (1.0, 2.2)
STUDENT_VERTICAL_DASH = (2.6, 1.8)
LEGEND_ROW1_BASELINE = 12.0
LEGEND_ROW2_BASELINE = 24.0
SUBCAPTION_BASELINE = 207.0
LEGEND_FONT_SIZE = 6.5
AXIS_FONT_SIZE = 6.8
TICK_FONT_SIZE = 6.5
SUBCAPTION_FONT_SIZE = 6.8
LEFT_BOUNDS = (30.0, 34.0, 160.0, 132.0)
RIGHT_BOUNDS = (226.0, 34.0, 160.0, 132.0)
VALUE_RANGE = (-7.5, 4.8)
SAMPLES = 2048

# The declared mathematical inputs: masses and angles, in multiples of pi.
# The angles are the website interactive's canonical default configuration
# (teachers 0, 0.6 pi; students 0.18 pi, 0.85 pi) rotated by 0.2 pi, so that
# no direction sits on the plot seam; the loss is rotation-equivariant, so
# this is the same configuration.
TEACHER_MASSES = (1.0, 1.0)
TEACHER_ANGLES = (0.2 * math.pi, 0.8 * math.pi)
STUDENT_MASSES = (1.0, 1.0)
STUDENT_ANGLES = (0.38 * math.pi, 1.05 * math.pi)
PROBE_MASS = 1.0
PROBE_ANGLE = 1.6 * math.pi
STEP_SCALE = 0.6  # one common factor for both arrow components

PAPER = (1.0, 1.0, 0.992)
INK = (0.12, 0.15, 0.19)
RULE = (0.48, 0.50, 0.53)
GRID = (0.83, 0.84, 0.85)
TEACHER = (0.13, 0.40, 0.67)
STUDENT = (0.78, 0.18, 0.26)


def clamp1(x: float) -> float:
    return max(-1.0, min(1.0, x))


def angular_kernel(t: float, plain: bool) -> float:
    value = math.cos(t) * math.asin(clamp1(math.cos(t))) + abs(math.sin(t))
    return value + 0.5 * math.pi * math.cos(t) if plain else value


def angular_kernel_slope(t: float, plain: bool) -> float:
    value = -math.sin(t) * math.asin(clamp1(math.cos(t)))
    return value - 0.5 * math.pi * math.sin(t) if plain else value


def pull(gamma: float, plain: bool) -> float:
    return sum(s * angular_kernel(gamma - b, plain)
               for s, b in zip(TEACHER_MASSES, TEACHER_ANGLES))


def push(gamma: float, plain: bool) -> float:
    background = sum(c * angular_kernel(gamma - th, plain)
                     for c, th in zip(STUDENT_MASSES, STUDENT_ANGLES))
    return -background - PROBE_MASS * angular_kernel(0.0, plain)


def step(gamma: float, plain: bool) -> float:
    return pull(gamma, plain) + push(gamma, plain)


def probe_adjoined_residual(gamma: float, plain: bool) -> float:
    """F_q of the configuration with the probe adjoined, evaluated at the probe.

    Independent of pull/push: the literal residual formula, student potential
    minus teacher potential, with the probe as one more student at gamma.
    """
    masses = list(STUDENT_MASSES) + [PROBE_MASS]
    angles = list(STUDENT_ANGLES) + [gamma]
    student_potential = sum(c * angular_kernel(gamma - th, plain)
                            for c, th in zip(masses, angles))
    teacher_potential = sum(s * angular_kernel(gamma - b, plain)
                            for s, b in zip(TEACHER_MASSES, TEACHER_ANGLES))
    return student_potential - teacher_potential


def pull_slope(gamma: float, plain: bool) -> float:
    return sum(s * angular_kernel_slope(gamma - b, plain)
               for s, b in zip(TEACHER_MASSES, TEACHER_ANGLES))


def push_slope(gamma: float, plain: bool) -> float:
    return -sum(c * angular_kernel_slope(gamma - th, plain)
                for c, th in zip(STUDENT_MASSES, STUDENT_ANGLES))


def step_slope(gamma: float, plain: bool) -> float:
    return pull_slope(gamma, plain) + push_slope(gamma, plain)


def arrow_vectors(plain: bool) -> dict[str, tuple[float, float]]:
    """The three drawn arrows in data units (angle axis, value axis)."""
    g = PROBE_ANGLE
    vectors = {
        "pull": (STEP_SCALE * pull_slope(g, plain), STEP_SCALE * pull(g, plain)),
        "push": (STEP_SCALE * push_slope(g, plain), STEP_SCALE * push(g, plain)),
        "step": (STEP_SCALE * step_slope(g, plain), STEP_SCALE * step(g, plain)),
    }
    return vectors


def verify_identities() -> dict[str, float]:
    pi = math.pi
    for k in range(SAMPLES + 1):
        t = 2.0 * pi * k / SAMPLES
        u = t % pi
        branch_c = (0.5 * pi - u) * math.cos(u) + math.sin(u)
        assert abs(angular_kernel(t, False) - branch_c) < 1e-12
        assert abs(angular_kernel(t + pi, False) - angular_kernel(t, False)) < 1e-12
        assert abs(angular_kernel(t + 2.0 * pi, True) - angular_kernel(t, True)) < 1e-12
        assert abs(angular_kernel(t, True) - angular_kernel(t, False)
                   - 0.5 * pi * math.cos(t)) < 1e-12
        assert 1.0 - 1e-12 <= angular_kernel(t, False) <= 0.5 * pi + 1e-12
        assert angular_kernel(t, True) >= -1e-12
    # the self term has zero angular derivative
    assert angular_kernel_slope(0.0, False) == 0.0
    assert angular_kernel_slope(0.0, True) == 0.0
    # analytic kernel slope against central finite differences, away from kinks
    h = 1e-5
    for k in range(1, 400):
        t = pi * k / 400.0
        if min(abs(t), abs(t - pi)) < 5 * h:
            continue
        for plain in (False, True):
            numeric = (angular_kernel(t + h, plain) - angular_kernel(t - h, plain)) / (2 * h)
            assert abs(numeric - angular_kernel_slope(t, plain)) < 1e-7
    # step = pull + push = -(probe-adjoined residual), two independent routes
    extremes = {}
    for plain, name in ((False, "centered"), (True, "plain")):
        values = []
        for k in range(SAMPLES + 1):
            g = 2.0 * pi * k / SAMPLES
            s = step(g, plain)
            assert abs(s - (pull(g, plain) + push(g, plain))) < 1e-12
            assert abs(s + probe_adjoined_residual(g, plain)) < 1e-12
            values.append((pull(g, plain), push(g, plain), s))
        extremes[name + "_pull_min"] = min(v[0] for v in values)
        extremes[name + "_pull_max"] = max(v[0] for v in values)
        extremes[name + "_low"] = min(v[1] for v in values)
        extremes[name + "_high"] = max(v[0] for v in values)
        # the pull of two unit-mass teachers inherits the kernel floor/zero gap
        if plain:
            assert extremes["plain_pull_min"] < 0.52  # nearly vanishes opposite the teachers
        else:
            assert extremes["centered_pull_min"] >= 2.0 - 1e-9  # Phi_C >= 1, two unit masses
        # the centered pull is pi-periodic
        if not plain:
            for k in range(0, SAMPLES + 1, 8):
                g = 2.0 * pi * k / SAMPLES
                assert abs(pull(g + pi, False) - pull(g, False)) < 1e-12
    # every drawn value fits the shared panel range
    for plain in (False, True):
        for k in range(SAMPLES + 1):
            g = 2.0 * pi * k / SAMPLES
            for value in (pull(g, plain), push(g, plain), step(g, plain)):
                assert VALUE_RANGE[0] < value < VALUE_RANGE[1]
    # head-to-tail arrow sum is exact, and the step arrow is the negative
    # gradient of the probe-adjoined loss (unit probe mass), commonly scaled:
    # (2 pi) dot(theta) = -F', (2 pi) dot(c) = -F.
    for plain in (False, True):
        vectors = arrow_vectors(plain)
        assert abs(vectors["pull"][0] + vectors["push"][0] - vectors["step"][0]) < 1e-12
        assert abs(vectors["pull"][1] + vectors["push"][1] - vectors["step"][1]) < 1e-12
        g, hh = PROBE_ANGLE, 1e-6
        residual_slope = (probe_adjoined_residual(g + hh, plain)
                          - probe_adjoined_residual(g - hh, plain)) / (2 * hh)
        assert abs(vectors["step"][0] - STEP_SCALE * (-residual_slope)) < 1e-6
        assert abs(vectors["step"][1] - STEP_SCALE * (-probe_adjoined_residual(g, plain))) < 1e-12
    return extremes


def verify_visual_structure() -> None:
    for left, top, width, height in (LEFT_BOUNDS, RIGHT_BOUNDS):
        assert left >= 0 and top >= 0 and left + width <= WIDTH and top + height <= HEIGHT
    assert LEFT_BOUNDS[1] == RIGHT_BOUNDS[1] and LEFT_BOUNDS[3] == RIGHT_BOUNDS[3]
    assert LEFT_BOUNDS[2] == RIGHT_BOUNDS[2]
    assert LEFT_BOUNDS[0] + LEFT_BOUNDS[2] + 12.0 <= RIGHT_BOUNDS[0]
    assert LEGEND_ROW2_BASELINE + 5.0 < LEFT_BOUNDS[1]
    assert GRID_LINE_WIDTH < AXIS_LINE_WIDTH < DATA_LINE_WIDTH
    assert GUIDE_LINE_WIDTH < DATA_LINE_WIDTH
    assert ARROW_LINE_WIDTH == DATA_LINE_WIDTH
    assert len({PULL_DASH, PUSH_DASH, STEP_DASH}) == 3
    assert TEACHER_VERTICAL_DASH != STUDENT_VERTICAL_DASH
    assert min(LEGEND_FONT_SIZE, AXIS_FONT_SIZE, TICK_FONT_SIZE, SUBCAPTION_FONT_SIZE) >= 6.5
    assert WIDTH == 396.0


def set_source(context: cairo.Context, colour, alpha: float = 1.0) -> None:
    context.set_source_rgba(colour[0], colour[1], colour[2], alpha)


def font(context: cairo.Context, size: float, bold: bool = False) -> None:
    context.select_font_face("DejaVu Sans", cairo.FONT_SLANT_NORMAL,
                             cairo.FONT_WEIGHT_BOLD if bold else cairo.FONT_WEIGHT_NORMAL)
    context.set_font_size(size)


def resolved_font_file() -> Path:
    result = subprocess.run(["fc-match", "-f", "%{file}\n", "DejaVu Sans"],
                            check=True, capture_output=True, text=True)
    path = Path(result.stdout.splitlines()[0]).resolve()
    assert path.is_file()
    return path


def text(context, x, y, label, size=7.2, colour=INK, bold=False) -> None:
    font(context, size, bold)
    set_source(context, colour)
    context.move_to(x, y)
    context.show_text(label)


def centered_text(context, x, y, label, size=7.2, colour=INK, bold=False) -> None:
    font(context, size, bold)
    extents = context.text_extents(label)
    text(context, x - extents.width / 2.0 - extents.x_bearing, y, label, size, colour, bold)


def stroke(context, colour=INK, width=0.8, alpha=1.0, dash: Sequence[float] = ()) -> None:
    set_source(context, colour, alpha)
    context.set_line_width(width)
    context.set_dash(dash)
    context.stroke()
    context.set_dash(())


def draw_line_key(context, x, baseline, colour, dash, label, width=DATA_LINE_WIDTH) -> float:
    context.move_to(x, baseline - 2.0)
    context.line_to(x + 12.0, baseline - 2.0)
    stroke(context, colour, width, 1.0, dash)
    font(context, LEGEND_FONT_SIZE)
    extents = context.text_extents(label)
    text(context, x + 15.0, baseline, label, LEGEND_FONT_SIZE, colour)
    return x + 15.0 + extents.width + 14.0


def draw_arrow(context, x0, y0, x1, y1, colour, width=ARROW_LINE_WIDTH) -> None:
    context.move_to(x0, y0)
    context.line_to(x1, y1)
    stroke(context, colour, width)
    angle = math.atan2(y1 - y0, x1 - x0)
    head, spread = 4.2, 0.42
    context.move_to(x1, y1)
    context.line_to(x1 - head * math.cos(angle - spread), y1 - head * math.sin(angle - spread))
    context.line_to(x1 - head * math.cos(angle + spread), y1 - head * math.sin(angle + spread))
    context.close_path()
    set_source(context, colour)
    context.fill()


def draw_arrow_key(context, x, baseline, colour, label) -> float:
    draw_arrow(context, x, baseline - 2.0, x + 13.0, baseline - 2.0, colour)
    font(context, LEGEND_FONT_SIZE)
    extents = context.text_extents(label)
    text(context, x + 17.0, baseline, label, LEGEND_FONT_SIZE, colour)
    return x + 17.0 + extents.width + 14.0


def panel(context, bounds, x_ticks, y_ticks, x_label):
    left, top, width, height = bounds
    x0, x1 = 0.0, 2.0 * math.pi
    y0, y1 = VALUE_RANGE

    def tx(x):
        return left + width * (x - x0) / (x1 - x0)

    def ty(y):
        return top + height - height * (y - y0) / (y1 - y0)

    for value, _ in y_ticks:
        context.move_to(left, ty(value)); context.line_to(left + width, ty(value))
        stroke(context, GRID, GRID_LINE_WIDTH)
    for value, _ in x_ticks:
        context.move_to(tx(value), top); context.line_to(tx(value), top + height)
        stroke(context, GRID, GRID_LINE_WIDTH)
    # the zero line, slightly stronger than the grid
    context.move_to(left, ty(0.0)); context.line_to(left + width, ty(0.0))
    stroke(context, RULE, GUIDE_LINE_WIDTH)
    context.rectangle(left, top, width, height)
    stroke(context, RULE, AXIS_LINE_WIDTH)
    for value, label in x_ticks:
        centered_text(context, tx(value), top + height + 10.0, label, TICK_FONT_SIZE, RULE)
    for value, label in y_ticks:
        font(context, TICK_FONT_SIZE)
        ext = context.text_extents(label)
        text(context, left - 4.0 - ext.width - ext.x_bearing, ty(value) + 2.3, label,
             TICK_FONT_SIZE, RULE)
    centered_text(context, left + width / 2.0, top + height + 21.0, x_label,
                  AXIS_FONT_SIZE, INK)
    return tx, ty


def plot(context, tx, ty, xs, ys, colour, dash) -> None:
    context.move_to(tx(xs[0]), ty(ys[0]))
    for x, y in zip(xs[1:], ys[1:]):
        context.line_to(tx(x), ty(y))
    stroke(context, colour, DATA_LINE_WIDTH, 1.0, dash)


def draw_panel(context, bounds, plain: bool) -> None:
    pi = math.pi
    tx, ty = panel(
        context, bounds,
        [(0.0, "0"), (0.5 * pi, "π/2"), (pi, "π"), (1.5 * pi, "3π/2"), (2.0 * pi, "2π")],
        [(-6.0, "−6"), (-4.0, "−4"), (-2.0, "−2"), (0.0, "0"), (2.0, "2"), (4.0, "4")],
        "probe angle γ")
    left, top, width, height = bounds
    # role verticals: mathematically present directions of the fixed units
    def verticals(angles, colour, dash):
        for angle in angles:
            copies = {angle % (2.0 * pi)}
            if min(copies) < 1e-12:  # a direction on the seam appears at both ends
                copies.add(2.0 * pi)
            for wrapped in copies:
                context.move_to(tx(wrapped), top)
                context.line_to(tx(wrapped), top + height)
                stroke(context, colour, GUIDE_LINE_WIDTH, 0.9, dash)

    verticals(TEACHER_ANGLES, TEACHER, TEACHER_VERTICAL_DASH)
    verticals(STUDENT_ANGLES, STUDENT, STUDENT_VERTICAL_DASH)
    gammas = [2.0 * pi * k / SAMPLES for k in range(SAMPLES + 1)]
    plot(context, tx, ty, gammas, [pull(g, plain) for g in gammas], TEACHER, PULL_DASH)
    plot(context, tx, ty, gammas, [push(g, plain) for g in gammas], STUDENT, PUSH_DASH)
    plot(context, tx, ty, gammas, [step(g, plain) for g in gammas], INK, STEP_DASH)
    # the arrows: teacher part, then student part head to tail, and their sum,
    # all from the step-curve point at the probe angle, in the plot's own units
    vectors = arrow_vectors(plain)
    per_radian = tx(1.0) - tx(0.0)
    per_value = ty(0.0) - ty(1.0)

    def to_pixels(vector):
        return vector[0] * per_radian, -vector[1] * per_value

    base = (tx(PROBE_ANGLE), ty(step(PROBE_ANGLE, plain)))
    pull_px = to_pixels(vectors["pull"])
    push_px = to_pixels(vectors["push"])
    step_px = to_pixels(vectors["step"])
    tip = (base[0] + pull_px[0], base[1] + pull_px[1])
    draw_arrow(context, base[0], base[1], tip[0], tip[1], TEACHER)
    draw_arrow(context, tip[0], tip[1], tip[0] + push_px[0], tip[1] + push_px[1], STUDENT)
    draw_arrow(context, base[0], base[1], base[0] + step_px[0], base[1] + step_px[1], INK)
    context.new_sub_path()
    context.arc(base[0], base[1], 1.6, 0.0, 2.0 * pi)
    set_source(context, INK)
    context.fill()


def render() -> dict[str, object]:
    verify_visual_structure()
    extremes = verify_identities()
    surface = cairo.PDFSurface(str(OUTPUT_PDF), WIDTH, HEIGHT)
    surface.restrict_to_version(PDF_VERSION)
    surface.set_metadata(cairo.PDF_METADATA_TITLE,
                         "The pull, the push, and the step they add up to")
    surface.set_metadata(cairo.PDF_METADATA_AUTHOR, "")
    surface.set_metadata(cairo.PDF_METADATA_CREATOR, "generate_pull_push_step.py")
    surface.set_metadata(cairo.PDF_METADATA_CREATE_DATE, "2000-01-01T00:00:00Z")
    surface.set_metadata(cairo.PDF_METADATA_MOD_DATE, "2000-01-01T00:00:00Z")
    context = cairo.Context(surface)
    set_source(context, PAPER)
    context.paint()

    x = LEFT_BOUNDS[0]
    x = draw_line_key(context, x, LEGEND_ROW1_BASELINE, TEACHER, PULL_DASH, "the pull P_q")
    x = draw_line_key(context, x, LEGEND_ROW1_BASELINE, STUDENT, PUSH_DASH,
                      "the push −S_q − Φ_q(0)")
    draw_line_key(context, x, LEGEND_ROW1_BASELINE, INK, STEP_DASH,
                  "their sum: the probe's step curve")
    x = LEFT_BOUNDS[0]
    x = draw_line_key(context, x, LEGEND_ROW2_BASELINE, TEACHER, TEACHER_VERTICAL_DASH,
                      "teacher directions", GUIDE_LINE_WIDTH)
    x = draw_line_key(context, x, LEGEND_ROW2_BASELINE, STUDENT, STUDENT_VERTICAL_DASH,
                      "student directions", GUIDE_LINE_WIDTH)
    draw_arrow_key(context, x, LEGEND_ROW2_BASELINE, INK,
                   "one scaled descent step, split and summed")

    draw_panel(context, LEFT_BOUNDS, plain=False)
    draw_panel(context, RIGHT_BOUNDS, plain=True)

    centered_text(context, LEFT_BOUNDS[0] + LEFT_BOUNDS[2] / 2.0, SUBCAPTION_BASELINE,
                  "(a) centered kernel", SUBCAPTION_FONT_SIZE, INK, True)
    centered_text(context, RIGHT_BOUNDS[0] + RIGHT_BOUNDS[2] / 2.0, SUBCAPTION_BASELINE,
                  "(b) plain-ReLU kernel", SUBCAPTION_FONT_SIZE, INK, True)
    context.show_page()
    surface.finish()
    pdf_bytes = OUTPUT_PDF.read_bytes()
    assert pdf_bytes.startswith(PDF_HEADER)
    script_path = Path(__file__).resolve()
    font_path = resolved_font_file()
    record = {
        "figure": "pull_push_step",
        "configuration": {
            "teacher_masses": list(TEACHER_MASSES),
            "teacher_angles_over_pi": [b / math.pi for b in TEACHER_ANGLES],
            "student_masses": list(STUDENT_MASSES),
            "student_angles_over_pi": [t / math.pi for t in STUDENT_ANGLES],
            "probe_mass": PROBE_MASS,
            "probe_angle_over_pi": PROBE_ANGLE / math.pi,
            "step_scale": STEP_SCALE,
        },
        "identities_checked": [
            "Phi_C branch (pi/2-u)cos u + sin u, pi-periodic; Phi_R 2pi-periodic",
            "Phi_R = Phi_C + (pi/2)cos t, 1 <= Phi_C <= pi/2, Phi_R >= 0",
            "Phi_q'(0) = 0: the probe's self term has zero angular derivative",
            "step = pull + push pointwise, and step = -(residual of the probe-adjoined"
            " configuration) computed independently from the residual formula",
            "analytic kernel slope matches central finite differences (tol 1e-7)",
            "centered pull >= 2 (kernel floor, two unit teachers); plain pull min < 0.52",
            "centered pull is pi-periodic",
            "pull arrow + push arrow = step arrow exactly; step arrow = common scale"
            " times (-F', -F) of the probe-adjoined residual (negative gradient,"
            " unit probe mass, 2 pi clock)",
            "all drawn values inside the shared panel value range",
        ],
        "field_extremes": {k: round(v, 6) for k, v in extremes.items()},
        "invocation": "python3 paper_tools/figures/pull_push_step/generate_pull_push_step.py",
        "output_sha256": {OUTPUT_PDF.name: hashlib.sha256(pdf_bytes).hexdigest()},
        "pdf_compatibility": {"asserted_header": PDF_HEADER.decode("ascii"),
                              "restricted_version": "1.5"},
        "sampling": {"uniform_samples": SAMPLES},
        "source_sha256": {script_path.name: hashlib.sha256(script_path.read_bytes()).hexdigest()},
        "toolchain": {
            "cairo": cairo.cairo_version_string(),
            "font_file": str(font_path),
            "font_sha256": hashlib.sha256(font_path.read_bytes()).hexdigest(),
            "pycairo": cairo.version,
            "python": platform.python_version(),
        },
        "visual_style": {
            "data_line_width_pt": DATA_LINE_WIDTH,
            "axis_line_width_pt": AXIS_LINE_WIDTH,
            "grid_line_width_pt": GRID_LINE_WIDTH,
            "pull_mark": "teacher blue, solid",
            "push_mark": "student red, long dash",
            "step_mark": "ink, dash-dot",
            "verticals": "role-coloured guides at the fixed directions;"
                         " teacher dotted, student short-dashed",
        },
    }
    OUTPUT_METADATA.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n",
                               encoding="utf-8")
    return record


if __name__ == "__main__":
    rec = render()
    print("wrote", OUTPUT_PDF.relative_to(HERE.parents[3]))
    print("pdf sha256", rec["output_sha256"][OUTPUT_PDF.name])
