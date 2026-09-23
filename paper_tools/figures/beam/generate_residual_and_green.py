#!/usr/bin/env python3
"""Generate the appendix figure of a planar residual field and the clamped beam
Green function.

Panel (a): the centered residual F_C(gamma) = sum_i c_i Phi_C(gamma-theta_i)
- sum_k s_k Phi_C(gamma-beta_k) on one projective period for a clean, positive,
strictly interlaced, centered-critical width-three configuration against a
positive width-three teacher.  The teacher lines are fixed below; the student
angles and masses are recomputed here by Newton's method from the mass and
angle stationarity equations and asserted to be critical (double zeros of F_C),
positive, and interlaced.

Panel (b): the clamped Green function G_l(p,z) of the beam operator (D^2+1)^2
on a gap of length l with unit point load at p: piecewise in
span{cos, sin, z cos z, z sin z}, value and slope zero at both ends, G, G', G''
continuous at p, and a unit jump of G''' at p.  The boundary and jump
conditions are asserted numerically after solving the 8x8 system.

Run from the repository root:

    python3 paper_tools/figures/beam/generate_residual_and_green.py
"""
from __future__ import annotations

import hashlib
import json
import math
import platform
import subprocess
from pathlib import Path
from typing import Sequence

import cairo

HERE = Path(__file__).resolve().parent
OUTPUT_PDF = HERE / "residual_and_green.pdf"
OUTPUT_METADATA = HERE / "residual_and_green.metadata.json"
PDF_VERSION = cairo.PDF_VERSION_1_5
PDF_HEADER = b"%PDF-1.5"

# Canonical teacher: three positive units on the projective lines below.
TEACHER_LINES = (0.0, 1.1, 2.0)
TEACHER_MASSES = (1.0, 1.0, 1.0)
# Newton start: gap midpoints (last gap wraps through pi).
GAP_LENGTH = 2.0
LOAD_POSITION = 0.7

WIDTH = 396.0
HEIGHT = 168.0
DATA_LINE_WIDTH = 1.05
AXIS_LINE_WIDTH = 0.65
GRID_LINE_WIDTH = 0.45
GUIDE_LINE_WIDTH = 0.50
LEGEND_BASELINE = 23.0
SUBCAPTION_BASELINE = 164.0
LEGEND_FONT_SIZE = 6.5
AXIS_FONT_SIZE = 6.8
TICK_FONT_SIZE = 6.5
SUBCAPTION_FONT_SIZE = 6.8
LEFT_BOUNDS = (34.0, 32.0, 168.0, 96.0)
RIGHT_BOUNDS = (244.0, 32.0, 142.0, 96.0)
SAMPLES = 2048

PAPER = (1.0, 1.0, 0.992)
INK = (0.12, 0.15, 0.19)
RULE = (0.48, 0.50, 0.53)
GRID = (0.83, 0.84, 0.85)
TEACHER = (0.16, 0.36, 0.62)
STUDENT = (0.78, 0.30, 0.17)
RESIDUAL = (0.18, 0.24, 0.28)


def angular_c(t: float) -> float:
    u = abs(t) % math.pi
    return (0.5 * math.pi - u) * math.cos(u) + math.sin(u)


def angular_c_prime(t: float) -> float:
    u = t % math.pi
    return -(0.5 * math.pi - u) * math.sin(u)


def residual(gamma, c, theta, s, beta) -> float:
    return (sum(ci * angular_c(gamma - ti) for ci, ti in zip(c, theta))
            - sum(sk * angular_c(gamma - bk) for sk, bk in zip(s, beta)))


def residual_prime(gamma, c, theta, s, beta) -> float:
    return (sum(ci * angular_c_prime(gamma - ti) for ci, ti in zip(c, theta))
            - sum(sk * angular_c_prime(gamma - bk) for sk, bk in zip(s, beta)))


def solve_linear(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    a = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(a[r][col]))
        a[col], a[pivot] = a[pivot], a[col]
        assert abs(a[col][col]) > 1e-14
        for r in range(n):
            if r != col:
                f = a[r][col] / a[col][col]
                for k in range(col, n + 1):
                    a[r][k] -= f * a[col][k]
    return [a[i][n] / a[i][i] for i in range(n)]


def masses_for(theta, s, beta) -> list[float]:
    matrix = [[angular_c(ti - tj) for tj in theta] for ti in theta]
    rhs = [sum(sk * angular_c(ti - bk) for sk, bk in zip(s, beta)) for ti in theta]
    return solve_linear(matrix, rhs)


def angle_equations(theta, s, beta):
    c = masses_for(theta, s, beta)
    return [residual_prime(ti, c, theta, s, beta) for ti in theta], c


def critical_configuration():
    beta = sorted(TEACHER_LINES)
    s = TEACHER_MASSES
    theta = [(beta[0] + beta[1]) / 2.0, (beta[1] + beta[2]) / 2.0, (beta[2] + beta[0] + math.pi) / 2.0]
    for _ in range(100):
        g, c = angle_equations(theta, s, beta)
        if max(abs(v) for v in g) < 1e-13:
            break
        h = 1e-7
        jac = [[0.0] * 3 for _ in range(3)]
        for j in range(3):
            shifted = theta[:]
            shifted[j] += h
            gj, _ = angle_equations(shifted, s, beta)
            for i in range(3):
                jac[i][j] = (gj[i] - g[i]) / h
        step = solve_linear(jac, g)
        theta = [t - d for t, d in zip(theta, step)]
    g, c = angle_equations(theta, s, beta)
    theta = [t % math.pi for t in theta]
    return theta, c, s, beta


def verify_configuration(theta, c, s, beta) -> dict[str, float]:
    assert all(ci > 0 for ci in c), c
    assert all(sk > 0 for sk in s)
    for ti in theta:
        assert abs(residual(ti, c, theta, s, beta)) < 1e-10
        assert abs(residual_prime(ti, c, theta, s, beta)) < 1e-9
    lines = sorted([(b, "T") for b in beta] + [(t, "S") for t in theta])
    kinds = [k for _, k in lines]
    assert kinds == ["T", "S"] * 3 or kinds == ["S", "T"] * 3, kinds
    assert len({round(x, 9) for x, _ in lines}) == 6
    loss = 0.0
    for ci, ti in zip(c, theta):
        loss += ci * residual(ti, c, theta, s, beta)
    for sk, bk in zip(s, beta):
        loss -= sk * residual(bk, c, theta, s, beta)
    loss /= 4.0 * math.pi
    assert loss > 1e-6, loss
    return {"loss": loss}


def resonant_basis(z: float, order: int) -> list[float]:
    """Derivatives of order 0..3 of cos z, sin z, z cos z, z sin z."""
    c, s = math.cos(z), math.sin(z)
    table = {
        0: [c, s, z * c, z * s],
        1: [-s, c, c - z * s, s + z * c],
        2: [-c, -s, -2 * s - z * c, 2 * c - z * s],
        3: [s, -c, -3 * c + z * s, -3 * s - z * c],
    }
    return table[order]


def green_coefficients(l: float, p: float) -> tuple[list[float], list[float]]:
    rows, rhs = [], []
    rows.append(resonant_basis(0.0, 0) + [0.0] * 4); rhs.append(0.0)
    rows.append(resonant_basis(0.0, 1) + [0.0] * 4); rhs.append(0.0)
    rows.append([0.0] * 4 + resonant_basis(l, 0)); rhs.append(0.0)
    rows.append([0.0] * 4 + resonant_basis(l, 1)); rhs.append(0.0)
    for order in range(3):
        left = resonant_basis(p, order)
        rows.append(left + [-v for v in left]); rhs.append(0.0)
    third = resonant_basis(p, 3)
    rows.append([-v for v in third] + third); rhs.append(1.0)
    sol = solve_linear(rows, rhs)
    return sol[:4], sol[4:]


def green(z: float, l: float, p: float, coeffs) -> float:
    a, b = coeffs
    basis = resonant_basis(z, 0)
    use = a if z <= p else b
    return sum(u * v for u, v in zip(use, basis))


def verify_green(l: float, p: float, coeffs) -> dict[str, float]:
    a, b = coeffs

    def piece(z, order, use):
        return sum(u * v for u, v in zip(use, resonant_basis(z, order)))
    assert abs(piece(0.0, 0, a)) < 1e-12 and abs(piece(0.0, 1, a)) < 1e-12
    assert abs(piece(l, 0, b)) < 1e-12 and abs(piece(l, 1, b)) < 1e-12
    for order in range(3):
        assert abs(piece(p, order, a) - piece(p, order, b)) < 1e-11
    jump = piece(p, 3, b) - piece(p, 3, a)
    assert abs(jump - 1.0) < 1e-11
    # (D^2+1)^2 G = 0 on each piece: check G'''' + 2G'' + G = 0 by finite differences
    # (D^2+1)^2 = D^4 + 2 D^2 + 1; the fourth derivatives of the basis are
    # cos, sin, 4 sin z + z cos z, -4 cos z + z sin z, so the identity is exact.
    for z in (0.3, 0.6, 1.2, 1.7):
        use = a if z <= p else b
        c_, s_ = math.cos(z), math.sin(z)
        fourth_basis = [c_, s_, 4 * s_ + z * c_, -4 * c_ + z * s_]
        fourth = sum(u * v for u, v in zip(use, fourth_basis))
        assert abs(fourth + 2 * piece(z, 2, use) + piece(z, 0, use)) < 1e-11
    values = [green(l * k / SAMPLES, l, p, coeffs) for k in range(1, SAMPLES)]
    assert min(values) > 0.0
    m0 = piece(0.0, 2, a)
    ml = piece(l, 2, b)
    assert m0 > 0 and ml > 0
    return {"end_curvature_0": m0, "end_curvature_l": ml, "max_value": max(values),
            "clamped_determinant": l * l - math.sin(l) ** 2}


def set_source(context, colour, alpha=1.0):
    context.set_source_rgba(colour[0], colour[1], colour[2], alpha)


def font(context, size, bold=False):
    context.select_font_face("DejaVu Sans", cairo.FONT_SLANT_NORMAL,
                             cairo.FONT_WEIGHT_BOLD if bold else cairo.FONT_WEIGHT_NORMAL)
    context.set_font_size(size)


def resolved_font_file() -> Path:
    result = subprocess.run(["fc-match", "-f", "%{file}\n", "DejaVu Sans"],
                            check=True, capture_output=True, text=True)
    path = Path(result.stdout.splitlines()[0]).resolve()
    assert path.is_file()
    return path


def text(context, x, y, label, size=7.2, colour=INK, bold=False):
    font(context, size, bold); set_source(context, colour)
    context.move_to(x, y); context.show_text(label)


def centered_text(context, x, y, label, size=7.2, colour=INK, bold=False):
    font(context, size, bold)
    ext = context.text_extents(label)
    text(context, x - ext.width / 2.0 - ext.x_bearing, y, label, size, colour, bold)


def stroke(context, colour=INK, width=0.8, alpha=1.0, dash: Sequence[float] = ()):
    set_source(context, colour, alpha); context.set_line_width(width)
    context.set_dash(dash); context.stroke(); context.set_dash(())


def draw_line_key(context, x, baseline, colour, dash, label):
    context.move_to(x, baseline - 2.0); context.line_to(x + 12.0, baseline - 2.0)
    stroke(context, colour, DATA_LINE_WIDTH, 1.0, dash)
    text(context, x + 15.0, baseline, label, LEGEND_FONT_SIZE, colour)


def draw_marker_key(context, x, baseline, colour, filled, label):
    context.new_sub_path(); context.arc(x + 6.0, baseline - 2.2, 2.0, 0.0, 2 * math.pi)
    set_source(context, colour if filled else PAPER); context.fill_preserve()
    stroke(context, colour, DATA_LINE_WIDTH)
    text(context, x + 15.0, baseline, label, LEGEND_FONT_SIZE, colour)


def panel(context, bounds, x_range, y_range, x_ticks, y_ticks, x_label):
    left, top, width, height = bounds
    x0, x1 = x_range; y0, y1 = y_range
    tx = lambda x: left + width * (x - x0) / (x1 - x0)
    ty = lambda y: top + height - height * (y - y0) / (y1 - y0)
    for value, _ in y_ticks:
        context.move_to(left, ty(value)); context.line_to(left + width, ty(value))
        stroke(context, GRID, GRID_LINE_WIDTH)
    for value, _ in x_ticks:
        context.move_to(tx(value), top); context.line_to(tx(value), top + height)
        stroke(context, GRID, GRID_LINE_WIDTH)
    context.rectangle(left, top, width, height); stroke(context, RULE, AXIS_LINE_WIDTH)
    for value, label in x_ticks:
        centered_text(context, tx(value), top + height + 10.0, label, TICK_FONT_SIZE, RULE)
    for value, label in y_ticks:
        font(context, TICK_FONT_SIZE); ext = context.text_extents(label)
        text(context, left - 4.0 - ext.width - ext.x_bearing, ty(value) + 2.3, label, TICK_FONT_SIZE, RULE)
    centered_text(context, left + width / 2.0, top + height + 21.0, x_label, AXIS_FONT_SIZE, INK)
    return tx, ty


def plot(context, tx, ty, xs, ys, colour, dash=()):
    context.move_to(tx(xs[0]), ty(ys[0]))
    for x, y in zip(xs[1:], ys[1:]):
        context.line_to(tx(x), ty(y))
    stroke(context, colour, DATA_LINE_WIDTH, 1.0, dash)


def render() -> dict[str, object]:
    assert WIDTH == 396.0 and LEFT_BOUNDS[0] + LEFT_BOUNDS[2] + 12.0 <= RIGHT_BOUNDS[0]
    assert min(LEGEND_FONT_SIZE, AXIS_FONT_SIZE, TICK_FONT_SIZE, SUBCAPTION_FONT_SIZE) >= 6.5
    theta, c, s, beta = critical_configuration()
    config_checks = verify_configuration(theta, c, s, beta)
    coeffs = green_coefficients(GAP_LENGTH, LOAD_POSITION)
    green_checks = verify_green(GAP_LENGTH, LOAD_POSITION, coeffs)

    surface = cairo.PDFSurface(str(OUTPUT_PDF), WIDTH, HEIGHT)
    surface.restrict_to_version(PDF_VERSION)
    surface.set_metadata(cairo.PDF_METADATA_TITLE, "Residual field and clamped beam Green function")
    surface.set_metadata(cairo.PDF_METADATA_AUTHOR, "")
    surface.set_metadata(cairo.PDF_METADATA_CREATOR, "generate_residual_and_green.py")
    surface.set_metadata(cairo.PDF_METADATA_CREATE_DATE, "2000-01-01T00:00:00Z")
    surface.set_metadata(cairo.PDF_METADATA_MOD_DATE, "2000-01-01T00:00:00Z")
    context = cairo.Context(surface)
    set_source(context, PAPER); context.paint()

    # (a) residual on one projective period
    gammas = [math.pi * k / SAMPLES for k in range(SAMPLES + 1)]
    values = [residual(g, c, theta, s, beta) for g in gammas]
    amp = max(abs(v) for v in values) * 1.15
    tx, ty = panel(context, LEFT_BOUNDS, (0.0, math.pi), (-amp, amp),
                   [(0.0, "0"), (0.5 * math.pi, "π/2"), (math.pi, "π")],
                   [(-amp / 1.15, f"−{amp / 1.15:.2f}"), (0.0, "0"), (amp / 1.15, f"{amp / 1.15:.2f}")],
                   "probe angle γ (lines mod π)")
    left, top, width, height = LEFT_BOUNDS
    context.move_to(left, ty(0.0)); context.line_to(left + width, ty(0.0))
    stroke(context, RULE, GUIDE_LINE_WIDTH)
    for b in beta:
        context.move_to(tx(b), top); context.line_to(tx(b), top + height)
        stroke(context, TEACHER, GUIDE_LINE_WIDTH, 0.9, (1.2, 2.0))
    plot(context, tx, ty, gammas, values, RESIDUAL)
    for b in beta:
        context.new_sub_path(); context.arc(tx(b), ty(residual(b, c, theta, s, beta)), 2.0, 0, 2 * math.pi)
        set_source(context, TEACHER); context.fill_preserve(); stroke(context, TEACHER, DATA_LINE_WIDTH)
    for t in theta:
        context.new_sub_path(); context.arc(tx(t), ty(0.0), 2.2, 0, 2 * math.pi)
        set_source(context, PAPER); context.fill_preserve(); stroke(context, STUDENT, DATA_LINE_WIDTH)
    draw_line_key(context, left + 2.0, LEGEND_BASELINE, RESIDUAL, (), "residual F_C(γ)")
    draw_marker_key(context, left + 78.0, LEGEND_BASELINE, STUDENT, False, "student: double zero")
    draw_marker_key(context, left + 168.0, LEGEND_BASELINE, TEACHER, True, "teacher")

    # (b) clamped Green function
    zs = [GAP_LENGTH * k / SAMPLES for k in range(SAMPLES + 1)]
    gvals = [green(z, GAP_LENGTH, LOAD_POSITION, coeffs) for z in zs]
    gmax = max(gvals) * 1.15
    tx2, ty2 = panel(context, RIGHT_BOUNDS, (0.0, GAP_LENGTH), (0.0, gmax),
                     [(0.0, "0"), (LOAD_POSITION, "p"), (GAP_LENGTH, "l")],
                     [(0.0, "0"), (max(gvals), f"{max(gvals):.3f}")],
                     "position z in the gap")
    left2, top2, width2, height2 = RIGHT_BOUNDS
    context.move_to(tx2(LOAD_POSITION), top2); context.line_to(tx2(LOAD_POSITION), top2 + height2)
    stroke(context, TEACHER, GUIDE_LINE_WIDTH, 0.9, (1.2, 2.0))
    plot(context, tx2, ty2, zs, gvals, RESIDUAL)
    draw_line_key(context, left2 + 2.0, LEGEND_BASELINE, RESIDUAL, (), "G_l(p,z), clamped at 0 and l")

    centered_text(context, left + width / 2.0, SUBCAPTION_BASELINE, "(a) residual field of a clean critical configuration",
                  SUBCAPTION_FONT_SIZE, INK, True)
    centered_text(context, left2 + width2 / 2.0, SUBCAPTION_BASELINE, "(b) beam Green function, load at p",
                  SUBCAPTION_FONT_SIZE, INK, True)
    context.show_page(); surface.finish()
    pdf_bytes = OUTPUT_PDF.read_bytes()
    assert pdf_bytes.startswith(PDF_HEADER)
    script_path = Path(__file__).resolve(); font_path = resolved_font_file()
    record = {
        "figure": "residual_and_green",
        "configuration": {
            "teacher_lines": list(beta), "teacher_masses": list(s),
            "student_lines": theta, "student_masses": c,
            "centered_loss": config_checks["loss"],
            "green_gap_length": GAP_LENGTH, "green_load_position": LOAD_POSITION,
            "green_checks": green_checks,
        },
        "identities_checked": [
            "F_C(theta_i) = 0 and F_C'(theta_i) = 0 at every student (double zeros), tolerance 1e-10 / 1e-9",
            "all student and teacher masses positive; six distinct lines; strict interlacing",
            "centered loss 4 pi L = sum c_i F_C(theta_i) - sum s_k F_C(beta_k) > 0",
            "G(0)=G'(0)=G(l)=G'(l)=0; G, G', G'' continuous at p; G''' jumps by exactly 1 at p",
            "(D^2+1)^2 G = 0 on each piece (finite differences), G > 0 inside the gap, end curvatures positive",
        ],
        "invocation": "python3 paper_tools/figures/beam/generate_residual_and_green.py",
        "output_sha256": {OUTPUT_PDF.name: hashlib.sha256(pdf_bytes).hexdigest()},
        "pdf_compatibility": {"asserted_header": PDF_HEADER.decode("ascii"), "restricted_version": "1.5"},
        "sampling": {"uniform_samples": SAMPLES},
        "source_sha256": {script_path.name: hashlib.sha256(script_path.read_bytes()).hexdigest()},
        "toolchain": {"cairo": cairo.cairo_version_string(), "font_file": str(font_path),
                       "font_sha256": hashlib.sha256(font_path.read_bytes()).hexdigest(),
                       "pycairo": cairo.version, "python": platform.python_version()},
        "visual_style": {"data_line_width_pt": DATA_LINE_WIDTH, "axis_line_width_pt": AXIS_LINE_WIDTH,
                          "grid_line_width_pt": GRID_LINE_WIDTH, "teacher": "blue filled marker",
                          "student": "red hollow marker on the zero line"},
    }
    OUTPUT_METADATA.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return record


if __name__ == "__main__":
    rec = render()
    print("wrote", OUTPUT_PDF.relative_to(HERE.parents[3]))
    print("configuration", json.dumps(rec["configuration"]))
    print("pdf sha256", rec["output_sha256"][OUTPUT_PDF.name])
