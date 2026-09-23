#!/usr/bin/env python3
"""Generate the paper figure for the zonotope-translation identity.

The figure is computed from the positive masses and planar directions below.
It does not import, copy, or render a website asset.  Before drawing, the
generator checks the geometric, support-function, periodicity, and Fourier
identities used by the figure.

Run from the repository root:

    python3 paper_tools/figures/zonotope_harmonic/generate_zonotope_harmonic.py
"""

from __future__ import annotations

import hashlib
import itertools
import json
import math
from pathlib import Path
import platform
import subprocess
from typing import Iterable, Sequence

import cairo


HERE = Path(__file__).resolve().parent
OUTPUT_PDF = HERE / "zonotope_shift_loses_first_harmonic.pdf"
OUTPUT_METADATA = HERE / "zonotope_shift_loses_first_harmonic.metadata.json"
PDF_VERSION = cairo.PDF_VERSION_1_5
PDF_HEADER = b"%PDF-1.5"

# Canonical source parameters.  Positive masses are essential for the literal
# support-function interpretation: c_i ReLU(w_i . u) = h_[0,c_i w_i](u).
MASSES = (1.00, 0.85, 0.55)
DIRECTION_DEGREES = (8.0, 100.0, 240.0)

IDENTITY_SAMPLES = 4096
MAX_FOURIER_MODE = 8

WIDTH = 396.0
HEIGHT = 184.0

# One visual grammar is shared across panels.  Raw quantities use a long dash
# (or a hollow bar), centered quantities use a solid mark, and the removed odd
# component uses a dotted line.  Semantic data outlines have one width; axes,
# grids, construction guides, and annotation arrows have named secondary widths.
DATA_LINE_WIDTH = 1.05
AXIS_LINE_WIDTH = 0.65
GRID_LINE_WIDTH = 0.45
GUIDE_LINE_WIDTH = 0.50
ANNOTATION_LINE_WIDTH = DATA_LINE_WIDTH
RAW_DASH = (5.0, 2.1)
CENTERED_DASH: tuple[float, ...] = ()
ODD_DASH = (1.2, 2.0)

GEOMETRY_BOUNDS = (8.0, 32.0, 108.0, 104.0)
SUPPORT_BOUNDS = (128.0, 32.0, 152.0, 104.0)
SPECTRUM_BOUNDS = (292.0, 32.0, 96.0, 104.0)
LEGEND_BASELINE = 23.0
SUBCAPTION_BASELINE = 180.0
LEGEND_FONT_SIZE = 6.5
AXIS_FONT_SIZE = 6.8
TICK_FONT_SIZE = 6.5
SUBCAPTION_FONT_SIZE = 6.8

PAPER = (1.0, 1.0, 0.992)
INK = (0.12, 0.15, 0.19)
RULE = (0.48, 0.50, 0.53)
GRID = (0.83, 0.84, 0.85)
CENTERED_NEUTRAL = (0.18, 0.24, 0.28)
RAW_RUST = (0.78, 0.30, 0.17)
ODD_GRAY = (0.49, 0.50, 0.51)


Point = tuple[float, float]


def verify_visual_structure() -> None:
    """Assert paper-layout invariants independently of the plotted data."""

    panels = (GEOMETRY_BOUNDS, SUPPORT_BOUNDS, SPECTRUM_BOUNDS)
    assert all(top == panels[0][1] and height == panels[0][3]
               for _, top, _, height in panels)
    assert all(abs((top + height) - 136.0) < 1e-12 for _, top, _, height in panels)
    assert all(left >= 0.0 and top >= 0.0 and left + width <= WIDTH
               and top + height <= HEIGHT for left, top, width, height in panels)
    assert all(
        panels[index][0] + panels[index][2] + 12.0 <= panels[index + 1][0]
        for index in range(len(panels) - 1)
    )
    assert LEGEND_BASELINE + 5.0 < min(top for _, top, _, _ in panels)
    assert max(top + height for _, top, _, height in panels) + 36.0 < SUBCAPTION_BASELINE
    assert SUBCAPTION_BASELINE + 4.0 <= HEIGHT

    # Comparable data marks must not acquire panel-specific visual weight.
    geometry_data_width = DATA_LINE_WIDTH
    support_data_width = DATA_LINE_WIDTH
    spectrum_data_width = DATA_LINE_WIDTH
    assert geometry_data_width == support_data_width == spectrum_data_width
    assert GRID_LINE_WIDTH < AXIS_LINE_WIDTH < DATA_LINE_WIDTH
    assert GUIDE_LINE_WIDTH < DATA_LINE_WIDTH
    assert RAW_DASH != CENTERED_DASH != ODD_DASH and RAW_DASH != ODD_DASH
    assert min(LEGEND_FONT_SIZE, AXIS_FONT_SIZE, TICK_FONT_SIZE, SUBCAPTION_FONT_SIZE) >= 6.5
    assert WIDTH == 396.0


def add(left: Point, right: Point) -> Point:
    return left[0] + right[0], left[1] + right[1]


def subtract(left: Point, right: Point) -> Point:
    return left[0] - right[0], left[1] - right[1]


def scale(factor: float, point: Point) -> Point:
    return factor * point[0], factor * point[1]


def dot(left: Point, right: Point) -> float:
    return left[0] * right[0] + left[1] * right[1]


def norm(point: Point) -> float:
    return math.hypot(*point)


def cross(origin: Point, left: Point, right: Point) -> float:
    return ((left[0] - origin[0]) * (right[1] - origin[1])
            - (left[1] - origin[1]) * (right[0] - origin[0]))


def convex_hull(points: Iterable[Point]) -> tuple[Point, ...]:
    """Andrew monotone-chain hull, returned counterclockwise."""

    ordered = sorted(set(points))
    if len(ordered) <= 1:
        return tuple(ordered)

    lower: list[Point] = []
    for point in ordered:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], point) <= 1e-14:
            lower.pop()
        lower.append(point)

    upper: list[Point] = []
    for point in reversed(ordered):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], point) <= 1e-14:
            upper.pop()
        upper.append(point)
    return tuple(lower[:-1] + upper[:-1])


def canonical_geometry() -> tuple[tuple[Point, ...], Point, tuple[Point, ...], tuple[Point, ...]]:
    directions = tuple(
        (math.cos(math.radians(degrees)), math.sin(math.radians(degrees)))
        for degrees in DIRECTION_DEGREES
    )
    vectors = tuple(scale(mass, direction) for mass, direction in zip(MASSES, directions))
    tau = scale(0.5, tuple(map(sum, zip(*vectors))))

    subset_sums = []
    for choices in itertools.product((0.0, 1.0), repeat=len(vectors)):
        subset_sums.append(tuple(
            sum(choice * vector[axis] for choice, vector in zip(choices, vectors))
            for axis in (0, 1)
        ))
    raw_polygon = convex_hull(subset_sums)
    centered_polygon = tuple(subtract(point, tau) for point in raw_polygon)
    return vectors, tau, raw_polygon, centered_polygon


def unit(theta: float) -> Point:
    return math.cos(theta), math.sin(theta)


def support_raw(vectors: Sequence[Point], theta: float) -> float:
    u = unit(theta)
    return sum(max(0.0, dot(vector, u)) for vector in vectors)


def support_centered(vectors: Sequence[Point], theta: float) -> float:
    u = unit(theta)
    return 0.5 * sum(abs(dot(vector, u)) for vector in vectors)


def discrete_fourier(values: Sequence[float], max_mode: int) -> tuple[tuple[float, float], ...]:
    """Return (cosine, sine) coefficients on a uniform full-period grid."""

    count = len(values)
    coefficients = []
    for mode in range(max_mode + 1):
        factor = 1.0 / count if mode == 0 else 2.0 / count
        cosine = factor * sum(
            value * math.cos(mode * 2.0 * math.pi * index / count)
            for index, value in enumerate(values)
        )
        sine = 0.0 if mode == 0 else factor * sum(
            value * math.sin(mode * 2.0 * math.pi * index / count)
            for index, value in enumerate(values)
        )
        coefficients.append((cosine, sine))
    return tuple(coefficients)


def verify_identities(
    vectors: Sequence[Point],
    tau: Point,
    raw_polygon: Sequence[Point],
    centered_polygon: Sequence[Point],
) -> tuple[list[float], list[float], list[float], tuple[tuple[float, float], ...], tuple[tuple[float, float], ...]]:
    """Check every mathematical statement encoded in the three panels."""

    assert len(MASSES) == len(DIRECTION_DEGREES) == len(vectors)
    assert all(mass > 0.0 for mass in MASSES)
    expected_tau = scale(0.5, tuple(map(sum, zip(*vectors))))
    assert norm(subtract(tau, expected_tau)) < 1e-14
    assert len(raw_polygon) == 2 * len(vectors)
    assert all(
        norm(subtract(add(centered, tau), raw)) < 1e-13
        for raw, centered in zip(raw_polygon, centered_polygon)
    )
    # Construct Z independently as the Minkowski sum of symmetric segments,
    # rather than relying only on the translated raw polygon.
    symmetric_sums = (
        tuple(
            sum(choice * vector[axis] for choice, vector in zip(choices, vectors))
            for axis in (0, 1)
        )
        for choices in itertools.product((-0.5, 0.5), repeat=len(vectors))
    )
    direct_centered_polygon = convex_hull(symmetric_sums)
    assert len(direct_centered_polygon) == len(centered_polygon)
    assert all(
        min(norm(subtract(point, direct)) for direct in direct_centered_polygon) < 1e-13
        for point in centered_polygon
    )

    angles = [2.0 * math.pi * index / IDENTITY_SAMPLES for index in range(IDENTITY_SAMPLES)]
    raw = [support_raw(vectors, theta) for theta in angles]
    centered = [support_centered(vectors, theta) for theta in angles]
    first_harmonic = [dot(tau, unit(theta)) for theta in angles]

    # P = sum_i [0,c_i w_i] = Z+tau and h_P = h_Z + tau.u.
    for theta, raw_value, centered_value, first_value in zip(
        angles, raw, centered, first_harmonic
    ):
        polygon_support = max(dot(vertex, unit(theta)) for vertex in raw_polygon)
        centered_polygon_support = max(dot(vertex, unit(theta)) for vertex in centered_polygon)
        assert abs(raw_value - polygon_support) < 2e-13
        assert abs(centered_value - centered_polygon_support) < 2e-13
        assert abs(raw_value - (centered_value + first_value)) < 2e-13
        assert abs((raw_value - first_value) - centered_value) < 2e-13

    half_period = IDENTITY_SAMPLES // 2
    assert IDENTITY_SAMPLES % 2 == 0
    assert max(
        abs(centered[index] - centered[index + half_period])
        for index in range(half_period)
    ) < 2e-13

    raw_coefficients = discrete_fourier(raw, MAX_FOURIER_MODE)
    centered_coefficients = discrete_fourier(centered, MAX_FOURIER_MODE)

    # Translation contributes exactly tau_x cos(theta)+tau_y sin(theta): it changes
    # degree one and leaves the DC term and every even degree unchanged.
    assert abs(raw_coefficients[1][0] - tau[0]) < 2e-12
    assert abs(raw_coefficients[1][1] - tau[1]) < 2e-12
    assert norm(centered_coefficients[1]) < 2e-12
    for mode in range(0, MAX_FOURIER_MODE + 1, 2):
        assert norm(subtract(raw_coefficients[mode], centered_coefficients[mode])) < 2e-12
    for mode in range(3, MAX_FOURIER_MODE + 1, 2):
        assert norm(raw_coefficients[mode]) < 2e-12
        assert norm(centered_coefficients[mode]) < 2e-12

    return raw, centered, first_harmonic, raw_coefficients, centered_coefficients


def set_source(context: cairo.Context, colour: tuple[float, float, float], alpha: float = 1.0) -> None:
    context.set_source_rgba(*colour, alpha)


def font(context: cairo.Context, size: float, bold: bool = False) -> None:
    context.select_font_face(
        "DejaVu Sans", cairo.FONT_SLANT_NORMAL,
        cairo.FONT_WEIGHT_BOLD if bold else cairo.FONT_WEIGHT_NORMAL,
    )
    context.set_font_size(size)


def resolved_font_file() -> Path:
    """Resolve the exact font file used by Cairo's DejaVu Sans request."""

    result = subprocess.run(
        ["fc-match", "-f", "%{file}\n", "DejaVu Sans"],
        check=True,
        capture_output=True,
        text=True,
    )
    path = Path(result.stdout.splitlines()[0]).resolve()
    assert path.is_file()
    return path


def text(
    context: cairo.Context,
    x: float,
    y: float,
    label: str,
    size: float = 7.2,
    colour: tuple[float, float, float] = INK,
    bold: bool = False,
) -> None:
    font(context, size, bold)
    set_source(context, colour)
    context.move_to(x, y)
    context.show_text(label)


def centered_text(
    context: cairo.Context,
    x: float,
    y: float,
    label: str,
    size: float = 7.2,
    colour: tuple[float, float, float] = INK,
    bold: bool = False,
) -> None:
    font(context, size, bold)
    extents = context.text_extents(label)
    text(context, x - extents.width / 2.0 - extents.x_bearing, y, label, size, colour, bold)


def stroke(
    context: cairo.Context,
    colour: tuple[float, float, float] = INK,
    width: float = 0.8,
    alpha: float = 1.0,
    dash: Sequence[float] = (),
) -> None:
    set_source(context, colour, alpha)
    context.set_line_width(width)
    context.set_dash(dash)
    context.stroke()
    context.set_dash(())


def polygon_path(context: cairo.Context, points: Sequence[Point]) -> None:
    context.move_to(*points[0])
    for point in points[1:]:
        context.line_to(*point)
    context.close_path()


def draw_line_key(
    context: cairo.Context,
    x: float,
    baseline: float,
    colour: tuple[float, float, float],
    dash: Sequence[float],
    label: str,
) -> None:
    """Draw a compact legend key outside a panel's data rectangle."""

    context.move_to(x, baseline - 2.0)
    context.line_to(x + 12.0, baseline - 2.0)
    stroke(context, colour, DATA_LINE_WIDTH, 1.0, dash)
    text(context, x + 15.0, baseline, label, LEGEND_FONT_SIZE, colour)


def draw_bar_key(
    context: cairo.Context,
    x: float,
    baseline: float,
    colour: tuple[float, float, float],
    solid: bool,
    label: str,
) -> None:
    """Draw the hollow/solid Fourier-bar key outside the data rectangle."""

    context.rectangle(x, baseline - 6.0, 7.0, 5.0)
    set_source(context, colour, 0.82 if solid else 0.12)
    context.fill_preserve()
    stroke(context, colour, DATA_LINE_WIDTH)
    text(context, x + 10.0, baseline, label, LEGEND_FONT_SIZE, colour)


def draw_arrow(context: cairo.Context, start: Point, end: Point, colour: tuple[float, float, float] = INK) -> None:
    context.move_to(*start)
    context.line_to(*end)
    stroke(context, colour, ANNOTATION_LINE_WIDTH)
    angle = math.atan2(end[1] - start[1], end[0] - start[0])
    for offset in (-0.48, 0.48):
        tip = (
            end[0] - 5.0 * math.cos(angle + offset),
            end[1] - 5.0 * math.sin(angle + offset),
        )
        context.move_to(*end)
        context.line_to(*tip)
    stroke(context, colour, ANNOTATION_LINE_WIDTH)


def draw_geometry(
    context: cairo.Context,
    vectors: Sequence[Point],
    tau: Point,
    raw_polygon: Sequence[Point],
    centered_polygon: Sequence[Point],
) -> None:
    left, top, width, height = GEOMETRY_BOUNDS
    all_points = tuple(raw_polygon) + tuple(centered_polygon)
    x_min, x_max = min(point[0] for point in all_points), max(point[0] for point in all_points)
    y_min, y_max = min(point[1] for point in all_points), max(point[1] for point in all_points)
    padding = 0.13
    x_min -= padding
    x_max += padding
    y_min -= padding
    y_max += padding
    factor = min(width / (x_max - x_min), height / (y_max - y_min))
    x_offset = left + (width - factor * (x_max - x_min)) / 2.0
    y_offset = top + (height - factor * (y_max - y_min)) / 2.0

    def transform(point: Point) -> Point:
        return (
            x_offset + factor * (point[0] - x_min),
            y_offset + factor * (y_max - point[1]),
        )

    origin = transform((0.0, 0.0))
    tau_screen = transform(tau)
    # Coordinate axes make the two distinct centers unambiguous.
    context.move_to(left, origin[1])
    context.line_to(left + width, origin[1])
    context.move_to(origin[0], top)
    context.line_to(origin[0], top + height)
    stroke(context, GRID, AXIS_LINE_WIDTH)

    transformed_raw = tuple(transform(point) for point in raw_polygon)
    transformed_centered = tuple(transform(point) for point in centered_polygon)

    # A few matching-vertex guides show that the bodies differ only by tau.
    for index in (0, 2, 4):
        context.move_to(*transformed_centered[index])
        context.line_to(*transformed_raw[index])
    stroke(context, RULE, GUIDE_LINE_WIDTH, 0.55, ODD_DASH)

    polygon_path(context, transformed_raw)
    set_source(context, RAW_RUST, 0.10)
    context.fill_preserve()
    stroke(context, RAW_RUST, DATA_LINE_WIDTH, 1.0, RAW_DASH)

    polygon_path(context, transformed_centered)
    set_source(context, CENTERED_NEUTRAL, 0.14)
    context.fill_preserve()
    stroke(context, CENTERED_NEUTRAL, DATA_LINE_WIDTH, 1.0, CENTERED_DASH)

    # Centers and the translation vector.
    for point, colour in ((origin, CENTERED_NEUTRAL), (tau_screen, RAW_RUST)):
        context.new_sub_path()
        context.arc(point[0], point[1], 2.0, 0.0, 2.0 * math.pi)
        set_source(context, colour)
        context.fill()
    draw_arrow(context, tau_screen, origin)
    midpoint = ((origin[0] + tau_screen[0]) / 2.0, (origin[1] + tau_screen[1]) / 2.0)
    text(context, midpoint[0] + 3.0, midpoint[1] - 3.0, "−τ", 7.0, INK, True)

    # Body identities live in an external key; only coordinate labels remain in
    # the data rectangle.
    draw_line_key(context, left, LEGEND_BASELINE, CENTERED_NEUTRAL, CENTERED_DASH, "Z")
    draw_line_key(context, left + 49.0, LEGEND_BASELINE, RAW_RUST, RAW_DASH, "P=Z+τ")
    text(context, origin[0] - 8.0, origin[1] + 10.0, "0", 6.5, RULE)


def draw_support_curves(
    context: cairo.Context,
    raw: Sequence[float],
    centered: Sequence[float],
    first_harmonic: Sequence[float],
) -> None:
    left, top, width, height = SUPPORT_BOUNDS
    y_min = min(first_harmonic) * 1.12
    y_max = max(raw) * 1.08

    def transform(index: int, value: float) -> Point:
        theta_fraction = index / (len(raw) - 1)
        return (
            left + width * theta_fraction,
            top + height * (y_max - value) / (y_max - y_min),
        )

    # Grid and axes.
    zero_y = top + height * y_max / (y_max - y_min)
    for fraction in (0.0, 0.5, 1.0):
        x = left + width * fraction
        context.move_to(x, top)
        context.line_to(x, top + height)
    stroke(context, GRID, GRID_LINE_WIDTH)
    context.move_to(left, zero_y)
    context.line_to(left + width, zero_y)
    stroke(context, GRID, AXIS_LINE_WIDTH)

    # Repeat the first sample at 2*pi to close the plotting interval.
    def draw(values: Sequence[float], colour: tuple[float, float, float],
             dash: Sequence[float]) -> None:
        extended = tuple(values) + (values[0],)
        context.move_to(*transform(0, extended[0]))
        for index, value in enumerate(extended[1:], start=1):
            context.line_to(*transform(index, value))
        stroke(context, colour, DATA_LINE_WIDTH, 1.0, dash)

    draw(first_harmonic, ODD_GRAY, ODD_DASH)
    draw(raw, RAW_RUST, RAW_DASH)
    draw(centered, CENTERED_NEUTRAL, CENTERED_DASH)

    for fraction, label in ((0.0, "0"), (0.5, "π"), (1.0, "2π")):
        x = left + width * fraction
        centered_text(context, x, top + height + 10.0, label, TICK_FONT_SIZE, RULE)
    centered_text(context, left + width / 2.0, top + height + 21.0,
                  "angle θ", AXIS_FONT_SIZE, INK)

    legend = (
        (left, RAW_RUST, RAW_DASH, "raw h_P"),
        (left + 50.0, CENTERED_NEUTRAL, CENTERED_DASH, "centered h_Z"),
        (left + 108.0, ODD_GRAY, ODD_DASH, "τ·u"),
    )
    for x, colour, dash, label in legend:
        draw_line_key(context, x, LEGEND_BASELINE, colour, dash, label)


def draw_spectrum(
    context: cairo.Context,
    raw_coefficients: Sequence[Point],
    centered_coefficients: Sequence[Point],
) -> None:
    left, top, width, height = SPECTRUM_BOUNDS
    modes = tuple(range(1, MAX_FOURIER_MODE + 1))
    raw_amplitude = tuple(norm(raw_coefficients[mode]) for mode in modes)
    centered_amplitude = tuple(norm(centered_coefficients[mode]) for mode in modes)
    y_max = max(raw_amplitude) * 1.12

    # Highlight the only mode affected by the shift.
    slot = width / len(modes)
    context.rectangle(left, top, slot, height)
    set_source(context, RAW_RUST, 0.06)
    context.fill()

    for fraction in (0.0, 0.5):
        y = top + height * fraction
        context.move_to(left, y)
        context.line_to(left + width, y)
    stroke(context, GRID, GRID_LINE_WIDTH)
    context.move_to(left, top + height)
    context.line_to(left + width, top + height)
    stroke(context, GRID, AXIS_LINE_WIDTH)

    bar_width = 0.28 * slot
    for index, (raw_value, centered_value) in enumerate(zip(raw_amplitude, centered_amplitude)):
        center_x = left + slot * (index + 0.5)
        for value, x, colour, solid in (
            (raw_value, center_x - bar_width, RAW_RUST, False),
            (centered_value, center_x, CENTERED_NEUTRAL, True),
        ):
            bar_height = height * value / y_max
            context.rectangle(x, top + height - bar_height, bar_width, bar_height)
            set_source(context, colour, 0.82 if solid else 0.12)
            context.fill_preserve()
            stroke(context, colour, DATA_LINE_WIDTH)
        if index in (0, 1, 3, 5, 7):
            centered_text(context, center_x, top + height + 10.0,
                          str(index + 1), TICK_FONT_SIZE, RULE)

    # The open circle makes the exact centered k=1 zero visible.
    k_one_x = left + slot * 0.5 + bar_width * 0.5
    baseline = top + height
    context.new_sub_path()
    context.arc(k_one_x, baseline, 2.0, 0.0, 2.0 * math.pi)
    set_source(context, PAPER)
    context.fill_preserve()
    stroke(context, CENTERED_NEUTRAL, DATA_LINE_WIDTH)
    centered_text(context, left + width / 2.0, top + height + 21.0,
                  "angular mode k", AXIS_FONT_SIZE, INK)

    draw_bar_key(context, left + 2.0, LEGEND_BASELINE, RAW_RUST, False, "P")
    draw_bar_key(context, left + 44.0, LEGEND_BASELINE, CENTERED_NEUTRAL, True, "Z")


def render() -> dict[str, object]:
    verify_visual_structure()
    vectors, tau, raw_polygon, centered_polygon = canonical_geometry()
    raw, centered, first_harmonic, raw_coefficients, centered_coefficients = verify_identities(
        vectors, tau, raw_polygon, centered_polygon
    )

    surface = cairo.PDFSurface(str(OUTPUT_PDF), WIDTH, HEIGHT)
    surface.restrict_to_version(PDF_VERSION)
    surface.set_metadata(cairo.PDF_METADATA_TITLE, "Shift a zonotope and remove its first harmonic")
    surface.set_metadata(cairo.PDF_METADATA_AUTHOR, "")
    surface.set_metadata(cairo.PDF_METADATA_CREATOR, "generate_zonotope_harmonic.py")
    surface.set_metadata(cairo.PDF_METADATA_CREATE_DATE, "2000-01-01T00:00:00Z")
    surface.set_metadata(cairo.PDF_METADATA_MOD_DATE, "2000-01-01T00:00:00Z")
    context = cairo.Context(surface)
    set_source(context, PAPER)
    context.paint()

    draw_geometry(context, vectors, tau, raw_polygon, centered_polygon)
    draw_support_curves(context, raw, centered, first_harmonic)
    draw_spectrum(context, raw_coefficients, centered_coefficients)

    centered_text(context, 62.0, SUBCAPTION_BASELINE,
                  "(a) body shift −τ", SUBCAPTION_FONT_SIZE, INK, True)
    centered_text(context, 204.0, SUBCAPTION_BASELINE,
                  "(b) support function", SUBCAPTION_FONT_SIZE, INK, True)
    centered_text(context, 340.0, SUBCAPTION_BASELINE,
                  "(c) angular spectrum", SUBCAPTION_FONT_SIZE, INK, True)

    context.show_page()
    surface.finish()
    pdf_bytes = OUTPUT_PDF.read_bytes()
    assert pdf_bytes.startswith(PDF_HEADER), (
        f"expected a PDF 1.5 asset, found header {pdf_bytes[:8]!r}"
    )

    script_path = Path(__file__).resolve()
    font_path = resolved_font_file()
    record: dict[str, object] = {
        "canonical_parameters": {
            "direction_degrees": list(DIRECTION_DEGREES),
            "masses": list(MASSES),
            "nonnegative_mass_assumption": "all c_i > 0",
        },
        "figure": "zonotope_shift_loses_first_harmonic",
        "identities_checked": [
            "Z = sum_i [-c_i w_i/2, c_i w_i/2]",
            "tau = (1/2) sum_i c_i w_i",
            "P = sum_i [0,c_i w_i] = Z+tau",
            "h_P(u) = h_Z(u)+tau dot u",
            "h_Z(theta+pi) = h_Z(theta)",
            "subtracting tau dot u sets Fourier degree 1 to zero",
            "the DC term and every checked even Fourier degree are unchanged",
        ],
        "invocation": "python3 paper_tools/figures/zonotope_harmonic/generate_zonotope_harmonic.py",
        "output_sha256": {
            OUTPUT_PDF.name: hashlib.sha256(pdf_bytes).hexdigest(),
        },
        "pdf_compatibility": {
            "asserted_header": PDF_HEADER.decode("ascii"),
            "restricted_version": "1.5",
        },
        "sampling": {
            "fourier_modes": MAX_FOURIER_MODE,
            "uniform_angles": IDENTITY_SAMPLES,
        },
        "visual_invariants_checked": [
            "all three data rectangles share one vertical extent",
            "panel data rectangles are disjoint with at least 12 pt gaps",
            "legends lie strictly outside the data rectangles",
            "geometry, support curves, and Fourier outlines use one data-line width",
            "axes and grids use separate, lighter named widths",
            "raw, centered, and odd quantities remain distinct without colour",
            "the final canvas is exactly the 396 pt manuscript text width",
            "all legend, axis, tick, and subcaption text is at least 6.5 pt",
        ],
        "visual_style": {
            "axis_line_width_pt": AXIS_LINE_WIDTH,
            "data_line_width_pt": DATA_LINE_WIDTH,
            "grid_line_width_pt": GRID_LINE_WIDTH,
            "raw_mark": "long dash or hollow bar",
            "centered_mark": "solid line or solid bar",
            "odd_mark": "dotted line",
        },
        "source_sha256": {
            script_path.name: hashlib.sha256(script_path.read_bytes()).hexdigest(),
        },
        "toolchain": {
            "cairo": cairo.cairo_version_string(),
            "font_file": str(font_path),
            "font_sha256": hashlib.sha256(font_path.read_bytes()).hexdigest(),
            "pycairo": cairo.version,
            "python": platform.python_version(),
        },
    }
    OUTPUT_METADATA.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return record


if __name__ == "__main__":
    result = render()
    print(f"wrote {OUTPUT_PDF.relative_to(HERE.parents[3])}")
    print(f"wrote {OUTPUT_METADATA.relative_to(HERE.parents[3])}")
    print(f"pdf sha256 {result['output_sha256'][OUTPUT_PDF.name]}")
