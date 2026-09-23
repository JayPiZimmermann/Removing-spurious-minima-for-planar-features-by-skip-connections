"""Focused mathematics and layout tests for the paper-native preview."""
import unittest
import numpy as np
from generate import check_geometry, make_figure, DATA_WIDTH, RADIAL_CUTOFF, MASSES


class FigureTests(unittest.TestCase):
    def test_mathematics(self):
        check_geometry()
        self.assertGreater(float(MASSES[2]), 1.3)

    def test_complete_lines_and_uniform_radial_cutoff(self):
        for panel, expected in (("student", 3), ("interlacing", 6)):
            ax = make_figure(panel).axes[0]
            self.assertEqual(sum(line.get_gid() == "radial-unit-line" for line in ax.lines), expected)
            self.assertEqual(sum(line.get_gid() == "radial-axis" for line in ax.lines), 2)
            for line in ax.lines:
                if line.get_gid() in ("radial-unit-line", "radial-axis"):
                    ends = line.get_xydata()
                    self.assertTrue(np.allclose(np.linalg.norm(ends, axis=1), RADIAL_CUTOFF))
                    self.assertTrue(np.allclose(ends[0], -ends[1]))

    def test_interlacing_labels_and_three_line_legend(self):
        fig = make_figure("interlacing")
        self.assertEqual(len(fig.texts), 3)
        self.assertTrue(all("\n" not in t.get_text() for t in fig.texts))
        labels = [t.get_text() for t in fig.axes[0].texts if t.get_text()]
        self.assertEqual(set(labels), {rf"${s}_{i}$" for s in ("v", "w") for i in (1, 2, 3)}
                         | {r"$\pi\equiv0$"})
        fig.canvas.draw()
        for text in fig.texts:
            extent = text.get_window_extent(fig.canvas.get_renderer())
            self.assertLess(extent.x1, fig.bbox.x1)

    def test_equal_circle_scale_axis_height_and_canvas_height(self):
        measurements = []
        for panel in ("student", "interlacing"):
            fig = make_figure(panel)
            fig.canvas.draw()
            transform = fig.axes[0].transData
            origin, unit = transform.transform([(0, 0), (1, 0)])
            measurements.append([np.linalg.norm(unit - origin) / fig.dpi,
                                 origin[1] / fig.dpi, fig.get_size_inches()[1]])
        self.assertTrue(np.allclose(*measurements, atol=1e-12, rtol=0))

    def test_widths_and_external_legends(self):
        for panel, expected_arrows in (("student", 3), ("interlacing", 6)):
            fig = make_figure(panel)
            arrow_count = 0
            for ax in fig.axes:
                for text in ax.texts:
                    patch = getattr(text, "arrow_patch", None)
                    if patch is not None and patch.get_arrowstyle().__class__.__name__ == "CurveB":
                        self.assertEqual(patch.get_linewidth(), DATA_WIDTH)
                        arrow_count += 1
            self.assertEqual(arrow_count, expected_arrows)
            for text in fig.texts:
                self.assertTrue(all(text.get_position()[0] > ax.get_position().x1 for ax in fig.axes))
            self.assertFalse(any("(a)" in t.get_text() or "(b)" in t.get_text()
                                 for t in fig.texts + fig.axes[0].texts))
            self.assertTrue(all(t.get_usetex() for t in fig.texts + fig.axes[0].texts))
            if panel == "student":
                sphere = next(t for t in fig.axes[0].texts if "mathbb" in t.get_text())
                fig.canvas.draw()
                extent = sphere.get_window_extent(fig.canvas.get_renderer())
                bounds = fig.axes[0].transData.inverted().transform(extent.get_points())
                # Here the label is wholly in the lower-right quadrant; its
                # upper-left corner is the closest point to the unit circle.
                self.assertGreater(np.linalg.norm([bounds[0, 0], bounds[1, 1]]), 1.02)
                labels = [t.get_text() for t in fig.axes[0].texts]
                self.assertNotIn(r"$s_i$", labels)
                self.assertIn(r"$0\equiv\pi$", labels)
                self.assertNotIn(r"$0$", labels)
                self.assertNotIn(r"$\pi$", labels)


if __name__ == "__main__":
    unittest.main()
