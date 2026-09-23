import unittest
import numpy as np
from generate_panels import make_panel, check_mathematics, DATA_WIDTH, POSITIONS


class PanelTests(unittest.TestCase):
    def test_mathematics(self):
        check_mathematics()

    def test_three_origins_and_nine_arrows(self):
        for plain in (False, True):
            fig = make_panel(plain)
            ax = fig.axes[0]
            origins = [line.get_xydata()[0] for line in ax.lines if line.get_gid() == "probe-origin"]
            self.assertTrue(np.allclose(origins, [[g, 0] for g in POSITIONS]))
            arrows = [line for line in ax.lines if line.get_gid() == "step-shaft"]
            self.assertEqual(len(arrows), 9)
            self.assertTrue(all(a.get_linewidth() == DATA_WIDTH for a in arrows))
            heads = [patch for patch in ax.patches if patch.get_gid() == "step-head"]
            self.assertEqual(len(heads), 9)
            for shaft, head in zip(arrows, heads):
                self.assertTrue(np.allclose(shaft.get_xydata()[-1], head.get_xy()[0], atol=1e-12))
            for i in range(0, 9, 3):
                self.assertTrue(np.array_equal(arrows[i].get_xydata()[-1], arrows[i+1].get_xydata()[0]))
            self.assertEqual(ax.get_xlabel(), "")
            self.assertEqual({t.get_text() for t in ax.texts if t.get_gid() == "unit-axis-label"},
                             {r"$\beta_1$", r"$\beta_2$", r"$\theta_1$", r"$\theta_2$"})
            self.assertEqual(sum(l.get_gid() == "probe-guide" for l in ax.lines), 1)
            guides = [l for l in ax.lines if l.get_gid() in ("unit-guide", "probe-guide")]
            self.assertEqual(len(guides), 5)
            self.assertTrue(all(l.get_linewidth() == DATA_WIDTH for l in guides))
            self.assertTrue(all(l.get_linestyle() == "--" for l in guides if l.get_gid() == "unit-guide"))
            curves = [l for l in ax.lines if l.get_gid() == "potential-curve"]
            self.assertEqual(len(curves), 3)
            self.assertTrue(all(l.get_linestyle() == "-" for l in curves))
            self.assertFalse(any("(a)" in t.get_text() or "(b)" in t.get_text() for t in ax.texts))

    def test_matching_scales_and_external_legends(self):
        positions = []
        for plain in (False, True):
            fig = make_panel(plain)
            fig.canvas.draw()
            ax = fig.axes[0]
            self.assertEqual(sum(l.get_gid() == "zero-axis" for l in ax.get_ygridlines()), 1)
            model = "R" if plain else "C"
            self.assertEqual([t.get_text() for t in fig.legends[0].get_texts()],
                             [rf"$P_{model}$", rf"$(-S_{model})$", rf"$(-F_{model})$"])
            self.assertEqual(fig.legends[0].handlelength, 1.6)
            for handle in fig.legends[0].legend_handles:
                self.assertAlmostEqual(np.ptp(handle.get_xdata()), 1.6*6.8)
                self.assertEqual(handle.get_linewidth(), DATA_WIDTH)
                self.assertEqual(handle.get_linestyle(), "-")
            positions.append(ax.transData.transform([(0, 0), (1, 1)]))
            legend = fig.legends[0].get_window_extent(fig.canvas.get_renderer())
            self.assertGreater(legend.x0, ax.get_window_extent().x1)
            self.assertLessEqual(legend.y1, ax.get_window_extent().y1+1e-8)
            self.assertLess(legend.x1, fig.bbox.x1)
            self.assertGreater(legend.x0, 0)
            for label in ax.texts:
                if label.get_gid() in ("unit-axis-label", "probe-axis-label"):
                    bounds = label.get_window_extent(fig.canvas.get_renderer())
                    self.assertGreater(bounds.y0, ax.get_window_extent().y1)
                    self.assertLess(bounds.y1, fig.bbox.y1)
                    self.assertLess(bounds.x1, legend.x0)
                    guide = next(l for l in ax.lines
                                 if l.get_gid() in ("unit-guide", "probe-guide")
                                 and l.get_xdata()[0] == label.xy[0])
                    tip = guide.get_transform().transform(guide.get_xydata()[-1])
                    self.assertAlmostEqual(tip[1], (bounds.y0+bounds.y1)/2)
            for guide in ax.lines:
                if guide.get_gid() in ("unit-guide", "probe-guide"):
                    self.assertGreater(guide.get_ydata()[-1], 1)
                    self.assertFalse(guide.get_clip_on())
        self.assertTrue(np.allclose(*positions))


if __name__ == "__main__":
    unittest.main()
