import unittest
import matplotlib.pyplot as plt
import numpy as np
from generate_panels import (check_mathematics, make_panel, WIDTH, critical_configuration,
                             residual, kernel, green, selected_gap, TEACHER_GUIDE, BLUE)


class BeamPanelTests(unittest.TestCase):
    def test_math(self):
        check_mathematics()

    def test_layout(self):
        sizes = []
        for gap, angular in ((False, False), (True, False), (False, True)):
            fig = make_panel(gap, angular=angular)
            fig.canvas.draw()
            ax = fig.axes[0]
            self.assertEqual(ax.get_xlabel(), "")
            for label in ax.get_yticklabels():
                self.assertGreaterEqual(label.get_window_extent(fig.canvas.get_renderer()).x0, 0)
            if gap:
                self.assertEqual(fig.legends, [])
                self.assertEqual(ax.get_xticklabels()[1].get_text(), r"$\zeta$")
            else:
                legend = fig.legends[0].get_window_extent(fig.canvas.get_renderer())
                self.assertGreater(legend.x0, ax.get_window_extent().x1)
                self.assertLess(legend.x1, fig.bbox.x1)
                self.assertLessEqual(legend.y1, ax.get_window_extent().y1+1e-8)
            if not gap and not angular:
                handles = fig.legends[0].legend_handles
                self.assertEqual(len(handles), 5)
                self.assertFalse(handles[0].is_dashed())
                self.assertTrue(all(h.get_linestyle() == ":" for h in handles[1:3]))
                self.assertEqual(handles[1].get_color(), handles[0].get_color())
                self.assertEqual(handles[2].get_color(), handles[0].get_color())
                self.assertEqual([h.get_label() for h in handles[1:3]],
                                 [r"$G(\cdot,\beta_2)$", r"$G(\cdot,\beta_3)$"])
                self.assertEqual(handles[3].get_marker(), "o")
                self.assertTrue(handles[3].is_dashed())
                self.assertEqual(handles[4].get_markerfacecolor(), "white")
            self.assertEqual(ax.get_ylim()[0 if gap or angular else 1], 0)
            curves = [l for l in ax.lines if l.get_gid() == "data-curve"]
            self.assertTrue(all(l.get_linewidth() == WIDTH for l in curves))
            if angular:
                self.assertEqual(len(curves), 2)
                x = curves[0].get_xdata()
                self.assertTrue(np.allclose(curves[1].get_ydata()-curves[0].get_ydata(),
                                            np.pi/2*np.cos(x), atol=1e-14, rtol=0))
            elif not gap:
                self.assertEqual(len(curves), 3)
                self.assertTrue(all(l.is_dashed() for l in curves[1:]))
                theta, masses = critical_configuration()
                self.assertTrue(np.allclose(curves[1].get_ydata()+curves[2].get_ydata(),
                                            residual(curves[1].get_xdata(), masses, theta),
                                            atol=1e-11, rtol=0))
            else:
                self.assertEqual(len(curves), 1)
                self.assertFalse(curves[0].is_dashed())
                theta, _ = critical_configuration()
                length, sources, _ = selected_gap(theta)
                self.assertTrue(np.allclose(curves[0].get_ydata(),
                                            green(curves[0].get_xdata(), length, sources[0])))
                markers = [l for l in ax.lines if l.get_marker() == "o"]
                self.assertEqual(len(markers), 1)
                self.assertEqual(markers[0].get_color(), BLUE)
                guide = [l for l in ax.lines if l.is_dashed()][0]
                self.assertEqual(guide.get_linewidth(), TEACHER_GUIDE["lw"])
                self.assertEqual(guide.get_alpha(), TEACHER_GUIDE["alpha"])
            sizes.append(ax.get_window_extent().size)
            plt.close(fig)
        self.assertTrue(all(np.isclose(sizes[0][1], s[1]) for s in sizes[1:]))
        self.assertGreater(sizes[0][0], sizes[1][0])
        self.assertTrue(np.allclose(sizes[1], sizes[2]))

    def test_angular_formulas(self):
        x = np.linspace(.01, np.pi-.01, 501)
        self.assertTrue(np.allclose(kernel(x), (np.pi/2-x)*np.cos(x)+np.sin(x)))
        self.assertTrue(np.allclose(kernel(x+np.pi), kernel(x)))
        self.assertTrue(np.allclose(kernel(x, 2)+kernel(x), 2*np.abs(np.sin(x))))
        self.assertAlmostEqual(kernel(np.pi)+np.pi/2*np.cos(np.pi), 0)
        self.assertGreaterEqual(np.min(kernel(x)), 1)

    def test_matching_source_guides_above_grid(self):
        figures = [make_panel(), make_panel(gap=True)]
        signatures = []
        for fig in figures:
            ax = fig.axes[0]
            guides = [line for line in ax.lines if line.get_color() == BLUE
                      and line.is_dashed() and len(line.get_xdata()) == 2]
            self.assertTrue(guides)
            for guide in guides:
                self.assertGreater(guide.get_zorder(), ax.xaxis.get_zorder())
                self.assertGreater(guide.get_zorder(), ax.yaxis.get_zorder())
                signatures.append((guide.get_color(), guide.get_linewidth(),
                                   guide.get_alpha(), guide._dash_pattern))
            plt.close(fig)
        self.assertTrue(all(s == signatures[0] for s in signatures))


if __name__ == "__main__":
    unittest.main()
