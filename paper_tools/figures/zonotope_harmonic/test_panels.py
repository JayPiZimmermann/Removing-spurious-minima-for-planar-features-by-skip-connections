import unittest
import matplotlib.pyplot as plt
import numpy as np
from generate_panels import make_panel, checked_data, WIDTH


class ZonotopePanels(unittest.TestCase):
    def test_identities(self):
        checked_data()

    def test_layout(self):
        for index in range(3):
            fig = make_panel(index)
            fig.canvas.draw()
            ax = fig.axes[0]
            renderer = fig.canvas.get_renderer()
            legend = fig.legends[0].get_window_extent(renderer)
            self.assertGreater(legend.x0, ax.get_window_extent().x1)
            self.assertLess(legend.x1, fig.bbox.x1)
            self.assertLessEqual(legend.y1, ax.get_window_extent().y1+1e-8)
            self.assertEqual(ax.get_xlabel(), "")
            self.assertEqual(ax.get_title(), "")
            if index == 0:
                origin, x, y = ax.transData.transform([(0, 0), (1, 0), (0, 1)])
                self.assertAlmostEqual(np.linalg.norm(x-origin), np.linalg.norm(y-origin))
                arrow = next(t for t in ax.texts if t.get_gid() == "translation-arrow")
                tau = checked_data()[0][1]
                self.assertTrue(np.allclose(arrow.xy, tau))
                self.assertEqual(arrow.xyann, (0, 0))
                label = next(t for t in ax.texts if t.get_gid() == "translation-label")
                self.assertEqual(label.get_text(), r"$\tau$")
                self.assertLess(np.linalg.norm(label.xyann), 3)
            for line in ax.lines:
                if line.get_gid() == "data-curve":
                    self.assertEqual(line.get_linewidth(), WIDTH)
            plt.close(fig)


if __name__ == "__main__":
    unittest.main()
