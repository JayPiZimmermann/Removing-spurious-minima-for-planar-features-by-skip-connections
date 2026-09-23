import Mathlib

/-!
# The residual as a bent ring

The planar centered residual is the radial displacement of a thin elastic ring of unit
radius bent in its plane by radial point forces (Love, *A Treatise on the Mathematical
Theory of Elasticity*, 4th ed., Art. 292). This module records the reduction behind that reading; the physical model itself is a
citation, not a theorem.

`eq_ring_operator`: Love's sixth-order operator on the tangential displacement `w` is
the derivative of the paper's beam operator `(D^2+1)^2` applied to the radial
displacement `u = w'`, which is the reduction used in the paper's remark.
-/

open Real MeasureTheory Set
open scoped BigOperators Interval

namespace PaperLeanFormalization.BentRing

noncomputable section

/-! ## Love's ring operator -/

/-- `eq:ring-operator`: for `u = w'`, `d/dθ [(D^2+1)^2 u] = w^{(6)} + 2 w^{(4)} + w''`. -/
theorem eq_ring_operator (w : ℝ → ℝ) (hw : ContDiff ℝ 6 w) (x : ℝ) :
    deriv (fun y => iteratedDeriv 4 (deriv w) y + 2 * iteratedDeriv 2 (deriv w) y + deriv w y)
        x =
      iteratedDeriv 6 w x + 2 * iteratedDeriv 4 w x + iteratedDeriv 2 w x := by
  have hw' : ContDiff ℝ ((5 + 1 : ℕ) : ℕ∞) w := by exact_mod_cast hw
  have h5 : ContDiff ℝ 5 (deriv w) := (contDiff_succ_iff_deriv.mp hw').2
  have hd4 : DifferentiableAt ℝ (iteratedDeriv 4 (deriv w)) x :=
    (h5.differentiable_iteratedDeriv 4 (by exact_mod_cast (by norm_num : (4 : ℕ) < 5))) x
  have hd2 : DifferentiableAt ℝ (iteratedDeriv 2 (deriv w)) x :=
    (h5.differentiable_iteratedDeriv 2 (by exact_mod_cast (by norm_num : (2 : ℕ) < 5))) x
  have hd0 : DifferentiableAt ℝ (deriv w) x :=
    (h5.differentiable (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 5))) x
  have e6 : iteratedDeriv 6 w = deriv (iteratedDeriv 4 (deriv w)) := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, iteratedDeriv_succ, show (5 : ℕ) = 4 + 1 from rfl,
      iteratedDeriv_succ']
  have e4 : iteratedDeriv 4 w = deriv (iteratedDeriv 2 (deriv w)) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, show (3 : ℕ) = 2 + 1 from rfl,
      iteratedDeriv_succ']
  have e2 : iteratedDeriv 2 w = deriv (deriv w) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hA : HasDerivAt (iteratedDeriv 4 (deriv w)) (iteratedDeriv 6 w x) x :=
    hd4.hasDerivAt.congr_deriv (by rw [e6])
  have hB : HasDerivAt (iteratedDeriv 2 (deriv w)) (iteratedDeriv 4 w x) x :=
    hd2.hasDerivAt.congr_deriv (by rw [e4])
  have hC : HasDerivAt (deriv w) (iteratedDeriv 2 w x) x :=
    hd0.hasDerivAt.congr_deriv (by rw [e2])
  exact ((hA.add (hB.const_mul 2)).add hC).deriv

end

end PaperLeanFormalization.BentRing
