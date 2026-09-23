import Definitions
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.LocalExtr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Networks, normalization, and residual formulas

The equations `eq:models-raw` and `eq:models` have separate declarations.
Normalization is proved on the open set of nonzero first-layer vectors;
the formula in the sketch does not define a sphere-valued map at zero.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

noncomputable section
open Real MeasureTheory Set
open scoped Interval

namespace PaperLeanFormalization.CircleMoments

theorem integral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn f g (Ioo a b)) : (∫ x in a..b, f x) = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := b)] with x hx
  rw [uIoc_of_le hab]
  intro hmem
  exact h (hx.mpr hmem)

theorem intervalIntegrable_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn f g (Ioo a b)) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hg ⊢
  apply hg.congr
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := b)] with x hx
  intro hmem
  exact (h (hx.mpr hmem)).symm

theorem integral_split_Ioo {f g k : ℝ → ℝ} {a r b : ℝ}
    (har : a ≤ r) (hrb : r ≤ b) (hg : Continuous g) (hk : Continuous k)
    (hleft : EqOn f g (Ioo a r)) (hright : EqOn f k (Ioo r b)) :
    (∫ x in a..b, f x) = (∫ x in a..r, g x) + ∫ x in r..b, k x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_congr_Ioo har hleft (hg.intervalIntegrable _ _))
    (intervalIntegrable_congr_Ioo hrb hright (hk.intervalIntegrable _ _)),
    integral_congr_Ioo har hleft, integral_congr_Ioo hrb hright]

theorem integral_cos_cos (a b t : ℝ) :
    (∫ y in a..b, cos y * cos (y + t)) =
      cos t * ((cos b * sin b - cos a * sin a + b - a) / 2) -
      sin t * ((sin b ^ 2 - sin a ^ 2) / 2) := by
  have heq : (fun y => cos y * cos (y + t)) =
      (fun y => cos t * cos y ^ 2 - sin t * (sin y * cos y)) := by
    funext y
    rw [cos_add]
    ring
  rw [heq, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_sq, integral_sin_mul_cos₁]
  · exact ((continuous_const.mul (continuous_cos.pow 2))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_sin.mul continuous_cos)).intervalIntegrable _ _

theorem integral_sin_cos (a b t : ℝ) :
    (∫ y in a..b, sin y * cos (y + t)) =
      cos t * ((sin b ^ 2 - sin a ^ 2) / 2) -
      sin t * ((sin a * cos a - sin b * cos b + b - a) / 2) := by
  have heq : (fun y => sin y * cos (y + t)) =
      (fun y => cos t * (sin y * cos y) - sin t * sin y ^ 2) := by
    funext y
    rw [cos_add]
    ring
  rw [heq, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_sin_mul_cos₁, integral_sin_sq]
  · exact (continuous_const.mul (continuous_sin.mul continuous_cos)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_sin.pow 2)).intervalIntegrable _ _

theorem integral_cos_sin (a b t : ℝ) :
    (∫ y in a..b, cos y * sin (y + t)) =
      cos t * ((sin b ^ 2 - sin a ^ 2) / 2) +
      sin t * ((cos b * sin b - cos a * sin a + b - a) / 2) := by
  have heq : (fun y => cos y * sin (y + t)) =
      (fun y => cos t * (sin y * cos y) + sin t * cos y ^ 2) := by
    funext y
    rw [sin_add]
    ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_sin_mul_cos₁, integral_cos_sq]
  · exact (continuous_const.mul (continuous_sin.mul continuous_cos)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_cos.pow 2)).intervalIntegrable _ _

theorem integral_sin_sin (a b t : ℝ) :
    (∫ y in a..b, sin y * sin (y + t)) =
      cos t * ((sin a * cos a - sin b * cos b + b - a) / 2) +
      sin t * ((sin b ^ 2 - sin a ^ 2) / 2) := by
  have heq : (fun y => sin y * sin (y + t)) =
      (fun y => cos t * sin y ^ 2 + sin t * (sin y * cos y)) := by
    funext y
    rw [sin_add]
    ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_sin_sq, integral_sin_mul_cos₁]
  · exact (continuous_const.mul (continuous_sin.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_sin.mul continuous_cos)).intervalIntegrable _ _

theorem sign_cos_mul_cos (y : ℝ) : sign (cos y) * cos y = |cos y| := by
  rcases lt_trichotomy (cos y) 0 with h | h | h
  · rw [sign_of_neg h, abs_of_neg h]
    ring
  · simp [h]
  · rw [sign_of_pos h, abs_of_pos h, one_mul]

theorem signed_pair_split {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ π)
    {h : ℝ → ℝ} (hh : Continuous h) :
    IntervalIntegrable (fun y => sign (cos y) * sign (cos (y+t)) * h y)
      volume (-(π/2)) (π/2) ∧
    (∫ y in -(π/2)..π/2, sign (cos y) * sign (cos (y+t)) * h y) =
      (∫ y in -(π/2)..π/2-t, h y) - ∫ y in π/2-t..π/2, h y := by
  have hleft : EqOn (fun y => sign (cos y) * sign (cos (y+t)) * h y)
      h (Ioo (-(π/2)) (π/2-t)) := by
    intro y hy
    have hy0 : 0 < cos y := cos_pos_of_mem_Ioo ⟨hy.1, by linarith [hy.2]⟩
    have hyt : 0 < cos (y+t) := cos_pos_of_mem_Ioo ⟨by linarith [hy.1], by linarith [hy.2]⟩
    simp only [sign_of_pos hy0, sign_of_pos hyt, one_mul]
  have hright : EqOn (fun y => sign (cos y) * sign (cos (y+t)) * h y)
      (fun y => -h y) (Ioo (π/2-t) (π/2)) := by
    intro y hy
    have hy0 : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith [hy.1], hy.2⟩
    have hyt : cos (y+t) < 0 := cos_neg_of_pi_div_two_lt_of_lt
      (by linarith [hy.1]) (by linarith [hy.2])
    simp only [sign_of_pos hy0, sign_of_neg hyt, one_mul, neg_one_mul]
  have har : -(π/2) ≤ π/2-t := by linarith
  have hrb : π/2-t ≤ π/2 := by linarith
  constructor
  · exact (intervalIntegrable_congr_Ioo har hleft (hh.intervalIntegrable _ _)).trans
      (intervalIntegrable_congr_Ioo hrb hright (hh.neg.intervalIntegrable _ _))
  · rw [integral_split_Ioo har hrb hh hh.neg hleft hright,
      intervalIntegral.integral_neg]
    simp only [sub_eq_add_neg]

theorem principal_cos_cos {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ π) :
    (∫ y in -(π/2)..π/2, |cos y| * |cos (y+t)|) =
      cos t * (π/2-t) + sin t := by
  have heq : (fun y => |cos y| * |cos (y+t)|) =
      (fun y => sign (cos y) * sign (cos (y+t)) * (cos y * cos (y+t))) := by
    funext y
    rw [← sign_cos_mul_cos y, ← sign_cos_mul_cos (y+t)]
    ring
  rw [heq, (signed_pair_split ht htpi (h := fun y => cos y * cos (y+t))
    (continuous_cos.mul (continuous_cos.comp (continuous_id.add continuous_const)))).2,
    integral_cos_cos, integral_cos_cos]
  simp only [cos_neg, cos_pi_div_two, sin_neg, sin_pi_div_two,
    cos_pi_div_two_sub, sin_pi_div_two_sub]
  nlinarith only [congrArg (fun z => sin t * z) (sin_sq_add_cos_sq t)]

theorem principal_sin_cos {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ π) :
    (∫ y in -(π/2)..π/2, (sign (cos y) * sin y) * |cos (y+t)|) =
      -sin t * (π/2-t) := by
  have heq : (fun y => (sign (cos y) * sin y) * |cos (y+t)|) =
      (fun y => sign (cos y) * sign (cos (y+t)) * (sin y * cos (y+t))) := by
    funext y
    rw [← sign_cos_mul_cos (y+t)]
    ring
  rw [heq, (signed_pair_split ht htpi (h := fun y => sin y * cos (y+t))
    (continuous_sin.mul (continuous_cos.comp (continuous_id.add continuous_const)))).2,
    integral_sin_cos, integral_sin_cos]
  simp only [cos_neg, cos_pi_div_two, sin_neg, sin_pi_div_two,
    cos_pi_div_two_sub, sin_pi_div_two_sub]
  nlinarith only [congrArg (fun z => cos t * z) (sin_sq_add_cos_sq t)]

theorem principal_cos_sin {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ π) :
    (∫ y in -(π/2)..π/2, |cos y| * (sign (cos (y+t)) * sin (y+t))) =
      sin t * (π/2-t) := by
  have heq : (fun y => |cos y| * (sign (cos (y+t)) * sin (y+t))) =
      (fun y => sign (cos y) * sign (cos (y+t)) * (cos y * sin (y+t))) := by
    funext y
    rw [← sign_cos_mul_cos y]
    ring
  rw [heq, (signed_pair_split ht htpi (h := fun y => cos y * sin (y+t))
    (continuous_cos.mul (continuous_sin.comp (continuous_id.add continuous_const)))).2,
    integral_cos_sin, integral_cos_sin]
  simp only [cos_neg, cos_pi_div_two, sin_neg, sin_pi_div_two,
    cos_pi_div_two_sub, sin_pi_div_two_sub]
  nlinarith only [congrArg (fun z => cos t * z) (sin_sq_add_cos_sq t)]

theorem principal_sin_sin {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ π) :
    (∫ y in -(π/2)..π/2,
      (sign (cos y) * sin y) * (sign (cos (y+t)) * sin (y+t))) =
      cos t * (π/2-t) - sin t := by
  have heq : (fun y => (sign (cos y) * sin y) * (sign (cos (y+t)) * sin (y+t))) =
      (fun y => sign (cos y) * sign (cos (y+t)) * (sin y * sin (y+t))) := by
    funext y
    ring
  rw [heq, (signed_pair_split ht htpi (h := fun y => sin y * sin (y+t))
    (continuous_sin.mul (continuous_sin.comp (continuous_id.add continuous_const)))).2,
    integral_sin_sin, integral_sin_sin]
  simp only [cos_neg, cos_pi_div_two, sin_neg, sin_pi_div_two,
    cos_pi_div_two_sub, sin_pi_div_two_sub]
  nlinarith only [congrArg (fun z => sin t * z) (sin_sq_add_cos_sq t)]

def A (y : ℝ) := |cos y|
def B (y : ℝ) := sign (cos y) * sin y
def K (t : ℝ) := cos t * arcsin (cos t) + |sin t|
def K1 (t : ℝ) := -sin t * arcsin (cos t)
def K2 (t : ℝ) := 2 * |sin t| - K t

theorem K_eq_sqrt (t : ℝ) :
    K t = cos t * arcsin (cos t) + sqrt (1-cos t^2) := by
  rw [K, abs_sin_eq_sqrt_one_sub_cos_sq]

theorem A_periodic : Function.Periodic A π := by
  intro y
  simp [A, cos_add_pi]

theorem B_periodic : Function.Periodic B π := by
  intro y
  simp [B, cos_add_pi, sin_add_pi, Real.sign_neg]

theorem K_periodic : Function.Periodic K π := by
  intro y
  simp [K, cos_add_pi, sin_add_pi, arcsin_neg]

theorem K1_periodic : Function.Periodic K1 π := by
  intro y
  simp [K1, cos_add_pi, sin_add_pi, arcsin_neg]

theorem K2_periodic : Function.Periodic K2 π := by
  intro y
  simp only [K2, sin_add_pi, abs_neg, K_periodic y]

theorem periodic_eq_of_principal {f g : ℝ → ℝ}
    (hf : Function.Periodic f π) (hg : Function.Periodic g π)
    (h : ∀ t, 0 ≤ t → t ≤ π → f t = g t) : f = g := by
  funext t
  obtain ⟨n, hn, _⟩ := existsUnique_add_zsmul_mem_Ico pi_pos t 0
  have hh := h (t+n•π) hn.1 (by simpa using hn.2.le)
  rwa [hf.zsmul n t, hg.zsmul n t] at hh

theorem moment_periodic (f g : ℝ → ℝ) (hg : Function.Periodic g π) :
    Function.Periodic (fun t => ∫ y in -(π/2)..π/2, f y * g (y+t)) π := by
  intro t
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [← add_assoc, hg]

theorem arcsin_cos_principal {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ π) :
    arcsin (cos t) = π/2-t := by
  rw [← sin_pi_div_two_sub t, arcsin_sin (by linarith) (by linarith)]

theorem moment_AA (t : ℝ) :
    (∫ y in -(π/2)..π/2, A y * A (y+t)) = K t := by
  apply congrFun (periodic_eq_of_principal
    (moment_periodic A A A_periodic) K_periodic ?_) t
  intro z hz hzpi
  simpa only [A, K, arcsin_cos_principal hz hzpi,
    abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hz hzpi)] using principal_cos_cos hz hzpi

theorem moment_BA (t : ℝ) :
    (∫ y in -(π/2)..π/2, B y * A (y+t)) = K1 t := by
  apply congrFun (periodic_eq_of_principal
    (moment_periodic B A A_periodic) K1_periodic ?_) t
  intro z hz hzpi
  simpa only [A, B, K1, arcsin_cos_principal hz hzpi] using principal_sin_cos hz hzpi

theorem moment_AB (t : ℝ) :
    (∫ y in -(π/2)..π/2, A y * B (y+t)) = -K1 t := by
  apply congrFun (periodic_eq_of_principal
    (moment_periodic A B B_periodic) (g := fun z => -K1 z)
    (fun z => congrArg Neg.neg (K1_periodic z)) ?_) t
  intro z hz hzpi
  simpa only [A, B, K1, arcsin_cos_principal hz hzpi, neg_mul, neg_neg]
    using principal_cos_sin hz hzpi

theorem moment_BB (t : ℝ) :
    (∫ y in -(π/2)..π/2, B y * B (y+t)) = -K2 t := by
  apply congrFun (periodic_eq_of_principal
    (moment_periodic B B B_periodic) (g := fun z => -K2 z)
    (fun z => congrArg Neg.neg (K2_periodic z)) ?_) t
  intro z hz hzpi
  rw [show (∫ y in -(π/2)..π/2, B y * B (y+z)) =
    cos z * (π/2-z) - sin z from principal_sin_sin hz hzpi]
  simp only [K2, K, arcsin_cos_principal hz hzpi,
    abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hz hzpi)]
  ring

theorem pair_shift (f g : ℝ → ℝ) (hf : Function.Periodic f π)
    (hg : Function.Periodic g π) (a b : ℝ) :
    (∫ y in (0:ℝ)..π, f (y-a) * g (y-b)) =
    ∫ y in -(π/2)..π/2, f y * g (y+(a-b)) := by
  have hp : Function.Periodic (fun y => f y * g (y+(a-b))) π := by
    intro y
    dsimp only
    rw [hf, add_right_comm y π (a-b), hg]
  have heq : (fun y => f (y-a) * g (y-b)) =
    (fun y => (fun z => f z * g (z+(a-b))) (y-a)) := by
    funext y
    congr 2
    ring
  rw [heq, intervalIntegral.integral_comp_sub_right (fun z => f z * g (z+(a-b))) a]
  convert hp.intervalIntegral_add_eq (-a) (-(π/2)) using 1 <;> congr 1 <;> ring

theorem pair_AA (a b : ℝ) :
    (∫ y in (0:ℝ)..π, |cos (y-a)| * |cos (y-b)|) = K (a-b) := by
  exact (pair_shift A A A_periodic A_periodic a b).trans (moment_AA (a-b))

theorem pair_BA (a b : ℝ) :
    (∫ y in (0:ℝ)..π, (sign (cos (y-a)) * sin (y-a)) * |cos (y-b)|) = K1 (a-b) := by
  exact (pair_shift B A B_periodic A_periodic a b).trans (moment_BA (a-b))

theorem pair_AB (a b : ℝ) :
    (∫ y in (0:ℝ)..π, |cos (y-a)| * (sign (cos (y-b)) * sin (y-b))) = -K1 (a-b) := by
  exact (pair_shift A B A_periodic B_periodic a b).trans (moment_AB (a-b))

theorem pair_BB (a b : ℝ) :
    (∫ y in (0:ℝ)..π, (sign (cos (y-a)) * sin (y-a)) *
      (sign (cos (y-b)) * sin (y-b))) = -K2 (a-b) := by
  exact (pair_shift B B B_periodic B_periodic a b).trans (moment_BB (a-b))

theorem measurable_sign : Measurable Real.sign := by
  unfold Real.sign
  exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const)

theorem abs_sign_le_one (r : ℝ) : |Real.sign r| ≤ 1 := by
  rcases sign_apply_eq r with h | h | h <;> simp [h]

theorem A_measurable : Measurable A := continuous_cos.abs.measurable

theorem B_measurable : Measurable B :=
  (measurable_sign.comp continuous_cos.measurable).mul continuous_sin.measurable

theorem A_bounded (y : ℝ) : |A y| ≤ 1 := by
  simpa [A] using abs_cos_le_one y

theorem B_bounded (y : ℝ) : |B y| ≤ 1 := by
  dsimp [B]
  rw [abs_mul]
  exact (mul_le_mul (abs_sign_le_one _) (abs_sin_le_one y) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

theorem pair_intervalIntegrable {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hfb : ∀ y, |f y| ≤ 1) (hgb : ∀ y, |g y| ≤ 1)
    (a b l r : ℝ) : IntervalIntegrable (fun y => f (y-a) * g (y-b)) volume l r := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun
  · exact ((hf.comp (measurable_id.sub_const a)).mul
      (hg.comp (measurable_id.sub_const b))).aestronglyMeasurable
  · apply Filter.eventually_of_forall
    intro y
    simp only [Real.norm_eq_abs, abs_one, abs_mul]
    exact (mul_le_mul (hfb _) (hgb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem pair_AA_integrable (a b l r : ℝ) :
    IntervalIntegrable (fun y => |cos (y-a)| * |cos (y-b)|) volume l r :=
  pair_intervalIntegrable A_measurable A_measurable A_bounded A_bounded a b l r

theorem pair_BA_integrable (a b l r : ℝ) :
    IntervalIntegrable (fun y => (sign (cos (y-a)) * sin (y-a)) * |cos (y-b)|) volume l r :=
  pair_intervalIntegrable B_measurable A_measurable B_bounded A_bounded a b l r

theorem pair_AB_integrable (a b l r : ℝ) :
    IntervalIntegrable (fun y => |cos (y-a)| * (sign (cos (y-b)) * sin (y-b))) volume l r :=
  pair_intervalIntegrable A_measurable B_measurable A_bounded B_bounded a b l r

theorem pair_BB_integrable (a b l r : ℝ) :
    IntervalIntegrable (fun y => (sign (cos (y-a)) * sin (y-a)) *
      (sign (cos (y-b)) * sin (y-b))) volume l r :=
  pair_intervalIntegrable B_measurable B_measurable B_bounded B_bounded a b l r

end PaperLeanFormalization.CircleMoments

/-!
Fresh rotational Gaussian reduction. All inactive coordinates are integrated
at once with finite-product Fubini, rather than a coordinate-peeling induction.
-/

noncomputable section
open Real MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace PaperLeanFormalization.Preliminaries

/-- The normalized scalar Gaussian is used only inside the product argument. -/
def GaussianScalarDensity (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)

theorem integral_gaussian_scalar_density : (∫ t : ℝ, GaussianScalarDensity t) = 1 := by
  unfold GaussianScalarDensity
  rw [integral_mul_left]
  have hfun : (fun t : ℝ => Real.exp (-t ^ 2 / 2)) =
      fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    ext t
    congr 1
    ring
  rw [hfun, integral_gaussian, show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
  rw [inv_mul_cancel (ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)))]

/-- Finite-product Fubini removes all independent Gaussian coordinates at once. -/
theorem integral_gaussian_product_density (I : Type*) [Fintype I] :
    (∫ x : I → ℝ, ∏ i, GaussianScalarDensity (x i)) = 1 := by
  rw [MeasureTheory.integral_fintype_prod_eq_pow, integral_gaussian_scalar_density,
    one_pow]

theorem gaussian_product_density_formula (I : Type*) [Fintype I] (x : I → ℝ) :
    (∏ i, GaussianScalarDensity (x i)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card I *
        Real.exp (-(∑ i, x i ^ 2) / 2) := by
  simp only [GaussianScalarDensity, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The first component of a sum-indexed Gaussian has the expected marginal.
No integrability side condition on the arbitrary test function is needed. -/
theorem gaussian_sum_marginal {I J : Type*} [Fintype I] [Fintype J]
    (F : (I → ℝ) → ℝ) :
    (∫ x : I ⊕ J → ℝ, F (fun i => x (.inl i)) *
      ∏ k, GaussianScalarDensity (x k)) =
      ∫ y : I → ℝ, F y * ∏ i, GaussianScalarDensity (y i) := by
  rw [← (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : I ⊕ J => ℝ)).integral_comp']
  have hpoint : (fun x : (I → ℝ) × (J → ℝ) =>
      F (fun i => (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm x
        (.inl i)) * ∏ k, GaussianScalarDensity
          ((MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm x k)) =
      fun x => (F x.1 * ∏ i, GaussianScalarDensity (x.1 i)) *
        ∏ j, GaussianScalarDensity (x.2 j) := by
    ext x
    simp only [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply,
      Sum.elim_inl, Sum.elim_inr, Fintype.prod_sum_type]
    ring
  rw [hpoint, show (volume : Measure ((I → ℝ) × (J → ℝ))) =
      (volume : Measure (I → ℝ)).prod (volume : Measure (J → ℝ)) from rfl,
    integral_prod_mul (fun y : I → ℝ => F y * ∏ i, GaussianScalarDensity (y i))
      (fun z : J → ℝ => ∏ j, GaussianScalarDensity (z j)),
    integral_gaussian_product_density J, mul_one]

/-- An orthonormal coordinate change identifies the radial density with the
product of normalized scalar densities. -/
theorem gaussian_density_in_basis {d : ℕ} {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) :
    (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2) =
      ∏ i, GaussianScalarDensity (b.repr x i) := by
  have hcard : Fintype.card I = d := by
    rw [← FiniteDimensional.finrank_eq_card_basis b.toBasis, finrank_euclideanSpace_fin]
  have hnorm : ‖x‖ ^ 2 = ∑ i, (b.repr x i) ^ 2 := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [gaussian_product_density_formula, hcard, hnorm]

/-- Gaussian rotation invariance, with the literal density and arbitrary
test functions. The two transports are volume-preserving equivalences. -/
theorem gaussian_integral_in_basis {d : ℕ} {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ (Fin d))) (F : (I → ℝ) → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin d), F (fun i => b.repr x i) *
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2))) =
      ∫ y : I → ℝ, F y * ∏ i, GaussianScalarDensity (y i) := by
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin d),
        (fun y : EuclideanSpace ℝ I => F (fun i => y i) *
          ∏ i, GaussianScalarDensity (y i)) (b.repr x) := by
      congr 1
      ext x
      rw [gaussian_density_in_basis b x]
    _ = ∫ y : EuclideanSpace ℝ I, F (fun i => y i) *
        ∏ i, GaussianScalarDensity (y i) :=
      b.measurePreserving_repr.integral_comp b.repr.toHomeomorph.measurableEmbedding
        (fun y : EuclideanSpace ℝ I => F (fun i => y i) *
          ∏ i, GaussianScalarDensity (y i))
    _ = _ := (EuclideanSpace.volume_preserving_measurableEquiv I).integral_comp'
      (fun y : I → ℝ => F y * ∏ i, GaussianScalarDensity (y i))

/-- The two-dimensional product density has normalization `1/(2π)`. -/
theorem gaussian_scalar_density_pair (a b : ℝ) :
    GaussianScalarDensity a * GaussianScalarDensity b =
      (2 * Real.pi)⁻¹ * Real.exp (-(a ^ 2 + b ^ 2) / 2) := by
  unfold GaussianScalarDensity
  have hsq : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 *
        (Real.exp (-a ^ 2 / 2) * Real.exp (-b ^ 2 / 2)) := by ring
    _ = _ := by
      rw [← Real.exp_add, inv_pow, hsq]
      congr 2
      ring

/-- Any two designated orthonormal coordinates have the literal bivariate
standard Gaussian law. All other coordinates disappear in one Fubini step. -/
theorem gaussian_first_two_coordinates {d k : ℕ}
    (b : OrthonormalBasis (Fin 2 ⊕ Fin k) ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ σ : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      |b.repr x (.inl 0)| * |ρ * b.repr x (.inl 0) + σ * b.repr x (.inl 1)| *
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2))) =
      ∫ p : ℝ × ℝ, |p.1| * |ρ * p.1 + σ * p.2| *
        ((2 * Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2)) := by
  rw [gaussian_integral_in_basis b
    (fun y => |y (.inl 0)| * |ρ * y (.inl 0) + σ * y (.inl 1)|),
    gaussian_sum_marginal (J := Fin k)
      (fun y : Fin 2 → ℝ => |y 0| * |ρ * y 0 + σ * y 1|)]
  have hp := (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm
  rw [← hp.integral_comp' (fun y : Fin 2 → ℝ =>
    |y 0| * |ρ * y 0 + σ * y 1| * ∏ i, GaussianScalarDensity (y i))]
  congr 1
  ext p
  change |p.1| * |ρ * p.1 + σ * p.2| *
    (∏ i : Fin 2, GaussianScalarDensity
      ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm p i)) = _
  rw [Fin.prod_univ_two]
  change |p.1| * |ρ * p.1 + σ * p.2| *
    (GaussianScalarDensity p.1 * GaussianScalarDensity p.2) = _
  rw [gaussian_scalar_density_pair]

end PaperLeanFormalization.Preliminaries

noncomputable section
open scoped RealInnerProductSpace

namespace PaperLeanFormalization.Preliminaries

private theorem basis_with_first {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (hdim : FiniteDimensional.finrank ℝ E = Fintype.card ι)
    (i : ι) (w : E) (hw : ‖w‖ = 1) :
    ∃ b : OrthonormalBasis ι ℝ E, b i = w := by
  classical
  have horth : Orthonormal ℝ (({i} : Set ι).restrict (fun _ => w)) := by
    constructor
    · intro _j
      exact hw
    · intro j k hjk
      have hj : j.val = i := j.property
      have hk : k.val = i := k.property
      exact (hjk (Subtype.ext (hj.trans hk.symm))).elim
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hdim
  exact ⟨b, hb i (by simp)⟩

private theorem basis_with_pair {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (hdim : FiniteDimensional.finrank ℝ E = Fintype.card ι)
    (i j : ι) (hij : i ≠ j) (w z : E) (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (hwz : (inner w z : ℝ) = 0) :
    ∃ b : OrthonormalBasis ι ℝ E, b i = w ∧ b j = z := by
  classical
  let v : ι → E := fun k => if k = i then w else z
  have hzw : (inner z w : ℝ) = 0 := by rw [real_inner_comm, hwz]
  have horth : Orthonormal ℝ (({i,j} : Set ι).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨l, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk hl
    rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;>
      simp [Set.restrict_apply, v, hij, hij.symm, real_inner_self_eq_norm_sq,
        hw, hz, hwz, hzw]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hdim
  refine ⟨b, ?_, ?_⟩
  · simpa [v] using hb i (by simp)
  · simpa [v, hij.symm] using hb j (by simp)

/-- Adapted Gaussian coordinates, with the first two variables explicitly
separated from the remaining `d-2` variables. Collinear directions use any
orthonormal completion of the first direction; their second coefficient is zero.
-/
theorem gaussian_adapted_coordinates {d : ℕ} (hd : 2 ≤ d)
    (w u : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 2 ⊕ Fin (d-2)) ℝ (EuclideanSpace ℝ (Fin d)),
      b (Sum.inl 0) = w ∧
      (∀ x, (inner w x : ℝ) = b.repr x (Sum.inl 0)) ∧
      (∀ x, (inner u x : ℝ) = (inner w u : ℝ) * b.repr x (Sum.inl 0) +
        Real.sqrt (1-(inner w u : ℝ)^2) * b.repr x (Sum.inl 1)) := by
  classical
  have hdim : FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin d)) =
      Fintype.card (Fin 2 ⊕ Fin (d-2)) := by
    simp only [finrank_euclideanSpace_fin, Fintype.card_sum, Fintype.card_fin]
    exact (Nat.add_sub_of_le hd).symm
  let ρ := (inner w u : ℝ)
  let q := u - ρ • w
  have hww : (inner w w : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hw, one_pow]
  have horth : (inner w q : ℝ) = 0 := by
    dsimp only [q, ρ]
    rw [inner_sub_right, real_inner_smul_right, hww, mul_one, sub_self]
  have hnorm : ‖q‖^2 = 1-ρ^2 := by
    dsimp only [q]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hw, hu,
      real_inner_smul_right, real_inner_comm u w]
    rw [mul_one, sq_abs]
    ring
  have hsqrt : Real.sqrt (1-ρ^2) = ‖q‖ := by
    rw [← hnorm, Real.sqrt_sq (norm_nonneg q)]
  have hfinish (b : OrthonormalBasis (Fin 2 ⊕ Fin (d-2)) ℝ
      (EuclideanSpace ℝ (Fin d))) (hb : b (Sum.inl 0) = w)
      (hu' : u = ρ • w + Real.sqrt (1-ρ^2) • b (Sum.inl 1)) :
      b (Sum.inl 0) = w ∧
      (∀ x, (inner w x : ℝ) = b.repr x (Sum.inl 0)) ∧
      (∀ x, (inner u x : ℝ) = (inner w u : ℝ) * b.repr x (Sum.inl 0) +
        Real.sqrt (1-(inner w u : ℝ)^2) * b.repr x (Sum.inl 1)) := by
    refine ⟨hb, ?_, ?_⟩
    · intro x
      rw [OrthonormalBasis.repr_apply_apply, hb]
    · intro x
      conv_lhs => rw [hu']
      simp only [inner_add_left, real_inner_smul_left,
        OrthonormalBasis.repr_apply_apply, hb]
  by_cases hq : q = 0
  · obtain ⟨b, hb⟩ := basis_with_first hdim (Sum.inl (0 : Fin 2)) w hw
    refine ⟨b, hfinish b hb ?_⟩
    have hu' : u = ρ • w := sub_eq_zero.mp hq
    rw [hsqrt, hq, norm_zero, zero_smul, add_zero, hu']
  · obtain ⟨b, hb0, hb1⟩ := basis_with_pair hdim
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) (by simp)
      w (‖q‖⁻¹ • q) hw (norm_smul_inv_norm hq) (by
        rw [real_inner_smul_right, horth, mul_zero])
    refine ⟨b, hfinish b hb0 ?_⟩
    rw [hb1, hsqrt, smul_smul, mul_inv_cancel (norm_ne_zero_iff.mpr hq), one_smul]
    dsimp only [q]
    abel

end PaperLeanFormalization.Preliminaries

noncomputable section
open Real MeasureTheory Set
open scoped Interval

namespace PaperLeanFormalization.GaussianAbsoluteMoment2D

open CircleMoments

theorem radial_fourth_moment :
    (∫ r in Ioi (0:ℝ), r^3 * exp (-(r^2)/2)) = 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hg : Gamma (2:ℝ) = 1 := by simp
  have hpow3 : ∀ r : ℝ, r^(3:ℝ) = r^3 := fun r => rpow_nat_cast r 3
  simp only [hpow3, rpow_two] at h
  have heq : (fun r : ℝ => r^3 * exp (-(1/2:ℝ)*r^2)) =
      (fun r : ℝ => r^3 * exp (-(r^2)/2)) := by
    funext r
    congr 2
    ring
  rw [heq] at h
  norm_num [rpow_neg (by norm_num : (0:ℝ) ≤ 1/2), rpow_two, hg] at h
  exact h

theorem circular_full_period (a b : ℝ) :
    (∫ y in Ioo (-π) π, |cos (y-a)| * |cos (y-b)|) = 2 * CircleMoments.K (a-b) := by
  let f : ℝ → ℝ := fun y => |cos (y-a)| * |cos (y-b)|
  have hf : Function.Periodic f π := by
    intro y
    dsimp [f]
    rw [show y+π-a = (y-a)+π by ring, show y+π-b = (y-b)+π by ring]
    simp [cos_add_pi]
  have hs : (∫ y in (-π)..π, f y) = 2 * ∫ y in (0:ℝ)..π, f y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (CircleMoments.pair_AA_integrable a b (-π) 0)
      (CircleMoments.pair_AA_integrable a b 0 π)]
    have hp := hf.intervalIntegral_add_eq (-π) 0
    simp only [add_left_neg, zero_add] at hp
    rw [hp]
    ring
  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  exact hs.trans (congrArg (fun z => 2*z) (CircleMoments.pair_AA a b))

theorem gaussian_abs_pair_angle (t : ℝ) :
    (∫ p : ℝ × ℝ, |p.1| * |cos t * p.1 + sin t * p.2| *
      (2*π)⁻¹ * exp (-(p.1^2+p.2^2)/2)) = (2/π) * CircleMoments.K t := by
  rw [← integral_comp_polarCoord_symm]
  have heq : (∫ p in polarCoord.target, p.1 •
      (|((polarCoord.symm p).1)| *
      |cos t * (polarCoord.symm p).1 + sin t * (polarCoord.symm p).2| *
      (2*π)⁻¹ * exp (-((polarCoord.symm p).1^2+(polarCoord.symm p).2^2)/2))) =
      (∫ r in Ioi (0:ℝ), r^3 * exp (-(r^2)/2)) *
      ∫ y in Ioo (-π) π, (2*π)⁻¹ * (|cos y| * |cos (y-t)|) := by
    rw [← set_integral_prod_mul]
    apply set_integral_congr (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    simp only [polarCoord_symm_apply, smul_eq_mul]
    have hr : 0 ≤ p.1 := le_of_lt hp.1
    have hlin : cos t * (p.1*cos p.2) + sin t * (p.1*sin p.2) =
        p.1 * cos (p.2-t) := by
      rw [cos_sub]
      ring
    have hs : (p.1*cos p.2)^2+(p.1*sin p.2)^2=p.1^2 := by
      nlinarith only [congrArg (fun z => p.1^2*z) (cos_sq_add_sin_sq p.2)]
    rw [hlin, hs, abs_mul, abs_mul, abs_of_nonneg hr]
    ring
  rw [heq, radial_fourth_moment, integral_mul_left]
  have hc := circular_full_period 0 t
  simp only [sub_zero] at hc
  rw [hc]
  have hK : CircleMoments.K (0-t) = CircleMoments.K t := by
    simp [CircleMoments.K, cos_neg, sin_neg]
  rw [hK]
  field_simp
  ring

theorem gaussian_abs_pair_correlation {ρ : ℝ} (hρlo : -1 ≤ ρ) (hρhi : ρ ≤ 1) :
    (∫ p : ℝ × ℝ, |p.1| * |ρ * p.1 + sqrt (1-ρ^2) * p.2| *
      (2*π)⁻¹ * exp (-(p.1^2+p.2^2)/2)) =
    (2/π) * (ρ * arcsin ρ + sqrt (1-ρ^2)) := by
  have htlo := arccos_nonneg ρ
  have hthi := arccos_le_pi ρ
  have hcos := cos_arccos hρlo hρhi
  have hsin : sin (arccos ρ) = sqrt (1-ρ^2) := by
    rw [sin_eq_sqrt_one_sub_cos_sq htlo hthi, hcos]
  have h := gaussian_abs_pair_angle (arccos ρ)
  rw [hcos, hsin, CircleMoments.K_eq_sqrt, hcos] at h
  exact h

end PaperLeanFormalization.GaussianAbsoluteMoment2D

noncomputable section
open Real MeasureTheory
open scoped RealInnerProductSpace

namespace PaperLeanFormalization.Preliminaries

/-- The literal Gaussian absolute pair moment, proved by an adapted
orthonormal coordinate change, one product-Fubini marginalization, and the
fresh polar evaluation of the two-dimensional moment. -/
theorem gaussian_absolute_pair_moment {d : ℕ} (hd : 2 ≤ d)
    {w u : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      |(inner w x : ℝ)| * |(inner u x : ℝ)| *
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2))) =
      (2 / Real.pi) * ((inner w u : ℝ) * Real.arcsin (inner w u) +
        Real.sqrt (1 - (inner w u : ℝ) ^ 2)) := by
  obtain ⟨b, _, hfirst, hsecond⟩ := gaussian_adapted_coordinates hd w u hw hu
  have hρ : |(inner w u : ℝ)| ≤ 1 := by
    simpa only [hw, hu, mul_one] using abs_real_inner_le_norm w u
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin d),
        |b.repr x (.inl 0)| *
          |(inner w u : ℝ) * b.repr x (.inl 0) +
            Real.sqrt (1 - (inner w u : ℝ) ^ 2) * b.repr x (.inl 1)| *
          ((Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-‖x‖ ^ 2 / 2)) := by
      congr 1
      ext x
      rw [hfirst x, hsecond x]
    _ = ∫ p : ℝ × ℝ, |p.1| *
        |(inner w u : ℝ) * p.1 + Real.sqrt (1 - (inner w u : ℝ) ^ 2) * p.2| *
          ((2 * Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2)) :=
      gaussian_first_two_coordinates b (inner w u) (Real.sqrt (1 - (inner w u : ℝ) ^ 2))
    _ = _ := by
      simpa only [mul_assoc] using
        GaussianAbsoluteMoment2D.gaussian_abs_pair_correlation
          (neg_le_of_abs_le hρ) (le_of_abs_le hρ)

end PaperLeanFormalization.Preliminaries

namespace PaperLeanFormalization.Preliminaries

open PaperLeanFormalization

/-- Literal pair-moment adapter, whose proof is entirely in this file. -/
theorem gaussian_absolute_pair_moment_anchor {d : ℕ} (hd : 2 ≤ d)
    {w u : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    gaussianVecAbsMoment d w u = (2 / Real.pi) * orthantPhi (inner w u : ℝ) :=
  gaussian_absolute_pair_moment hd hw hu

end PaperLeanFormalization.Preliminaries

namespace PaperLeanFormalization.Preliminaries

open PaperLeanFormalization.Definitions

abbrev Model := PaperLeanFormalization.Model

/-- `eq:parameter-spaces`: the full signed cylinder and its free skip factor.
These are sets in the ambient vector spaces, so no auxiliary positivity or
manifold predicates hide the constraints used by the local-minimum statements. -/
theorem eq_parameter_spaces (d n : ℕ) :
    {p : Parameters d n | ∀ i, ‖p.2 i‖ = 1} =
      (Set.univ : Set (Fin n → ℝ)) ×ˢ
        (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : Vec d) 1) ∧
    {p : Vec d × Parameters d n | ∀ i, ‖p.2.2 i‖ = 1} =
      (Set.univ : Set (Vec d)) ×ˢ
        ((Set.univ : Set (Fin n → ℝ)) ×ˢ
          (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : Vec d) 1)) := by
  constructor <;> ext p <;>
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and,
      Set.mem_pi, mem_sphere_zero_iff_norm, forall_true_left]

/-- `eq:parameter-classes`: the three displayed classes, expressed without
adding names that would obscure either the sign or the span condition. -/
theorem eq_parameter_classes (d n : ℕ) :
    {p : Parameters d n | (∀ i, 0 ≤ p.1 i) ∧ (∀ i, ‖p.2 i‖ = 1)} =
      (Set.univ.pi fun _ : Fin n => Set.Ici (0 : ℝ)) ×ˢ
        (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : Vec d) 1) ∧
    {p : Parameters d n | (∀ i, 0 < p.1 i) ∧ (∀ i, ‖p.2 i‖ = 1)} =
      (Set.univ.pi fun _ : Fin n => Set.Ioi (0 : ℝ)) ×ˢ
        (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : Vec d) 1) ∧
    {p : Parameters d n | (∀ i, ‖p.2 i‖ = 1) ∧
        FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range p.2)) ≤ 2} =
      ((Set.univ : Set (Fin n → ℝ)) ×ˢ
        (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : Vec d) 1)) ∩
      {p | FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range p.2)) ≤ 2} := by
  have hsphere (p : Parameters d n) : (∀ i, ‖p.2 i‖ = 1) ↔
      p.2 ∈ (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : Vec d) 1) := by
    have h := Set.ext_iff.mp (eq_parameter_spaces d n).1 p
    simpa only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and] using h
  constructor
  · ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      Set.mem_Ici, forall_true_left, hsphere]
  constructor
  · ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioi, forall_true_left, hsphere]
  · ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
      true_and, hsphere]

/-- The nonnegative parameter class intersected with mass upper bounds is the
concrete product of closed intervals and spheres used in the empirical proof. -/
theorem nonnegative_parameter_box {d n : ℕ} (C : ℝ) (p : Parameters d n) :
    p ∈ ((Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) C) ×ˢ
      (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : Vec d) 1)) ↔
      (∀ i, 0 ≤ p.1 i) ∧ (∀ i, p.1 i ≤ C) ∧ (∀ i, ‖p.2 i‖ = 1) := by
  have hclass := Set.ext_iff.mp (eq_parameter_classes d n).1 p
  change ((∀ i, 0 ≤ p.1 i) ∧ (∀ i, ‖p.2 i‖ = 1)) ↔
    p ∈ ((Set.univ.pi fun _ : Fin n => Set.Ici (0 : ℝ)) ×ˢ
      (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : Vec d) 1)) at hclass
  constructor
  · intro hp
    have hnonnegative := hclass.mpr
      ⟨fun i hi => (hp.1 i hi).1, hp.2⟩
    exact ⟨hnonnegative.1, fun i => (hp.1 i (Set.mem_univ i)).2, hnonnegative.2⟩
  · rintro ⟨h0, hC, hw⟩
    have hnonnegative := hclass.mp ⟨h0, hw⟩
    exact ⟨fun i hi => ⟨hnonnegative.1 i hi, hC i⟩, hnonnegative.2⟩

/-- Equation `eq:models-raw`: output weights and unnormalized first-layer vectors. -/
def RawNetwork {d n : ℕ} (q : Model) (o : Fin n → ℝ)
    (a : Fin n → Vec d) (x : Vec d) : ℝ :=
  ∑ i, o i * Feature q (inner (a i) x)

theorem eq_models_raw {d n : ℕ} (q : Model) (o : Fin n → ℝ)
    (a : Fin n → Vec d) (x : Vec d) :
    RawNetwork q o a x = ∑ i, o i * Feature q (inner (a i) x) := rfl

/-- Equation `eq:models`: signed masses and unit directions. -/
theorem eq_models {d n : ℕ} (q : Model) (c : Fin n → ℝ)
    (w : Fin n → Vec d) (x : Vec d) :
    Network q c w x = ∑ i, c i * Feature q (inner (w i) x) := rfl

/-- The even and odd parts of the plain feature. -/
theorem plain_feature_eq_centered_add_half (z : ℝ) :
    Feature .plainRelu z = Feature .centered z + z / 2 := by
  change max 0 z = |z| / 2 + z / 2
  rcases le_total 0 z with hz | hz
  · rw [max_eq_right hz, abs_of_nonneg hz]
    ring
  · rw [max_eq_left hz, abs_of_nonpos hz]
    ring

/-- Both features are positively homogeneous, including scale zero. -/
theorem feature_nonnegative_homogeneity (q : Model) {r : ℝ} (hr : 0 ≤ r)
    (z : ℝ) : Feature q (r * z) = r * Feature q z := by
  cases q with
  | centered =>
      change |r * z| / 2 = r * (|z| / 2)
      rw [abs_mul, abs_of_nonneg hr]
      ring
  | plainRelu =>
      change max 0 (r * z) = r * max 0 z
      rcases le_total 0 z with hz | hz
      · rw [max_eq_right hz, max_eq_right (mul_nonneg hr hz)]
      · rw [max_eq_left hz, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hr hz),
          mul_zero]

/-- The two features vanish at zero. -/
theorem feature_zero (q : Model) : Feature q 0 = 0 := by
  cases q <;> norm_num [Feature]

theorem normalize_directions_unit {d n : ℕ} (o : Fin n → ℝ)
    (a : Fin n → Vec d) (ha : ∀ i, a i ≠ 0) :
    ∀ i, ‖(Normalize o a).2 i‖ = 1 := by
  intro i
  change ‖‖a i‖⁻¹ • a i‖ = 1
  exact norm_smul_inv_norm (ha i)

/-- The factorization used before introducing the mass coordinate. -/
theorem raw_unit_normalization {d : ℕ} (q : Model) (o : ℝ)
    (a x : Vec d) (ha : a ≠ 0) :
    o * Feature q (inner a x) =
      (o * ‖a‖) * Feature q (inner (‖a‖⁻¹ • a) x) := by
  have hfactor : ‖a‖ * (inner (‖a‖⁻¹ • a) x : ℝ) = inner a x := by
    rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel (norm_ne_zero_iff.mpr ha),
      one_mul]
  rw [mul_assoc, ← feature_nonnegative_homogeneity q (norm_nonneg a), hfactor]

/-- Normalization preserves the network pointwise, including zero raw rows:
their normalized direction is zero, but their mass is also zero. -/
theorem raw_network_eq_normalized {d n : ℕ} (q : Model) (o : Fin n → ℝ)
    (a : Fin n → Vec d) :
    RawNetwork q o a = Network q (Normalize o a).1 (Normalize o a).2 := by
  funext x
  rw [eq_models_raw, eq_models]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : a i = 0
  · simp only [Normalize, hi, inner_zero_left, norm_zero, mul_zero,
      inv_zero, zero_smul, feature_zero]
  · exact raw_unit_normalization q (o i) (a i) x hi

/-- A normalized parameter has the explicit raw preimage `(c,w)`. -/
theorem normalize_unit_directions {d n : ℕ} (c : Fin n → ℝ)
    (w : Fin n → Vec d) (hw : ∀ i, ‖w i‖ = 1) :
    Normalize c w = (c, w) := by
  apply Prod.ext
  · funext i
    change c i * ‖w i‖ = c i
    rw [hw i, mul_one]
  · funext i
    change ‖w i‖⁻¹ • w i = w i
    rw [hw i, inv_one, one_smul]

/-- Surjectivity onto the full signed mass--direction cylinder, with an
explicit preimage having no zero raw row. -/
theorem normalization_surjective {d n : ℕ} (c : Fin n → ℝ)
    (w : Fin n → Vec d) (hw : ∀ i, ‖w i‖ = 1) :
    ∃ (o : Fin n → ℝ) (a : Fin n → Vec d),
      (∀ i, a i ≠ 0) ∧ Normalize o a = (c, w) := by
  refine ⟨c, w, ?_, normalize_unit_directions c w hw⟩
  intro i hzero
  have h := hw i
  rw [hzero, norm_zero] at h
  exact zero_ne_one h

/-- The feature network splits into its even part and its first moment. -/
theorem plain_network_eq_centered_add_first_moment {d n : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Vec d) (x : Vec d) :
    Network .plainRelu c w x = Network .centered c w x +
      (1 / 2 : ℝ) * inner (∑ i, c i • w i) x := by
  simp only [eq_models, plain_feature_eq_centered_add_half, mul_add, Finset.sum_add_distrib,
    sum_inner, real_inner_smul_left, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The angular representation keeps oriented angles for plain ReLU. -/
theorem angle_inner (α β : ℝ) :
    (inner (Angle α) (Angle β) : ℝ) = Real.cos (α - β) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  rfl

theorem angle_unit (α : ℝ) : ‖Angle α‖ = 1 := by
  have h : (inner (Angle α) (Angle α) : ℝ) = 1 := by
    rw [angle_inner, sub_self, Real.cos_zero]
  rw [real_inner_self_eq_norm_mul_norm] at h
  nlinarith only [h, norm_nonneg (Angle α)]

/-- Equation `eq:ambient-residual-main`, with the normalization in `Kernel`. -/
theorem eq_ambient_residual_main {d n m : ℕ} (q : Model) (c : Fin n → ℝ)
    (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) (u : Vec d) :
    Residual q c w s v u = (∑ i, c i * Kernel q (inner u (w i))) -
      ∑ k, s k * Kernel q (inner u (v k)) := rfl

/-- Equation `eq:residual-potential-paper`, on actual direction angles. -/
theorem eq_residual_potential_paper {n m : ℕ} (q : Model)
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (γ : ℝ) :
    PlanarResidual q c θ s β γ =
      (∑ i, c i * Kernel q (Real.cos (γ - θ i))) -
        ∑ k, s k * Kernel q (Real.cos (γ - β k)) := rfl

/-- The missing non-tautological identity in the planar-equivalence remark. -/
theorem ambient_residual_eq_planar {n m : ℕ} (q : Model)
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (γ : ℝ) :
    Residual q c (fun i => Angle (θ i)) s (fun k => Angle (β k)) (Angle γ) =
      PlanarResidual q c θ s β γ := by
  simp only [eq_ambient_residual_main, eq_residual_potential_paper, angle_inner]

/-- The finite Gram quadratic, with the paper's literal loss normalization. -/
def KernelEnergy {d n m : ℕ} (q : Model) (c : Fin n → ℝ)
    (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) : ℝ :=
  (1 / (4 * Real.pi)) *
    ((∑ i, ∑ j, c i * c j * Kernel q (inner (w i) (w j))) -
      2 * (∑ i, ∑ k, c i * s k * Kernel q (inner (w i) (v k))) +
      ∑ k, ∑ l, s k * s l * Kernel q (inner (v k) (v l)))

/-- A coordinate update is differentiated directly, including all other rows. -/
theorem hasDerivAt_mass_update {n : ℕ} (c : Fin n → ℝ) (a i : Fin n) :
    HasDerivAt (fun t : ℝ => Function.update c a t i)
      (if i = a then 1 else 0) (c a) := by
  by_cases h : i = a
  · subst i
    simpa using hasDerivAt_id (c a)
  · simpa [Function.update_noteq h, h] using hasDerivAt_const (c a) (c i)

/-- Symmetry gives the factor two in the derivative of the student Gram term. -/
theorem hasDerivAt_symmetric_quadratic_update {n : ℕ}
    (c : Fin n → ℝ) (K : Fin n → Fin n → ℝ)
    (hK : ∀ i j, K i j = K j i) (a : Fin n) :
    HasDerivAt (fun t : ℝ => ∑ i, ∑ j,
      Function.update c a t i * Function.update c a t j * K i j)
      (2 * ∑ j, c j * K a j) (c a) := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      ((hasDerivAt_mass_update c a i).mul
        (hasDerivAt_mass_update c a j)).mul_const (K i j)))
  simp only [Function.update_eq_self] at hd
  convert hd using 1
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, mul_ite,
    one_mul, zero_mul, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [hK _ a]
  ring

theorem hasDerivAt_linear_mass_update {n : ℕ}
    (c f : Fin n → ℝ) (a : Fin n) :
    HasDerivAt (fun t : ℝ => ∑ i, Function.update c a t i * f i)
      (f a) (c a) := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_mass_update c a i).mul_const (f i))
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using hd

/-- The paper's mass derivative, first proved at the finite Gram level.
Only kernel symmetry is used: no positivity or noncollision assumption. -/
theorem hasDerivAt_kernelEnergy_mass_update {d n m : ℕ} (q : Model)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ)
    (v : Fin m → Vec d) (a : Fin n) :
    HasDerivAt (fun t => KernelEnergy q (Function.update c a t) w s v)
      ((1 / (2 * Real.pi)) * Residual q c w s v (w a)) (c a) := by
  have hSS := hasDerivAt_symmetric_quadratic_update c
    (fun i j => Kernel q (inner (w i) (w j)))
    (fun i j => congrArg (Kernel q) (real_inner_comm (w j) (w i))) a
  have hST := hasDerivAt_linear_mass_update c
    (fun i => ∑ k, s k * Kernel q (inner (w i) (v k))) a
  have h := ((hSS.sub (hST.const_mul 2)).add_const
    (∑ k, ∑ l, s k * s l * Kernel q (inner (v k) (v l)))).const_mul
      (1 / (4 * Real.pi))
  convert h using 1
  · funext t
    simp only [KernelEnergy, Finset.mul_sum, ← mul_assoc]
  · rw [eq_ambient_residual_main]
    ring

/-- The residual pairing is a finite-sum identity for either symmetric kernel.
It requires no positivity, unit length, stationarity, or separation assumption. -/
theorem kernel_energy_eq_residual_pairing {d n m : ℕ} (q : Model)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    KernelEnergy q c w s v = (1 / (4 * Real.pi)) *
      ((∑ i, c i * Residual q c w s v (w i)) -
        ∑ k, s k * Residual q c w s v (v k)) := by
  have hcross : (∑ k, ∑ i, s k * c i * Kernel q (inner (v k) (w i))) =
      ∑ i, ∑ k, c i * s k * Kernel q (inner (w i) (v k)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm (v k) (w i), mul_comm (s k) (c i)]
  have hstudent : (∑ i, c i * Residual q c w s v (w i)) =
      (∑ i, ∑ j, c i * c j * Kernel q (inner (w i) (w j))) -
        ∑ i, ∑ k, c i * s k * Kernel q (inner (w i) (v k)) := by
    simp only [eq_ambient_residual_main, mul_sub, Finset.mul_sum,
      Finset.sum_sub_distrib, ← mul_assoc]
  have hteacher : (∑ k, s k * Residual q c w s v (v k)) =
      (∑ k, ∑ i, s k * c i * Kernel q (inner (v k) (w i))) -
        ∑ k, ∑ l, s k * s l * Kernel q (inner (v k) (v l)) := by
    simp only [eq_ambient_residual_main, mul_sub, Finset.mul_sum,
      Finset.sum_sub_distrib, ← mul_assoc]
  rw [hstudent, hteacher, hcross]
  unfold KernelEnergy
  ring

/-- At mass-stationarity the loss pairing has only the teacher term. -/
theorem kernel_energy_at_mass_stationarity {d n m : ℕ} (q : Model)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hstationary : ∀ i, Residual q c w s v (w i) = 0) :
    KernelEnergy q c w s v = -(1 / (4 * Real.pi)) *
      ∑ k, s k * Residual q c w s v (v k) := by
  rw [kernel_energy_eq_residual_pairing]
  simp only [hstationary, mul_zero, Finset.sum_const_zero, zero_sub, mul_neg, neg_mul]

/-- Exact residual agreement follows immediately when every unit matches. -/
theorem residual_self {d n : ℕ} (q : Model) (c : Fin n → ℝ)
    (w : Fin n → Vec d) (u : Vec d) : Residual q c w c w u = 0 := by
  exact sub_self _

theorem centered_loss_self {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d) :
    CenteredLoss c w c w = 0 := by
  simp only [CenteredLoss, sub_self, zero_pow (by decide : 0 < 2), zero_mul,
    MeasureTheory.integral_zero, mul_zero]

theorem plain_loss_self {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d) :
    PlainLoss c w c w = 0 := by
  simp only [PlainLoss, sub_self, zero_pow (by decide : 0 < 2), zero_mul,
    MeasureTheory.integral_zero, mul_zero]

end PaperLeanFormalization.Preliminaries

open Real Filter Set
open scoped Topology

noncomputable section

namespace PaperLeanFormalization.KernelCalculus

def centeredKernel (r : ℝ) : ℝ := r * arcsin r + sqrt (1 - r ^ 2)

theorem continuous_centeredKernel : Continuous centeredKernel := by
  unfold centeredKernel
  exact (continuous_id.mul continuous_arcsin).add
    (continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))

theorem centeredKernel_even (r : ℝ) : centeredKernel (-r) = centeredKernel r := by
  simp [centeredKernel]

/-- Cancellation is algebraic away from the two endpoints, including the clamped rays. -/
theorem hasDerivAt_centeredKernel_of_ne {r : ℝ} (hm : r ≠ -1) (hp : r ≠ 1) :
    HasDerivAt centeredKernel (arcsin r) r := by
  have hs : 1 - r ^ 2 ≠ 0 := by
    intro h
    have : (r - 1) * (r + 1) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp this with h | h
    · exact hp (by linarith only [h])
    · exact hm (by linarith only [h])
  have h := ((hasDerivAt_id r).mul (hasDerivAt_arcsin hm hp)).add
    ((hasDerivAt_sqrt hs).comp r ((hasDerivAt_pow 2 r).const_sub 1))
  convert h using 1; try rfl
  field_simp
  ; ring

theorem centeredKernel_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    centeredKernel r = r * (π / 2) := by
  rw [centeredKernel, arcsin_of_one_le hr,
    sqrt_eq_zero_of_nonpos (by nlinarith only [hr] : 1 - r ^ 2 ≤ 0), add_zero]

/-- Continuous extension of the derivative replaces a Taylor estimate at alignment. -/
theorem hasDerivAt_centeredKernel_one :
    HasDerivAt centeredKernel (π / 2) 1 := by
  have hleft : HasDerivWithinAt centeredKernel (π / 2) (Iic 1) 1 := by
    apply has_deriv_at_interval_right_endpoint_of_tendsto_deriv
      (s := Ioo (0 : ℝ) 1)
    · intro r hr
      exact (hasDerivAt_centeredKernel_of_ne (by linarith only [hr.1])
        (ne_of_lt hr.2)).differentiableAt.differentiableWithinAt
    · exact continuous_centeredKernel.continuousAt.continuousWithinAt
    · exact Ioo_mem_nhdsWithin_Iio (by norm_num : (1 : ℝ) ∈ Ioc 0 1)
    · have ht := (continuous_arcsin.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Iio 1))
      rw [arcsin_one] at ht
      apply ht.congr'
      filter_upwards [Ioo_mem_nhdsWithin_Iio
        (by norm_num : (1 : ℝ) ∈ Ioc 0 1)] with r hr
      exact (hasDerivAt_centeredKernel_of_ne (by linarith only [hr.1])
        (ne_of_lt hr.2)).deriv.symm
  have hright : HasDerivWithinAt centeredKernel (π / 2) (Ici 1) 1 := by
    have h := ((hasDerivAt_id (1 : ℝ)).mul_const (π / 2)).hasDerivWithinAt
      (s := Ici (1 : ℝ))
    simp only [one_mul] at h
    exact h.congr_of_mem (fun _ hr => centeredKernel_of_one_le hr) (by simp)
  simpa using hleft.union hright

theorem hasDerivAt_centeredKernel (r : ℝ) :
    HasDerivAt centeredKernel (arcsin r) r := by
  by_cases hp : r = 1
  · simpa [hp, arcsin_one] using hasDerivAt_centeredKernel_one
  by_cases hm : r = -1
  · subst r
    have hpoint : HasDerivAt centeredKernel (π / 2) (- -(1 : ℝ)) := by
      simpa using hasDerivAt_centeredKernel_one
    have h := hpoint.comp (-1) (hasDerivAt_neg' (-1))
    simpa [Function.comp_def, centeredKernel_even, arcsin_neg, arcsin_one] using h
  exact hasDerivAt_centeredKernel_of_ne hm hp

theorem hasDerivAt_plainKernel (r : ℝ) :
    HasDerivAt (fun t => centeredKernel t + (π / 2) * t)
      (arcsin r + π / 2) r := by
  simpa using (hasDerivAt_centeredKernel r).add ((hasDerivAt_id r).const_mul (π / 2))

def angularKernel (t : ℝ) : ℝ := centeredKernel (cos t)

theorem hasDerivAt_angularKernel (t : ℝ) :
    HasDerivAt angularKernel (-sin t * arcsin (cos t)) t := by
  convert (hasDerivAt_centeredKernel (cos t)).comp t (hasDerivAt_cos t) using 1
  ; ring

/-- At a zero, multiplying a differentiable factor by a continuous factor needs no
derivative of the latter. This is the endpoint cancellation in the angular kernel. -/
theorem hasDerivAt_mul_continuousAt_of_zero {f g : ℝ → ℝ} {x f' : ℝ}
    (hf : HasDerivAt f f' x) (hg : ContinuousAt g x) (hz : f x = 0) :
    HasDerivAt (fun t => f t * g t) (f' * g x) x := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  convert hf.mul (hg.mono_left nhdsWithin_le_nhds) using 1
  ext t
  simp only [slope_def_field, hz, zero_mul, sub_zero]
  ring

theorem sqrt_one_sub_cos_sq (t : ℝ) : sqrt (1 - cos t ^ 2) = |sin t| := by
  have hsq : 1 - cos t ^ 2 = sin t ^ 2 := by nlinarith only [sin_sq_add_cos_sq t]
  rw [hsq]
  exact sqrt_sq_eq_abs _

theorem hasDerivAt_angularKernel_first (t : ℝ) :
    HasDerivAt (fun x => -sin x * arcsin (cos x))
      (2 * |sin t| - angularKernel t) t := by
  by_cases hz : sin t = 0
  · have h := hasDerivAt_mul_continuousAt_of_zero (hasDerivAt_sin t).neg
      (continuous_arcsin.comp continuous_cos).continuousAt (by simp [hz])
    convert h using 1
    simp only [angularKernel, centeredKernel, sqrt_one_sub_cos_sq, hz, abs_zero,
      Function.comp_def]
    ring
  · have hm : cos t ≠ -1 := by
      intro h
      have : sin t ^ 2 = 0 := by nlinarith only [sin_sq_add_cos_sq t, h]
      exact hz (sq_eq_zero_iff.mp this)
    have hp : cos t ≠ 1 := by
      intro h
      have : sin t ^ 2 = 0 := by nlinarith only [sin_sq_add_cos_sq t, h]
      exact hz (sq_eq_zero_iff.mp this)
    have h := (hasDerivAt_sin t).neg.mul
      ((hasDerivAt_arcsin hm hp).comp t (hasDerivAt_cos t))
    convert h using 1
    rw [angularKernel, centeredKernel, sqrt_one_sub_cos_sq]
    have habs : |sin t| ≠ 0 := (abs_pos.mpr hz).ne'
    field_simp [habs]
    nlinarith only [sq_abs (sin t)]

end PaperLeanFormalization.KernelCalculus

/-!
Fresh finite-family Gaussian anchoring: regard teacher units as negatively
weighted extra units, integrate one Gram sum, and only then split the blocks.
No population-loss identity from the original tree is used.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace PaperLeanFormalization.Preliminaries

open PaperLeanFormalization
open PaperLeanFormalization.Definitions

/-- Expand a finite square under the integral. Pairwise integrability is the
only analytic hypothesis, and no positivity is required. -/
theorem finite_square_integral {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) (f : I → X → ℝ) (ρ : X → ℝ)
    (hi : ∀ i j, Integrable (fun x => f i x * f j x * ρ x) μ) :
    (∫ x, (∑ i, f i x) ^ 2 * ρ x ∂μ) =
      ∑ i, ∑ j, ∫ x, f i x * f j x * ρ x ∂μ := by
  have hexpand : (fun x => (∑ i, f i x) ^ 2 * ρ x) =
      fun x => ∑ i, ∑ j, f i x * f j x * ρ x := by
    funext x
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hexpand, integral_finset_sum Finset.univ
    (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  exact Finset.sum_congr rfl (fun i _ =>
    integral_finset_sum Finset.univ (fun j _ => hi i j))

/-- A weighted feature family is anchored by its two-feature moment formula. -/
theorem weighted_square_integral {X V I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) (φ : V → X → ℝ) (ρ : X → ℝ)
    (a : I → ℝ) (z : I → V) (K : V → V → ℝ) (κ : ℝ)
    (hi : ∀ i j, Integrable (fun x => φ (z i) x * φ (z j) x * ρ x) μ)
    (hm : ∀ i j, (∫ x, φ (z i) x * φ (z j) x * ρ x ∂μ) = κ * K (z i) (z j)) :
    (∫ x, (∑ i, a i * φ (z i) x) ^ 2 * ρ x ∂μ) =
      κ * ∑ i, ∑ j, a i * a j * K (z i) (z j) := by
  have hscaled : ∀ i j, Integrable
      (fun x => (a i * φ (z i) x) * (a j * φ (z j) x) * ρ x) μ := by
    intro i j
    convert (hi i j).const_mul (a i * a j) using 1
    ext x
    ring
  rw [finite_square_integral μ (fun i x => a i * φ (z i) x) ρ hscaled,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc
    _ = (a i * a j) * ∫ x, φ (z i) x * φ (z j) x * ρ x ∂μ := by
      rw [← integral_mul_left]
      congr 1
      ext x
      ring
    _ = _ := by rw [hm i j]; ring

/-- The student--teacher residual is one signed finite family. Splitting its
Gram sum yields the three terms of the paper's energy formula. -/
theorem residual_square_integral_eq_gram
    {X V I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]
    (μ : Measure X) (φ : V → X → ℝ) (ρ : X → ℝ)
    (c : I → ℝ) (w : I → V) (s : J → ℝ) (v : J → V)
    (K : V → V → ℝ) (κ : ℝ)
    (hsym : ∀ x y, K x y = K y x)
    (hi : ∀ x y, Integrable (fun g => φ x g * φ y g * ρ g) μ)
    (hm : ∀ x y, (∫ g, φ x g * φ y g * ρ g ∂μ) = κ * K x y) :
    (∫ g, ((∑ i, c i * φ (w i) g) - ∑ k, s k * φ (v k) g) ^ 2 * ρ g ∂μ) =
      κ * ((∑ i, ∑ j, c i * c j * K (w i) (w j)) -
        2 * (∑ i, ∑ k, c i * s k * K (w i) (v k)) +
          ∑ k, ∑ l, s k * s l * K (v k) (v l)) := by
  let a : I ⊕ J → ℝ := Sum.elim c (fun k => -s k)
  let z : I ⊕ J → V := Sum.elim w v
  have h := weighted_square_integral μ φ ρ a z K κ
    (fun i j => hi (z i) (z j)) (fun i j => hm (z i) (z j))
  have hcross : (∑ k, ∑ i, s k * c i * K (v k) (w i)) =
      ∑ i, ∑ k, c i * s k * K (w i) (v k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsym (v k) (w i), mul_comm (s k) (c i)]
  simp only [a, z, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, Finset.sum_add_distrib,
    ← sub_eq_add_neg, Finset.sum_sub_distrib] at h
  rw [hcross] at h
  calc
    _ = _ := h
    _ = _ := by ring

theorem gaussian_square_moment {d : ℕ} (hd : 2 ≤ d)
    (z : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      (inner z x : ℝ) * (inner z x : ℝ) * stdGaussianDensity x) = ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · subst z
    simp
  let e := ‖z‖⁻¹ • z
  have he : ‖e‖ = 1 := norm_smul_inv_norm hz
  have hdiag : gaussianVecAbsMoment d e e = 1 := by
    rw [gaussian_absolute_pair_moment_anchor hd he he,
      real_inner_self_eq_norm_mul_norm, he]
    norm_num [orthantPhi, Real.arcsin_one]
    field_simp [Real.pi_ne_zero]
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      (inner z x : ℝ) = ‖z‖ * inner e x := by
    simp only [e, real_inner_smul_left, ← mul_assoc,
      mul_inv_cancel (norm_ne_zero_iff.mpr hz), one_mul]
  calc
    _ = ‖z‖ ^ 2 * gaussianVecAbsMoment d e e := by
      rw [gaussianVecAbsMoment, ← integral_mul_left]
      congr 1
      ext x
      rw [hpoint, abs_mul_abs_self]
      ring
    _ = _ := by rw [hdiag, mul_one]

/-- A nonzero computed square integral supplies integrability; the zero
vector case is handled separately and does not use `integral_undef`. -/
theorem gaussian_square_integrable {d : ℕ} (hd : 2 ≤ d)
    (z : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (inner z x : ℝ) * (inner z x : ℝ) * stdGaussianDensity x) := by
  by_cases hz : z = 0
  · subst z
    simp
  · by_contra hi
    have h := gaussian_square_moment hd z
    rw [integral_undef hi] at h
    exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)) h.symm

/-- Continuous features bounded by absolute value have integrable Gaussian
pair products. One common domination proof covers linear, absolute and ReLU. -/
theorem gaussian_pair_integrable_of_abs_bound {d : ℕ} (hd : 2 ≤ d)
    (φ ψ : ℝ → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (bφ : ∀ t, |φ t| ≤ |t|) (bψ : ∀ t, |ψ t| ≤ |t|)
    (w v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      φ (inner w x) * ψ (inner v x) * stdGaussianDensity x) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => stdGaussianDensity x) := by
    unfold stdGaussianDensity
    exact continuous_const.mul (Real.continuous_exp.comp
      (((continuous_norm.pow 2).neg).div_const 2))
  have hcφ := hφ.comp (continuous_const.inner continuous_id :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) => (inner w x : ℝ)))
  have hcψ := hψ.comp (continuous_const.inner continuous_id :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) => (inner v x : ℝ)))
  refine ((gaussian_square_integrable hd w).add (gaussian_square_integrable hd v)).mono'
    ((hcφ.mul hcψ).mul hc).aestronglyMeasurable (Filter.eventually_of_forall fun x => ?_)
  have hdens : 0 ≤ stdGaussianDensity x := by
    unfold stdGaussianDensity
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
      (Real.exp_pos _).le
  have hprod : |φ (inner w x) * ψ (inner v x)| ≤
      (inner w x : ℝ) * inner w x + (inner v x : ℝ) * inner v x := by
    have htwo := two_mul_le_add_sq |(inner w x : ℝ)| |(inner v x : ℝ)|
    rw [sq_abs, sq_abs] at htwo
    have hnonneg := mul_nonneg (abs_nonneg (inner w x : ℝ)) (abs_nonneg (inner v x : ℝ))
    calc
      _ = |φ (inner w x)| * |ψ (inner v x)| := abs_mul _ _
      _ ≤ |(inner w x : ℝ)| * |(inner v x : ℝ)| :=
        mul_le_mul (bφ _) (bψ _) (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := by nlinarith only [htwo, hnonneg]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdens]
  calc
    _ ≤ ((inner w x : ℝ) * inner w x + (inner v x : ℝ) * inner v x) *
        stdGaussianDensity x := mul_le_mul_of_nonneg_right hprod hdens
    _ = _ := by
      dsimp only [Pi.add_apply]
      ring

theorem gaussian_abs_pair_integrable {d : ℕ} (hd : 2 ≤ d)
    (w v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      |(inner w x : ℝ)| * |(inner v x : ℝ)| * stdGaussianDensity x) :=
  gaussian_pair_integrable_of_abs_bound hd abs abs continuous_abs continuous_abs
    (fun t => (abs_abs t).le) (fun t => (abs_abs t).le) w v

theorem gaussian_linear_pair_integrable {d : ℕ} (hd : 2 ≤ d)
    (w v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (inner w x : ℝ) * (inner v x : ℝ) * stdGaussianDensity x) :=
  gaussian_pair_integrable_of_abs_bound hd id id continuous_id continuous_id
    (fun _ => le_rfl) (fun _ => le_rfl) w v

theorem gaussian_plain_pair_integrable {d : ℕ} (hd : 2 ≤ d)
    (w v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      max 0 (inner w x : ℝ) * max 0 (inner v x : ℝ) * stdGaussianDensity x) := by
  have hb (t : ℝ) : |max 0 t| ≤ |t| := by
    rw [abs_of_nonneg (le_max_left 0 t)]
    exact max_le (abs_nonneg t) (le_abs_self t)
  exact gaussian_pair_integrable_of_abs_bound hd (max 0) (max 0)
    (continuous_const.max continuous_id) (continuous_const.max continuous_id) hb hb w v

/-- Covariance is obtained by polarization of the locally evaluated squares. -/
theorem gaussian_linear_pair_moment {d : ℕ} (hd : 2 ≤ d)
    (w v : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      (inner w x : ℝ) * (inner v x : ℝ) * stdGaussianDensity x) = inner w v := by
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      (inner (w + v) x : ℝ) * inner (w + v) x * stdGaussianDensity x =
        (inner w x : ℝ) * inner w x * stdGaussianDensity x +
          (inner v x : ℝ) * inner v x * stdGaussianDensity x +
            2 * ((inner w x : ℝ) * inner v x * stdGaussianDensity x) := by
    rw [inner_add_left]
    ring
  have h := integral_congr_ae (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (Filter.eventually_of_forall hpoint)
  rw [integral_add
      (f := fun x : EuclideanSpace ℝ (Fin d) =>
        (inner w x : ℝ) * inner w x * stdGaussianDensity x +
          (inner v x : ℝ) * inner v x * stdGaussianDensity x)
      (g := fun x : EuclideanSpace ℝ (Fin d) =>
        2 * ((inner w x : ℝ) * inner v x * stdGaussianDensity x))
      ((gaussian_square_integrable hd w).add (gaussian_square_integrable hd v))
      ((gaussian_linear_pair_integrable hd w v).const_mul 2),
    integral_add (gaussian_square_integrable hd w) (gaussian_square_integrable hd v),
    integral_mul_left, gaussian_square_moment hd (w + v),
    gaussian_square_moment hd w, gaussian_square_moment hd v] at h
  have hnorm := norm_add_sq_real w v
  linarith only [h, hnorm]

/-- Scaling the absolute pair is the only centered-feature normalization. -/
theorem centered_feature_pair_integrable {d : ℕ} (hd : 2 ≤ d)
    (w v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (|inner w x| / 2) * (|inner v x| / 2) * stdGaussianDensity x) := by
  convert (gaussian_abs_pair_integrable hd w v).const_mul (1 / 4 : ℝ) using 1
  ext x
  ring

/-- The centered two-feature covariance, normalized for the displayed loss.
The analytic input is the Gaussian absolute pair integral, not a loss theorem. -/
theorem centered_feature_pair_moment {d : ℕ} (hd : 2 ≤ d)
    (w v : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      (|inner w x| / 2) * (|inner v x| / 2) * stdGaussianDensity x) =
      (1 / (2 * Real.pi)) *
        ((inner w v : ℝ) * Real.arcsin (inner w v) +
          Real.sqrt (1 - (inner w v : ℝ) ^ 2)) := by
  calc
    _ = (1 / 4 : ℝ) * gaussianVecAbsMoment d w v := by
      rw [gaussianVecAbsMoment, ← integral_mul_left]
      congr 1
      ext x
      ring
    _ = _ := by
      rw [gaussian_absolute_pair_moment_anchor hd hw hv]
      unfold orthantPhi
      ring

/-- Simultaneous reflection removes the two odd cross terms in a ReLU pair. -/
theorem plain_feature_pair_moment_from_symmetry {d : ℕ} (hd : 2 ≤ d)
    (w v : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      max 0 (inner w x : ℝ) * max 0 (inner v x : ℝ) * stdGaussianDensity x) =
      (1 / 4 : ℝ) * (gaussianVecAbsMoment d w v + (inner w v : ℝ)) := by
  let f := fun x : EuclideanSpace ℝ (Fin d) =>
    max 0 (inner w x : ℝ) * max 0 (inner v x : ℝ) * stdGaussianDensity x
  have hpoint (x : EuclideanSpace ℝ (Fin d)) : f x + f (-x) =
      (1 / 2 : ℝ) * (|(inner w x : ℝ)| * |(inner v x : ℝ)| * stdGaussianDensity x +
        (inner w x : ℝ) * (inner v x : ℝ) * stdGaussianDensity x) := by
    simp only [f, inner_neg_right, stdGaussianDensity, norm_neg]
    rcases le_total 0 (inner w x : ℝ) with hw | hw <;>
      rcases le_total 0 (inner v x : ℝ) with hv | hv
    · rw [max_eq_right hw, max_eq_right hv, max_eq_left (neg_nonpos.mpr hw),
        max_eq_left (neg_nonpos.mpr hv), abs_of_nonneg hw, abs_of_nonneg hv]
      ring
    · rw [max_eq_right hw, max_eq_left hv, max_eq_left (neg_nonpos.mpr hw),
        max_eq_right (neg_nonneg.mpr hv), abs_of_nonneg hw, abs_of_nonpos hv]
      ring
    · rw [max_eq_left hw, max_eq_right hv, max_eq_right (neg_nonneg.mpr hw),
        max_eq_left (neg_nonpos.mpr hv), abs_of_nonpos hw, abs_of_nonneg hv]
      ring
    · rw [max_eq_left hw, max_eq_left hv, max_eq_right (neg_nonneg.mpr hw),
        max_eq_right (neg_nonneg.mpr hv), abs_of_nonpos hw, abs_of_nonpos hv]
      ring
  have hf : Integrable f := gaussian_plain_pair_integrable hd w v
  have hint := congrArg (fun g : EuclideanSpace ℝ (Fin d) → ℝ => ∫ x, g x)
    (funext hpoint)
  change (∫ x, f x + f (-x)) = ∫ x, (1 / 2 : ℝ) *
    (|(inner w x : ℝ)| * |(inner v x : ℝ)| * stdGaussianDensity x +
      (inner w x : ℝ) * (inner v x : ℝ) * stdGaussianDensity x) at hint
  rw [integral_add hf hf.comp_neg, integral_neg_eq_self f volume,
    integral_mul_left,
    integral_add (gaussian_abs_pair_integrable hd w v)
      (gaussian_linear_pair_integrable hd w v),
    gaussian_linear_pair_moment hd w v] at hint
  change (∫ x, f x) + (∫ x, f x) =
    (1 / 2 : ℝ) * (gaussianVecAbsMoment d w v + (inner w v : ℝ)) at hint
  change (∫ x, f x) = _
  linarith only [hint]

/-- The elementary overlap-arc calculation, valid even outside the principal
angle range because the interval integral has its usual orientation. -/
theorem relu_overlap_integral (θ : ℝ) :
    (∫ a in (θ - Real.pi / 2)..(Real.pi / 2),
      Real.cos a * Real.cos (a - θ)) =
      (Real.sin θ + (Real.pi - θ) * Real.cos θ) / 2 := by
  have h := CircleMoments.integral_cos_cos (θ - Real.pi / 2) (Real.pi / 2) (-θ)
  calc
    _ = Real.cos (-θ) *
        ((Real.cos (Real.pi / 2) * Real.sin (Real.pi / 2) -
          Real.cos (θ - Real.pi / 2) * Real.sin (θ - Real.pi / 2) +
          Real.pi / 2 - (θ - Real.pi / 2)) / 2) -
        Real.sin (-θ) * ((Real.sin (Real.pi / 2) ^ 2 -
          Real.sin (θ - Real.pi / 2) ^ 2) / 2) := by
      simpa only [sub_eq_add_neg] using h
    _ = _ := by
      simp only [Real.cos_neg, Real.sin_neg, Real.cos_sub, Real.sin_sub,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring

/-- `eq:relu-pair-angular`: both equalities of the displayed angular pair
moment. The Gaussian input uses the already established absolute-pair moment
and simultaneous-reflection identity; the overlap integral is evaluated above. -/
theorem eq_relu_pair_angular {d : ℕ} (hd : 2 ≤ d) (u z : Vec d)
    (hu : ‖u‖ = 1) (hz : ‖z‖ = 1) :
    let θ := Real.arccos (inner u z : ℝ)
    ((∫ x : Vec d, max 0 (inner u x : ℝ) * max 0 (inner z x : ℝ) *
      stdGaussianDensity x) =
      (1 / Real.pi) * ∫ a in (θ - Real.pi / 2)..(Real.pi / 2),
        Real.cos a * Real.cos (a - θ)) ∧
    ((1 / Real.pi) * ∫ a in (θ - Real.pi / 2)..(Real.pi / 2),
      Real.cos a * Real.cos (a - θ)) =
      (Real.sin θ + (Real.pi - θ) * Real.cos θ) / (2 * Real.pi) := by
  let θ := Real.arccos (inner u z : ℝ)
  change _ = (1 / Real.pi) * (∫ a in (θ - Real.pi / 2)..(Real.pi / 2),
    Real.cos a * Real.cos (a - θ)) ∧ _
  have hρ : |(inner u z : ℝ)| ≤ 1 := by
    simpa only [hu, hz, mul_one] using abs_real_inner_le_norm u z
  have hc : Real.cos θ = (inner u z : ℝ) :=
    Real.cos_arccos (neg_le_of_abs_le hρ) (le_of_abs_le hρ)
  have hs : Real.sin θ = Real.sqrt (1 - (inner u z : ℝ) ^ 2) :=
    Real.sin_arccos _
  have ha : Real.arcsin (inner u z : ℝ) = Real.pi / 2 - θ :=
    Real.arcsin_eq_pi_div_two_sub_arccos _
  have hmoment : (∫ x : Vec d,
      max 0 (inner u x : ℝ) * max 0 (inner z x : ℝ) * stdGaussianDensity x) =
      (Real.sin θ + (Real.pi - θ) * Real.cos θ) / (2 * Real.pi) := by
    rw [plain_feature_pair_moment_from_symmetry hd u z,
      gaussian_absolute_pair_moment_anchor hd hu hz, hc, hs]
    unfold orthantPhi
    rw [ha]
    field_simp [Real.pi_ne_zero]
    ring
  have hint : ((1 / Real.pi) * ∫ a in (θ - Real.pi / 2)..(Real.pi / 2),
      Real.cos a * Real.cos (a - θ)) =
      (Real.sin θ + (Real.pi - θ) * Real.cos θ) / (2 * Real.pi) := by
    rw [relu_overlap_integral]
    ring
  exact ⟨hmoment.trans hint.symm, hint⟩


/-- Plain-ReLU adds precisely the linear kernel term to the centered kernel. -/
theorem plain_feature_pair_moment {d : ℕ} (hd : 2 ≤ d)
    (w v : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      max 0 (inner w x : ℝ) * max 0 (inner v x : ℝ) * stdGaussianDensity x) =
      (1 / (2 * Real.pi)) *
        ((inner w v : ℝ) * Real.arcsin (inner w v) +
          Real.sqrt (1 - (inner w v : ℝ) ^ 2) + (Real.pi / 2) * (inner w v : ℝ)) := by
  have h := eq_relu_pair_angular hd w v hw hv
  dsimp only at h
  rw [h.1, h.2]
  have hρ : |(inner w v : ℝ)| ≤ 1 := by
    simpa only [hw, hv, mul_one] using abs_real_inner_le_norm w v
  rw [Real.cos_arccos (neg_le_of_abs_le hρ) (le_of_abs_le hρ),
    Real.sin_arccos, Real.arccos_eq_pi_div_two_sub_arcsin]
  field_simp [Real.pi_ne_zero]
  ring


/-- Equation `eq:q-losses`, with the Gaussian expectation written as its
literal density integral. This identity is used in the square expansion. -/
theorem eq_q_losses {d n m : ℕ} (q : Model)
    (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) :
    Loss q c w s v = (1 / 2 : ℝ) * ∫ x : Vec d,
      (Network q c w x - Network q s v x) ^ 2 * stdGaussianDensity x := by
  cases q <;> rfl

/-- Equation `eq:kernels`: the pair moment and both displayed scalar kernels.
The Gaussian integral has been proved locally, including at correlations ±1. -/
theorem eq_kernels {d : ℕ} (hd : 2 ≤ d) (q : Model) (u z : Vec d)
    (hu : ‖u‖ = 1) (hz : ‖z‖ = 1) :
    (2 * Real.pi) * (∫ x : Vec d,
      Feature q (inner u x) * Feature q (inner z x) * stdGaussianDensity x) =
        Kernel q (inner u z) ∧
    Kernel .centered (inner u z) = (inner u z : ℝ) * Real.arcsin (inner u z) +
      Real.sqrt (1 - (inner u z : ℝ) ^ 2) ∧
    Kernel .plainRelu (inner u z) = Kernel .centered (inner u z) +
      (Real.pi / 2) * (inner u z : ℝ) := by
  refine ⟨?_, rfl, rfl⟩
  cases q with
  | centered =>
      change (2 * Real.pi) * (∫ x : Vec d,
        (|inner u x| / 2) * (|inner z x| / 2) * stdGaussianDensity x) = _
      rw [centered_feature_pair_moment hd u z hu hz]
      unfold Kernel
      field_simp [Real.pi_ne_zero]
      ring
  | plainRelu =>
      change (2 * Real.pi) * (∫ x : Vec d,
        max 0 (inner u x : ℝ) * max 0 (inner z x : ℝ) * stdGaussianDensity x) = _
      rw [plain_feature_pair_moment hd u z hu hz]
      unfold Kernel
      field_simp [Real.pi_ne_zero]
      ring

/-- Lemma `lem:pair-moments`, in the normalization used by the manuscript. -/
theorem lem_pair_moments {d : ℕ} (hd : 2 ≤ d) (q : Model) (u z : Vec d)
    (hu : ‖u‖ = 1) (hz : ‖z‖ = 1) :
    (2 * Real.pi) * (∫ x : Vec d,
      Feature q (inner u x) * Feature q (inner z x) * stdGaussianDensity x) =
        Kernel q (inner u z) :=
  (eq_kernels hd q u z hu hz).1

/-- The Gaussian loss--kernel identity follows from the two-feature formula.
Only the displayed directions need unit norm; masses may have either sign. -/
theorem gaussian_loss_eq_kernel_energy_of_pair_moment {d n m : ℕ}
    (φ K : ℝ → ℝ) (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (hi : ∀ u z : EuclideanSpace ℝ (Fin d), Integrable
      (fun x => φ (inner u x) * φ (inner z x) * stdGaussianDensity x))
    (hm : ∀ u z : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ‖z‖ = 1 →
      (∫ x, φ (inner u x) * φ (inner z x) * stdGaussianDensity x) =
        (1 / (2 * Real.pi)) * K (inner u z)) :
    (1 / 2 : ℝ) * (∫ x : EuclideanSpace ℝ (Fin d),
      ((∑ i, c i * φ (inner (w i) x)) - ∑ k, s k * φ (inner (v k) x)) ^ 2 *
        stdGaussianDensity x) =
      (1 / (4 * Real.pi)) *
        ((∑ i, ∑ j, c i * c j * K (inner (w i) (w j))) -
          2 * (∑ i, ∑ k, c i * s k * K (inner (w i) (v k))) +
            ∑ k, ∑ l, s k * s l * K (inner (v k) (v l))) := by
  let W : Fin n → {u : EuclideanSpace ℝ (Fin d) // ‖u‖ = 1} :=
    fun i => ⟨w i, hw i⟩
  let V : Fin m → {u : EuclideanSpace ℝ (Fin d) // ‖u‖ = 1} :=
    fun k => ⟨v k, hv k⟩
  have h := residual_square_integral_eq_gram volume
    (fun (u : {u : EuclideanSpace ℝ (Fin d) // ‖u‖ = 1}) x => φ (inner u.val x))
    stdGaussianDensity c W s V (fun u z => K (inner u.val z.val))
    (1 / (2 * Real.pi)) (fun u z => congrArg K (real_inner_comm _ _))
    (fun u z => hi u.val z.val) (fun u z => hm u.val z.val u.property z.property)
  change (∫ x : EuclideanSpace ℝ (Fin d),
      ((∑ i, c i * φ (inner (w i) x)) - ∑ k, s k * φ (inner (v k) x)) ^ 2 *
        stdGaussianDensity x) = _ at h
  rw [h]
  dsimp only [W, V]
  ring

/-- `eq:loss-quadratic`: the complete finite kernel expansion of the literal
Gaussian loss. Masses are arbitrary signed reals and both widths may be zero. -/
theorem eq_loss_quadratic {d n m : ℕ} (hd : 2 ≤ d)
    (q : Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    (4 * Real.pi) * Loss q c w s v =
      (∑ i, ∑ j, c i * c j * Kernel q (inner (w i) (w j))) -
        2 * (∑ i, ∑ k, c i * s k * Kernel q (inner (w i) (v k))) +
        ∑ k, ∑ l, s k * s l * Kernel q (inner (v k) (v l)) := by
  have h : Loss q c w s v = KernelEnergy q c w s v := by
    rw [eq_q_losses]
    apply gaussian_loss_eq_kernel_energy_of_pair_moment
      (Feature q) (Kernel q) c w s v hw hv
    · intro u z
      cases q with
      | centered => exact centered_feature_pair_integrable hd u z
      | plainRelu => exact gaussian_plain_pair_integrable hd u z
    · intro u z hu hz
      calc
        _ = (1 / (2 * Real.pi)) *
            ((2 * Real.pi) * (∫ x : Vec d,
              Feature q (inner u x) * Feature q (inner z x) * stdGaussianDensity x)) := by
          field_simp [Real.pi_ne_zero]
          ring
        _ = _ := by rw [lem_pair_moments hd q u z hu hz]
  rw [h]
  unfold KernelEnergy
  field_simp [Real.pi_ne_zero]
  ring

theorem loss_eq_kernelEnergy {d n m : ℕ} (hd : 2 ≤ d)
    (q : Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    Loss q c w s v = KernelEnergy q c w s v := by
  unfold KernelEnergy
  have h := eq_loss_quadratic hd q c w s v hw hv
  rw [← h]
  field_simp [Real.pi_ne_zero]
  ring

theorem eq_residual_loss {d n m : ℕ} (hd : 2 ≤ d)
    (q : Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    Loss q c w s v = (1 / (4 * Real.pi)) *
      ((∑ i, c i * Residual q c w s v (w i)) -
        ∑ k, s k * Residual q c w s v (v k)) := by
  rw [loss_eq_kernelEnergy hd q c w s v hw hv,
    kernel_energy_eq_residual_pairing]

/-- Equation `eq:residual-mass-gradient`, for the literal loss. -/
theorem eq_residual_mass_gradient {d n m : ℕ} (hd : 2 ≤ d)
    (q : Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (a : Fin n) :
    HasDerivAt (fun t => Loss q (Function.update c a t) w s v)
      ((1 / (2 * Real.pi)) * Residual q c w s v (w a)) (c a) := by
  have heq : (fun t => Loss q (Function.update c a t) w s v) =
      (fun t => KernelEnergy q (Function.update c a t) w s v) := by
    funext t
    exact loss_eq_kernelEnergy hd q _ w s v hw hv
  rw [heq]
  exact hasDerivAt_kernelEnergy_mass_update q c w s v a

/-- A negative second derivative at a stationary point gives actual descent.
The proof uses one neighborhood and one mean-value point; it requires no
continuity of the second derivative on a neighborhood. -/
theorem negative_second_derivative_not_local_min {f : ℝ → ℝ} {x a : ℝ}
    (hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hfirst : deriv f x = 0) (hsecond : HasDerivAt (deriv f) a x)
    (ha : a < 0) : ¬ IsLocalMin f x := by
  intro hmin
  have hslope : ∀ᶠ y in 𝓝[≠] x, slope (deriv f) x y < 0 :=
    (hasDerivAt_iff_tendsto_slope.mp hsecond).eventually (gt_mem_nhds ha)
  have hnear := (hdiff.and hmin).and (eventually_nhdsWithin_iff.mp hslope)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let b := x + ε / 2
  have hxb : x < b := by dsimp [b]; linarith
  have hdist {y : ℝ} (hy : y ∈ Icc x b) : dist y x < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
    dsimp [b] at hy
    linarith only [hy.2, hε]
  have hcont : ContinuousOn f (Icc x b) := fun y hy =>
    (hball (hdist hy)).1.1.continuousAt.continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ f (Ioo x b) := fun y hy =>
    (hball (hdist ⟨hy.1.le, hy.2.le⟩)).1.1.differentiableWithinAt
  obtain ⟨z, hz, hmvt⟩ := exists_deriv_eq_slope f hxb hcont hdiffOn
  have hzdata := hball (hdist ⟨hz.1.le, hz.2.le⟩)
  have hneg := hzdata.2 (by simpa only [mem_compl_iff, mem_singleton_iff] using hz.1.ne')
  rw [slope_def_field, hfirst, sub_zero] at hneg
  have hderivneg : deriv f z < 0 := by
    have h := (div_lt_iff (sub_pos.mpr hz.1)).mp hneg
    simpa only [zero_mul] using h
  rw [hmvt] at hderivneg
  have hdecrease := (div_lt_iff (sub_pos.mpr hxb)).mp hderivneg
  have hminb := (hball (hdist ⟨hxb.le, le_rfl⟩)).1.2
  exact (not_lt_of_ge hminb) (sub_neg.mp (by simpa only [zero_mul] using hdecrease))

/-- At mass stationarity the literal loss has only the teacher residual term. -/
theorem loss_at_mass_stationarity {d n m : ℕ} (hd : 2 ≤ d)
    (q : Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (hstationary : ∀ i, Residual q c w s v (w i) = 0) :
    Loss q c w s v = -(1 / (4 * Real.pi)) *
      ∑ k, s k * Residual q c w s v (v k) := by
  rw [loss_eq_kernelEnergy hd q c w s v hw hv]
  exact kernel_energy_at_mass_stationarity q c w s v hstationary

end PaperLeanFormalization.Preliminaries

open Real
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace PaperLeanFormalization.SphericalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_greatCircle (u e : E) :
    HasDerivAt (fun t : ℝ => cos t • u + sin t • e) e 0 := by
  simpa using ((hasDerivAt_cos 0).smul_const u).add
    ((hasDerivAt_sin 0).smul_const e)

theorem norm_greatCircle (u e : E) (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (hue : ⟪u,e⟫_ℝ = 0) (t : ℝ) : ‖cos t • u + sin t • e‖ = 1 := by
  have hsq : ‖cos t • u + sin t • e‖ ^ 2 = 1 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, hu, he, mul_one,
      real_inner_smul_left, real_inner_smul_right, hue, mul_zero, zero_add,
      add_zero, sq_abs]
    exact cos_sq_add_sin_sq t
  nlinarith only [hsq, norm_nonneg (cos t • u + sin t • e)]

theorem hasDerivAt_inner_greatCircle (u e w : E) :
    HasDerivAt (fun t : ℝ => ⟪cos t • u + sin t • e, w⟫_ℝ) ⟪e,w⟫_ℝ 0 := by
  simpa using (hasDerivAt_greatCircle u e).inner ℝ (hasDerivAt_const (0 : ℝ) w)

/-- The paper's spherical residual derivative is a finite sum chain rule. -/
theorem hasDerivAt_residual_greatCircle {n m : ℕ}
    (K K' : ℝ → ℝ) (hK : ∀ r, HasDerivAt K (K' r) r)
    (c : Fin n → ℝ) (w : Fin n → E) (s : Fin m → ℝ) (v : Fin m → E)
    (u e : E) :
    HasDerivAt (fun t : ℝ =>
      (∑ i, c i * K ⟪cos t • u + sin t • e, w i⟫_ℝ) -
        ∑ k, s k * K ⟪cos t • u + sin t • e, v k⟫_ℝ)
      ((∑ i, c i * K' ⟪u,w i⟫_ℝ * ⟪e,w i⟫_ℝ) -
        ∑ k, s k * K' ⟪u,v k⟫_ℝ * ⟪e,v k⟫_ℝ) 0 := by
  have hterm (a : ℝ) (z : E) :
      HasDerivAt (fun t : ℝ => a * K ⟪cos t • u + sin t • e, z⟫_ℝ)
        (a * K' ⟪u,z⟫_ℝ * ⟪e,z⟫_ℝ) 0 := by
    have hpoint : HasDerivAt K (K' ⟪u,z⟫_ℝ) ⟪cos 0 • u + sin 0 • e,z⟫_ℝ := by
      simpa using hK ⟪u,z⟫_ℝ
    have h := (hpoint.comp 0 (hasDerivAt_inner_greatCircle u e z)).const_mul a
    simpa [mul_assoc] using h
  exact (HasDerivAt.sum fun i _ => hterm (c i) (w i)).sub
    (HasDerivAt.sum fun k _ => hterm (s k) (v k))

/-- Writing the finite chain rule as an inner product identifies the gradient. -/
theorem residual_directional_pairing {n m : ℕ}
    (K' : ℝ → ℝ) (c : Fin n → ℝ) (w : Fin n → E)
    (s : Fin m → ℝ) (v : Fin m → E) (u e : E) :
    ((∑ i, c i * K' ⟪u,w i⟫_ℝ * ⟪e,w i⟫_ℝ) -
      ∑ k, s k * K' ⟪u,v k⟫_ℝ * ⟪e,v k⟫_ℝ) =
      ⟪e, (∑ i, (c i * K' ⟪u,w i⟫_ℝ) • w i) -
        ∑ k, (s k * K' ⟪u,v k⟫_ℝ) • v k⟫_ℝ := by
  simp only [inner_sub_right, inner_sum, real_inner_smul_right]

/-- Interchanging the two student indices makes both directional contributions equal. -/
theorem kernel_self_directional_symmetry {n : ℕ} (K' : ℝ → ℝ)
    (c : Fin n → ℝ) (w η : Fin n → E) :
    (∑ i, ∑ j, c i * c j * (K' ⟪w i,w j⟫_ℝ *
      (⟪w i,η j⟫_ℝ + ⟪η i,w j⟫_ℝ))) =
      2 * ∑ i, c i * ∑ j, c j * K' ⟪w i,w j⟫_ℝ * ⟪η i,w j⟫_ℝ := by
  have hswap : (∑ i, ∑ j, c i * c j * K' ⟪w i,w j⟫_ℝ * ⟪w i,η j⟫_ℝ) =
      ∑ i, ∑ j, c i * c j * K' ⟪w i,w j⟫_ℝ * ⟪η i,w j⟫_ℝ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (w j) (w i), real_inner_comm (w j) (η i)]
    ring
  have hfact : (∑ i, c i * ∑ j, c j * K' ⟪w i,w j⟫_ℝ * ⟪η i,w j⟫_ℝ) =
      ∑ i, ∑ j, c i * c j * K' ⟪w i,w j⟫_ℝ * ⟪η i,w j⟫_ℝ := by
    simp only [Finset.mul_sum, ← mul_assoc]
  rw [hfact]
  simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc]
  rw [hswap]
  ring

theorem hasDerivAt_student_gram {n : ℕ} (K K' : ℝ → ℝ)
    (hK : ∀ r, HasDerivAt K (K' r) r) (c : Fin n → ℝ)
    (W : ℝ → Fin n → E) (η : Fin n → E) (t₀ : ℝ)
    (hW : ∀ i, HasDerivAt (fun t => W t i) (η i) t₀) :
    HasDerivAt (fun t => ∑ i, ∑ j, c i * c j * K ⟪W t i,W t j⟫_ℝ)
      (2 * ∑ i, c i * ∑ j, c j * K' ⟪W t₀ i,W t₀ j⟫_ℝ * ⟪η i,W t₀ j⟫_ℝ) t₀ := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      ((hK ⟪W t₀ i,W t₀ j⟫_ℝ).comp t₀ ((hW i).inner ℝ (hW j))).const_mul (c i*c j)))
  convert h using 1
  exact (kernel_self_directional_symmetry K' c (W t₀) η).symm

/-- The entire finite Gram loss differentiates to the residual pairing, before
specializing to a single direction or assuming that the path lies on the spheres. -/
theorem hasDerivAt_kernelEnergy_curve {n m : ℕ} (K K' : ℝ → ℝ)
    (hK : ∀ r, HasDerivAt K (K' r) r) (c : Fin n → ℝ)
    (W : ℝ → Fin n → E) (η : Fin n → E) (t₀ : ℝ)
    (hW : ∀ i, HasDerivAt (fun t => W t i) (η i) t₀)
    (s : Fin m → ℝ) (v : Fin m → E) :
    HasDerivAt (fun t => (1/(4*π)) *
      ((∑ i, ∑ j, c i * c j * K ⟪W t i,W t j⟫_ℝ) -
        2*(∑ i, ∑ k, c i*s k*K ⟪W t i,v k⟫_ℝ) +
        ∑ k, ∑ l, s k*s l*K ⟪v k,v l⟫_ℝ))
      ((1/(2*π)) * ∑ i, c i *
        ((∑ j, c j*K' ⟪W t₀ i,W t₀ j⟫_ℝ*⟪η i,W t₀ j⟫_ℝ) -
          ∑ k, s k*K' ⟪W t₀ i,v k⟫_ℝ*⟪η i,v k⟫_ℝ)) t₀ := by
  have hST := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      ((hK ⟪W t₀ i,v k⟫_ℝ).comp t₀
        ((hW i).inner ℝ (hasDerivAt_const t₀ (v k)))).const_mul (c i*s k)))
  simp only [inner_zero_right, zero_add] at hST
  have h := (((hasDerivAt_student_gram K K' hK c W η t₀ hW).sub
    (hST.const_mul 2)).add_const (∑ k, ∑ l, s k*s l*K ⟪v k,v l⟫_ℝ)).const_mul
      (1/(4*π))
  convert h using 1
  have hfact (i : Fin n) : (∑ k, c i*s k*(K' ⟪W t₀ i,v k⟫_ℝ*⟪η i,v k⟫_ℝ)) =
      c i * ∑ k, s k*K' ⟪W t₀ i,v k⟫_ℝ*⟪η i,v k⟫_ℝ := by
    simp only [Finset.mul_sum, mul_assoc]
  simp only [hfact, mul_sub, Finset.sum_sub_distrib]
  ring

/-- One moving student yields exactly its mass times the residual direction derivative. -/
theorem hasDerivAt_kernelEnergy_greatCircle {n m : ℕ} (K K' : ℝ → ℝ)
    (hK : ∀ r, HasDerivAt K (K' r) r)
    (c : Fin n → ℝ) (w : Fin n → E) (s : Fin m → ℝ) (v : Fin m → E)
    (a : Fin n) (e : E) :
    HasDerivAt (fun t => (1/(4*π)) *
      ((∑ i, ∑ j, c i*c j*K
        ⟪Function.update w a (cos t • w a + sin t • e) i,
          Function.update w a (cos t • w a + sin t • e) j⟫_ℝ) -
        2*(∑ i, ∑ k, c i*s k*K
          ⟪Function.update w a (cos t • w a + sin t • e) i,v k⟫_ℝ) +
        ∑ k, ∑ l, s k*s l*K ⟪v k,v l⟫_ℝ))
      ((1/(2*π))*c a*
        ((∑ j, c j*K' ⟪w a,w j⟫_ℝ*⟪e,w j⟫_ℝ) -
          ∑ k, s k*K' ⟪w a,v k⟫_ℝ*⟪e,v k⟫_ℝ)) 0 := by
  classical
  have hW (i : Fin n) :
      HasDerivAt (fun t => Function.update w a (cos t • w a + sin t • e) i)
        (if i = a then e else 0) 0 := by
    by_cases hi : i = a
    · subst i
      simpa using hasDerivAt_greatCircle (w a) e
    · simpa [Function.update_noteq hi, hi] using hasDerivAt_const (0 : ℝ) (w i)
  have h := hasDerivAt_kernelEnergy_curve K K' hK c
    (fun t => Function.update w a (cos t • w a + sin t • e))
    (fun i => if i = a then e else 0) 0 hW s v
  simp only [cos_zero, sin_zero, one_smul, zero_smul, add_zero,
    Function.update_eq_self] at h
  convert h using 1
  have hterm (i : Fin n) :
      c i*((∑ j, c j*K' ⟪w i,w j⟫_ℝ*⟪if i = a then e else 0,w j⟫_ℝ) -
        ∑ k, s k*K' ⟪w i,v k⟫_ℝ*⟪if i = a then e else 0,v k⟫_ℝ) =
      if i = a then c a*((∑ j, c j*K' ⟪w a,w j⟫_ℝ*⟪e,w j⟫_ℝ) -
        ∑ k, s k*K' ⟪w a,v k⟫_ℝ*⟪e,v k⟫_ℝ) else 0 := by
    split_ifs with hi
    · subst i
      rfl
    · simp only [inner_zero_left, mul_zero, Finset.sum_const_zero, sub_self]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end PaperLeanFormalization.SphericalCalculus

namespace PaperLeanFormalization.Preliminaries

open PaperLeanFormalization.Definitions

/-- The two kernel derivatives, written without an intervening model wrapper. -/
def KernelDerivative : Model → ℝ → ℝ
  | .centered, r => Real.arcsin r
  | .plainRelu, r => Real.arcsin r + Real.pi / 2

theorem hasDerivAt_Kernel (q : Model) (r : ℝ) :
    HasDerivAt (Kernel q) (KernelDerivative q r) r := by
  cases q with
  | centered => exact KernelCalculus.hasDerivAt_centeredKernel r
  | plainRelu => exact KernelCalculus.hasDerivAt_plainKernel r

theorem hasDerivAt_residual_greatCircle {d n m : ℕ} (q : Model)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ)
    (v : Fin m → Vec d) (u e : Vec d) :
    HasDerivAt (fun t => Residual q c w s v (Real.cos t • u + Real.sin t • e))
      ((∑ i, c i * KernelDerivative q (inner u (w i)) * inner e (w i)) -
        ∑ k, s k * KernelDerivative q (inner u (v k)) * inner e (v k)) 0 :=
  SphericalCalculus.hasDerivAt_residual_greatCircle (Kernel q) (KernelDerivative q)
    (hasDerivAt_Kernel q) c w s v u e

/-- Spherical clause of `eq:residual-loss-pairing-main`: the derivative is a
genuine derivative of the literal Gaussian loss along a unit-sphere path. -/
theorem eq_residual_loss_pairing_main {d n m : ℕ} (hd : 2 ≤ d)
    (q : Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (a : Fin n) (e : Vec d) (he : ‖e‖ = 1) (htan : inner (w a) e = (0 : ℝ)) :
    HasDerivAt (fun t => Loss q c
      (Function.update w a (Real.cos t • w a + Real.sin t • e)) s v)
      ((1 / (2 * Real.pi)) * c a *
        deriv (fun t => Residual q c w s v (Real.cos t • w a + Real.sin t • e)) 0) 0 := by
  classical
  have hunit (t : ℝ) : ∀ i,
      ‖Function.update w a (Real.cos t • w a + Real.sin t • e) i‖ = 1 := by
    intro i
    by_cases hi : i = a
    · subst i
      simpa using SphericalCalculus.norm_greatCircle (w a) e (hw a) he htan t
    · simpa [Function.update_noteq hi] using hw i
  have heq : (fun t => Loss q c
      (Function.update w a (Real.cos t • w a + Real.sin t • e)) s v) =
      (fun t => KernelEnergy q c
        (Function.update w a (Real.cos t • w a + Real.sin t • e)) s v) := by
    funext t
    exact loss_eq_kernelEnergy hd q c _ s v (hunit t) hv
  rw [heq, (hasDerivAt_residual_greatCircle q c w s v (w a) e).deriv]
  exact SphericalCalculus.hasDerivAt_kernelEnergy_greatCircle (Kernel q) (KernelDerivative q)
    (hasDerivAt_Kernel q) c w s v a e

end PaperLeanFormalization.Preliminaries

open Set Filter
open scoped Topology

namespace PaperLeanFormalization.Preliminaries

open PaperLeanFormalization.Definitions
variable {d n : ℕ}

/-- Keep the base point's incoming row radii and vary only masses and directions. -/
def FixedRadiusSection (base q : Parameters d n) : Parameters d n :=
  (fun i => q.1 i / ‖base.2 i‖, fun i => ‖base.2 i‖ • q.2 i)

theorem normalize_has_unit_rows {p : Parameters d n} (hp : ∀ i, p.2 i ≠ 0) :
    ∀ i, ‖(Normalize p.1 p.2).2 i‖ = 1 := by
  intro i
  exact norm_smul_inv_norm (hp i)

/-- The section passes through the chosen raw point, not just a unit-radius lift. -/
theorem section_normalize {p : Parameters d n} (hp : ∀ i, p.2 i ≠ 0) :
    FixedRadiusSection p (Normalize p.1 p.2) = p := by
  apply Prod.ext
  · funext i
    change (p.1 i * ‖p.2 i‖) / ‖p.2 i‖ = p.1 i
    exact mul_div_cancel _ (norm_ne_zero_iff.mpr (hp i))
  · funext i
    change ‖p.2 i‖ • (‖p.2 i‖⁻¹ • p.2 i) = p.2 i
    rw [smul_smul, mul_inv_cancel (norm_ne_zero_iff.mpr (hp i)), one_smul]

/-- On the cylinder the section is a right inverse of normalization. -/
theorem normalize_section {p q : Parameters d n} (hp : ∀ i, p.2 i ≠ 0)
    (hq : ∀ i, ‖q.2 i‖ = 1) :
    Normalize (FixedRadiusSection p q).1 (FixedRadiusSection p q).2 = q := by
  have hn (i : Fin n) : ‖‖p.2 i‖ • q.2 i‖ = ‖p.2 i‖ := by
    rw [norm_smul, norm_norm, hq i, mul_one]
  apply Prod.ext
  · funext i
    change (q.1 i / ‖p.2 i‖) * ‖‖p.2 i‖ • q.2 i‖ = q.1 i
    rw [hn, div_mul_cancel _ (norm_ne_zero_iff.mpr (hp i))]
  · funext i
    change ‖‖p.2 i‖ • q.2 i‖⁻¹ • (‖p.2 i‖ • q.2 i) = q.2 i
    rw [hn, smul_smul, inv_mul_cancel (norm_ne_zero_iff.mpr (hp i)), one_smul]

theorem nonzero_rows_open : IsOpen {p : Parameters d n | ∀ i, p.2 i ≠ 0} := by
  have heq : {p : Parameters d n | ∀ i, p.2 i ≠ 0} =
      ⋂ i : Fin n, (fun p : Parameters d n => p.2 i) ⁻¹' ({0}ᶜ) := by
    ext p
    simp
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_compl_singleton.preimage
    ((continuous_apply i).comp continuous_snd)

/-- Smoothness uses only smooth coordinate projections and the norm away from zero. -/
theorem normalize_smooth {p : Parameters d n} (hp : ∀ i, p.2 i ≠ 0) :
    ContDiffAt ℝ ⊤ (fun p : Parameters d n => Normalize p.1 p.2) p := by
  have hc (i : Fin n) : ContDiffAt ℝ ⊤ (fun q : Parameters d n => q.1 i) p :=
    ((contDiff_apply ℝ ℝ i).comp contDiff_fst).contDiffAt
  have hw (i : Fin n) : ContDiffAt ℝ ⊤ (fun q : Parameters d n => q.2 i) p :=
    ((contDiff_apply ℝ (Vec d) i).comp contDiff_snd).contDiffAt
  apply ContDiffAt.prod
  · apply contDiffAt_pi.mpr
    exact fun i => (hc i).mul ((hw i).norm ℝ (hp i))
  · apply contDiffAt_pi.mpr
    exact fun i => (((hw i).norm ℝ (hp i)).inv
      (norm_ne_zero_iff.mpr (hp i))).smul (hw i)

/-- The section is globally smooth, even when some fixed base radius vanishes. -/
theorem fixed_radius_section_smooth (p : Parameters d n) :
    ContDiff ℝ ⊤ (FixedRadiusSection p) := by
  apply ContDiff.prod
  · apply contDiff_pi.mpr
    intro i
    simpa only [FixedRadiusSection, div_eq_mul_inv] using
      ((contDiff_apply ℝ ℝ i).comp contDiff_fst).mul contDiff_const
  · apply contDiff_pi.mpr
    exact fun i => contDiff_const.smul
      ((contDiff_apply ℝ (Vec d) i).comp contDiff_snd)

/-- Ordinary local minima transport by the continuous map and its explicit section.
No differentiability or regularity assumption on the objective is necessary. -/
theorem raw_local_minimum_iff (L : Parameters d n → ℝ) {p : Parameters d n}
    (hp : ∀ i, p.2 i ≠ 0) :
    IsLocalMin (fun p : Parameters d n => L (Normalize p.1 p.2)) p ↔
      IsLocalMinOn L {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2) := by
  constructor
  · intro hraw
    have hbase : IsLocalMin (fun p : Parameters d n => L (Normalize p.1 p.2))
        (FixedRadiusSection p (Normalize p.1 p.2)) := by
      rw [section_normalize hp]
      exact hraw
    have hcomp := hbase.comp_continuous
      (fixed_radius_section_smooth p).continuous.continuousAt
    apply (hcomp.on {q | ∀ i, ‖q.2 i‖ = 1}).congr
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact congrArg L (normalize_section hp hq)
    · exact normalize_has_unit_rows hp
  · intro hpolar
    have hcomp := hpolar.comp_continuousOn
      (g := fun p : Parameters d n => Normalize p.1 p.2)
      (s := {q : Parameters d n | ∀ i, q.2 i ≠ 0})
      (fun q hq => normalize_has_unit_rows hq)
      (fun q hq => (normalize_smooth hq).continuousAt.continuousWithinAt) hp
    exact hcomp.isLocalMin (nonzero_rows_open.mem_nhds hp)

section RowChainCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The differential of the row norm is the normalized row, viewed as a linear form. -/
theorem norm_derivative_at_nonzero {a : E} (ha : a ≠ 0) :
    HasFDerivAt (fun z : E => ‖z‖) (innerSL ℝ (‖a‖⁻¹ • a)) a := by
  have hr : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  convert (hasStrictFDerivAt_norm_sq a).hasFDerivAt.sqrt (pow_ne_zero 2 hr) using 1
  · funext z
    exact (Real.sqrt_sq (norm_nonneg z)).symm
  · ext z
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply, real_inner_smul_left,
      Real.sqrt_sq (norm_nonneg a), smul_eq_mul]
    field_simp
    ring

/-- The derivative of row normalization is the orthogonal tangent projection
divided by the row radius. There is no derivative-definition chain to unfold. -/
theorem direction_normalization_derivative {a : E} (ha : a ≠ 0) :
    HasFDerivAt (fun z : E => ‖z‖⁻¹ • z)
      (‖a‖⁻¹ • ((ContinuousLinearMap.id ℝ E) -
        (innerSL ℝ (‖a‖⁻¹ • a)).smulRight (‖a‖⁻¹ • a))) a := by
  have hr : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hn := norm_derivative_at_nonzero ha
  have hi := (hasFDerivAt_inv hr).comp a hn
  convert hi.smul (hasFDerivAt_id a) using 1
  ext z
  change ‖a‖⁻¹ • (z - (inner (‖a‖⁻¹ • a) z : ℝ) • (‖a‖⁻¹ • a)) =
    ‖a‖⁻¹ • z + ((inner (‖a‖⁻¹ • a) z : ℝ) * -((‖a‖ ^ 2)⁻¹)) • a
  rw [smul_sub]
  simp only [real_inner_smul_left, smul_smul]
  rw [sub_eq_add_neg, ← neg_smul]
  congr 1
  congr 1
  ring

/-- An objective's differential with one mass and one direction free. -/
def RowDifferential (massGradient : ℝ) (directionGradient : E) : (ℝ × E) →L[ℝ] ℝ :=
  massGradient • ContinuousLinearMap.fst ℝ ℝ E +
    (innerSL ℝ directionGradient).comp (ContinuousLinearMap.snd ℝ ℝ E)

theorem row_differential_apply (alpha : ℝ) (g : E) (v : ℝ × E) :
    RowDifferential alpha g v = alpha * v.1 + inner g v.2 := rfl

/-- `eq:raw-chain-rule`, output derivative and incoming-row gradient, as genuine
derivative witnesses. Apply this to the loss with all other neurons fixed. -/
theorem eq_raw_chain_rule (L : ℝ × E → ℝ) (o alpha : ℝ) (a g : E)
    (ha : a ≠ 0)
    (hL : HasFDerivAt L (RowDifferential alpha g) (o * ‖a‖, ‖a‖⁻¹ • a)) :
    HasDerivAt (fun t : ℝ => L (t * ‖a‖, ‖a‖⁻¹ • a)) (‖a‖ * alpha) o ∧
    HasFDerivAt (fun z : E => L (o * ‖z‖, ‖z‖⁻¹ • z))
      (innerSL ℝ ((o * alpha) • (‖a‖⁻¹ • a) +
        ‖a‖⁻¹ • (g - (inner (‖a‖⁻¹ • a) g : ℝ) • (‖a‖⁻¹ • a)))) a := by
  constructor
  · have hpath : HasDerivAt (fun t : ℝ => (t * ‖a‖, ‖a‖⁻¹ • a)) (‖a‖, 0) o := by
      simpa using ((hasDerivAt_id o).mul_const ‖a‖).prod (hasDerivAt_const o (‖a‖⁻¹ • a))
    convert hL.comp_hasDerivAt o hpath using 1
    simp [RowDifferential, innerSL_apply]
    ring
  · have hpath := ((norm_derivative_at_nonzero ha).const_smul o).prod
      (direction_normalization_derivative ha)
    convert hL.comp a hpath using 1
    ext z
    change inner ((o * alpha) • (‖a‖⁻¹ • a) +
        ‖a‖⁻¹ • (g - (inner (‖a‖⁻¹ • a) g : ℝ) • (‖a‖⁻¹ • a))) z =
      alpha * (o * inner (‖a‖⁻¹ • a) z) +
        inner g (‖a‖⁻¹ • (z - (inner (‖a‖⁻¹ • a) z : ℝ) • (‖a‖⁻¹ • a)))
    simp only [real_inner_smul_left, real_inner_smul_right,
      inner_add_left, inner_sub_left, inner_sub_right]
    rw [real_inner_comm g a]
    ring

/-- The radial and spherical summands in the second chain-rule equation are orthogonal. -/
theorem raw_chain_rule_orthogonal (o alpha : ℝ) (a g : E) (ha : a ≠ 0) :
    inner ((o * alpha) • (‖a‖⁻¹ • a))
      (‖a‖⁻¹ • (g - (inner (‖a‖⁻¹ • a) g : ℝ) • (‖a‖⁻¹ • a))) = (0 : ℝ) := by
  have hunit : ‖(‖a‖⁻¹ : ℝ) • a‖ = 1 := norm_smul_inv_norm ha
  have hh : (inner (‖a‖⁻¹ • a) (‖a‖⁻¹ • a) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit]
    norm_num
  rw [real_inner_smul_left, real_inner_smul_right, inner_sub_right,
    real_inner_smul_right, hh]
  ring

end RowChainCalculus

/-- Applying the displayed chain rule to coordinate linear functionals recovers
the differentiability of row normalization. This is the chain rule used in
the critical-point transfer, not a separate unused display theorem. -/
theorem direction_differentiable_from_chain_rule {a : Vec d} (ha : a ≠ 0) :
    DifferentiableAt ℝ (fun z : Vec d => ‖z‖⁻¹ • z) a := by
  have hcoordinate (j : Fin d) : DifferentiableAt ℝ
      (fun z : Vec d => (‖z‖⁻¹ • z) j) a := by
    let g : Vec d := EuclideanSpace.single j 1
    have hlinear : HasFDerivAt (fun z : ℝ × Vec d => (inner g z.2 : ℝ))
        (RowDifferential 0 g) (0 * ‖a‖, ‖a‖⁻¹ • a) := by
      simpa only [RowDifferential, zero_smul, zero_add] using
        ((innerSL ℝ g).comp (ContinuousLinearMap.snd ℝ ℝ (Vec d))).hasFDerivAt
    have h := (eq_raw_chain_rule (fun z : ℝ × Vec d => (inner g z.2 : ℝ))
      0 0 a g ha hlinear).2.differentiableAt
    simpa only [g, EuclideanSpace.inner_single_left, map_one, one_mul] using h
  have hpi : DifferentiableAt ℝ
      (fun z : Vec d => EuclideanSpace.equiv (Fin d) ℝ (‖z‖⁻¹ • z)) a := by
    apply differentiableAt_pi.mpr
    exact hcoordinate
  have h := (EuclideanSpace.equiv (Fin d) ℝ).symm.differentiableAt.comp a hpi
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

/-- The normalization map differential, with its directional part supplied
by `eq:raw-chain-rule`. No dimension, sign, or objective hypotheses are needed. -/
theorem normalize_differentiable_from_chain_rule {p : Parameters d n}
    (hp : ∀ i, p.2 i ≠ 0) :
    DifferentiableAt ℝ (fun z : Parameters d n => Normalize z.1 z.2) p := by
  have hc (i : Fin n) : DifferentiableAt ℝ (fun z : Parameters d n => z.1 i) p :=
    ((contDiff_apply ℝ ℝ i).comp contDiff_fst).differentiable le_top p
  have hw (i : Fin n) : DifferentiableAt ℝ (fun z : Parameters d n => z.2 i) p :=
    ((contDiff_apply ℝ (Vec d) i).comp contDiff_snd).differentiable le_top p
  apply DifferentiableAt.prod
  · apply differentiableAt_pi.mpr
    intro i
    exact (hc i).mul ((norm_derivative_at_nonzero (hp i)).differentiableAt.comp p (hw i))
  · apply differentiableAt_pi.mpr
    intro i
    exact (direction_differentiable_from_chain_rule (hp i)).comp p (hw i)

/-- First-order stationarity transports by exactly the same map and section.
Using derivative witnesses within the cylinder avoids an unnecessary extension
assumption on the objective away from unit directions. -/
theorem raw_stationarity_iff (L : Parameters d n → ℝ) {p : Parameters d n}
    (hp : ∀ i, p.2 i ≠ 0) :
    HasFDerivAt (fun p : Parameters d n => L (Normalize p.1 p.2))
        (0 : Parameters d n →L[ℝ] ℝ) p ↔
      HasFDerivWithinAt L (0 : Parameters d n →L[ℝ] ℝ)
        {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2) := by
  constructor
  · intro hraw
    have hbase : HasFDerivAt (fun p : Parameters d n => L (Normalize p.1 p.2))
        (0 : Parameters d n →L[ℝ] ℝ) (FixedRadiusSection p (Normalize p.1 p.2)) := by
      rw [section_normalize hp]
      exact hraw
    have hcomp := hbase.comp (Normalize p.1 p.2)
      ((fixed_radius_section_smooth p).differentiable le_top
        (Normalize p.1 p.2)).hasFDerivAt
    have hwithin : HasFDerivWithinAt
        ((fun p : Parameters d n => L (Normalize p.1 p.2)) ∘ FixedRadiusSection p)
        (0 : Parameters d n →L[ℝ] ℝ) {q | ∀ i, ‖q.2 i‖ = 1}
        (Normalize p.1 p.2) := by
      simpa only [ContinuousLinearMap.zero_comp] using hcomp.hasFDerivWithinAt
    apply hwithin.congr'
    · exact fun q hq => congrArg L (normalize_section hp hq).symm
    · exact normalize_has_unit_rows hp
  · intro hpolar
    have hcomp := hpolar.comp p
      (normalize_differentiable_from_chain_rule hp).hasFDerivAt.hasFDerivWithinAt
      (show MapsTo (fun p : Parameters d n => Normalize p.1 p.2)
        {p | ∀ i, p.2 i ≠ 0} {q | ∀ i, ‖q.2 i‖ = 1} from
          fun q hq => normalize_has_unit_rows hq)
    have hambient := hcomp.hasFDerivAt (nonzero_rows_open.mem_nhds hp)
    simpa only [ContinuousLinearMap.zero_comp] using hambient

end PaperLeanFormalization.Preliminaries


namespace PaperLeanFormalization.Preliminaries

open PaperLeanFormalization.Definitions

/-- Proposition `prop:loss_in_residual`: the value, mass derivative, and
spherical directional derivative are genuine statements about the literal
Gaussian loss. The last clause tests each unit tangent direction. -/
theorem prop_loss_in_residual {d n m : ℕ} (hd : 2 ≤ d)
    (q : Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    Loss q c w s v = (1 / (4 * Real.pi)) *
      ((∑ i, c i * Residual q c w s v (w i)) -
        ∑ k, s k * Residual q c w s v (v k)) ∧
    (∀ a : Fin n, HasDerivAt (fun t => Loss q (Function.update c a t) w s v)
      ((1 / (2 * Real.pi)) * Residual q c w s v (w a)) (c a)) ∧
    (∀ (a : Fin n) (e : Vec d), ‖e‖ = 1 → inner (w a) e = (0 : ℝ) →
      HasDerivAt (fun t => Loss q c
        (Function.update w a (Real.cos t • w a + Real.sin t • e)) s v)
        ((1 / (2 * Real.pi)) * c a * deriv
          (fun t => Residual q c w s v (Real.cos t • w a + Real.sin t • e)) 0) 0) := by
  exact ⟨eq_residual_loss hd q c w s v hw hv,
    eq_residual_mass_gradient hd q c w s v hw hv,
    fun a e he htan => eq_residual_loss_pairing_main hd q c w s v hw hv a e he htan⟩

end PaperLeanFormalization.Preliminaries

noncomputable section

open Real MeasureTheory Filter
open scoped BigOperators

namespace PaperLeanFormalization.Preliminaries

private theorem coordinate_norm_square {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [pow_two, ← real_inner_self_eq_norm_mul_norm, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => by change (x i) * (x i) = (x i) ^ 2; ring

theorem gaussian_norm_square_integrable {d : ℕ} (hd : 2 ≤ d) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 2 * stdGaussianDensity x) := by
  have hcoordinate (i : Fin d) : Integrable
      (fun x : EuclideanSpace ℝ (Fin d) => (x i) ^ 2 * stdGaussianDensity x) := by
    simpa only [pow_two, EuclideanSpace.inner_single_left, map_one, one_mul] using
      gaussian_square_integrable hd (EuclideanSpace.single i 1)
  have h := integrable_finset_sum Finset.univ (fun i _ => hcoordinate i)
  convert h using 1
  funext x
  rw [coordinate_norm_square, Finset.sum_mul]

/-- The Gaussian norm moment is the sum of the locally proved coordinate
moments. It does not require the polar-coordinate normalization. -/
theorem gaussian_norm_square_moment {d : ℕ} (hd : 2 ≤ d) :
    (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 * stdGaussianDensity x) = (d : ℝ) := by
  have hcoordinate (i : Fin d) :
      (∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 2 * stdGaussianDensity x) = 1 := by
    simpa only [pow_two, EuclideanSpace.inner_single_left, map_one, one_mul,
      EuclideanSpace.norm_single, norm_one] using
      gaussian_square_moment hd (EuclideanSpace.single i 1)
  have hi (i : Fin d) : Integrable
      (fun x : EuclideanSpace ℝ (Fin d) => (x i) ^ 2 * stdGaussianDensity x) := by
    simpa only [pow_two, EuclideanSpace.inner_single_left, map_one, one_mul] using
      gaussian_square_integrable hd (EuclideanSpace.single i 1)
  simp_rw [coordinate_norm_square, Finset.sum_mul]
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  simp only [hcoordinate, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- A linear-growth function has an integrable Gaussian square, by direct
domination by the norm-square integrand. -/
theorem gaussian_growth_square_integrable {d : ℕ} (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    {B : ℝ} (hbound : ∀ x, |g x| ≤ B * ‖x‖) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => g x ^ 2 * stdGaussianDensity x) := by
  have hdensity : Continuous (fun x : EuclideanSpace ℝ (Fin d) => stdGaussianDensity x) := by
    unfold stdGaussianDensity
    exact continuous_const.mul (continuous_exp.comp (((continuous_norm.pow 2).neg).div_const 2))
  refine ((gaussian_norm_square_integrable hd).const_mul (B ^ 2)).mono'
    ((hg.pow 2).mul hdensity).aestronglyMeasurable (eventually_of_forall fun x => ?_)
  have hdens : 0 ≤ stdGaussianDensity x := by unfold stdGaussianDensity; positivity
  have hsq : g x ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2 := by
    simpa only [sq_abs, mul_pow] using pow_le_pow_left (abs_nonneg (g x)) (hbound x) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hdens)]
  nlinarith only [mul_le_mul_of_nonneg_right hsq hdens]

/-- The even and odd terms are orthogonal by antipodal averaging. This one
lemma serves both learned-skip transport and empirical coercivity. -/
theorem gaussian_even_add_linear_square_split {d : ℕ} (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    (heven : ∀ x, g (-x) = g x) {B : ℝ} (hbound : ∀ x, |g x| ≤ B * ‖x‖)
    (u : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d), (g x + (inner u x : ℝ)) ^ 2 * stdGaussianDensity x) =
      (∫ x : EuclideanSpace ℝ (Fin d), g x ^ 2 * stdGaussianDensity x) +
      ∫ x : EuclideanSpace ℝ (Fin d), (inner u x : ℝ) ^ 2 * stdGaussianDensity x := by
  have hG := gaussian_growth_square_integrable hd
    (hg.add (continuous_const.inner continuous_id))
    (show ∀ x, |g x + (inner u x : ℝ)| ≤ (B + ‖u‖) * ‖x‖ from fun x => by
      have h := abs_add (g x) (inner u x : ℝ)
      nlinarith only [h, hbound x, abs_real_inner_le_norm u x])
  simp only [id_eq] at hG
  have hE := gaussian_growth_square_integrable hd hg hbound
  have hL := gaussian_growth_square_integrable hd
    (continuous_const.inner continuous_id : Continuous (fun x : EuclideanSpace ℝ (Fin d) => (inner u x : ℝ)))
    (fun x => abs_real_inner_le_norm u x)
  have hdensity (x : EuclideanSpace ℝ (Fin d)) : stdGaussianDensity (-x) = stdGaussianDensity x := by
    simp only [stdGaussianDensity, norm_neg]
  have hGneg : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (g (-x) + (inner u (-x) : ℝ)) ^ 2 * stdGaussianDensity x) := by
    simpa only [hdensity] using hG.comp_neg
  have hneg : (∫ x : EuclideanSpace ℝ (Fin d), (g (-x) + (inner u (-x) : ℝ)) ^ 2 * stdGaussianDensity x) =
      ∫ x : EuclideanSpace ℝ (Fin d), (g x + (inner u x : ℝ)) ^ 2 * stdGaussianDensity x := by
    simpa only [hdensity] using integral_neg_eq_self
      (fun x : EuclideanSpace ℝ (Fin d) => (g x + (inner u x : ℝ)) ^ 2 * stdGaussianDensity x) volume
  have hpoint (x : EuclideanSpace ℝ (Fin d)) :
      (g x + (inner u x : ℝ)) ^ 2 * stdGaussianDensity x +
        (g (-x) + (inner u (-x) : ℝ)) ^ 2 * stdGaussianDensity x =
      2 * (g x ^ 2 * stdGaussianDensity x) +
        2 * ((inner u x : ℝ) ^ 2 * stdGaussianDensity x) := by
    rw [heven, inner_neg_right]
    ring
  have h := integral_congr_ae (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (eventually_of_forall hpoint)
  rw [integral_add hG hGneg, integral_add (hE.const_mul 2) (hL.const_mul 2),
    integral_mul_left, integral_mul_left, hneg] at h
  linarith only [h]

end PaperLeanFormalization.Preliminaries

noncomputable section
open Real MeasureTheory Set
open scoped Interval BigOperators RealInnerProductSpace


namespace PaperLeanFormalization.Preliminaries

open PaperLeanFormalization.Definitions

/- Generated integration block: assemble_raw_addition.py; handwritten input bodies unchanged. -/
section RawTransferAdditions
open Set Filter Classical MeasureTheory
open scoped Topology BigOperators RealInnerProductSpace
variable {d n : ℕ}

/-! The skip coordinate is carried unchanged. -/

def SkipNormalize (p : Vec d × Parameters d n) : Vec d × Parameters d n :=
  (p.1, Normalize p.2.1 p.2.2)

/-- The skip component is unchanged; only the neuron coordinates use the raw
chain rule. -/
theorem skip_normalize_differentiable_from_chain_rule {p : Vec d × Parameters d n}
    (hp : ∀ i, p.2.2 i ≠ 0) : DifferentiableAt ℝ SkipNormalize p := by
  exact differentiableAt_fst.prod
    ((normalize_differentiable_from_chain_rule hp).comp p differentiableAt_snd)

def SkipFixedRadiusSection (base q : Vec d × Parameters d n) : Vec d × Parameters d n :=
  (q.1, FixedRadiusSection base.2 q.2)

theorem skip_section_normalize {p : Vec d × Parameters d n}
    (hp : ∀ i, p.2.2 i ≠ 0) : SkipFixedRadiusSection p (SkipNormalize p) = p := by
  exact Prod.ext rfl (section_normalize hp)

theorem skip_normalize_section {p q : Vec d × Parameters d n}
    (hp : ∀ i, p.2.2 i ≠ 0) (hq : ∀ i, ‖q.2.2 i‖ = 1) :
    SkipNormalize (SkipFixedRadiusSection p q) = q := by
  exact Prod.ext rfl (normalize_section hp hq)

theorem skip_normalize_smooth {p : Vec d × Parameters d n}
    (hp : ∀ i, p.2.2 i ≠ 0) : ContDiffAt ℝ ⊤ SkipNormalize p := by
  exact contDiffAt_fst.prod ((normalize_smooth hp).comp p contDiffAt_snd)

theorem skip_section_smooth (p : Vec d × Parameters d n) :
    ContDiff ℝ ⊤ (SkipFixedRadiusSection p) := by
  exact contDiff_fst.prod ((fixed_radius_section_smooth p.2).comp contDiff_snd)

theorem skip_nonzero_rows_open :
    IsOpen {p : Vec d × Parameters d n | ∀ i, p.2.2 i ≠ 0} :=
  nonzero_rows_open.preimage continuous_snd

theorem skip_raw_local_minimum_iff (L : Vec d × Parameters d n → ℝ)
    {p : Vec d × Parameters d n} (hp : ∀ i, p.2.2 i ≠ 0) :
    IsLocalMin (L ∘ SkipNormalize) p ↔
      IsLocalMinOn L {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p) := by
  constructor
  · intro hraw
    have hbase : IsLocalMin (L ∘ SkipNormalize)
        (SkipFixedRadiusSection p (SkipNormalize p)) := by
      rw [skip_section_normalize hp]
      exact hraw
    have hcomp := hbase.comp_continuous (skip_section_smooth p).continuous.continuousAt
    apply (hcomp.on {q | ∀ i, ‖q.2.2 i‖ = 1}).congr
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact congrArg L (skip_normalize_section hp hq)
    · exact normalize_has_unit_rows hp
  · intro hpolar
    have hcomp := hpolar.comp_continuousOn (g := SkipNormalize)
      (s := {q : Vec d × Parameters d n | ∀ i, q.2.2 i ≠ 0})
      (fun q hq => normalize_has_unit_rows hq)
      (fun q hq => (skip_normalize_smooth hq).continuousAt.continuousWithinAt) hp
    exact hcomp.isLocalMin (skip_nonzero_rows_open.mem_nhds hp)

theorem skip_raw_stationarity_iff (L : Vec d × Parameters d n → ℝ)
    {p : Vec d × Parameters d n} (hp : ∀ i, p.2.2 i ≠ 0) :
    HasFDerivAt (L ∘ SkipNormalize) (0 : (Vec d × Parameters d n) →L[ℝ] ℝ) p ↔
      HasFDerivWithinAt L (0 : (Vec d × Parameters d n) →L[ℝ] ℝ)
        {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p) := by
  constructor
  · intro hraw
    have hbase : HasFDerivAt (L ∘ SkipNormalize) (0 : (Vec d × Parameters d n) →L[ℝ] ℝ)
        (SkipFixedRadiusSection p (SkipNormalize p)) := by
      rw [skip_section_normalize hp]
      exact hraw
    have hcomp := hbase.comp (SkipNormalize p)
      ((skip_section_smooth p).differentiable le_top (SkipNormalize p)).hasFDerivAt
    have hwithin : HasFDerivWithinAt ((L ∘ SkipNormalize) ∘ SkipFixedRadiusSection p)
        (0 : (Vec d × Parameters d n) →L[ℝ] ℝ) {q | ∀ i, ‖q.2.2 i‖ = 1}
        (SkipNormalize p) := by
      simpa only [ContinuousLinearMap.zero_comp] using hcomp.hasFDerivWithinAt
    apply hwithin.congr'
    · exact fun q hq => congrArg L (skip_normalize_section hp hq).symm
    · exact normalize_has_unit_rows hp
  · intro hpolar
    have hcomp := hpolar.comp p
      (skip_normalize_differentiable_from_chain_rule hp).hasFDerivAt.hasFDerivWithinAt
      (show MapsTo SkipNormalize {p : Vec d × Parameters d n | ∀ i, p.2.2 i ≠ 0}
        {q | ∀ i, ‖q.2.2 i‖ = 1} from fun q hq => normalize_has_unit_rows hq)
    have hambient := hcomp.hasFDerivAt (skip_nonzero_rows_open.mem_nhds hp)
    simpa only [ContinuousLinearMap.zero_comp] using hambient

/-! Global minimum is an order comparison, not a positive-loss condition. -/

theorem normalized_unit_point {q : Parameters d n} (hq : ∀ i, ‖q.2 i‖ = 1) :
    Normalize q.1 q.2 = q := by
  apply Prod.ext
  · funext i
    change q.1 i * ‖q.2 i‖ = q.1 i
    rw [hq i, mul_one]
  · funext i
    change ‖q.2 i‖⁻¹ • q.2 i = q.2 i
    rw [hq i, inv_one, one_smul]

theorem unit_rows_nonzero {q : Parameters d n} (hq : ∀ i, ‖q.2 i‖ = 1) :
    ∀ i, q.2 i ≠ 0 := by
  intro i hi
  have h := hq i
  rw [hi, norm_zero] at h
  exact zero_ne_one h

/-- Surjectivity transfers global minima on the natural nonzero-row domain.
The full ambient raw space requires, additionally, completing the zero rows. -/
theorem raw_global_minimum_iff (L : Parameters d n → ℝ) (p : Parameters d n) :
    IsMinOn (fun p : Parameters d n => L (Normalize p.1 p.2))
      {q | ∀ i, q.2 i ≠ 0} p ↔
    IsMinOn L {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2) := by
  constructor
  · intro h q hq
    have hle := h (unit_rows_nonzero hq)
    change L (Normalize p.1 p.2) ≤ L (Normalize q.1 q.2) at hle
    simpa only [normalized_unit_point hq] using hle
  · intro h q hq
    exact h (normalize_has_unit_rows hq)

theorem skip_raw_global_minimum_iff (L : Vec d × Parameters d n → ℝ)
    (p : Vec d × Parameters d n) :
    IsMinOn (L ∘ SkipNormalize) {q | ∀ i, q.2.2 i ≠ 0} p ↔
      IsMinOn L {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p) := by
  constructor
  · intro h q hq
    have hle := h (unit_rows_nonzero hq)
    have hfix : SkipNormalize q = q := Prod.ext rfl (normalized_unit_point hq)
    change L (SkipNormalize p) ≤ L (SkipNormalize q) at hle
    simpa only [Function.comp_apply, hfix] using hle
  · intro h q hq
    exact h (normalize_has_unit_rows hq)

theorem raw_spurious_minimum_iff (L : Parameters d n → ℝ)
    {p : Parameters d n} (hp : ∀ i, p.2 i ≠ 0) :
    (IsLocalMin (fun p : Parameters d n => L (Normalize p.1 p.2)) p ∧
      ¬ IsMinOn (fun p : Parameters d n => L (Normalize p.1 p.2))
        {q | ∀ i, q.2 i ≠ 0} p) ↔
    (IsLocalMinOn L {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2) ∧
      ¬ IsMinOn L {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2)) :=
  and_congr (raw_local_minimum_iff L hp) (not_congr (raw_global_minimum_iff L p))

theorem skip_raw_spurious_minimum_iff (L : Vec d × Parameters d n → ℝ)
    {p : Vec d × Parameters d n} (hp : ∀ i, p.2.2 i ≠ 0) :
    (IsLocalMin (L ∘ SkipNormalize) p ∧
      ¬ IsMinOn (L ∘ SkipNormalize) {q | ∀ i, q.2.2 i ≠ 0} p) ↔
    (IsLocalMinOn L {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p) ∧
      ¬ IsMinOn L {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p)) :=
  and_congr (skip_raw_local_minimum_iff L hp) (not_congr (skip_raw_global_minimum_iff L p))

/-! Zero incoming rows require a value-preserving completion for ambient globals. -/

def CompleteRaw (base p : Parameters d n) : Parameters d n :=
  ((Normalize p.1 p.2).1, fun i =>
    if p.2 i = 0 then (Normalize base.1 base.2).2 i else (Normalize p.1 p.2).2 i)

theorem complete_raw_unit {base : Parameters d n} (hb : ∀ i, base.2 i ≠ 0)
    (p : Parameters d n) : ∀ i, ‖(CompleteRaw base p).2 i‖ = 1 := by
  intro i
  by_cases hi : p.2 i = 0
  · simpa only [CompleteRaw, if_pos hi] using normalize_has_unit_rows hb i
  · simpa only [CompleteRaw, if_neg hi] using norm_smul_inv_norm hi

/-- Completing a zero row changes no feature sum, because its mass is zero. -/
theorem complete_raw_feature_sum (phi : ℝ → ℝ) (hzero : phi 0 = 0)
    (hhom : ∀ (r z : ℝ), 0 ≤ r → phi (r * z) = r * phi z)
    (base p : Parameters d n) (x : Vec d) :
    (∑ i, (CompleteRaw base p).1 i * phi (inner ((CompleteRaw base p).2 i) x)) =
      ∑ i, p.1 i * phi (inner (p.2 i) x) := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p.2 i = 0
  · simp [CompleteRaw, Normalize, hi, hzero]
  · simp only [CompleteRaw, Normalize, if_neg hi]
    have hfactor : ‖p.2 i‖ * (inner (‖p.2 i‖⁻¹ • p.2 i) x : ℝ) = inner (p.2 i) x := by
      rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel (norm_ne_zero_iff.mpr hi), one_mul]
    rw [mul_assoc, ← hhom _ _ (norm_nonneg _), hfactor]

/-- A purely order-theoretic global-minimum bridge. Equal attainable values,
not zero optimum or nonnegative loss, are what global minimality needs. -/
theorem global_minimum_iff_of_value_completion {α : Type*} (L : α → ℝ)
    (S : Set α) (p q : α) (heq : L p = L q)
    (hcomplete : ∀ x, ∃ y ∈ S, L y = L x) :
    IsMinOn L Set.univ p ↔ IsMinOn L S q := by
  constructor
  · intro h x _
    have hx : L p ≤ L x := h (Set.mem_univ x)
    rwa [heq] at hx
  · intro h x _
    obtain ⟨y, hy, hvalue⟩ := hcomplete x
    have hy' : L q ≤ L y := h hy
    rwa [hvalue, ← heq] at hy'

theorem normalized_feature_sum (phi : ℝ → ℝ) (hzero : phi 0 = 0)
    (hhom : ∀ (r z : ℝ), 0 ≤ r → phi (r * z) = r * phi z)
    (p : Parameters d n) (x : Vec d) :
    (∑ i, (Normalize p.1 p.2).1 i * phi (inner ((Normalize p.1 p.2).2 i) x)) =
      ∑ i, p.1 i * phi (inner (p.2 i) x) := by
  rw [← complete_raw_feature_sum phi hzero hhom p p x]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p.2 i = 0
  · simp [CompleteRaw, Normalize, hi]
  · simp only [CompleteRaw, if_neg hi]

/-- The full transfer theorem for any functional of a positively homogeneous
network. It applies to the literal Gaussian loss without any analytic assumptions
on the functional, and handles all raw competitors, including zero rows. -/
theorem raw_feature_functional_transfer (phi : ℝ → ℝ) (hzero : phi 0 = 0)
    (hhom : ∀ (r z : ℝ), 0 ≤ r → phi (r * z) = r * phi z)
    (G : (Vec d → ℝ) → ℝ) {p : Parameters d n} (hp : ∀ i, p.2 i ≠ 0) :
    let L := fun q : Parameters d n => G (fun x => ∑ i, q.1 i * phi (inner (q.2 i) x))
    (HasFDerivAt L (0 : Parameters d n →L[ℝ] ℝ) p ↔
      HasFDerivWithinAt L (0 : Parameters d n →L[ℝ] ℝ)
        {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2)) ∧
    (IsLocalMin L p ↔ IsLocalMinOn L {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2)) ∧
    ((IsLocalMin L p ∧ ¬ IsMinOn L Set.univ p) ↔
      (IsLocalMinOn L {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2) ∧
        ¬ IsMinOn L {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2))) := by
  intro L
  have hnormal (q : Parameters d n) : L (Normalize q.1 q.2) = L q :=
    congrArg G (funext fun x => normalized_feature_sum phi hzero hhom q x)
  have hlocal := raw_local_minimum_iff L hp
  have hcritical := raw_stationarity_iff L hp
  simp only [hnormal] at hlocal hcritical
  have hglobal : IsMinOn L Set.univ p ↔ IsMinOn L {q | ∀ i, ‖q.2 i‖ = 1} (Normalize p.1 p.2) := by
    apply global_minimum_iff_of_value_completion L _ p _ (hnormal p).symm
    intro q
    exact ⟨CompleteRaw p q, complete_raw_unit hp q,
      congrArg G (funext fun x => complete_raw_feature_sum phi hzero hhom p q x)⟩
  exact ⟨hcritical, hlocal, and_congr hlocal (not_congr hglobal)⟩

/-- The skip vector is an untouched input to the network functional. -/
theorem skip_feature_functional_transfer (phi : ℝ → ℝ) (hzero : phi 0 = 0)
    (hhom : ∀ (r z : ℝ), 0 ≤ r → phi (r * z) = r * phi z)
    (G : Vec d → (Vec d → ℝ) → ℝ) {p : Vec d × Parameters d n}
    (hp : ∀ i, p.2.2 i ≠ 0) :
    let L := fun q : Vec d × Parameters d n => G q.1 (fun x => ∑ i, q.2.1 i * phi (inner (q.2.2 i) x))
    (HasFDerivAt L (0 : (Vec d × Parameters d n) →L[ℝ] ℝ) p ↔
      HasFDerivWithinAt L (0 : (Vec d × Parameters d n) →L[ℝ] ℝ)
        {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p)) ∧
    (IsLocalMin L p ↔ IsLocalMinOn L {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p)) ∧
    ((IsLocalMin L p ∧ ¬ IsMinOn L Set.univ p) ↔
      (IsLocalMinOn L {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p) ∧
        ¬ IsMinOn L {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p))) := by
  intro L
  have hnormal (q : Vec d × Parameters d n) : L (SkipNormalize q) = L q :=
    congrArg (G q.1) (funext fun x => normalized_feature_sum phi hzero hhom q.2 x)
  have hfun : L ∘ SkipNormalize = L := funext hnormal
  have hlocal := skip_raw_local_minimum_iff L hp
  have hcritical := skip_raw_stationarity_iff L hp
  rw [hfun] at hlocal hcritical
  have hglobal : IsMinOn L Set.univ p ↔
      IsMinOn L {q | ∀ i, ‖q.2.2 i‖ = 1} (SkipNormalize p) := by
    apply global_minimum_iff_of_value_completion L _ p _ (hnormal p).symm
    intro q
    exact ⟨(q.1, CompleteRaw p.2 q.2), complete_raw_unit hp q.2,
      congrArg (G q.1) (funext fun x => complete_raw_feature_sum phi hzero hhom p.2 q.2 x)⟩
  exact ⟨hcritical, hlocal, and_congr hlocal (not_congr hglobal)⟩

private theorem raw_feature_homogeneous (q : PaperLeanFormalization.Model)
    (r z : ℝ) (hr : 0 ≤ r) : Feature q (r * z) = r * Feature q z := by
  cases q with
  | centered => simp only [Feature, abs_mul, abs_of_nonneg hr]; ring
  | plainRelu =>
    rcases le_total 0 z with hz | hz
    · simp only [Feature, max_eq_right hz, max_eq_right (mul_nonneg hr hz)]
    · simp only [Feature, max_eq_left hz, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hr hz), mul_zero]

/-- `lem:raw-transfer`, proved from the local coordinate and feature calculations.
Spurious means local but not global, including all zero-row raw competitors. -/
theorem lem_raw_transfer {m : ℕ} (q : PaperLeanFormalization.Model)
    (o : Fin n → ℝ) (a : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (ha : ∀ i, a i ≠ 0) :
    (HasFDerivAt (fun p : Parameters d n => Loss q p.1 p.2 s v)
        (0 : Parameters d n →L[ℝ] ℝ) (o, a) ↔
      HasFDerivWithinAt (fun p : Parameters d n => Loss q p.1 p.2 s v)
        (0 : Parameters d n →L[ℝ] ℝ) {p | ∀ i, ‖p.2 i‖ = 1} (Normalize o a)) ∧
    (IsLocalMin (fun p : Parameters d n => Loss q p.1 p.2 s v) (o, a) ↔
      IsLocalMinOn (fun p : Parameters d n => Loss q p.1 p.2 s v)
        {p | ∀ i, ‖p.2 i‖ = 1} (Normalize o a)) ∧
    ((IsLocalMin (fun p : Parameters d n => Loss q p.1 p.2 s v) (o, a) ∧
        ¬ IsMinOn (fun p : Parameters d n => Loss q p.1 p.2 s v) Set.univ (o, a)) ↔
      (IsLocalMinOn (fun p : Parameters d n => Loss q p.1 p.2 s v)
          {p | ∀ i, ‖p.2 i‖ = 1} (Normalize o a) ∧
        ¬ IsMinOn (fun p : Parameters d n => Loss q p.1 p.2 s v)
          {p | ∀ i, ‖p.2 i‖ = 1} (Normalize o a))) := by
  have h := raw_feature_functional_transfer (Feature q) (by cases q <;> norm_num [Feature])
    (raw_feature_homogeneous q)
    (fun f : Vec d → ℝ => (1 / 2 : ℝ) * ∫ x : Vec d,
      (f x - Network q s v x)^2 * stdGaussianDensity x) (p := (o, a)) ha
  cases q <;> exact h

/-- The skip clause keeps the skip vector fixed under normalization, while
allowing it to vary freely in all local and global comparisons. -/
theorem lem_raw_transfer_skip {m : ℕ} (b : Vec d)
    (o : Fin n → ℝ) (a : Fin n → Vec d) (bStar : Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (ha : ∀ i, a i ≠ 0) :
    (HasFDerivAt (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bStar s v)
        (0 : (Vec d × Parameters d n) →L[ℝ] ℝ) (b, (o, a)) ↔
      HasFDerivWithinAt (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bStar s v)
        (0 : (Vec d × Parameters d n) →L[ℝ] ℝ)
        {p | ∀ i, ‖p.2.2 i‖ = 1} (b, Normalize o a)) ∧
    (IsLocalMin (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bStar s v) (b, (o, a)) ↔
      IsLocalMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bStar s v)
        {p | ∀ i, ‖p.2.2 i‖ = 1} (b, Normalize o a)) ∧
    ((IsLocalMin (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bStar s v) (b, (o, a)) ∧
        ¬ IsMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bStar s v)
          Set.univ (b, (o, a))) ↔
      (IsLocalMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bStar s v)
          {p | ∀ i, ‖p.2.2 i‖ = 1} (b, Normalize o a) ∧
        ¬ IsMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bStar s v)
          {p | ∀ i, ‖p.2.2 i‖ = 1} (b, Normalize o a))) := by
  exact skip_feature_functional_transfer (Feature .plainRelu) (by norm_num [Feature])
    (raw_feature_homogeneous .plainRelu)
    (fun b f => (1 / 2 : ℝ) * ∫ x : Vec d,
      (inner b x + f x - (inner bStar x + Network .plainRelu s v x))^2 * stdGaussianDensity x)
    (p := (b, (o, a))) ha





/-- Updating one raw output changes exactly one normalized mass. -/
theorem normalize_output_update (o : Fin n → ℝ) (a : Fin n → Vec d)
    (i : Fin n) (t : ℝ) :
    Normalize (Function.update o i t) a =
      (Function.update (Normalize o a).1 i (t * ‖a i‖), (Normalize o a).2) := by
  apply Prod.ext
  · funext j
    by_cases hj : j = i <;> simp [Normalize, Function.update, hj]
  · rfl

/-- Updating one raw row changes its mass and direction, and no other coordinates. -/
theorem normalize_direction_update (o : Fin n → ℝ) (a : Fin n → Vec d)
    (i : Fin n) (z : Vec d) :
    Normalize o (Function.update a i z) =
      (Function.update (Normalize o a).1 i (o i * ‖z‖),
        Function.update (Normalize o a).2 i (‖z‖⁻¹ • z)) := by
  apply Prod.ext
  · funext j
    by_cases hj : j = i <;> simp [Normalize, Function.update, hj]
  · funext j
    by_cases hj : j = i <;> simp [Normalize, Function.update, hj]

/-- Concrete consumer of `eq:raw-chain-rule` for the manuscript's literal q-loss.
The input is its mass/direction differential with all other neurons fixed;
the output contains actual derivatives of the raw-coordinate composition. -/
theorem eq_raw_chain_rule_loss_row {m : ℕ} (q : PaperLeanFormalization.Model)
    (o : Fin n → ℝ) (a : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (i : Fin n) (alpha : ℝ) (g : Vec d) (hai : a i ≠ 0)
    (hrow : HasFDerivAt
      (fun z : ℝ × Vec d => Loss q (Function.update (Normalize o a).1 i z.1)
        (Function.update (Normalize o a).2 i z.2) s v)
      (RowDifferential alpha g) (o i * ‖a i‖, ‖a i‖⁻¹ • a i)) :
    HasDerivAt (fun t : ℝ => Loss q (Normalize (Function.update o i t) a).1
        (Normalize (Function.update o i t) a).2 s v) (‖a i‖ * alpha) (o i) ∧
    HasFDerivAt (fun z : Vec d => Loss q (Normalize o (Function.update a i z)).1
        (Normalize o (Function.update a i z)).2 s v)
      (innerSL ℝ ((o i * alpha) • (‖a i‖⁻¹ • a i) +
        ‖a i‖⁻¹ • (g - (inner (‖a i‖⁻¹ • a i) g : ℝ) • (‖a i‖⁻¹ • a i)))) (a i) := by
  have h := eq_raw_chain_rule
    (fun z : ℝ × Vec d => Loss q (Function.update (Normalize o a).1 i z.1)
      (Function.update (Normalize o a).2 i z.2) s v) (o i) alpha (a i) g hai hrow
  constructor
  · convert h.1 using 1
    funext t
    rw [normalize_output_update]
    have hw : Function.update (Normalize o a).2 i (‖a i‖⁻¹ • a i) = (Normalize o a).2 :=
      Function.update_eq_self i (Normalize o a).2
    simp only [hw]
  · convert h.2 using 1
    funext z
    rw [normalize_direction_update]

variable {m : ℕ}

/-- The finite kernel expression is differentiable before imposing unit constraints. -/
theorem kernelEnergy_differentiable (q : Model) (s : Fin m → ℝ)
    (v : Fin m → Vec d) :
    Differentiable ℝ (fun p : Parameters d n => KernelEnergy q p.1 p.2 s v) := by
  intro p
  have hc (i : Fin n) : DifferentiableAt ℝ (fun z : Parameters d n => z.1 i) p :=
    ((contDiff_apply ℝ ℝ i).comp contDiff_fst).differentiable le_top p
  have hw (i : Fin n) : DifferentiableAt ℝ (fun z : Parameters d n => z.2 i) p :=
    ((contDiff_apply ℝ (Vec d) i).comp contDiff_snd).differentiable le_top p
  unfold KernelEnergy
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.add _ (differentiableAt_const _)
  apply DifferentiableAt.sub
  · apply DifferentiableAt.sum
    intro i _hi
    apply DifferentiableAt.sum
    intro j _hj
    exact ((hc i).mul (hc j)).mul
      ((hasDerivAt_Kernel q _).differentiableAt.comp p ((hw i).inner ℝ (hw j)))
  · apply DifferentiableAt.const_mul
    apply DifferentiableAt.sum
    intro i _hi
    apply DifferentiableAt.sum
    intro k _hk
    exact ((hc i).mul_const (s k)).mul
      ((hasDerivAt_Kernel q _).differentiableAt.comp p
        ((hw i).inner ℝ (differentiableAt_const _)))

/-- Positive homogeneity proves loss normalization even at zero incoming rows. -/
theorem loss_normalization_fresh (q : Model) (p : Parameters d n)
    (s : Fin m → ℝ) (v : Fin m → Vec d) :
    Loss q (Normalize p.1 p.2).1 (Normalize p.1 p.2).2 s v = Loss q p.1 p.2 s v := by
  have hnet := raw_network_eq_normalized q p.1 p.2
  rw [eq_q_losses, eq_q_losses]
  congr 1
  apply integral_congr_ae
  exact eventually_of_forall fun x => by
    dsimp only
    rw [← hnet]
    rfl

/-- The literal Gaussian loss is differentiable on the open nonzero-row locus.
The equality to the smooth finite formula is used only in this neighborhood. -/
theorem loss_differentiableAt_nonzero (hd : 2 ≤ d) (q : Model)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (hv : ∀ k, ‖v k‖ = 1)
    {p : Parameters d n} (hp : ∀ i, p.2 i ≠ 0) :
    DifferentiableAt ℝ (fun z : Parameters d n => Loss q z.1 z.2 s v) p := by
  have hk := (kernelEnergy_differentiable (n := n) q s v (Normalize p.1 p.2)).comp p
    ((normalize_smooth hp).differentiableAt le_top)
  apply hk.congr_of_eventuallyEq
  filter_upwards [nonzero_rows_open.mem_nhds hp] with z hz
  exact (loss_normalization_fresh q z s v).symm.trans
    (loss_eq_kernelEnergy hd q _ _ s v (normalize_has_unit_rows hz) hv)

/-- Every linear differential in one scalar and one Euclidean row has the
manuscript's mass-gradient plus inner-product representation. -/
theorem row_differential_representation (D : (ℝ × Vec d) →L[ℝ] ℝ) :
    ∃ alpha : ℝ, ∃ g : Vec d, RowDifferential alpha g = D := by
  let R : Vec d →L[ℝ] ℝ := D.comp
    ((0 : Vec d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec d)))
  refine ⟨D (1, 0), (InnerProductSpace.toDual ℝ (Vec d)).symm R, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  rw [row_differential_apply, InnerProductSpace.toDual_symm_apply]
  change D (1, 0) * z.1 + D (0, z.2) = D z
  have hscalar : D (z.1, (0 : Vec d)) = z.1 * D (1, 0) := by
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using
      D.map_smul z.1 (1, (0 : Vec d))
  rw [mul_comm, ← hscalar, ← D.map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]

/-- The row differential in `eq:raw-chain-rule` is supplied by the literal
loss itself; it is not an additional regularity hypothesis. -/
theorem loss_row_hasFDerivAt (hd : 2 ≤ d) (q : Model)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ j, w j ≠ 0) (hv : ∀ k, ‖v k‖ = 1) (i : Fin n) :
    ∃ alpha : ℝ, ∃ g : Vec d,
      HasFDerivAt (fun z : ℝ × Vec d =>
        Loss q (Function.update c i z.1) (Function.update w i z.2) s v)
        (RowDifferential alpha g) (c i, w i) := by
  have hup : DifferentiableAt ℝ (fun z : ℝ × Vec d =>
      (Function.update c i z.1, Function.update w i z.2)) (c i, w i) :=
    (((hasFDerivAt_update (𝕜 := ℝ) (i := i) c (c i)).comp (c i, w i)
      hasFDerivAt_fst).prod
      ((hasFDerivAt_update (𝕜 := ℝ) (i := i) w (w i)).comp (c i, w i)
        hasFDerivAt_snd)).differentiableAt
  have hbase := loss_differentiableAt_nonzero hd q s v hv (p := (c, w)) hw
  have hbase' : DifferentiableAt ℝ (fun z : Parameters d n => Loss q z.1 z.2 s v)
      (Function.update c i (c i), Function.update w i (w i)) := by
    simpa only [Function.update_eq_self] using hbase
  have hcomp := hbase'.comp (c i, w i) hup
  obtain ⟨alpha, g, hg⟩ := row_differential_representation
    (fderiv ℝ (fun z : ℝ × Vec d =>
      Loss q (Function.update c i z.1) (Function.update w i z.2) s v) (c i, w i))
  refine ⟨alpha, g, ?_⟩
  rw [hg]
  simpa only [Function.update_eq_self] using hcomp.hasFDerivAt

/-- For each raw neuron both displayed derivatives exist, with no assumed
row-differential witness. -/
theorem raw_loss_row_chain_rule (hd : 2 ≤ d) (q : Model)
    (o : Fin n → ℝ) (a : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (ha : ∀ i, a i ≠ 0) (hv : ∀ k, ‖v k‖ = 1) (i : Fin n) :
    ∃ alpha : ℝ, ∃ g : Vec d,
      HasDerivAt (fun t : ℝ => Loss q (Function.update o i t) a s v)
        (‖a i‖ * alpha) (o i) ∧
      HasFDerivAt (fun z : Vec d => Loss q o (Function.update a i z) s v)
        (innerSL ℝ ((o i * alpha) • (‖a i‖⁻¹ • a i) +
          ‖a i‖⁻¹ • (g - (inner (‖a i‖⁻¹ • a i) g : ℝ) • (‖a i‖⁻¹ • a i)))) (a i) := by
  have hn : ∀ j, (Normalize o a).2 j ≠ 0 := by
    intro j h
    have hu := normalize_has_unit_rows (p := (o, a)) ha j
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨alpha, g, hrow⟩ := loss_row_hasFDerivAt hd q (Normalize o a).1
    (Normalize o a).2 s v hn hv i
  have h := eq_raw_chain_rule_loss_row q o a s v i alpha g (ha i) hrow
  refine ⟨alpha, g, ?_, ?_⟩
  · exact h.1.congr_of_eventuallyEq (eventually_of_forall fun t =>
      (loss_normalization_fresh q (Function.update o i t, a) s v).symm)
  · exact h.2.congr_of_eventuallyEq (eventually_of_forall fun z =>
      (loss_normalization_fresh q (o, Function.update a i z) s v).symm)

end RawTransferAdditions

end PaperLeanFormalization.Preliminaries
