import Definitions
import Preliminaries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Learned skip: even/odd splitting and the quadratic shear

This file proves `eq:loss-connection` directly from the pointwise ReLU identity,
Gaussian parity, and covariance. The same local identity is then used for all
three transport clauses. The matching section is a finite bilinear polynomial;
the critical-point clause therefore follows by the chain rule through its
shear and inverse, without a differentiability assumption on the reduced loss.
-/

noncomputable section
open Real Set MeasureTheory
open scoped BigOperators Topology RealInnerProductSpace

namespace PaperLeanFormalization.Skip

open Filter

section QuadraticProduct

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Z]

private theorem quadratic_product_section (u : E) (T : Set Z) (z : Z) :
    Tendsto (fun y : Z => (u, y)) (𝓝[T] z) (𝓝[Prod.snd ⁻¹' T] (u, z)) := by
  exact tendsto_nhdsWithin_iff.mpr
    ⟨(continuous_const.prod_mk continuous_id).continuousAt.mono_left nhdsWithin_le_nhds,
      self_mem_nhdsWithin⟩

private theorem quadratic_product_projection (u : E) (T : Set Z) (z : Z) :
    Tendsto (Prod.snd : E × Z → Z) (𝓝[Prod.snd ⁻¹' T] (u, z)) (𝓝[T] z) := by
  exact tendsto_nhdsWithin_iff.mpr
    ⟨continuous_snd.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩

/-- Along a free radial variation, the entire objective is a scalar quadratic. -/
private theorem quadratic_product_radial_derivative
    (f : Z → ℝ) (κ : ℝ) (u : E) (z : Z) :
    HasDerivAt (fun t : ℝ => f z + κ * ‖t • u‖ ^ 2) (2 * κ * ‖u‖ ^ 2) 1 := by
  have h := (((hasDerivAt_pow 2 (1 : ℝ)).mul_const (‖u‖ ^ 2)).const_mul κ).const_add (f z)
  convert h using 1
  · funext t
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  · norm_num
    ring

/-- A local minimum cannot have a nonzero free quadratic coordinate. -/
theorem quadratic_product_center_of_local_min
    (f : Z → ℝ) {κ : ℝ} (hκ : 0 < κ) {T : Set Z} {u : E} {z : Z}
    (hz : z ∈ T)
    (h : IsLocalMinOn (fun q : E × Z => f q.2 + κ * ‖q.1‖ ^ 2)
      (Prod.snd ⁻¹' T) (u, z)) : u = 0 := by
  have hpath : Tendsto (fun t : ℝ => (t • u, z)) (𝓝 (1 : ℝ))
      (𝓝[Prod.snd ⁻¹' T] (u, z)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_of_forall (fun _ => hz)⟩
    have hc : Continuous (fun t : ℝ => (t • u, z)) :=
      (continuous_id.smul continuous_const).prod_mk continuous_const
    simpa only [one_smul] using
      (hc.continuousAt (x := (1 : ℝ))).tendsto
  have hmin : IsLocalMin (fun t : ℝ => f z + κ * ‖t • u‖ ^ 2) 1 := by
    change ∀ᶠ t in 𝓝 (1 : ℝ), f z + κ * ‖(1 : ℝ) • u‖ ^ 2 ≤ f z + κ * ‖t • u‖ ^ 2
    simpa only [one_smul] using hpath.eventually h
  have hzero := hmin.hasDerivAt_eq_zero (quadratic_product_radial_derivative f κ u z)
  have hn : ‖u‖ ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left (mul_pos (by norm_num) hκ).ne'
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

/-- Product neighborhoods separate the free, positive quadratic coordinate
from the arbitrary constrained objective. No continuity of the latter is needed. -/
theorem quadratic_product_local_min_iff
    (f : Z → ℝ) {κ : ℝ} (hκ : 0 < κ) {T : Set Z} {u : E} {z : Z} (hz : z ∈ T) :
    IsLocalMinOn (fun q : E × Z => f q.2 + κ * ‖q.1‖ ^ 2) (Prod.snd ⁻¹' T) (u, z) ↔
      u = 0 ∧ IsLocalMinOn f T z := by
  constructor
  · intro h
    have hu := quadratic_product_center_of_local_min f hκ hz h
    refine ⟨hu, ?_⟩
    have hpull := (quadratic_product_section u T z).eventually h
    simpa only [add_le_add_iff_right] using hpull
  · rintro ⟨rfl, h⟩
    have hpull := (quadratic_product_projection (0 : E) T z).eventually h
    filter_upwards [hpull] with q hq
    simpa only [norm_zero, zero_pow (by norm_num : (0 : ℕ) < 2), mul_zero, add_zero] using
      hq.trans (le_add_of_nonneg_right (mul_nonneg hκ.le (sq_nonneg ‖q.1‖)))

/-- Strictness has exactly the same product reduction.  The explicit eventual
form avoids introducing another hidden local-minimum predicate. -/
theorem quadratic_product_strict_local_min_iff
    (f : Z → ℝ) {κ : ℝ} (hκ : 0 < κ) {T : Set Z} {u : E} {z : Z} (hz : z ∈ T) :
    (∀ᶠ q : E × Z in 𝓝[Prod.snd ⁻¹' T] (u, z), q ≠ (u, z) →
      f z + κ * ‖u‖ ^ 2 < f q.2 + κ * ‖q.1‖ ^ 2) ↔
      u = 0 ∧ (∀ᶠ y in 𝓝[T] z, y ≠ z → f z < f y) := by
  constructor
  · intro h
    have hmin : IsLocalMinOn (fun q : E × Z => f q.2 + κ * ‖q.1‖ ^ 2)
        (Prod.snd ⁻¹' T) (u, z) := by
      filter_upwards [h] with q hq
      by_cases heq : q = (u, z)
      · simp only [heq, le_refl]
      · exact (hq heq).le
    have hu := quadratic_product_center_of_local_min f hκ hz hmin
    refine ⟨hu, ?_⟩
    have hpull := (quadratic_product_section u T z).eventually h
    filter_upwards [hpull] with y hy hyne
    have hne : (u, y) ≠ (u, z) := fun heq => hyne (congrArg Prod.snd heq)
    exact (add_lt_add_iff_right _).mp (hy hne)
  · rintro ⟨rfl, h⟩
    have hpull := (quadratic_product_projection (0 : E) T z).eventually h
    filter_upwards [hpull] with q hq hne
    simp only [norm_zero, zero_pow (by norm_num : (0 : ℕ) < 2), mul_zero, add_zero]
    by_cases heq : q.2 = z
    · have hu : q.1 ≠ 0 := fun hu => hne (Prod.ext hu heq)
      rw [heq]
      exact lt_add_of_pos_right _ (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hu)))
    · exact (hq heq).trans_le (le_add_of_nonneg_right (mul_nonneg hκ.le (sq_nonneg ‖q.1‖)))

end QuadraticProduct

section QuadraticProductCritical

variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- First-order stationarity obeys the same product reduction.  The objective
on the constrained factor need not be differentiable away from this point. -/
theorem quadratic_product_critical_iff
    (f : Z → ℝ) {κ : ℝ} (hκ : 0 < κ) {T : Set Z} {u : E} {z : Z} (hz : z ∈ T) :
    HasFDerivWithinAt (fun q : E × Z => f q.2 + κ * ‖q.1‖ ^ 2)
      (0 : (E × Z) →L[ℝ] ℝ) (Prod.snd ⁻¹' T) (u, z) ↔
      u = 0 ∧ HasFDerivWithinAt f (0 : Z →L[ℝ] ℝ) T z := by
  constructor
  · intro h
    have hfree : HasFDerivAt (fun x : E => (x, z))
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] Z)) u :=
      (hasFDerivAt_id (𝕜 := ℝ) u).prod (hasFDerivAt_const z u)
    have hfree_comp := h.comp u (hfree.hasFDerivWithinAt (s := Set.univ))
      (show MapsTo (fun x : E => (x, z)) Set.univ (Prod.snd ⁻¹' T) from fun _ _ => hz)
    have hzero : HasFDerivAt (fun x : E => f z + κ * ‖x‖ ^ 2)
        (0 : E →L[ℝ] ℝ) u := by
      simpa only [Function.comp_apply, ContinuousLinearMap.zero_comp, hasFDerivWithinAt_univ] using
        hfree_comp
    have hexplicit := (((hasStrictFDerivAt_norm_sq u).hasFDerivAt).const_mul κ).const_add (f z)
    have heq := hexplicit.unique hzero
    have hval := congrArg (fun L : E →L[ℝ] ℝ => L u) heq
    have hn : ‖u‖ ^ 2 = 0 := by
      simp only [two_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply,
        innerSL_apply, real_inner_self_eq_norm_sq] at hval
      nlinarith only [hval, hκ, sq_nonneg ‖u‖]
    have hu : u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    refine ⟨hu, ?_⟩
    have hsection : HasFDerivAt (fun y : Z => (u, y))
        ((0 : Z →L[ℝ] E).prod (ContinuousLinearMap.id ℝ Z)) z :=
      (hasFDerivAt_const u z).prod (hasFDerivAt_id z)
    have hcomp := h.comp z (hsection.hasFDerivWithinAt (s := T))
      (show MapsTo (fun y : Z => (u, y)) T (Prod.snd ⁻¹' T) from fun _ hy => hy)
    convert hcomp using 1
    funext y
    simp [hu]
  · rintro ⟨rfl, h⟩
    have hproj := h.comp ((0 : E), z) (hasFDerivAt_snd.hasFDerivWithinAt)
      (show MapsTo (Prod.snd : E × Z → Z) (Prod.snd ⁻¹' T) T from fun _ hy => hy)
    have hnorm0 : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (0 : E →L[ℝ] ℝ) 0 := by
      simpa only [map_zero, smul_zero] using (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    have hnorm := hnorm0.comp ((0 : E), z) hasFDerivAt_fst
    rw [ContinuousLinearMap.zero_comp] at hnorm hproj
    have hpenalty := (hnorm.const_mul κ).hasFDerivWithinAt (s := Prod.snd ⁻¹' T)
    simpa only [Function.comp_apply, smul_zero, add_zero] using hproj.add hpenalty

end QuadraticProductCritical

section QuadraticShear

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem quadratic_shear_add_tendsto
    (M : Z → E) (hM : Continuous M) (T : Set Z) (u : E) (z : Z) :
    Tendsto (fun q : E × Z => (q.1 + M q.2, q.2)) (𝓝[Prod.snd ⁻¹' T] (u, z))
      (𝓝[Prod.snd ⁻¹' T] (u + M z, z)) := by
  exact tendsto_nhdsWithin_iff.mpr
    ⟨((continuous_fst.add (hM.comp continuous_snd)).prod_mk continuous_snd).continuousAt.mono_left
      nhdsWithin_le_nhds, self_mem_nhdsWithin⟩

private theorem quadratic_shear_sub_tendsto
    (M : Z → E) (hM : Continuous M) (T : Set Z) (b : E) (z : Z) :
    Tendsto (fun q : E × Z => (q.1 - M q.2, q.2)) (𝓝[Prod.snd ⁻¹' T] (b, z))
      (𝓝[Prod.snd ⁻¹' T] (b - M z, z)) := by
  exact tendsto_nhdsWithin_iff.mpr
    ⟨((continuous_fst.sub (hM.comp continuous_snd)).prod_mk continuous_snd).continuousAt.mono_left
      nhdsWithin_le_nhds, self_mem_nhdsWithin⟩

/-- A continuous shear transports ordinary constrained local minima through
the product theorem. These two explicit inverse maps preserve the cylinder. -/
theorem quadratic_shear_local_min_iff
    (f : Z → ℝ) (M : Z → E) (hM : Continuous M)
    {κ : ℝ} (hκ : 0 < κ) {T : Set Z} {b : E} {z : Z} (hz : z ∈ T) :
    IsLocalMinOn (fun q : E × Z => f q.2 + κ * ‖q.1 - M q.2‖ ^ 2)
      (Prod.snd ⁻¹' T) (b, z) ↔
      b = M z ∧ IsLocalMinOn f T z := by
  constructor
  · intro h
    have ht := quadratic_shear_add_tendsto M hM T (b - M z) z
    simp only [sub_add_cancel] at ht
    have hp : IsLocalMinOn (fun q : E × Z => f q.2 + κ * ‖q.1‖ ^ 2)
        (Prod.snd ⁻¹' T) (b - M z, z) := by
      show ∀ᶠ q in 𝓝[Prod.snd ⁻¹' T] (b - M z, z),
        f z + κ * ‖b - M z‖ ^ 2 ≤ f q.2 + κ * ‖q.1‖ ^ 2
      simpa only [add_sub_cancel] using ht.eventually h
    obtain ⟨hc, hf⟩ := (quadratic_product_local_min_iff f hκ hz).mp hp
    exact ⟨sub_eq_zero.mp hc, hf⟩
  · rintro ⟨hc, hf⟩
    have hp := (quadratic_product_local_min_iff f hκ hz).mpr
      (show b - M z = 0 ∧ IsLocalMinOn f T z from ⟨sub_eq_zero.mpr hc, hf⟩)
    exact (quadratic_shear_sub_tendsto M hM T b z).eventually hp

/-- Strict transport uses injectivity of each explicit shear map. -/
theorem quadratic_shear_strict_local_min_iff
    (f : Z → ℝ) (M : Z → E) (hM : Continuous M)
    {κ : ℝ} (hκ : 0 < κ) {T : Set Z} {b : E} {z : Z} (hz : z ∈ T) :
    (∀ᶠ q : E × Z in 𝓝[Prod.snd ⁻¹' T] (b, z), q ≠ (b, z) →
      f z + κ * ‖b - M z‖ ^ 2 < f q.2 + κ * ‖q.1 - M q.2‖ ^ 2) ↔
      b = M z ∧ (∀ᶠ y in 𝓝[T] z, y ≠ z → f z < f y) := by
  constructor
  · intro h
    have ht := quadratic_shear_add_tendsto M hM T (b - M z) z
    simp only [sub_add_cancel] at ht
    have hp : ∀ᶠ q : E × Z in 𝓝[Prod.snd ⁻¹' T] (b - M z, z), q ≠ (b - M z, z) →
        f z + κ * ‖b - M z‖ ^ 2 < f q.2 + κ * ‖q.1‖ ^ 2 := by
      filter_upwards [ht.eventually h] with q hq hne
      have hneq : (q.1 + M q.2, q.2) ≠ (b, z) := by
        intro heq
        have h2 : q.2 = z := congrArg Prod.snd heq
        have h1 : q.1 + M q.2 = b := congrArg Prod.fst heq
        exact hne (Prod.ext (by simpa only [h2] using (eq_sub_iff_add_eq.mpr h1)) h2)
      simpa only [add_sub_cancel] using hq hneq
    obtain ⟨hc, hf⟩ := (quadratic_product_strict_local_min_iff f hκ hz).mp hp
    exact ⟨sub_eq_zero.mp hc, hf⟩
  · rintro ⟨hc, hf⟩
    have hp := (quadratic_product_strict_local_min_iff f hκ hz).mpr
      (show b - M z = 0 ∧ (∀ᶠ y in 𝓝[T] z, y ≠ z → f z < f y) from
        ⟨sub_eq_zero.mpr hc, hf⟩)
    filter_upwards [(quadratic_shear_sub_tendsto M hM T b z).eventually hp] with q hq hne
    apply hq
    intro heq
    have h2 : q.2 = z := congrArg Prod.snd heq
    have h1 : q.1 - M q.2 = b - M z := congrArg Prod.fst heq
    apply hne
    refine Prod.ext ?_ h2
    have hd : q.1 - M z = b - M z := by simpa only [h2] using h1
    simpa only [sub_add_cancel] using congrArg (fun x : E => x + M z) hd

end QuadraticShear

section QuadraticShearCritical

variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The critical-point transport is just the chain rule through a differentiable
shear and its differentiable inverse. No Lipschitz remainder estimate is needed. -/
theorem quadratic_shear_critical_iff
    (f : Z → ℝ) (M : Z → E) (hM : Differentiable ℝ M)
    {κ : ℝ} (hκ : 0 < κ) {T : Set Z} {b : E} {z : Z} (hz : z ∈ T) :
    HasFDerivWithinAt (fun q : E × Z => f q.2 + κ * ‖q.1 - M q.2‖ ^ 2)
      (0 : (E × Z) →L[ℝ] ℝ) (Prod.snd ⁻¹' T) (b, z) ↔
      b = M z ∧ HasFDerivWithinAt f (0 : Z →L[ℝ] ℝ) T z := by
  have hplus : Differentiable ℝ (fun q : E × Z => (q.1 + M q.2, q.2)) :=
    (differentiable_fst.add (hM.comp differentiable_snd)).prod differentiable_snd
  have hminus : Differentiable ℝ (fun q : E × Z => (q.1 - M q.2, q.2)) :=
    (differentiable_fst.sub (hM.comp differentiable_snd)).prod differentiable_snd
  constructor
  · intro h
    have hbase : HasFDerivWithinAt (fun q : E × Z => f q.2 + κ * ‖q.1 - M q.2‖ ^ 2)
        (0 : (E × Z) →L[ℝ] ℝ) (Prod.snd ⁻¹' T) ((b - M z) + M z, z) := by
      simpa only [sub_add_cancel] using h
    have hcomp := hbase.comp (b - M z, z)
      (hplus (b - M z, z)).hasFDerivAt.hasFDerivWithinAt
      (show MapsTo (fun q : E × Z => (q.1 + M q.2, q.2))
        (Prod.snd ⁻¹' T) (Prod.snd ⁻¹' T) from fun _ hq => hq)
    have hp : HasFDerivWithinAt (fun q : E × Z => f q.2 + κ * ‖q.1‖ ^ 2)
        (0 : (E × Z) →L[ℝ] ℝ) (Prod.snd ⁻¹' T) (b - M z, z) := by
      simpa only [Function.comp_def, add_sub_cancel, ContinuousLinearMap.zero_comp] using hcomp
    obtain ⟨hc, hf⟩ := (quadratic_product_critical_iff f hκ hz).mp hp
    exact ⟨sub_eq_zero.mp hc, hf⟩
  · rintro ⟨hc, hf⟩
    have hp := (quadratic_product_critical_iff f hκ hz).mpr
      (show b - M z = 0 ∧ HasFDerivWithinAt f (0 : Z →L[ℝ] ℝ) T z from
        ⟨sub_eq_zero.mpr hc, hf⟩)
    have hcomp := hp.comp (b, z) (hminus (b, z)).hasFDerivAt.hasFDerivWithinAt
      (show MapsTo (fun q : E × Z => (q.1 - M q.2, q.2))
        (Prod.snd ⁻¹' T) (Prod.snd ⁻¹' T) from fun _ hq => hq)
    simpa only [Function.comp_def, ContinuousLinearMap.zero_comp] using hcomp

end QuadraticShearCritical

open PaperLeanFormalization.Definitions

variable {d n m : ℕ}

theorem finite_square_integrable {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) (f : I → X → ℝ) (ρ : X → ℝ)
    (hi : ∀ i j, Integrable (fun x ↦ f i x * f j x * ρ x) μ) :
    Integrable (fun x ↦ (∑ i, f i x) ^ 2 * ρ x) μ := by
  have h := integrable_finset_sum Finset.univ
    (fun i _ ↦ integrable_finset_sum Finset.univ (fun j _ ↦ hi i j))
  convert h using 1
  funext x
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem centered_residual_square_integrable {d n m : ℕ} (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    Integrable (fun x : Vec d ↦
      ((∑ i, c i * (|inner (w i) x| / 2)) -
        ∑ k, s k * (|inner (v k) x| / 2)) ^ 2 * stdGaussianDensity x) := by
  let a : Fin n ⊕ Fin m → ℝ := Sum.elim c (fun k ↦ -s k)
  let z : Fin n ⊕ Fin m → Vec d := Sum.elim w v
  have hpair (i j : Fin n ⊕ Fin m) : Integrable (fun x : Vec d ↦
      (a i * (|inner (z i) x| / 2)) * (a j * (|inner (z j) x| / 2)) *
        stdGaussianDensity x) := by
    convert (Preliminaries.centered_feature_pair_integrable hd (z i) (z j)).const_mul
      (a i * a j) using 1
    funext x
    ring
  have h := finite_square_integrable volume
    (fun i x ↦ a i * (|inner (z i) x| / 2)) stdGaussianDensity hpair
  simpa only [a, z, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg] using h

theorem linear_centered_residual_integrable {d n m : ℕ} (hd : 2 ≤ d)
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) :
    Integrable (fun x : Vec d ↦ inner b x *
      ((∑ i, c i * (|inner (w i) x| / 2)) -
        ∑ k, s k * (|inner (v k) x| / 2)) * stdGaussianDensity x) := by
  have hpair (u : Vec d) : Integrable (fun x : Vec d ↦
      inner b x * (|inner u x| / 2) * stdGaussianDensity x) := by
    apply Preliminaries.gaussian_pair_integrable_of_abs_bound hd id (fun t ↦ |t| / 2)
      continuous_id (continuous_abs.div_const 2) (fun _ ↦ le_rfl)
    intro t
    rw [abs_div, abs_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [abs_nonneg t]
  have hsum {N : ℕ} (a : Fin N → ℝ) (z : Fin N → Vec d) : Integrable (fun x : Vec d ↦
      inner b x * (∑ i, a i * (|inner (z i) x| / 2)) * stdGaussianDensity x) := by
    have h := integrable_finset_sum Finset.univ (fun i _ ↦ (hpair (z i)).const_mul (a i))
    convert h using 1
    funext x
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  convert (hsum c w).sub (hsum s v) using 1
  funext x
  simp only [Pi.sub_apply]
  ring

/-- The pointwise even/odd decomposition of the ReLU feature. -/
theorem relu_even_odd (t : ℝ) : max 0 t = |t| / 2 + t / 2 := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_right ht, abs_of_nonneg ht]
    ring
  · rw [max_eq_left ht, abs_of_nonpos ht]
    ring

/-- A finite ReLU network splits into a centered network and its first moment. -/
theorem network_even_odd
    (c : Fin n → ℝ) (w : Fin n → Vec d) (x : Vec d) :
    (∑ i, c i * max 0 ⟪w i, x⟫_ℝ) =
      (∑ i, c i * (|⟪w i, x⟫_ℝ| / 2)) +
        (1 / 2 : ℝ) * ⟪∑ i, c i • w i, x⟫_ℝ := by
  calc
    _ = ∑ i, (c i * (|⟪w i, x⟫_ℝ| / 2) +
        (1 / 2 : ℝ) * (c i * ⟪w i, x⟫_ℝ)) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [relu_even_odd]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_inner]
      simp_rw [real_inner_smul_left]
      rw [Finset.mul_sum]


/-- `eq:skip-centered-split`: a skip network is its even centered network
plus the linear map determined by the skip and the finite first moment. -/
theorem eq_skip_centered_split
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d) (x : Vec d) :
    ⟪b, x⟫_ℝ + (∑ i, c i * max 0 ⟪w i, x⟫_ℝ) =
      ⟪b + (1 / 2 : ℝ) • ∑ i, c i • w i, x⟫_ℝ +
        ∑ i, c i * (|⟪w i, x⟫_ℝ| / 2) := by
  rw [network_even_odd]
  simp only [inner_add_left, real_inner_smul_left]
  ring

/-- `eq:losses`: the literal Gaussian square of the two skip-network outputs.
This display is unfolded in the actual even/odd integration proof below. -/
theorem eq_losses
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    SkipLoss b c w bStar s v =
      (1 / 2 : ℝ) * ∫ x : Vec d,
        ((⟪b, x⟫_ℝ + Network .plainRelu c w x) -
          (⟪bStar, x⟫_ℝ + Network .plainRelu s v x)) ^ 2 * stdGaussianDensity x := rfl

/-- The skip mismatch is exactly the odd component of the network residual. -/
theorem residual_even_odd
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) (x : Vec d) :
    ⟪b, x⟫_ℝ + (∑ i, c i * max 0 ⟪w i, x⟫_ℝ) -
      (⟪bStar, x⟫_ℝ + ∑ k, s k * max 0 ⟪v k, x⟫_ℝ) =
    ((∑ i, c i * (|⟪w i, x⟫_ℝ| / 2)) -
      ∑ k, s k * (|⟪v k, x⟫_ℝ| / 2)) +
      ⟪b - MatchingSkip bStar s v c w, x⟫_ℝ := by
  rw [eq_skip_centered_split b c w x, eq_skip_centered_split bStar s v x]
  unfold MatchingSkip
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  ring

/-- Even residuals have zero Gaussian cross moment with every linear function. -/
theorem centered_odd_cross_moment_zero
    (a : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) :
    (∫ x : Vec d, ⟪a, x⟫_ℝ *
      ((∑ i, c i * (|⟪w i, x⟫_ℝ| / 2)) -
        ∑ k, s k * (|⟪v k, x⟫_ℝ| / 2)) * stdGaussianDensity x) = 0 := by
  let f : Vec d → ℝ := fun x ↦ ⟪a, x⟫_ℝ *
    ((∑ i, c i * (|⟪w i, x⟫_ℝ| / 2)) -
      ∑ k, s k * (|⟪v k, x⟫_ℝ| / 2)) * stdGaussianDensity x
  have hchange := integral_neg_eq_self f volume
  have hodd : (fun x ↦ f (-x)) = fun x ↦ -f x := by
    funext x
    simp only [f, inner_neg_right, abs_neg, stdGaussianDensity, norm_neg]
    ring
  rw [hodd, integral_neg] at hchange
  change (∫ x, f x) = 0
  linarith only [hchange]

/-- `eq:skip-connection`: expand the square and integrate its
even, odd and cross terms. The only analytic inputs are integrability,
Gaussian parity, and the Gaussian second moment. -/
theorem eq_skip_connection
    (hd : 2 ≤ d)
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    SkipLoss b c w bStar s v = CenteredLoss c w s v +
      (1 / 2 : ℝ) * ‖b - MatchingSkip bStar s v c w‖ ^ 2 := by
  let a := b - MatchingSkip bStar s v c w
  let C := fun x : Vec d ↦
    (∑ i, c i * (|⟪w i, x⟫_ℝ| / 2)) - ∑ k, s k * (|⟪v k, x⟫_ℝ| / 2)
  have hC : Integrable (fun x : Vec d ↦ C x ^ 2 * stdGaussianDensity x) :=
    centered_residual_square_integrable hd c w s v
  have hcross : Integrable (fun x : Vec d ↦
      ⟪a, x⟫_ℝ * C x * stdGaussianDensity x) :=
    linear_centered_residual_integrable hd a c w s v
  have hlinear : Integrable (fun x : Vec d ↦
      ⟪a, x⟫_ℝ * ⟪a, x⟫_ℝ * stdGaussianDensity x) :=
    Preliminaries.gaussian_square_integrable hd a
  have hcrossZero : (∫ x : Vec d,
      ⟪a, x⟫_ℝ * C x * stdGaussianDensity x) = 0 :=
    centered_odd_cross_moment_zero a c w s v
  have hlinearValue : (∫ x : Vec d,
      ⟪a, x⟫_ℝ * ⟪a, x⟫_ℝ * stdGaussianDensity x) = ‖a‖ ^ 2 := by
    exact Preliminaries.gaussian_square_moment hd a
  rw [eq_losses]
  simp only [Network, Feature]
  unfold CenteredLoss
  simp_rw [residual_even_odd]
  change (1 / 2 : ℝ) * (∫ x : Vec d,
      (C x + ⟪a, x⟫_ℝ) ^ 2 * stdGaussianDensity x) =
    (1 / 2 : ℝ) * (∫ x : Vec d, C x ^ 2 * stdGaussianDensity x) +
      (1 / 2 : ℝ) * ‖a‖ ^ 2
  have hexpand : (fun x : Vec d ↦
      (C x + ⟪a, x⟫_ℝ) ^ 2 * stdGaussianDensity x) =
      (fun x : Vec d ↦ C x ^ 2 * stdGaussianDensity x +
        (2 * (⟪a, x⟫_ℝ * C x * stdGaussianDensity x) +
          ⟪a, x⟫_ℝ * ⟪a, x⟫_ℝ * stdGaussianDensity x)) := by
    funext x
    ring
  have hrest : Integrable (fun x : Vec d ↦
      2 * (⟪a, x⟫_ℝ * C x * stdGaussianDensity x) +
        ⟪a, x⟫_ℝ * ⟪a, x⟫_ℝ * stdGaussianDensity x) := by
    exact (hcross.const_mul 2).add hlinear
  rw [hexpand, integral_add hC hrest,
    integral_add (hcross.const_mul 2) hlinear, integral_mul_left,
    hcrossZero, hlinearValue]
  ring

/-- Setting both skips to zero recovers the plain loss literally. -/
theorem skip_zero_is_plain
    (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) :
    SkipLoss 0 c w 0 s v = PlainLoss c w s v := by
  simp only [SkipLoss, PlainLoss, inner_zero_left, zero_add]

/-- `eq:loss-connection`, with its factor `1/8` made explicit. -/
theorem eq_loss_connection
    (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) :
    PlainLoss c w s v = CenteredLoss c w s v +
      (1 / 8 : ℝ) * ‖(∑ i, c i • w i) - ∑ k, s k • v k‖ ^ 2 := by
  rw [← skip_zero_is_plain, eq_skip_connection hd]
  simp only [MatchingSkip, zero_add, zero_sub, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [norm_sub_rev (∑ k, s k • v k) (∑ i, c i • w i)]
  ring


/-- The two exact loss identities in `lem:equivalence_loss_skip_centered`.
The following transport clauses use this same quadratic decomposition. -/
theorem lem_equivalence_loss_skip_centered
    (hd : 2 ≤ d)
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    (SkipLoss b c w bStar s v = CenteredLoss c w s v +
      (1 / 2 : ℝ) * ‖b - MatchingSkip bStar s v c w‖ ^ 2) ∧
    (PlainLoss c w s v = CenteredLoss c w s v +
      (1 / 8 : ℝ) * ‖(∑ i, c i • w i) - ∑ k, s k • v k‖ ^ 2) :=
  ⟨eq_skip_connection hd b c w bStar s v, eq_loss_connection hd c w s v⟩

/-- The exact matching skip realizes the centered loss. -/
theorem loss_at_matching_skip
    (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d)
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    SkipLoss (MatchingSkip bStar s v c w) c w bStar s v = CenteredLoss c w s v := by
  rw [(lem_equivalence_loss_skip_centered hd (MatchingSkip bStar s v c w)
    c w bStar s v).1]
  simp

/-- Continuity of the matching section follows directly from its finite formula. -/
theorem matching_skip_continuous
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    Continuous (fun z : Parameters d n ↦ MatchingSkip bStar s v z.1 z.2) := by
  unfold MatchingSkip
  exact continuous_const.add (Continuous.const_smul
    (continuous_const.sub (continuous_finset_sum Finset.univ fun i _ ↦
      (((continuous_apply i).comp continuous_fst).smul
        ((continuous_apply i).comp continuous_snd)))) _)


theorem matching_skip_differentiable {d n m : ℕ}
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    Differentiable ℝ (fun z : Parameters d n ↦ MatchingSkip bStar s v z.1 z.2) := by
  intro z
  unfold MatchingSkip
  apply DifferentiableAt.add (differentiableAt_const bStar)
  apply DifferentiableAt.const_smul
  apply DifferentiableAt.sub (differentiableAt_const (∑ k, s k • v k))
  apply DifferentiableAt.sum
  intro i _
  have hmass : DifferentiableAt ℝ (fun z : Parameters d n ↦ z.1 i) z :=
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).differentiableAt.comp z
      differentiableAt_fst
  have hdir : DifferentiableAt ℝ (fun z : Parameters d n ↦ z.2 i) z :=
    (ContinuousLinearMap.proj i : (Fin n → Vec d) →L[ℝ] Vec d).differentiableAt.comp z
      differentiableAt_snd
  exact hmass.smul hdir


/-- Ordinary local-minimum transport on the signed-mass, unit-sphere cylinder. -/
theorem skip_local_minimum_iff
    (hd : 2 ≤ d)
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) :
    IsLocalMinOn (fun p : Vec d × Parameters d n ↦ SkipLoss p.1 p.2.1 p.2.2 bStar s v)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (b, (c, w)) ↔
      b = MatchingSkip bStar s v c w ∧
        IsLocalMinOn (fun p : Parameters d n ↦ CenteredLoss p.1 p.2 s v)
          {p | ∀ i, ‖p.2 i‖ = 1} (c, w) := by
  simp_rw [eq_skip_connection hd]
  exact quadratic_shear_local_min_iff
    (κ := 1 / 2) (T := {p : Parameters d n | ∀ i, ‖p.2 i‖ = 1})
    (b := b) (z := (c, w))
    (fun z : Parameters d n ↦ CenteredLoss z.1 z.2 s v)
    (fun z : Parameters d n ↦ MatchingSkip bStar s v z.1 z.2)
    (matching_skip_continuous bStar s v) (by norm_num) hw

/-- Strict local-minimum transport uses the same product decomposition. -/
theorem skip_strict_local_minimum_iff
    (hd : 2 ≤ d)
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) :
    (∀ᶠ p : Vec d × Parameters d n in 𝓝[{p | ∀ i, ‖p.2.2 i‖ = 1}] (b, (c, w)),
      p ≠ (b, (c, w)) → SkipLoss b c w bStar s v < SkipLoss p.1 p.2.1 p.2.2 bStar s v) ↔
      b = MatchingSkip bStar s v c w ∧
        (∀ᶠ p : Parameters d n in 𝓝[{p | ∀ i, ‖p.2 i‖ = 1}] (c, w),
          p ≠ (c, w) → CenteredLoss c w s v < CenteredLoss p.1 p.2 s v) := by
  simp_rw [eq_skip_connection hd]
  exact quadratic_shear_strict_local_min_iff
    (κ := 1 / 2) (T := {p : Parameters d n | ∀ i, ‖p.2 i‖ = 1})
    (b := b) (z := (c, w))
    (fun z : Parameters d n ↦ CenteredLoss z.1 z.2 s v)
    (fun z : Parameters d n ↦ MatchingSkip bStar s v z.1 z.2)
    (matching_skip_continuous bStar s v) (by norm_num) hw


/-- Critical-point transport on the sphere cylinder. This is first-order
stationarity of the literal loss, with no abstract hidden critical predicate. -/
theorem skip_critical_point_iff
    (hd : 2 ≤ d)
    (b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (bStar : Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) :
    HasFDerivWithinAt
      (fun p : Vec d × Parameters d n ↦ SkipLoss p.1 p.2.1 p.2.2 bStar s v)
      (0 : (Vec d × Parameters d n) →L[ℝ] ℝ)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (b, (c, w)) ↔
      b = MatchingSkip bStar s v c w ∧
        HasFDerivWithinAt (fun p : Parameters d n ↦ CenteredLoss p.1 p.2 s v)
          (0 : Parameters d n →L[ℝ] ℝ) {p | ∀ i, ‖p.2 i‖ = 1} (c, w) := by
  simp_rw [eq_skip_connection hd]
  exact quadratic_shear_critical_iff
    (κ := 1 / 2) (T := {p : Parameters d n | ∀ i, ‖p.2 i‖ = 1})
    (b := b) (z := (c, w))
    (fun z : Parameters d n ↦ CenteredLoss z.1 z.2 s v)
    (fun z : Parameters d n ↦ MatchingSkip bStar s v z.1 z.2)
    (matching_skip_differentiable bStar s v) (by norm_num) hw

end PaperLeanFormalization.Skip
