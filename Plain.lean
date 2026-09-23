import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Preliminaries
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.TangentCone
import Mathlib.Tactic.SplitIfs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Periodic
import Mathlib.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.Jensen
import Definitions
open Real Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace PaperLeanFormalization.SeedCertificate

/-- Away from its kink the ReLU feature is locally one affine branch. -/
theorem differentiableAt_relu_of_ne {a : ℝ} (ha : a ≠ 0) :
    DifferentiableAt ℝ (fun x : ℝ => max 0 x) a := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · apply (differentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    exact eventuallyEq_of_mem (Iio_mem_nhds hn) (fun _ hy => max_eq_left (le_of_lt hy))
  · apply differentiableAt_id.congr_of_eventuallyEq
    exact eventuallyEq_of_mem (Ioi_mem_nhds hp) (fun _ hy => max_eq_right (le_of_lt hy))

theorem not_differentiableAt_relu_zero :
    ¬ DifferentiableAt ℝ (fun x : ℝ => max 0 x) 0 := by
  intro h
  apply not_differentiableAt_abs_zero
  have hid : DifferentiableAt ℝ (fun x : ℝ => x) 0 := differentiableAt_id
  have hfun : (fun x : ℝ => 2 * max 0 x - x) = abs := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_right hx, abs_of_nonneg hx]
      ring
    · rw [max_eq_left hx, abs_of_nonpos hx]
      ring
  rw [← hfun]
  exact (h.const_mul 2).sub hid

theorem differentiableAt_affine_relu {a b : ℝ} (ha : a ≠ 0) :
    DifferentiableAt ℝ (fun t : ℝ => max 0 (a + t * b)) 0 := by
  have hp : DifferentiableAt ℝ (fun x : ℝ => max 0 x) (a + (0 : ℝ)*b) := by
    simpa using differentiableAt_relu_of_ne ha
  have h := hp.comp 0
    (((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a).differentiableAt
  simpa using h

/-- A finite collection of smooth feature branches cannot hide an unmatched
teacher kink. This replaces a numerical Fourier lower bound for spuriousness. -/
theorem finite_relu_cannot_equal_kink {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c a b : ι → ℝ) (s α β : κ → ℝ) (mass : ℝ) (hmass : mass ≠ 0)
    (ha : ∀ i, a i ≠ 0) (hα : ∀ k, α k ≠ 0) :
    ∃ t : ℝ, (∑ i, c i * max 0 (a i + t * b i)) ≠
      mass * max 0 t + ∑ k, s k * max 0 (α k + t * β k) := by
  classical
  by_contra h
  push_neg at h
  have hs : DifferentiableAt ℝ (fun t : ℝ => ∑ i, c i * max 0 (a i+t*b i)) 0 :=
    DifferentiableAt.sum fun i _ => (differentiableAt_affine_relu (ha i)).const_mul (c i)
  have ht : DifferentiableAt ℝ (fun t : ℝ => ∑ k, s k * max 0 (α k+t*β k)) 0 :=
    DifferentiableAt.sum fun k _ => (differentiableAt_affine_relu (hα k)).const_mul (s k)
  have hdiff := (hs.sub ht).const_mul mass⁻¹
  have heq : (fun t : ℝ => mass⁻¹ *
      ((∑ i, c i*max 0 (a i+t*b i)) - ∑ k, s k*max 0 (α k+t*β k))) =
      (fun t : ℝ => max 0 t) := by
    funext t
    rw [h t, add_sub_cancel, ← mul_assoc, inv_mul_cancel hmass, one_mul]
  rw [heq] at hdiff
  exact not_differentiableAt_relu_zero hdiff

/-- Continuous unequal networks have positive weighted square error under any
measure positive on nonempty open sets, with strictly positive continuous density. -/
theorem positive_weighted_square_of_ne {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    (f g density : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hρ : Continuous density) (hρpos : ∀ x, 0 < density x)
    (hint : Integrable (fun x => (f x-g x)^2*density x) μ)
    (hne : ∃ x, f x ≠ g x) :
    0 < ∫ x, (f x-g x)^2*density x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg
    (fun x => mul_nonneg (sq_nonneg _) (hρpos x).le) hint).mpr
  apply (((hf.sub hg).pow 2).mul hρ).isOpen_support.measure_pos μ
  obtain ⟨x,hx⟩ := hne
  exact ⟨x, mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hx)) (hρpos x).ne'⟩

/-- The transverse line through the first teacher gives a witness for every
student configuration missing that teacher's unoriented line. -/
theorem three_teacher_transverse_witness {n : ℕ} (c θ : Fin n → ℝ)
    (β₁ β₂ : ℝ) (hθ : ∀ i, sin (θ i) ≠ 0)
    (hβ₁ : sin β₁ ≠ 0) (hβ₂ : sin β₂ ≠ 0) :
    ∃ t : ℝ, (∑ i, c i*max 0 (sin (θ i)+t*cos (θ i))) ≠
      max 0 t + max 0 (sin β₁+t*cos β₁) + max 0 (sin β₂+t*cos β₂) := by
  have h := finite_relu_cannot_equal_kink c (fun i => sin (θ i))
    (fun i => cos (θ i)) (fun _ : Fin 2 => (1 : ℝ)) ![sin β₁,sin β₂]
    ![cos β₁,cos β₂] 1 one_ne_zero hθ (by
      intro k
      fin_cases k
      · simpa using hβ₁
      · simpa using hβ₂)
  simpa [Fin.sum_univ_two, add_assoc] using h

/-- Explicit rational candidate; it is not asserted to be a critical point. -/
def seedCentre : (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  (![(1000437388123 / 1000000000000 : ℝ),
     (695398940163 / 500000000000 : ℝ),
     (604352649479 / 1000000000000 : ℝ)],
   ![(222166734523 / 125000000000 : ℝ) * π,
     (66013352661 / 62500000000 : ℝ) * π,
     (363169886907 / 1000000000000 : ℝ) * π])

theorem eq_trap_student_masses : seedCentre.1 =
    ![(1000437388123/1000000000000 : ℝ), (695398940163/500000000000 : ℝ),
      (604352649479/1000000000000 : ℝ)] := rfl

theorem eq_trap_student_angles : seedCentre.2 =
    ![(222166734523/125000000000 : ℝ)*π, (66013352661/62500000000 : ℝ)*π,
      (363169886907/1000000000000 : ℝ)*π] := rfl

theorem coordinate_bounds_of_closedBall {n : ℕ}
    {p q : (Fin n → ℝ) × (Fin n → ℝ)} {r : ℝ}
    (hp : p ∈ Metric.closedBall q r) (i : Fin n) :
    |p.1 i-q.1 i| ≤ r ∧ |p.2 i-q.2 i| ≤ r := by
  rw [Metric.mem_closedBall, Prod.dist_eq] at hp
  constructor
  · exact (Real.dist_eq _ _ ▸ dist_le_pi_dist p.1 q.1 i).trans
      ((le_max_left _ _).trans hp)
  · exact (Real.dist_eq _ _ ▸ dist_le_pi_dist p.2 q.2 i).trans
      ((le_max_right _ _).trans hp)

/-- The geometric margins tolerate a ball fifty times larger than the original
existence certificate. They require no trigonometric interval arithmetic. -/
theorem seed_ball_mass_and_angle_separation
    {p : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hp : p ∈ Metric.closedBall seedCentre (1/1000 : ℝ)) :
    (∀ i, 0 < p.1 i) ∧
      π < p.2 0 ∧ p.2 0 < 2*π ∧
      π < p.2 1 ∧ p.2 1 < 2*π ∧
      0 < p.2 2 ∧ p.2 2 < π := by
  have hc (i : Fin 3) := (coordinate_bounds_of_closedBall hp i).1
  have ht0 := (coordinate_bounds_of_closedBall hp 0).2
  have ht1 := (coordinate_bounds_of_closedBall hp 1).2
  have ht2 := (coordinate_bounds_of_closedBall hp 2).2
  rw [eq_trap_student_angles] at ht0 ht1 ht2
  change |p.2 2 - (363169886907/1000000000000 : ℝ)*π| ≤ (1/1000 : ℝ) at ht2
  dsimp at ht0 ht1 ht2
  rw [abs_le] at ht0 ht1 ht2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := hc i
    rw [eq_trap_student_masses] at h
    fin_cases i <;> norm_num [abs_le] at h ⊢ <;> linarith only [h.1]
  all_goals linarith only [ht0.1, ht0.2, ht1.1, ht1.2, ht2.1, ht2.2, two_le_pi]

theorem sin_ne_zero_of_pi_lt_of_lt_two_pi {t : ℝ} (hlo : π < t) (hhi : t < 2*π) :
    sin t ≠ 0 := by
  have h := sin_pos_of_pos_of_lt_pi (by linarith only [hlo] : 0 < t-π)
    (by linarith only [hhi] : t-π < π)
  rw [sin_sub_pi] at h
  exact (neg_pos.mp h).ne

theorem seed_ball_missing_first_teacher_line
    {p : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hp : p ∈ Metric.closedBall seedCentre (1/1000 : ℝ)) :
    ∀ i, sin (p.2 i) ≠ 0 := by
  obtain ⟨_, h0lo,h0hi,h1lo,h1hi,h2lo,h2hi⟩ := seed_ball_mass_and_angle_separation hp
  intro i
  fin_cases i
  · exact sin_ne_zero_of_pi_lt_of_lt_two_pi h0lo h0hi
  · exact sin_ne_zero_of_pi_lt_of_lt_two_pi h1lo h1hi
  · exact (sin_pos_of_pos_of_lt_pi h2lo h2hi).ne'

theorem seed_ball_transverse_witness
    {p : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hp : p ∈ Metric.closedBall seedCentre (1/1000 : ℝ)) :
    ∃ t : ℝ, (∑ i, p.1 i*max 0 (sin (p.2 i)+t*cos (p.2 i))) ≠
      max 0 t + max 0 (sin ((5/6 : ℝ)*π)+t*cos ((5/6 : ℝ)*π)) +
        max 0 (sin ((4/3 : ℝ)*π)+t*cos ((4/3 : ℝ)*π)) := by
  apply three_teacher_transverse_witness p.1 p.2 _ _ (seed_ball_missing_first_teacher_line hp)
  · exact (sin_pos_of_pos_of_lt_pi (by positivity)
      (by linarith only [pi_pos] : (5/6 : ℝ)*π < π)).ne'
  · exact sin_ne_zero_of_pi_lt_of_lt_two_pi
      (by linarith only [pi_pos]) (by linarith only [pi_pos])

/-- The kernel ODE is preserved by each finite residual sum. -/
theorem eq_sine_load_identity {n m : ℕ} (K : ℝ → ℝ)
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (x : ℝ) :
    ((∑ i, c i*(2*|sin (x-θ i)|-K (x-θ i))) -
      ∑ k, s k*(2*|sin (x-β k)|-K (x-β k))) +
      ((∑ i, c i*K (x-θ i)) - ∑ k, s k*K (x-β k)) =
      2*((∑ i, c i*|sin (x-θ i)|) - ∑ k, s k*|sin (x-β k)|) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [mul_left_comm (c _) 2, mul_left_comm (s _) 2]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

private theorem cos_lower_small {x r : ℝ} (hx : |x| ≤ r) (hr : r ≤ 1) :
    1-r^2/2-r^4*(5/96) ≤ cos x := by
  have h2 := pow_le_pow_left (abs_nonneg x) hx 2
  have h4 := pow_le_pow_left (abs_nonneg x) hx 4
  rw [sq_abs] at h2
  have hb := (abs_le.mp (cos_bound (hx.trans hr))).1
  linarith only [h2,h4,hb]

private theorem cos_upper_middle {x : ℝ} (hlo : (2/5 : ℝ) ≤ x)
    (hhi : x ≤ (1/2 : ℝ)) : cos x ≤ (37/40 : ℝ) := by
  have hx : 0 ≤ x := by linarith only [hlo]
  have h2 := pow_le_pow_left (by norm_num : (0 : ℝ) ≤ 2/5) hlo 2
  have h4 := pow_le_pow_left hx hhi 4
  have hb := (abs_le.mp (cos_bound (by rw [abs_of_nonneg hx]; linarith only [hhi]))).2
  rw [abs_of_nonneg hx] at hb
  norm_num at h2 h4
  linarith only [h2,h4,hb]

private theorem sin_two_pi_thirds_lower {e : ℝ} (hlo : 0 ≤ e)
    (hhi : e ≤ (43/500 : ℝ)) : (163/200 : ℝ) ≤ sin (2*π/3+e) := by
  have hc := cos_lower_small (by rwa [abs_of_nonneg hlo] : |e| ≤ (43/500 : ℝ))
    (by norm_num)
  have hcf : (249/250 : ℝ) ≤ cos e := by norm_num at hc; linarith only [hc]
  have hs : sin e ≤ (43/500 : ℝ) := by
    rcases eq_or_lt_of_le hlo with he | he
    · rw [← he, sin_zero]
      norm_num
    · exact (sin_lt he).le.trans hhi
  have hroot : (433/500 : ℝ) ≤ sqrt 3/2 := by
    nlinarith only [sqrt_nonneg (3 : ℝ), sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hprod := mul_le_mul hroot hcf (by norm_num : (0 : ℝ) ≤ 249/250)
    (by positivity : (0 : ℝ) ≤ sqrt 3/2)
  rw [sin_add, show 2*π/3 = π-π/3 by ring, sin_pi_sub, cos_pi_sub,
    sin_pi_div_three, cos_pi_div_three]
  nlinarith only [hprod,hs]

/-- Four wide angular sectors suffice for the splitting sign; no tiny interval
enclosure of the kernel or its derivative is needed. -/
theorem seed_ball_transverse_sine_bounds
    {p : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hp : p ∈ Metric.closedBall seedCentre (1/1000 : ℝ)) :
    (24/25 : ℝ) ≤ |sin (p.2 2-p.2 0)| ∧
    (163/200 : ℝ) ≤ |sin (p.2 2-p.2 1)| ∧
    |sin (p.2 2)| ≤ (37/40 : ℝ) ∧
    |sin (p.2 2-(4/3 : ℝ)*π)| ≤ (1/10 : ℝ) := by
  have ht0 := (coordinate_bounds_of_closedBall hp 0).2
  have ht1 := (coordinate_bounds_of_closedBall hp 1).2
  have ht2 := (coordinate_bounds_of_closedBall hp 2).2
  rw [eq_trap_student_angles] at ht0 ht1 ht2
  change |p.2 2-(363169886907/1000000000000 : ℝ)*π| ≤ (1/1000 : ℝ) at ht2
  dsimp at ht0 ht1
  rw [abs_le] at ht0 ht1 ht2
  have hpi : π < (22/7 : ℝ) := by
    have hb := pi_lt_31416
    norm_num at hb
    linarith only [hb]
  have h0 : |p.2 2-p.2 0+3*π/2| ≤ (7/25 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [ht0.1,ht0.2,ht2.1,ht2.2,pi_gt_three,hpi]
  have h1 : 0 ≤ p.2 1-p.2 2-2*π/3 ∧
      p.2 1-p.2 2-2*π/3 ≤ (43/500 : ℝ) := by
    constructor <;> linarith only [ht1.1,ht1.2,ht2.1,ht2.2,pi_gt_three,hpi]
  have h2 : (2/5 : ℝ) ≤ π/2-p.2 2 ∧ π/2-p.2 2 ≤ (1/2 : ℝ) := by
    constructor <;> linarith only [ht2.1,ht2.2,pi_gt_three,hpi]
  have h3 : 0 < p.2 2-π/3 ∧ p.2 2-π/3 ≤ (1/10 : ℝ) := by
    constructor <;> linarith only [ht2.1,ht2.2,pi_gt_three,hpi]
  refine ⟨?_,?_,?_,?_⟩
  · have hcos := cos_lower_small h0 (by norm_num)
    have hid : sin (p.2 2-p.2 0) = cos (p.2 2-p.2 0+3*π/2) := by
      rw [show p.2 2-p.2 0+3*π/2 = (p.2 2-p.2 0+π)+π/2 by ring,
        cos_add_pi_div_two, sin_add_pi, neg_neg]
    rw [hid]
    have hle := le_abs_self (cos (p.2 2-p.2 0+3*π/2))
    norm_num at hcos
    linarith only [hcos,hle]
  · have hs := sin_two_pi_thirds_lower h1.1 h1.2
    rw [show 2*π/3+(p.2 1-p.2 2-2*π/3) = p.2 1-p.2 2 by ring] at hs
    have habs : |sin (p.2 1-p.2 2)| = |sin (p.2 2-p.2 1)| := by
      rw [show p.2 1-p.2 2 = -(p.2 2-p.2 1) by ring, sin_neg, abs_neg]
    exact hs.trans (habs ▸ le_abs_self (sin (p.2 1-p.2 2)))
  · have hsin := (seed_ball_mass_and_angle_separation hp).2.2.2.2.2
    rw [abs_of_pos (sin_pos_of_pos_of_lt_pi hsin.1 hsin.2), ← cos_pi_div_two_sub]
    exact cos_upper_middle h2.1 h2.2
  · rw [show p.2 2-(4/3 : ℝ)*π = (p.2 2-π/3)-π by ring, sin_sub_pi, abs_neg,
      abs_of_pos (sin_pos_of_pos_of_lt_pi h3.1 (by linarith only [h3.2,pi_gt_three]))]
    exact (sin_lt h3.1).le.trans h3.2

/-- The exact rational margin used for the selected seed's residual curvature. -/
theorem eq_trap_curvature_rational_margin :
    2 * ((999/1000 : ℝ) * (24/25) + (1389/1000) * (163/200) -
      37/40 - 1 - 1/10) = 2643/20000 ∧ (1/8 : ℝ) < 2643/20000 := by
  norm_num

theorem seed_ball_slot_two_sine_load_positive
    {p : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hp : p ∈ Metric.closedBall seedCentre (1/1000 : ℝ)) :
    (1/8 : ℝ) < 2*(p.1 0*|sin (p.2 2-p.2 0)| +
      p.1 1*|sin (p.2 2-p.2 1)| - |sin (p.2 2)| -
      |sin (p.2 2-(5/6 : ℝ)*π)| - |sin (p.2 2-(4/3 : ℝ)*π)|) := by
  obtain ⟨ha,hb,hc,hd⟩ := seed_ball_transverse_sine_bounds hp
  have hmass0 := (coordinate_bounds_of_closedBall hp 0).1
  have hmass1 := (coordinate_bounds_of_closedBall hp 1).1
  rw [eq_trap_student_masses] at hmass0 hmass1
  norm_num [abs_le] at hmass0 hmass1
  have hm0 : (999/1000 : ℝ) ≤ p.1 0 := by linarith only [hmass0.1]
  have hm1 : (1389/1000 : ℝ) ≤ p.1 1 := by linarith only [hmass1.1]
  have hprod0 := mul_le_mul hm0 ha (by norm_num : (0 : ℝ) ≤ 24/25)
    ((seed_ball_mass_and_angle_separation hp).1 0).le
  have hprod1 := mul_le_mul hm1 hb (by norm_num : (0 : ℝ) ≤ 163/200)
    ((seed_ball_mass_and_angle_separation hp).1 1).le
  have hmargin : (1/8 : ℝ) < 2*((999/1000 : ℝ)*(24/25) +
      (1389/1000)*(163/200)-37/40-1-1/10) := by
    rw [eq_trap_curvature_rational_margin.1]
    exact eq_trap_curvature_rational_margin.2
  apply lt_of_lt_of_le hmargin
  linarith only [hprod0,hprod1,hc,hd,abs_sin_le_one (p.2 2-(5/6 : ℝ)*π)]

end PaperLeanFormalization.SeedCertificate

noncomputable section
open Set Filter Topology

namespace PaperLeanFormalization.Plain.LocalSeed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem line_derivative {f : E → ℝ} {x h : E} {t a : ℝ}
    (H : HasDerivAt (fun s : ℝ => f (x + t • h + s • h)) a 0) :
    HasDerivAt (fun s : ℝ => f (x + s • h)) a t := by
  have H0 : HasDerivAt (fun s : ℝ => f (x + t • h + s • h)) a (t-t) := by
    simpa only [sub_self] using H
  convert HasDerivAt.comp (h := fun s : ℝ => s-t) t H0
    ((hasDerivAt_id t).sub_const t) using 1
  · ext s
    simp only [Function.comp_apply, sub_smul]
    congr 1
    abel
  · exact (mul_one a).symm

/-- `eq:trap-taylor`: subtract the certified quadratic and integrate the
nonnegative derivative twice along the segment. -/
theorem eq_trap_taylor {f : E → ℝ} {D₁ D₂ : E → E → ℝ}
    (hD₁ : ∀ x h, HasDerivAt (fun t : ℝ => f (x+t•h)) (D₁ x h) 0)
    (hD₂ : ∀ x h, HasDerivAt (fun t : ℝ => D₁ (x+t•h) h) (D₂ x h) 0)
    {c x y : E} {r K : ℝ} (hx : x ∈ Metric.closedBall c r)
    (hy : y ∈ Metric.closedBall c r)
    (hcurv : ∀ z ∈ Metric.closedBall c r, K ≤ D₂ z (y-x)) :
    f x + D₁ x (y-x) + K/2 ≤ f y := by
  let h := y-x
  have hseg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : x+t•h ∈ Metric.closedBall c r := by
    have H := (convex_closedBall c r) hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
    convert H using 1
    dsimp [h]
    rw [sub_smul, one_smul, smul_sub]
    abel
  let q := fun t : ℝ => f (x+t•h) - D₁ x h*t - K/2*t^2
  let q' := fun t : ℝ => D₁ (x+t•h) h - D₁ x h - K*t
  have hq (t : ℝ) : HasDerivAt q (q' t) t := by
    convert ((line_derivative (hD₁ (x+t•h) h)).sub
      ((hasDerivAt_id t).const_mul (D₁ x h))).sub
        (((hasDerivAt_id t).pow 2).const_mul (K/2)) using 1
    dsimp [q, q']
    ring
  have hq' (t : ℝ) : HasDerivAt q' (D₂ (x+t•h) h-K) t := by
    simpa only [q', mul_one] using
      ((line_derivative (f := fun z : E => D₁ z h)
        (hD₂ (x+t•h) h)).sub_const (D₁ x h)).sub
          ((hasDerivAt_id t).const_mul K)
  have hmono : MonotoneOn q' (Icc (0:ℝ) 1) :=
    (convex_Icc 0 1).monotoneOn_of_deriv_nonneg
      (fun t _ => (hq' t).continuousAt.continuousWithinAt)
      (fun t _ => (hq' t).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hq' t).deriv]; exact sub_nonneg.mpr (hcurv _ (hseg t (interior_subset ht))))
  have hnonneg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ q' t := by
    have H := hmono (by norm_num) ht ht.1
    simpa [q'] using H
  have hmonoQ : MonotoneOn q (Icc (0:ℝ) 1) :=
    (convex_Icc 0 1).monotoneOn_of_deriv_nonneg
      (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hq t).deriv]; exact hnonneg t (interior_subset ht))
  have H := hmonoQ (by norm_num) (by norm_num) zero_le_one
  dsimp [q, h] at H
  simp only [zero_smul, add_zero, mul_zero, zero_pow (by decide : 0 < 2),
    sub_zero, one_smul, one_pow, mul_one, add_sub_cancel'] at H
  rw [show x+(y-x)=y by abel] at H
  linarith only [H]

/-- Taylor's lower bound and the centre-gradient bound give the strict
boundary margin; `Q` allows the Euclidean square inside a max-norm box. -/
theorem eq_box_boundary_margin {f₀ f₁ d Q μ g r : ℝ}
    (hr : 0 < r) (hμ : 0 < μ) (hQ : 0 ≤ Q)
    (hR : r ≤ Real.sqrt Q) (hgap : g < μ*r/2)
    (hT : f₀ + d + μ/2*Q ≤ f₁) (hg : -(g*Real.sqrt Q) ≤ d) :
    Real.sqrt Q * (μ/2*Real.sqrt Q-g) ≤ f₁-f₀ ∧
      0 < Real.sqrt Q * (μ/2*Real.sqrt Q-g) := by
  have hs := Real.sq_sqrt hQ
  have hid : Real.sqrt Q * (μ/2*Real.sqrt Q-g) =
      μ/2*Q-g*Real.sqrt Q := by
    calc
      _ = μ/2*(Real.sqrt Q)^2-g*Real.sqrt Q := by ring
      _ = _ := by rw [hs]
  constructor
  · rw [hid]
    linarith only [hT, hg]
  · apply mul_pos (hr.trans_le hR)
    nlinarith only [hR, hgap, hμ]

/-- A common quadratic certificate may use a different norm from the compact
box. The stronger boundary-value margin is sufficient for the certified data. -/
theorem interior_strict_minimum [ProperSpace E]
    {f : E → ℝ} {D₁ : E → E → ℝ} {Q : E → ℝ} {c : E} {r μ G : ℝ}
    (hr : 0 < r) (hμ : 0 < μ) (hG : 0 ≤ G)
    (hQ : ∀ h, ‖h‖^2 ≤ Q h)
    (hD₁ : ∀ x h, HasDerivAt (fun t : ℝ => f (x+t•h)) (D₁ x h) 0)
    (hc : ContinuousOn f (Metric.closedBall c r))
    (hT : ∀ x ∈ Metric.closedBall c r, ∀ y ∈ Metric.closedBall c r,
      f x + D₁ x (y-x) + μ/2*Q (y-x) ≤ f y)
    (hg : ∀ h, (D₁ c h)^2 ≤ G*Q h) (hsmall : 4*G < μ^2*r^2) :
    ∃ z, ‖z-c‖ < r ∧ (∀ h, D₁ z h = 0) ∧
      (∀ᶠ y in 𝓝 z, y ≠ z → f z < f y) ∧
      ∀ y ∈ Metric.closedBall c r, f c-G/(2*μ) ≤ f y := by
  have hQ0 (h : E) : 0 ≤ Q h := (sq_nonneg ‖h‖).trans (hQ h)
  have hb (h : E) : -(Real.sqrt G * Real.sqrt (Q h)) ≤ D₁ c h := by
    have H := Real.abs_le_sqrt (hg h)
    rw [Real.sqrt_mul hG] at H
    exact (abs_le.mp H).1
  have hgap : Real.sqrt G < μ*r/2 := by
    have H := Real.sq_sqrt hG
    nlinarith only [H, Real.sqrt_nonneg G, mul_pos hμ hr, hsmall]
  obtain ⟨z, hz, hmin⟩ := Metric.exists_isLocalMin_mem_ball hc
    (Metric.mem_closedBall_self hr.le) (by
      intro y hy
      have hn : ‖y-c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hy
      have hR : r ≤ Real.sqrt (Q (y-c)) := by
        rw [← hn]
        simpa only [abs_of_nonneg (norm_nonneg (y-c))] using Real.abs_le_sqrt (hQ (y-c))
      have H := hT c (Metric.mem_closedBall_self hr.le) y (Metric.sphere_subset_closedBall hy)
      obtain ⟨hbound, hpositive⟩ := eq_box_boundary_margin hr hμ
        (hQ0 (y-c)) hR hgap H (hb (y-c))
      linarith only [hbound, hpositive])
  have hzclosed := Metric.ball_subset_closedBall hz
  have hcrit (h : E) : D₁ z h = 0 := by
    have H : IsLocalMin f (z+(0:ℝ)•h) := by simpa using hmin
    exact (H.comp_continuous (g := fun t : ℝ => z+t•h) (continuous_const.add
      (continuous_id.smul continuous_const)).continuousAt).hasDerivAt_eq_zero (hD₁ z h)
  refine ⟨z, ?_, hcrit, ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_eq_norm] using hz
  · filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy hne
    have H := hT z hzclosed y (Metric.ball_subset_closedBall hy)
    rw [hcrit] at H
    have hpos := mul_pos (div_pos hμ (by norm_num : (0:ℝ)<2))
      ((sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).trans_le (hQ (y-z)))
    linarith only [H, hpos]
  · intro y hy
    have H := hT c (Metric.mem_closedBall_self hr.le) y hy
    have hs := Real.sq_sqrt (hQ0 (y-c))
    have hg := Real.sq_sqrt hG
    have hsq := sq_nonneg (μ * Real.sqrt (Q (y-c)) - Real.sqrt G)
    have hden : 0 < 2*μ := by positivity
    have hid : (μ * Real.sqrt (Q (y-c)) - Real.sqrt G)^2 =
        (2*μ) * (μ/2 * Q (y-c) - Real.sqrt G * Real.sqrt (Q (y-c)) + G/(2*μ)) := by
      calc
        _ = μ^2 * Real.sqrt (Q (y-c))^2 -
          2*μ*Real.sqrt G*Real.sqrt (Q (y-c)) + Real.sqrt G^2 := by ring
        _ = _ := by rw [hs, hg]; field_simp [hμ.ne']; ring
    rw [hid] at hsq
    have hcomplete := nonneg_of_mul_nonneg_right hsq hden
    linarith only [H, hb (y-c), hcomplete]

end PaperLeanFormalization.Plain.LocalSeed

noncomputable section

namespace PaperLeanFormalization.BoxDirectional

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restricting an actual Fréchet derivative to an affine line. -/
theorem hasDerivAt_line {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (h : E) :
    HasDerivAt (fun t : ℝ => f (x + t • h)) (fderiv ℝ f x h) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  have hfx : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • h) := by
    simpa using hf.hasFDerivAt
  exact hfx.comp_hasDerivAt 0 hline

/-- A `C²` function supplies the actual first derivative on every line. -/
theorem first_line_derivative {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x h : E) :
    HasDerivAt (fun t : ℝ => f (x + t • h)) (fderiv ℝ f x h) 0 :=
  hasDerivAt_line (hf.differentiable (by norm_num) x) h

/-- Differentiating that first derivative gives the actual Hessian diagonal. -/
theorem second_line_derivative {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x h : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • h) h)
      ((fderiv ℝ (fderiv ℝ f) x h) h) 0 := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hline := hasDerivAt_line (hDf.differentiable (by norm_num) x) h
  simpa using hline.clm_apply (hasDerivAt_const (0 : ℝ) h)

end PaperLeanFormalization.BoxDirectional

noncomputable section
open Real Set Filter
open scoped Topology BigOperators

namespace PaperLeanFormalization.Plain

/-- Two coordinate blocks allow arbitrary finite dimension, including an empty
block. The product norm is the box norm; this sum is Euclidean squared length. -/
private theorem two_block_size_dominates_norm {a b : ℕ}
    (p : (Fin a → ℝ) × (Fin b → ℝ)) :
    ‖p‖ ^ 2 ≤ (∑ i, p.1 i ^ 2) + ∑ j, p.2 j ^ 2 := by
  have hpi {n : ℕ} (v : Fin n → ℝ) : ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
    have hsum : (0 : ℝ) ≤ ∑ i, v i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg (v i)
    have hn : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro i
      exact Real.abs_le_sqrt (Finset.single_le_sum
        (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
    have hs := Real.sq_sqrt hsum
    nlinarith only [hn, hs, norm_nonneg v, Real.sqrt_nonneg (∑ i, v i ^ 2)]
  have hfirst := hpi p.1
  have hsecond := hpi p.2
  have hfirst0 : (0 : ℝ) ≤ ∑ i, p.1 i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (p.1 i)
  have hsecond0 : (0 : ℝ) ≤ ∑ j, p.2 j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (p.2 j)
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h]
    linarith only [hsecond, hfirst0]
  · rw [max_eq_left h]
    linarith only [hfirst, hsecond0]

/-- A C² objective with a uniform Euclidean Hessian floor and a sufficiently
small center gradient has one interior strict minimum on the coordinate box.
The derivative bound is the dual formulation of `‖∇f(z₀)‖₂ ≤ g`.
Neither a Taylor inequality nor an already existing minimum is a hypothesis. -/
theorem box_strict_minimum {a b : ℕ}
    {f : ((Fin a → ℝ) × (Fin b → ℝ)) → ℝ} (hf : ContDiff ℝ 2 f)
    {z₀ : (Fin a → ℝ) × (Fin b → ℝ)} {r lam g : ℝ}
    (hr : 0 < r) (hlam : 0 < lam) (hg : 0 ≤ g)
    (hcurv : ∀ z ∈ Metric.closedBall z₀ r,
      ∀ h : (Fin a → ℝ) × (Fin b → ℝ),
        lam * ((∑ i, h.1 i ^ 2) + ∑ j, h.2 j ^ 2) ≤
          (fderiv ℝ (fderiv ℝ f) z h) h)
    (hgrad : ∀ h : (Fin a → ℝ) × (Fin b → ℝ),
      |fderiv ℝ f z₀ h| ≤
        g * Real.sqrt ((∑ i, h.1 i ^ 2) + ∑ j, h.2 j ^ 2))
    (hsmall : 2 * g < lam * r) :
    ∃ z : (Fin a → ℝ) × (Fin b → ℝ),
      ‖z - z₀‖ < r ∧ fderiv ℝ f z = 0 ∧
      (∀ᶠ y in 𝓝 z, y ≠ z → f z < f y) ∧
      ∀ y ∈ Metric.closedBall z₀ r, y ≠ z → f z < f y := by
  let Q : ((Fin a → ℝ) × (Fin b → ℝ)) → ℝ :=
    fun h => (∑ i, h.1 i ^ 2) + ∑ j, h.2 j ^ 2
  have hQ (h : (Fin a → ℝ) × (Fin b → ℝ)) : ‖h‖ ^ 2 ≤ Q h :=
    two_block_size_dominates_norm h
  have hQ0 (h : (Fin a → ℝ) × (Fin b → ℝ)) : 0 ≤ Q h :=
    (sq_nonneg ‖h‖).trans (hQ h)
  have hT (x : (Fin a → ℝ) × (Fin b → ℝ))
      (hx : x ∈ Metric.closedBall z₀ r)
      (y : (Fin a → ℝ) × (Fin b → ℝ))
      (hy : y ∈ Metric.closedBall z₀ r) :
      f x + fderiv ℝ f x (y - x) + lam / 2 * Q (y - x) ≤ f y := by
    convert LocalSeed.eq_trap_taylor
      (BoxDirectional.first_line_derivative hf)
      (BoxDirectional.second_line_derivative hf) hx hy
      (fun z hz => hcurv z hz (y - x)) using 1
    ring
  have hG (h : (Fin a → ℝ) × (Fin b → ℝ)) :
      (fderiv ℝ f z₀ h) ^ 2 ≤ g ^ 2 * Q h := by
    calc
      _ = |fderiv ℝ f z₀ h| * |fderiv ℝ f z₀ h| := by rw [← pow_two, sq_abs]
      _ ≤ (g * Real.sqrt (Q h)) * (g * Real.sqrt (Q h)) :=
        mul_self_le_mul_self (abs_nonneg _) (hgrad h)
      _ = g ^ 2 * Real.sqrt (Q h) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hQ0 h)]
  have hsmallSq : 4 * g ^ 2 < lam ^ 2 * r ^ 2 := by
    have hs := mul_self_lt_mul_self (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg) hsmall
    nlinarith only [hs]
  obtain ⟨z, hz, hzero, hstrict, _hfloor⟩ := LocalSeed.interior_strict_minimum
    hr hlam (sq_nonneg g) hQ (BoxDirectional.first_line_derivative hf)
    hf.continuous.continuousOn hT hG hsmallSq
  refine ⟨z, hz, ?_, hstrict, ?_⟩
  · apply ContinuousLinearMap.ext
    intro h
    simpa only [ContinuousLinearMap.zero_apply] using hzero h
  · intro y hy hne
    have hzbox : z ∈ Metric.closedBall z₀ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz.le
    have H := hT z hzbox y hy
    rw [hzero] at H
    have hsize : 0 < Q (y - z) :=
      (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).trans_le (hQ (y - z))
    have hpos := mul_pos (div_pos hlam (by norm_num : (0 : ℝ) < 2)) hsize
    linarith only [H, hpos]

/-- Positive affine normalization transfers strict minimality to the actual
loss. Positivity on the box and an exact-fit competitor make it spurious;
positivity of an unrelated normalized objective would not suffice. -/
theorem box_minimum_affine_spurious {a b : ℕ}
    {f L : ((Fin a → ℝ) × (Fin b → ℝ)) → ℝ}
    {z₀ z : (Fin a → ℝ) × (Fin b → ℝ)} {r scale shift : ℝ}
    (hz : z ∈ Metric.closedBall z₀ r)
    (hstrict : ∀ᶠ y in 𝓝 z, y ≠ z → f z < f y)
    (hscale : 0 < scale) (heq : ∀ y, f y = scale * L y + shift)
    (hpositive : ∀ y ∈ Metric.closedBall z₀ r, 0 < L y)
    (hexact : ∃ y, L y = 0) :
    (∀ᶠ y in 𝓝 z, y ≠ z → L z < L y) ∧
      0 < L z ∧
      ((∀ y ∈ Metric.closedBall z₀ r, ∀ i, 0 < y.1 i) → ∀ i, 0 < z.1 i) ∧
      ∃ y, L y = 0 ∧ L y < L z := by
  refine ⟨?_, hpositive z hz, fun hmass => hmass z hz, ?_⟩
  · filter_upwards [hstrict] with y hy hne
    have H := hy hne
    rw [heq z, heq y] at H
    nlinarith only [H, hscale]
  · obtain ⟨y, hy⟩ := hexact
    exact ⟨y, hy, by simpa only [hy] using hpositive z hz⟩

end PaperLeanFormalization.Plain

open Real MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace PaperLeanFormalization.SeedCertificate

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def direction (t : ℝ) : Plane := ![cos t,sin t]

def teacher : Fin 3 → Plane :=
  ![direction 0,direction ((5/6 : ℝ)*π),direction ((4/3 : ℝ)*π)]

def network {n : ℕ} (c : Fin n → ℝ) (w : Fin n → Plane) (x : Plane) : ℝ :=
  ∑ i, c i*max 0 ⟪w i,x⟫_ℝ

theorem continuous_network {n : ℕ} (c : Fin n → ℝ) (w : Fin n → Plane) :
    Continuous (network c w) := by
  apply continuous_finset_sum _
  intro i _
  exact continuous_const.mul (continuous_const.max (continuous_const.inner continuous_id))

theorem integrable_finite_square {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) (f : I → X → ℝ) (ρ : X → ℝ)
    (hi : ∀ i j, Integrable (fun x => f i x*f j x*ρ x) μ) :
    Integrable (fun x => (∑ i, f i x)^2*ρ x) μ := by
  have h := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))
  convert h using 1
  funext x
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

set_option maxHeartbeats 800000 in
theorem integrable_residual_square {n m : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Plane) (s : Fin m → ℝ) (v : Fin m → Plane) :
    Integrable (fun x => (network c w x-network s v x)^2*
      stdGaussianDensity x) := by
  let a : Fin n ⊕ Fin m → ℝ := Sum.elim c (fun k => -s k)
  let z : Fin n ⊕ Fin m → Plane := Sum.elim w v
  have hi (i j : Fin n ⊕ Fin m) : Integrable (fun x =>
      (a i*max 0 ⟪z i,x⟫_ℝ)*(a j*max 0 ⟪z j,x⟫_ℝ)*
        stdGaussianDensity x) := by
    convert (Preliminaries.gaussian_plain_pair_integrable
      (by norm_num : 2 ≤ 2) (z i) (z j)).const_mul (a i*a j) using 1
    funext x
    ring
  have h := integrable_finite_square volume (fun i x => a i*max 0 ⟪z i,x⟫_ℝ)
    stdGaussianDensity hi
  simpa [network,a,z,Fintype.sum_sum_type,Finset.sum_neg_distrib,sub_eq_add_neg] using h

theorem direction_inner_transverse (θ t : ℝ) :
    ⟪direction θ,(![t,1] : Plane)⟫_ℝ = sin θ+t*cos θ := by
  rw [PiLp.inner_apply,Fin.sum_univ_two]
  change cos θ*t+sin θ*1 = _
  ring

theorem seed_ball_networks_differ
    {p : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hp : p ∈ Metric.closedBall seedCentre (1/1000 : ℝ)) :
    ∃ x : Plane, network p.1 (fun i => direction (p.2 i)) x ≠
      network (fun _ : Fin 3 => 1) teacher x := by
  obtain ⟨t,ht⟩ := seed_ball_transverse_witness hp
  refine ⟨![t,1],?_⟩
  unfold network
  simp only [direction_inner_transverse]
  simpa [teacher, direction, PiLp.inner_apply, Fin.sum_univ_two,
    Fin.sum_univ_three, mul_comm, add_comm, add_left_comm, add_assoc] using ht

/-- Literal Gaussian half-loss is positive throughout the separated seed ball.
The witness is structural; no numeric loss lower bound enters this proof. -/
theorem seed_ball_positive_gaussian_loss
    {p : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hp : p ∈ Metric.closedBall seedCentre (1/1000 : ℝ)) :
    0 < (1/2 : ℝ)*∫ x : Plane,
      ((∑ i, p.1 i*max 0 ⟪direction (p.2 i),x⟫_ℝ) -
        ∑ k : Fin 3, max 0 ⟪teacher k,x⟫_ℝ)^2*
          stdGaussianDensity x := by
  have hρ : Continuous (fun x : Plane => stdGaussianDensity x) := by
    unfold stdGaussianDensity
    exact continuous_const.mul
      (continuous_exp.comp ((continuous_norm.pow 2).neg.div_const 2))
  have hρpos (x : Plane) : 0 < stdGaussianDensity x := by
    unfold stdGaussianDensity
    have hs : 0 < sqrt (2*π) := sqrt_pos.mpr (by positivity)
    exact mul_pos (pow_pos (inv_pos.mpr hs) 2) (exp_pos _)
  have h := positive_weighted_square_of_ne volume
    (network p.1 (fun i => direction (p.2 i)))
    (network (fun _ : Fin 3 => 1) teacher)
    stdGaussianDensity
    (continuous_network _ _) (continuous_network _ _) hρ hρpos
    (integrable_residual_square _ _ _ _) (seed_ball_networks_differ hp)
  simpa only [network,one_mul] using mul_pos (by norm_num : (0 : ℝ) < 1/2) h

end PaperLeanFormalization.SeedCertificate

/-! Generated by consolidate_count.rb from checked local proof snippets.
This is the exact dependency closure of the fresh plain sine-moment count. -/
noncomputable section

open Real Set Filter
open scoped BigOperators Topology

noncomputable section
open Real
open scoped BigOperators

namespace PaperLeanFormalization.Plain.LocalKernelCalculus

def plainKernel (x : ℝ) : ℝ := KernelCalculus.angularKernel x + (π / 2) * cos x
def plainTorque (x : ℝ) : ℝ := sin x * arcsin (cos x) + (π / 2) * sin x
def plainCurvature (x : ℝ) : ℝ := 2 * |sin x| - plainKernel x

/-- The derivative exists also at coincident and opposite directions. -/
theorem plainKernel_derivative (x : ℝ) :
    HasDerivAt plainKernel (-plainTorque x) x := by
  convert (KernelCalculus.hasDerivAt_angularKernel x).add
    ((hasDerivAt_cos x).const_mul (π / 2)) using 1
  simp only [plainTorque]
  ring

/-- The global second derivative uses the endpoint cancellation proved in
the new kernel calculus, not a differentiability assumption at the kinks. -/
theorem plainKernel_second_derivative (x : ℝ) :
    HasDerivAt (fun t => -plainTorque t) (plainCurvature x) x := by
  convert (KernelCalculus.hasDerivAt_angularKernel_first x).sub
    ((hasDerivAt_sin x).const_mul (π / 2)) using 1
  · funext t
    simp only [plainTorque]
    ring
  · simp only [plainCurvature, plainKernel]
    ring

theorem continuous_plainKernel : Continuous plainKernel :=
  continuous_iff_continuousAt.mpr (fun x => (plainKernel_derivative x).continuousAt)

theorem continuous_plainTorque : Continuous plainTorque := by
  unfold plainTorque
  exact (continuous_sin.mul (continuous_arcsin.comp continuous_cos)).add
    (continuous_const.mul continuous_sin)

theorem continuous_plainCurvature : Continuous plainCurvature := by
  unfold plainCurvature
  exact (continuous_const.mul continuous_sin.abs).sub continuous_plainKernel

def residual {n m : ℕ} (c : Fin n → ℝ) (beta s : Fin m → ℝ) (theta : Fin n → ℝ)
    (x : ℝ) : ℝ :=
  (∑ i, c i * plainKernel (x - theta i)) - ∑ k, s k * plainKernel (x - beta k)

def torque {n m : ℕ} (c : Fin n → ℝ) (beta s : Fin m → ℝ) (theta : Fin n → ℝ)
    (x : ℝ) : ℝ :=
  (∑ i, c i * plainTorque (x - theta i)) - ∑ k, s k * plainTorque (x - beta k)

def curvature {n m : ℕ} (c : Fin n → ℝ) (beta s : Fin m → ℝ) (theta : Fin n → ℝ)
    (x : ℝ) : ℝ :=
  (∑ i, c i * plainCurvature (x - theta i)) - ∑ k, s k * plainCurvature (x - beta k)

theorem finite_residual_derivative {n m : ℕ} (K D : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (D x) x)
    (c : Fin n → ℝ) (beta s : Fin m → ℝ) (theta : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun y => (∑ i, c i * K (y - theta i)) - ∑ k, s k * K (y - beta k))
      ((∑ i, c i * D (x - theta i)) - ∑ k, s k * D (x - beta k)) x := by
  have hterm (a w : ℝ) : HasDerivAt (fun y => w * K (y - a)) (w * D (x - a)) x := by
    simpa only [mul_one] using
      ((hK (x - a)).comp x ((hasDerivAt_id x).sub_const a)).const_mul w
  exact (HasDerivAt.sum (fun i _ => hterm (theta i) (c i))).sub
    (HasDerivAt.sum (fun k _ => hterm (beta k) (s k)))

/-- The complete two-step derivative chain of the actual finite plain
residual. The signs match the torque convention `T = -R'`. -/
theorem residual_derivative_chain {n m : ℕ} (c : Fin n → ℝ)
    (beta s : Fin m → ℝ) (theta : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (residual c beta s theta) (-torque c beta s theta x) x ∧
      HasDerivAt (fun y => -torque c beta s theta y) (curvature c beta s theta x) x := by
  have hfirst := finite_residual_derivative plainKernel (fun x => -plainTorque x)
    plainKernel_derivative c beta s theta x
  have hsecond := finite_residual_derivative (fun x => -plainTorque x) plainCurvature
    plainKernel_second_derivative c beta s theta x
  have hneg (y : ℝ) : ((∑ i, c i * -plainTorque (y - theta i)) -
      ∑ k, s k * -plainTorque (y - beta k)) = -torque c beta s theta y := by
    simp only [torque, mul_neg, Finset.sum_neg_distrib]
    ring
  constructor
  · simpa only [hneg] using hfirst
  · simpa only [hneg] using hsecond

/-- Joint continuity is finite arithmetic in the model parameters and the
probe angle, with no separate curvature provider. -/
theorem residual_curvature_continuous {n m : ℕ} (beta s : Fin m → ℝ) :
    Continuous (fun z : (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) =>
      curvature z.1.1 beta s z.1.2 z.2) := by
  unfold curvature
  apply Continuous.sub
  · apply continuous_finset_sum
    intro i _
    exact (((continuous_apply i).comp (continuous_fst.comp continuous_fst))).mul
      (continuous_plainCurvature.comp
        (continuous_snd.sub ((continuous_apply i).comp (continuous_snd.comp continuous_fst))))
  · apply continuous_finset_sum
    intro k _
    exact continuous_const.mul
      (continuous_plainCurvature.comp (continuous_snd.sub continuous_const))

end PaperLeanFormalization.Plain.LocalKernelCalculus

namespace PaperLeanFormalization.Plain

def phiCosJSecondDeriv (t : ℝ) : ℝ := LocalKernelCalculus.plainCurvature t

def residualCurvatureJ {n m : ℕ} (c : Fin n → ℝ) (β s : Fin m → ℝ)
    (θ : Fin n → ℝ) (x : ℝ) : ℝ := LocalKernelCalculus.curvature c β s θ x

end PaperLeanFormalization.Plain


open Real
open scoped BigOperators

noncomputable section

namespace PaperLeanFormalization.Plain.ParameterCalculus

open LocalKernelCalculus

abbrev Parameters (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

def loss {n m : ℕ} (beta s : Fin m → ℝ) (p : Parameters n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, p.1 i * p.1 j * plainKernel (p.2 i - p.2 j) -
    ∑ i, ∑ k, p.1 i * s k * plainKernel (p.2 i - beta k)

theorem kernel_even (x : ℝ) : plainKernel (-x) = plainKernel x := by
  simp only [plainKernel, KernelCalculus.angularKernel, cos_neg]

theorem torque_odd (x : ℝ) : plainTorque (-x) = -plainTorque x := by
  simp only [plainTorque, sin_neg, cos_neg]
  ring

theorem loss_differentiable {n m : ℕ} (beta s : Fin m → ℝ) (p : Parameters n) :
    DifferentiableAt ℝ (loss beta s) p := by
  have hm (i : Fin n) : DifferentiableAt ℝ (fun q : Parameters n => q.1 i) p :=
    (differentiableAt_pi.mp differentiableAt_fst) i
  have ht (i : Fin n) : DifferentiableAt ℝ (fun q : Parameters n => q.2 i) p :=
    (differentiableAt_pi.mp differentiableAt_snd) i
  unfold loss
  apply DifferentiableAt.sub
  · apply DifferentiableAt.const_mul
    apply DifferentiableAt.sum
    intro i _
    apply DifferentiableAt.sum
    intro j _
    exact ((hm i).mul (hm j)).mul
      ((plainKernel_derivative _).differentiableAt.comp p ((ht i).sub (ht j)))
  · apply DifferentiableAt.sum
    intro i _
    apply DifferentiableAt.sum
    intro k _
    exact ((hm i).mul_const (s k)).mul
      ((plainKernel_derivative _).differentiableAt.comp p ((ht i).sub_const (beta k)))

/-- Exchanging the two student indices halves the self-interaction derivative.
This is the entire symmetry argument behind the residual/torque gradient. -/
theorem self_gradient_symmetry {n : ℕ} (c theta dc dt : Fin n → ℝ) :
    (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n,
      ((dc i * c j + c i * dc j) * plainKernel (theta i - theta j) -
        c i * c j * plainTorque (theta i - theta j) * (dt i - dt j))) =
      ∑ i : Fin n, ∑ j : Fin n, (dc i * c j * plainKernel (theta i - theta j) -
        c i * dt i * c j * plainTorque (theta i - theta j)) := by
  let A (i j : Fin n) := dc i * c j * plainKernel (theta i - theta j) -
    c i * dt i * c j * plainTorque (theta i - theta j)
  have hterm (i j : Fin n) :
      (dc i * c j + c i * dc j) * plainKernel (theta i - theta j) -
        c i * c j * plainTorque (theta i - theta j) * (dt i - dt j) = A i j + A j i := by
    have hK : plainKernel (theta j - theta i) = plainKernel (theta i - theta j) := by
      rw [← neg_sub (theta i) (theta j), kernel_even]
    have hT : plainTorque (theta j - theta i) = -plainTorque (theta i - theta j) := by
      rw [← neg_sub (theta i) (theta j), torque_odd]
    simp only [A, hK, hT]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => A j i)]
  change (1 / 2 : ℝ) * ((∑ i, ∑ j, A i j) + ∑ i, ∑ j, A i j) = ∑ i, ∑ j, A i j
  ring

theorem line_derivative {n m : ℕ} (beta s : Fin m → ℝ)
    (c theta dc dt : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => loss beta s
      ((fun i => c i + t * dc i), fun i => theta i + t * dt i))
      (∑ i : Fin n, (dc i * residual c beta s theta (theta i) -
        c i * dt i * torque c beta s theta (theta i))) 0 := by
  have hm (i : Fin n) : HasDerivAt (fun t : ℝ => c i + t * dc i) (dc i) 0 := by
    simpa only [one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (dc i)).const_add (c i)
  have ht (i : Fin n) : HasDerivAt (fun t : ℝ => theta i + t * dt i) (dt i) 0 := by
    simpa only [one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (dt i)).const_add (theta i)
  have hself (i j : Fin n) : HasDerivAt
      (fun t : ℝ => (c i + t * dc i) * (c j + t * dc j) *
        plainKernel ((theta i + t * dt i) - (theta j + t * dt j)))
      ((dc i * c j + c i * dc j) * plainKernel (theta i - theta j) -
        c i * c j * plainTorque (theta i - theta j) * (dt i - dt j)) 0 := by
    have hk := (plainKernel_derivative ((theta i + 0 * dt i) - (theta j + 0 * dt j))).comp (0 : ℝ)
      ((ht i).sub (ht j))
    convert ((hm i).mul (hm j)).mul hk using 1
    simp only [Function.comp_apply, zero_mul, add_zero]
    ring
  have hteacher (i : Fin n) (k : Fin m) : HasDerivAt
      (fun t : ℝ => (c i + t * dc i) * s k *
        plainKernel ((theta i + t * dt i) - beta k))
      (dc i * s k * plainKernel (theta i - beta k) -
        c i * dt i * s k * plainTorque (theta i - beta k)) 0 := by
    have hk := (plainKernel_derivative ((theta i + 0 * dt i) - beta k)).comp (0 : ℝ)
      ((ht i).sub_const (beta k))
    convert ((hm i).mul_const (s k)).mul hk using 1
    simp only [Function.comp_apply, zero_mul, add_zero]
    ring
  have hraw := ((HasDerivAt.sum (u := Finset.univ) fun i _ =>
    HasDerivAt.sum (u := Finset.univ) fun j _ => hself i j).const_mul
    (1 / 2 : ℝ)).sub (HasDerivAt.sum (u := Finset.univ) fun i _ =>
      HasDerivAt.sum (u := Finset.univ) fun k _ => hteacher i k)
  rw [self_gradient_symmetry] at hraw
  convert hraw using 1
  simp only [LocalKernelCalculus.residual, torque, mul_sub, Finset.mul_sum,
    Finset.sum_sub_distrib, mul_assoc]
  ring

/-- The actual Fréchet derivative, evaluated on an arbitrary joint mass-angle
direction. No separately declared gradient model is assumed. -/
theorem fderiv_loss_apply {n m : ℕ} (beta s : Fin m → ℝ) (p h : Parameters n) :
    fderiv ℝ (loss beta s) p h =
      ∑ i : Fin n, (h.1 i * residual p.1 beta s p.2 (p.2 i) -
        p.1 i * h.2 i * torque p.1 beta s p.2 (p.2 i)) := by
  have hline : HasDerivAt (fun t : ℝ => p + t • h) h 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add p
  have hd := (loss_differentiable beta s p).hasFDerivAt
  have hd0 : HasFDerivAt (loss beta s) (fderiv ℝ (loss beta s) p) (p + (0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using hd
  have hd' := hd0.comp_hasDerivAt 0 hline
  have heq : (fun t : ℝ => loss beta s (p + t • h)) =
      (fun t : ℝ => loss beta s
        ((fun i => p.1 i + t * h.1 i), fun i => p.2 i + t * h.2 i)) := rfl
  simp only [Function.comp_def] at hd'
  rw [heq] at hd'
  exact hd'.unique (line_derivative beta s p.1 p.2 h.1 h.2)

theorem critical_iff_parts {n m : ℕ} (beta s : Fin m → ℝ) (c theta : Fin n → ℝ) :
    fderiv ℝ (loss beta s) (c, theta) = 0 ↔
      (∀ i, residual c beta s theta (theta i) = 0) ∧
        ∀ i, c i * torque c beta s theta (theta i) = 0 := by
  classical
  constructor
  · intro hcrit
    have hzero (h : Parameters n) :
        (∑ i : Fin n, (h.1 i * residual c beta s theta (theta i) -
          c i * h.2 i * torque c beta s theta (theta i))) = 0 := by
      have h := congrArg (fun D : Parameters n →L[ℝ] ℝ => D h) hcrit
      simpa only [fderiv_loss_apply, ContinuousLinearMap.zero_apply] using h
    constructor
    · intro a
      simpa using hzero ((fun i => if i = a then 1 else 0), fun _ => 0)
    · intro a
      have h := hzero ((fun _ => 0), fun i => if i = a then 1 else 0)
      simpa using h
  · rintro ⟨hR, hT⟩
    apply ContinuousLinearMap.ext
    intro h
    rw [fderiv_loss_apply]
    simp only [hR, mul_zero, ContinuousLinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [show c i * h.2 i * torque c beta s theta (theta i) =
      h.2 i * (c i * torque c beta s theta (theta i)) by ring, hT i]
    ring

theorem critical_iff_double_zero {n m : ℕ} {beta s : Fin m → ℝ}
    {c theta : Fin n → ℝ} (hc : ∀ i, c i ≠ 0) :
    fderiv ℝ (loss beta s) (c, theta) = 0 ↔
      ∀ i, residual c beta s theta (theta i) = 0 ∧ torque c beta s theta (theta i) = 0 := by
  rw [critical_iff_parts]
  constructor
  · rintro ⟨hR, hT⟩ i
    exact ⟨hR i, (mul_eq_zero.mp (hT i)).resolve_left (hc i)⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => by rw [(h i).2, mul_zero]⟩

end PaperLeanFormalization.Plain.ParameterCalculus

noncomputable section
open scoped BigOperators

namespace PaperLeanFormalization.Plain.LocalKernelCalculus

/-- Endpoint cancellation makes the actual plain angular kernel globally C²,
including direction collisions and antipodal directions. -/
theorem plainKernel_contDiff_two : ContDiff ℝ 2 plainKernel := by
  have hfirst : deriv plainKernel = fun x => -plainTorque x := by
    funext x
    exact (plainKernel_derivative x).deriv
  have hsecond : deriv (fun x => -plainTorque x) = plainCurvature := by
    funext x
    exact (plainKernel_second_derivative x).deriv
  have hC1 : ContDiff ℝ 1 (fun x => -plainTorque x) := by
    apply contDiff_one_iff_deriv.mpr
    constructor
    · intro x
      exact (plainKernel_second_derivative x).differentiableAt
    · rw [hsecond]
      exact continuous_plainCurvature
  apply (contDiff_succ_iff_deriv (n := 1)).mpr
  constructor
  · intro x
    exact (plainKernel_derivative x).differentiableAt
  · rw [hfirst]
    exact hC1

end PaperLeanFormalization.Plain.LocalKernelCalculus

namespace PaperLeanFormalization.Plain.ParameterCalculus

open LocalKernelCalculus

/-- The actual finite plain loss is globally C² in every mass and angle,
without a sign, separation, teacher-width, or derivative-witness hypothesis. -/
theorem loss_contDiff_two {n m : ℕ} (beta s : Fin m → ℝ) :
    ContDiff ℝ 2 (loss (n := n) beta s) := by
  have hm (i : Fin n) : ContDiff ℝ 2 (fun q : Parameters n => q.1 i) :=
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  have ht (i : Fin n) : ContDiff ℝ 2 (fun q : Parameters n => q.2 i) :=
    (contDiff_apply ℝ ℝ i).comp contDiff_snd
  unfold loss
  apply ContDiff.sub
  · apply ContDiff.mul contDiff_const
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact ((hm i).mul (hm j)).mul (plainKernel_contDiff_two.comp ((ht i).sub (ht j)))
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro k _
    exact ((hm i).mul contDiff_const).mul
      (plainKernel_contDiff_two.comp ((ht i).sub contDiff_const))

end PaperLeanFormalization.Plain.ParameterCalculus

namespace PaperLeanFormalization.Plain

/-- The locally differentiated finite loss has one residual and one torque
zero at every nonzero-mass student. This changes only definitional notation. -/
theorem critical_iff_student_double_zeros {n m : ℕ}
    {β s : Fin m → ℝ} {c θ : Fin n → ℝ} (hc : ∀ i, c i ≠ 0) :
    PaperLeanFormalization.IsSignedMassCriticalNoncentered β s c θ ↔
      ∀ i, PaperLeanFormalization.residualPotentialJ c β s θ (θ i) = 0 ∧
        PaperLeanFormalization.massTorqueFieldJ c β s θ (θ i) = 0 :=
  ParameterCalculus.critical_iff_double_zero hc

end PaperLeanFormalization.Plain





/-! Counting step: PositiveIntervals. -/
namespace PositiveIntervals

/-- The nearest zero on either side of a positive value bounds an interval
on which the function is strictly positive. Only continuity is needed. -/
theorem exists_positive_zero_interval {S : ℝ → ℝ} (hS : Continuous S)
    {a p b : ℝ} (hap : a < p) (hpb : p < b)
    (ha : S a ≤ 0) (hp : 0 < S p) (hb : S b ≤ 0) :
    ∃ l r : ℝ, a ≤ l ∧ l < p ∧ p < r ∧ r ≤ b ∧
      S l = 0 ∧ S r = 0 ∧ ∀ t ∈ Ioo l r, 0 < S t := by
  let ZL : Set ℝ := Icc a p ∩ S ⁻¹' {0}
  let ZR : Set ℝ := Icc p b ∩ S ⁻¹' {0}
  have hclosed : IsClosed (S ⁻¹' {0}) := isClosed_singleton.preimage hS
  have hcL : IsCompact ZL := isCompact_Icc.inter_right hclosed
  have hcR : IsCompact ZR := isCompact_Icc.inter_right hclosed
  have hnL : ZL.Nonempty := by
    obtain ⟨z, hz, hSz⟩ := intermediate_value_Icc hap.le hS.continuousOn ⟨ha, hp.le⟩
    exact ⟨z, hz, hSz⟩
  have hnR : ZR.Nonempty := by
    obtain ⟨z, hz, hSz⟩ := intermediate_value_Icc' hpb.le hS.continuousOn ⟨hb, hp.le⟩
    exact ⟨z, hz, hSz⟩
  obtain ⟨l, hl, hlmax⟩ := hcL.exists_isGreatest hnL
  obtain ⟨r, hr, hrmin⟩ := hcR.exists_isLeast hnR
  have hSl : S l = 0 := hl.2
  have hSr : S r = 0 := hr.2
  have hlp : l < p := by
    apply lt_of_le_of_ne hl.1.2
    intro heq
    have hpzero : S p = 0 := by rw [← heq]; exact hSl
    exact (ne_of_gt hp) hpzero
  have hpr : p < r := by
    apply lt_of_le_of_ne hr.1.1
    intro heq
    have hpzero : S p = 0 := by rw [heq]; exact hSr
    exact (ne_of_gt hp) hpzero
  refine ⟨l, r, hl.1.1, hlp, hpr, hr.1.2, hSl, hSr, ?_⟩
  intro t ht
  by_contra hnot
  have hSt : S t ≤ 0 := le_of_not_gt hnot
  rcases le_or_gt t p with htp | hpt
  · obtain ⟨z, hz, hSz⟩ := intermediate_value_Icc htp hS.continuousOn ⟨hSt, hp.le⟩
    have hzL : z ∈ ZL := ⟨⟨le_trans hl.1.1 (le_trans ht.1.le hz.1), hz.2⟩, hSz⟩
    have hzl : z ≤ l := hlmax hzL
    linarith only [ht.1, hz.1, hzl]
  · obtain ⟨z, hz, hSz⟩ := intermediate_value_Icc' hpt.le hS.continuousOn ⟨hSt, hp.le⟩
    have hzR : z ∈ ZR := ⟨⟨hz.1, le_trans hz.2 (le_trans ht.2.le hr.1.2)⟩, hSz⟩
    have hrz : r ≤ z := hrmin hzR
    linarith only [ht.2, hz.2, hrz]

/-- Overlapping positive intervals with zero left endpoints have the same
left endpoint. The right endpoints need not be zeros. -/
theorem left_endpoints_eq_of_overlap {S : ℝ → ℝ} {l r l' r' p : ℝ}
    (hl : S l = 0) (hl' : S l' = 0)
    (hpos : ∀ t ∈ Ioo l r, 0 < S t)
    (hpos' : ∀ t ∈ Ioo l' r', 0 < S t)
    (hp : p ∈ Ioo l r) (hp' : p ∈ Ioo l' r') : l = l' := by
  rcases lt_trichotomy l l' with hlt | heq | hgt
  · have h := hpos l' ⟨hlt, lt_trans hp'.1 hp.2⟩
    linarith only [h, hl']
  · exact heq
  · have h := hpos' l ⟨hgt, lt_trans hp.1 hp'.2⟩
    linarith only [h, hl]

/-- Overlapping positive intervals with zero right endpoints have the same
right endpoint. In particular this identifies the endpoint adjacent to a
given positive flank without constructing a second left endpoint. -/
theorem right_endpoints_eq_of_overlap {S : ℝ → ℝ} {l r l' r' p : ℝ}
    (hr : S r = 0) (hr' : S r' = 0)
    (hpos : ∀ t ∈ Ioo l r, 0 < S t)
    (hpos' : ∀ t ∈ Ioo l' r', 0 < S t)
    (hp : p ∈ Ioo l r) (hp' : p ∈ Ioo l' r') : r = r' := by
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · have h := hpos' r ⟨lt_trans hp'.1 hp.2, hlt⟩
    linarith only [h, hr]
  · exact heq
  · have h := hpos r' ⟨lt_trans hp.1 hp'.2, hgt⟩
    linarith only [h, hr']

/-- Positive zero-endpoint intervals are either equal or disjoint. This
overlap formulation uses only pointwise positivity and order, not continuity. -/
theorem positive_zero_intervals_eq_of_overlap {S : ℝ → ℝ} {l r l' r' p : ℝ}
    (hl : S l = 0) (hr : S r = 0) (hl' : S l' = 0) (hr' : S r' = 0)
    (hpos : ∀ t ∈ Ioo l r, 0 < S t)
    (hpos' : ∀ t ∈ Ioo l' r', 0 < S t)
    (hp : p ∈ Ioo l r) (hp' : p ∈ Ioo l' r') : l = l' ∧ r = r' :=
  ⟨left_endpoints_eq_of_overlap hl hl' hpos hpos' hp hp',
    right_endpoints_eq_of_overlap hr hr' hpos hpos' hp hp'⟩

end PositiveIntervals

/-! Counting step: FreshBoundary. -/
namespace FreshBoundary

/-- The actual derivative of a harmonic field, used by the corner-free
boundary identity below. -/
theorem hasDerivAt_harmonic (A B x : ℝ) :
    HasDerivAt (fun t => A * cos t + B * sin t) (-A * sin x + B * cos x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul A).add
    ((Real.hasDerivAt_sin x).const_mul B) using 1
  ring

/-- The actual second derivative of the harmonic field is its negative. -/
theorem hasDerivAt_harmonic_derivative (A B x : ℝ) :
    HasDerivAt (deriv (fun t => A * cos t + B * sin t))
      (-(A * cos x + B * sin x)) x := by
  convert hasDerivAt_harmonic B (-A) x using 1
  · ext t
    rw [(hasDerivAt_harmonic A B t).deriv]
    ring
  · ring

/-- The classical homogeneous equation on a corner-free harmonic piece. -/
theorem harmonic_ode (A B x : ℝ) :
    deriv (deriv (fun t => A * cos t + B * sin t)) x +
      (A * cos x + B * sin x) = 0 := by
  rw [(hasDerivAt_harmonic_derivative A B x).deriv]
  ring

/-- Differentiating the boundary expression cancels its mixed terms. Here D
is a genuine derivative of W, and d₂ is a genuine derivative of D. -/
theorem hasDerivAt_boundary_expression {W D : ℝ → ℝ} {x d₂ : ℝ}
    (γ : ℝ) (hW : HasDerivAt W (D x) x) (hD : HasDerivAt D d₂ x) :
    HasDerivAt (fun t => D t * sin (γ - t) + W t * cos (γ - t))
      ((d₂ + W x) * sin (γ - x)) x := by
  have harg : HasDerivAt (fun t : ℝ => γ - t) (-1) x := by
    convert (hasDerivAt_const x γ).sub (hasDerivAt_id x) using 1
    ring
  convert (hD.mul harg.sin).add (hW.mul harg.cos) using 1
  ring

/-- The full integral-to-boundary equation in `eq:corner-free-boundary`.
The fundamental theorem of calculus applies to the genuinely differentiated
boundary expression; no endpoint trigonometric simplification proves this step. -/
theorem harmonic_integral_boundary (A B a b γ : ℝ) :
    (∫ x in a..b,
      (deriv (deriv (fun t => A * cos t + B * sin t)) x +
        (A * cos x + B * sin x)) * sin (γ - x)) =
      (deriv (fun t => A * cos t + B * sin t) b * sin (γ - b) +
        (A * cos b + B * sin b) * cos (γ - b)) -
      (deriv (fun t => A * cos t + B * sin t) a * sin (γ - a) +
        (A * cos a + B * sin a) * cos (γ - a)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact hasDerivAt_boundary_expression γ
      (hasDerivAt_harmonic A B x).differentiableAt.hasDerivAt
      (hasDerivAt_harmonic_derivative A B x).differentiableAt.hasDerivAt
  · have hzero : (fun x =>
        (deriv (deriv (fun t => A * cos t + B * sin t)) x +
          (A * cos x + B * sin x)) * sin (γ - x)) = (fun _ : ℝ => (0 : ℝ)) := by
      funext x
      rw [harmonic_ode, zero_mul]
    rw [hzero]
    exact intervalIntegrable_const

/-- `eq:corner-free-boundary`: the harmonic boundary expression is conserved
between any two endpoints, using the genuine derivatives of the field. -/
theorem eq_corner_free_boundary (A B a b γ : ℝ) :
    deriv (fun t => A * cos t + B * sin t) b * sin (γ - b) +
      (A * cos b + B * sin b) * cos (γ - b) =
    deriv (fun t => A * cos t + B * sin t) a * sin (γ - a) +
      (A * cos a + B * sin a) * cos (γ - a) := by
  have h := harmonic_integral_boundary A B a b γ
  simp only [harmonic_ode, zero_mul, intervalIntegral.integral_zero] at h
  exact sub_eq_zero.mp h.symm

/-- Explicit derivative-trace form for finite piecewise-harmonic telescoping. -/
theorem eq_corner_free_boundary_explicit (A B a b γ : ℝ) :
    (-A * sin b + B * cos b) * sin (γ - b) +
      (A * cos b + B * sin b) * cos (γ - b) =
    (-A * sin a + B * cos a) * sin (γ - a) +
      (A * cos a + B * sin a) * cos (γ - a) := by
  have h := eq_corner_free_boundary A B a b γ
  rwa [(hasDerivAt_harmonic A B b).deriv, (hasDerivAt_harmonic A B a).deriv] at h

/-- The genuine derivative of the reversed shifted sine used before an atom's
next corner. -/
theorem hasDerivAt_reverse_sine (z x : ℝ) :
    HasDerivAt (fun t => sin (z - t)) (-cos (z - x)) x := by
  convert hasDerivAt_harmonic (sin z) (-cos z) x using 1
  · ext t
    rw [Real.sin_sub]
    ring
  · rw [Real.cos_sub]
    ring

/-- Corner-free conservation for the descending sine branch before the next
atom. The value term is first to match the finite-jump telescoping expression. -/
theorem eq_corner_free_shifted_sine_boundary (z a b γ : ℝ) :
    sin (z - b) * cos (γ - b) + (-cos (z - b)) * sin (γ - b) =
      sin (z - a) * cos (γ - a) + (-cos (z - a)) * sin (γ - a) := by
  have hW (t : ℝ) : sin z * cos t + -cos z * sin t = sin (z - t) := by
    rw [Real.sin_sub]
    ring
  have hD (t : ℝ) : -sin z * sin t + -cos z * cos t = -cos (z - t) := by
    rw [Real.cos_sub]
    ring
  have h := eq_corner_free_boundary_explicit (sin z) (-cos z) a b γ
  rw [hW a, hW b, hD a, hD b] at h
  exact (add_comm _ _).trans (h.trans (add_comm _ _))

/-- Corner-free conservation for the ascending sine branch after the atom. -/
theorem eq_corner_free_forward_sine_boundary (z a b γ : ℝ) :
    sin (b - z) * cos (γ - b) + cos (b - z) * sin (γ - b) =
      sin (a - z) * cos (γ - a) + cos (a - z) * sin (γ - a) := by
  have hW (t : ℝ) : -sin z * cos t + cos z * sin t = sin (t - z) := by
    rw [Real.sin_sub]
    ring
  have hD (t : ℝ) : -(-sin z) * sin t + cos z * cos t = cos (t - z) := by
    rw [Real.cos_sub]
    ring
  have h := eq_corner_free_boundary_explicit (-sin z) (cos z) a b γ
  rw [hW a, hW b, hD a, hD b] at h
  exact (add_comm _ _).trans (h.trans (add_comm _ _))

end FreshBoundary

/-! Counting step: FreshJumpSummation. -/
namespace FreshJumpSummation

/-- Finite telescoping with distinct left and right boundary traces. -/
theorem trace_telescoping {N : ℕ} (Bminus Bplus : Fin (N + 2) → ℝ)
    (hpiece : ∀ i : Fin (N + 1), Bminus i.succ = Bplus i.castSucc) :
    Bminus (Fin.last (N + 1)) - Bplus 0 =
      ∑ i : Fin N, (Bplus i.succ.castSucc - Bminus i.succ.castSucc) := by
  have hsum : (∑ i : Fin (N + 1), Bminus i.succ) =
      ∑ i : Fin (N + 1), Bplus i.castSucc :=
    Finset.sum_congr rfl (fun i _ => hpiece i)
  rw [Fin.sum_univ_castSucc (fun i : Fin (N + 1) => Bminus i.succ),
    Fin.sum_univ_succ (fun i : Fin (N + 1) => Bplus i.castSucc)] at hsum
  change (∑ i : Fin N, Bminus i.succ.castSucc) + Bminus (Fin.last (N + 1)) =
    Bplus 0 + ∑ i : Fin N, Bplus i.succ.castSucc at hsum
  rw [Finset.sum_sub_distrib]
  linarith

/-- Summing conserved corner-free boundary expressions cancels interior
values and leaves the derivative jumps, with their actual signs. -/
theorem boundary_jump_sum {N : ℕ} (τ V Dminus Dplus : Fin (N + 2) → ℝ) (γ : ℝ)
    (hpiece : ∀ i : Fin (N + 1),
      Dminus i.succ * Real.sin (γ - τ i.succ) + V i.succ * Real.cos (γ - τ i.succ) =
      Dplus i.castSucc * Real.sin (γ - τ i.castSucc) +
        V i.castSucc * Real.cos (γ - τ i.castSucc)) :
    (Dminus (Fin.last (N + 1)) * Real.sin (γ - τ (Fin.last (N + 1))) +
      V (Fin.last (N + 1)) * Real.cos (γ - τ (Fin.last (N + 1)))) -
      (Dplus 0 * Real.sin (γ - τ 0) + V 0 * Real.cos (γ - τ 0)) =
    ∑ i : Fin N, (Dplus i.succ.castSucc - Dminus i.succ.castSucc) *
      Real.sin (γ - τ i.succ.castSucc) := by
  have h := trace_telescoping
    (fun i => Dminus i * Real.sin (γ - τ i) + V i * Real.cos (γ - τ i))
    (fun i => Dplus i * Real.sin (γ - τ i) + V i * Real.cos (γ - τ i)) hpiece
  calc
    _ = ∑ i : Fin N,
        ((Dplus i.succ.castSucc * Real.sin (γ - τ i.succ.castSucc) +
          V i.succ.castSucc * Real.cos (γ - τ i.succ.castSucc)) -
        (Dminus i.succ.castSucc * Real.sin (γ - τ i.succ.castSucc) +
          V i.succ.castSucc * Real.cos (γ - τ i.succ.castSucc))) := h
    _ = _ := Finset.sum_congr rfl (fun i _ => by ring)

/-- `eq:jump-summation`, with `τ.last = γ`. -/
theorem eq_jump_summation {N : ℕ} (τ V Dminus Dplus : Fin (N + 2) → ℝ) (γ : ℝ)
    (hlast : τ (Fin.last (N + 1)) = γ)
    (hpiece : ∀ i : Fin (N + 1),
      Dminus i.succ * Real.sin (γ - τ i.succ) + V i.succ * Real.cos (γ - τ i.succ) =
      Dplus i.castSucc * Real.sin (γ - τ i.castSucc) +
        V i.castSucc * Real.cos (γ - τ i.castSucc)) :
    0 = V (Fin.last (N + 1)) - V 0 * Real.cos (γ - τ 0) -
      Dplus 0 * Real.sin (γ - τ 0) -
      ∑ i : Fin N, (Dplus i.succ.castSucc - Dminus i.succ.castSucc) *
        Real.sin (γ - τ i.succ.castSucc) := by
  have h := boundary_jump_sum τ V Dminus Dplus γ hpiece
  rw [hlast, sub_self, Real.sin_zero, Real.cos_zero, mul_zero, mul_one, zero_add] at h
  linarith

/-- `eq:duhamel-sum`, obtained from the preceding labeled identity by
substituting the actual derivative jumps `Dplus - Dminus = 2w`. -/
theorem eq_duhamel_sum {N : ℕ} (τ V Dminus Dplus : Fin (N + 2) → ℝ)
    (w : Fin N → ℝ) (γ : ℝ) (hlast : τ (Fin.last (N + 1)) = γ)
    (hpiece : ∀ i : Fin (N + 1),
      Dminus i.succ * Real.sin (γ - τ i.succ) + V i.succ * Real.cos (γ - τ i.succ) =
      Dplus i.castSucc * Real.sin (γ - τ i.castSucc) +
        V i.castSucc * Real.cos (γ - τ i.castSucc))
    (hjump : ∀ i : Fin N, Dplus i.succ.castSucc - Dminus i.succ.castSucc = 2 * w i) :
    V (Fin.last (N + 1)) = V 0 * Real.cos (γ - τ 0) +
      Dplus 0 * Real.sin (γ - τ 0) +
      ∑ i : Fin N, 2 * w i * Real.sin (γ - τ i.succ.castSucc) := by
  have h := eq_jump_summation τ V Dminus Dplus γ hlast hpiece
  have hsum : (∑ i : Fin N, (Dplus i.succ.castSucc - Dminus i.succ.castSucc) *
      Real.sin (γ - τ i.succ.castSucc)) =
      ∑ i : Fin N, 2 * w i * Real.sin (γ - τ i.succ.castSucc) :=
    Finset.sum_congr rfl (fun i _ => by rw [hjump i])
  rw [hsum] at h
  linarith

/-- The zero-corner case, consuming the complete finite summation chain. -/
theorem no_corner_duhamel (a b Va Vb Da : ℝ)
    (hboundary : Vb = Da * Real.sin (b - a) + Va * Real.cos (b - a)) :
    Vb = Va * Real.cos (b - a) + Da * Real.sin (b - a) := by
  have h := eq_duhamel_sum (N := 0) ![a, b] ![Va, Vb] ![0, 0] ![Da, 0]
    (fun i => Fin.elim0 i) b rfl (by
      intro i
      fin_cases i
      simpa using hboundary) (by intro i; exact Fin.elim0 i)
  simpa using h

/-- The one-corner case.  The two scalar conservation equations come from
the actual harmonic branches on the two sides of the corner. -/
theorem single_corner_duhamel (a z b Va Vz Vb Da DminusZ DplusZ w : ℝ)
    (hleft : DminusZ * Real.sin (b - z) + Vz * Real.cos (b - z) =
      Da * Real.sin (b - a) + Va * Real.cos (b - a))
    (hright : Vb = DplusZ * Real.sin (b - z) + Vz * Real.cos (b - z))
    (hjump : DplusZ - DminusZ = 2 * w) :
    Vb = Va * Real.cos (b - a) + Da * Real.sin (b - a) +
      2 * w * Real.sin (b - z) := by
  have h := eq_duhamel_sum (N := 1) ![a, z, b] ![Va, Vz, Vb]
    ![0, DminusZ, 0] ![Da, DplusZ, 0] (fun _ => w) b rfl (by
      intro i
      fin_cases i
      · simpa using hleft
      · simpa using hright) (by
      intro i
      fin_cases i
      simpa using hjump)
  simpa using h

end FreshJumpSummation

/-! Counting step: FreshDuhamel. -/
namespace FreshDuhamel

/-- The first lift of an atom strictly after the starting point. -/
def nextTurn (a alpha : ℝ) : ℤ := ⌊(a - alpha) / π⌋ + 1

def nextKnot (a alpha : ℝ) : ℝ := alpha + nextTurn a alpha * π

theorem lt_nextKnot (a alpha : ℝ) : a < nextKnot a alpha := by
  have h := (div_lt_iff Real.pi_pos).mp (Int.lt_floor_add_one ((a - alpha) / π))
  dsimp [nextKnot, nextTurn]
  push_cast
  linarith only [h]

theorem nextKnot_le_add_pi (a alpha : ℝ) : nextKnot a alpha ≤ a + π := by
  have h := (le_div_iff Real.pi_pos).mp (Int.floor_le ((a - alpha) / π))
  dsimp [nextKnot, nextTurn]
  push_cast
  nlinarith only [h]

theorem abs_sine_eq_nextKnot (a alpha t : ℝ) :
    |sin (t - alpha)| = |sin (nextKnot a alpha - t)| := by
  have hperiod : Function.Periodic (fun x : ℝ => |sin x|) π := by
    intro x
    change |sin (x + π)| = |sin x|
    rw [Real.sin_add_pi, abs_neg]
  have h := hperiod.int_mul (nextTurn a alpha) (alpha - t)
  rw [show alpha - t + (nextTurn a alpha : ℝ) * π = nextKnot a alpha - t by
    dsimp [nextKnot]; ring] at h
  rw [show alpha - t = -(t - alpha) by ring, Real.sin_neg, abs_neg] at h
  exact h.symm

theorem abs_sine_before_nextKnot {a alpha t : ℝ} (hat : a ≤ t)
    (htz : t ≤ nextKnot a alpha) :
    |sin (t - alpha)| = sin (nextKnot a alpha - t) := by
  rw [abs_sine_eq_nextKnot a alpha t]
  exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith only [htz]) (by linarith only [nextKnot_le_add_pi a alpha, hat]))

theorem abs_sine_after_nextKnot {a alpha t : ℝ} (hzt : nextKnot a alpha ≤ t)
    (hta : t - a < π) :
    |sin (t - alpha)| = sin (t - nextKnot a alpha) := by
  rw [abs_sine_eq_nextKnot a alpha t,
    show nextKnot a alpha - t = -(t - nextKnot a alpha) by ring,
    Real.sin_neg, abs_neg]
  exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith only [hzt]) (by linarith only [lt_nextKnot a alpha, hta]))

/-- The initial coefficient is the genuine right derivative, including the
case where the starting point itself is an atom. -/
theorem hasDerivWithinAt_abs_sine_right (a alpha : ℝ) :
    HasDerivWithinAt (fun t => |sin (t - alpha)|)
      (-cos (nextKnot a alpha - a)) (Ioi a) a := by
  have hd := FreshBoundary.hasDerivAt_reverse_sine (nextKnot a alpha) a
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, lt_nextKnot a alpha⟩] with t ht
    exact abs_sine_before_nextKnot ht.1.le ht.2.le
  · exact abs_sine_before_nextKnot le_rfl (lt_nextKnot a alpha).le

theorem sine_sum_right_derivative {ι : Type*} [Fintype ι]
    (w alpha : ι → ℝ) (a : ℝ) :
    derivWithin (fun t => ∑ i, w i * |sin (t - alpha i)|) (Ioi a) a =
      ∑ i, w i * (-cos (nextKnot a (alpha i) - a)) := by
  have hd : HasDerivWithinAt (fun t => ∑ i, w i * |sin (t - alpha i)|)
      (∑ i, w i * (-cos (nextKnot a (alpha i) - a))) (Ioi a) a :=
    HasDerivWithinAt.sum fun i _ =>
      (hasDerivWithinAt_abs_sine_right a (alpha i)).const_mul (w i)
  exact hd.derivWithin (uniqueDiffWithinAt_Ioi a)

/-- The actual one-atom Duhamel formula, obtained by summing its zero or one
corner-free pieces. Its source location is the explicit next integer lift. -/
theorem abs_sine_duhamel (alpha : ℝ) {a y : ℝ} (hay : a < y) (hpi : y - a < π) :
    |sin (y - alpha)| = |sin (a - alpha)| * cos (y - a) +
      (-cos (nextKnot a alpha - a)) * sin (y - a) +
      if nextKnot a alpha < y then 2 * sin (y - nextKnot a alpha) else 0 := by
  let z := nextKnot a alpha
  have hstart : |sin (a - alpha)| = sin (z - a) :=
    abs_sine_before_nextKnot le_rfl (lt_nextKnot a alpha).le
  by_cases hzy : z < y
  · have hfinish : |sin (y - alpha)| = sin (y - z) :=
      abs_sine_after_nextKnot hzy.le hpi
    have hleft := FreshBoundary.eq_corner_free_shifted_sine_boundary z a z y
    have hright := FreshBoundary.eq_corner_free_forward_sine_boundary z z y y
    have hj := FreshJumpSummation.single_corner_duhamel a z y
      (sin (z - a)) 0 (sin (y - z)) (-cos (z - a)) (-1) 1 1
      (by simpa only [sub_self, sin_zero, cos_zero, zero_mul, one_mul, neg_one_mul,
        zero_add, add_comm] using hleft)
      (by convert hright using 1 <;>
        simp only [sub_self, sin_zero, cos_zero, zero_mul, one_mul, mul_zero,
          mul_one, zero_add, add_zero])
      (by ring)
    rw [hfinish, hstart, if_pos hzy]
    simpa only [mul_one] using hj
  · have hfinish : |sin (y - alpha)| = sin (z - y) :=
      abs_sine_before_nextKnot hay.le (le_of_not_gt hzy)
    have hboundary := FreshBoundary.eq_corner_free_shifted_sine_boundary z a y y
    have hj := FreshJumpSummation.no_corner_duhamel a y
      (sin (z - a)) (sin (z - y)) (-cos (z - a))
      (by simpa only [sub_self, sin_zero, cos_zero, mul_zero, mul_one, add_zero,
        zero_add, add_comm] using hboundary)
    rw [hfinish, hstart, if_neg hzy, add_zero]
    exact hj

/-- `eq:duhamel-sum` for a finite sine load on a short interval, with its
genuine initial right derivative and the finite set of crossed atom lifts.
Coincident atoms are retained as separate summands, whose weights add. -/
theorem eq_duhamel_sum {ι : Type*} [Fintype ι] (w alpha : ι → ℝ)
    {a y : ℝ} (hay : a < y) (hpi : y - a < π) :
    (∑ i, w i * |sin (y - alpha i)|) =
      (∑ i, w i * |sin (a - alpha i)|) * cos (y - a) +
      derivWithin (fun t => ∑ i, w i * |sin (t - alpha i)|) (Ioi a) a * sin (y - a) +
      ∑ i in Finset.univ.filter (fun i => nextKnot a (alpha i) < y),
        2 * w i * sin (y - nextKnot a (alpha i)) := by
  classical
  rw [sine_sum_right_derivative, Finset.sum_filter, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_sine_duhamel (alpha i) hay hpi]
  split_ifs <;> ring

/-- The manuscript's hump-ownership argument through the finite Duhamel
formula: its initial right derivative is positive; a zero terminal value
therefore forces a negative source strictly inside the hump. -/
theorem positive_hump_owns_negative_atom {ι : Type*} [Fintype ι]
    (w alpha : ι → ℝ) {a b : ℝ} (hab : a < b) (hpi : b - a < π)
    (ha : (∑ i, w i * |sin (a - alpha i)|) = 0)
    (hb : (∑ i, w i * |sin (b - alpha i)|) = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < ∑ i, w i * |sin (t - alpha i)|) :
    ∃ i, w i < 0 ∧ ∃ q : ℤ, a < alpha i + q * π ∧ alpha i + q * π < b ∧
      0 < ∑ j, w j * |sin (alpha i + q * π - alpha j)| := by
  classical
  let D : ℝ := derivWithin (fun t => ∑ i, w i * |sin (t - alpha i)|) (Ioi a) a
  have hevent : ∀ᶠ t in 𝓝 a, t < b ∧ ∀ i, t < nextKnot a (alpha i) :=
    (eventually_lt_nhds hab).and (Filter.eventually_all.mpr fun i =>
      eventually_lt_nhds (lt_nextKnot a (alpha i)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let y : ℝ := a + ε / 2
  have hay : a < y := by dsimp [y]; linarith only [hε]
  have hy := hball (y := y) (by
    rw [Real.dist_eq, show y - a = ε / 2 by dsimp [y]; ring,
      abs_of_pos (by linarith only [hε] : 0 < ε / 2)]
    linarith only [hε])
  have hempty : Finset.univ.filter (fun i => nextKnot a (alpha i) < y) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    exact (not_lt_of_ge (hy.2 i).le) hi
  have hyformula := eq_duhamel_sum w alpha hay (by linarith only [hy.1, hpi])
  rw [ha, zero_mul, zero_add, hempty, Finset.sum_empty, add_zero] at hyformula
  have hD : 0 < D := by
    have hp := hpos y ⟨hay, hy.1⟩
    have hs := Real.sin_pos_of_pos_of_lt_pi
      (show 0 < y - a by linarith only [hay]) (by linarith only [hy.1, hpi])
    change (∑ i, w i * |sin (y - alpha i)|) = D * sin (y - a) at hyformula
    nlinarith only [hyformula, hp, hs]
  have hbformula := eq_duhamel_sum w alpha hab hpi
  rw [ha, hb, zero_mul, zero_add] at hbformula
  change 0 = D * sin (b - a) + _ at hbformula
  have hDb : 0 < D * sin (b - a) := mul_pos hD
    (Real.sin_pos_of_pos_of_lt_pi (by linarith only [hab]) hpi)
  have hnegative :
      (∑ i in Finset.univ.filter (fun i => nextKnot a (alpha i) < b),
        2 * w i * sin (b - nextKnot a (alpha i))) <
      ∑ _i in Finset.univ.filter (fun i => nextKnot a (alpha i) < b), (0 : ℝ) := by
    rw [Finset.sum_const_zero]
    linarith only [hbformula, hDb]
  obtain ⟨i, hi, hterm⟩ := Finset.exists_lt_of_sum_lt hnegative
  have hiz : nextKnot a (alpha i) < b := (Finset.mem_filter.mp hi).2
  have hsin : 0 < sin (b - nextKnot a (alpha i)) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hiz])
      (by linarith only [lt_nextKnot a (alpha i), hpi])
  have hwi : w i < 0 := by
    by_contra hnot
    have hnonneg := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (not_lt.mp hnot)) hsin.le
    exact (not_lt_of_ge hnonneg) hterm
  exact ⟨i, hwi, nextTurn a (alpha i), lt_nextKnot a (alpha i), hiz,
    hpos (nextKnot a (alpha i)) ⟨lt_nextKnot a (alpha i), hiz⟩⟩

end FreshDuhamel

/-! Counting step: PositiveComponents. -/
namespace PlainPositiveComponents

/-- A positive point of a periodic load with a negative value lies in a
zero-endpoint positive interval shorter than one period. -/
theorem positive_point_in_short_interval {S : ℝ → ℝ}
    (hS : Continuous S) (hperiod : Function.Periodic S π)
    {p q : ℝ} (hp : 0 < S p) (hq : S q < 0) :
    ∃ l r : ℝ, l < p ∧ p < r ∧ r - l < π ∧ S l = 0 ∧ S r = 0 ∧
      ∀ t ∈ Set.Ioo l r, 0 < S t := by
  let k : ℤ := ⌊(p - q) / π⌋
  let a : ℝ := q + (k : ℝ) * π
  have hSa : S a = S q := hperiod.int_mul k q
  have hSaπ : S (a + π) = S q := (hperiod a).trans hSa
  have hal : a ≤ p := by
    have hfloor := (le_div_iff Real.pi_pos).mp (Int.floor_le ((p - q) / π))
    dsimp [a, k]
    linarith only [hfloor]
  have hpr : p < a + π := by
    have hfloor := (div_lt_iff Real.pi_pos).mp (Int.lt_floor_add_one ((p - q) / π))
    dsimp [a, k]
    nlinarith only [hfloor]
  have hap : a < p := lt_of_le_of_ne hal (by
    intro heq
    rw [heq] at hSa
    linarith only [hSa, hp, hq])
  obtain ⟨l, r, hal', hlp, hpr', hra, hSl, hSr, hpos⟩ :=
    PositiveIntervals.exists_positive_zero_interval hS hap hpr
      (by rw [hSa]; exact hq.le) hp (by rw [hSaπ]; exact hq.le)
  have halstrict : a < l := lt_of_le_of_ne hal' (by
    intro heq
    rw [heq, hSl] at hSa
    linarith only [hSa, hq])
  exact ⟨l, r, hlp, hpr', by linarith only [halstrict, hra], hSl, hSr, hpos⟩

end PlainPositiveComponents

/-! Counting step: ShortGapAlternation. -/
namespace ShortGapAlternation

/-- A continuous function nonnegative in the interior is nonnegative at the
endpoints too. -/
theorem nonnegative_on_closed_of_open {f : ℝ → ℝ} (hf : Continuous f)
    {u v : ℝ} (huv : u < v) (hnn : ∀ x ∈ Ioo u v, 0 ≤ f x) :
    ∀ x ∈ Icc u v, 0 ≤ f x := by
  have hclosed : IsClosed {x : ℝ | 0 ≤ f x} := isClosed_le continuous_const hf
  have hsub : closure (Ioo u v) ⊆ {x : ℝ | 0 ≤ f x} :=
    closure_minimal hnn hclosed
  rw [closure_Ioo (ne_of_lt huv)] at hsub
  exact hsub

/-- Strict integral positivity from one interior strict value, using the
standard continuous integral comparison theorem. -/
theorem integral_positive_of_nonnegative_on_open {f : ℝ → ℝ}
    (hf : Continuous f) {u v : ℝ} (huv : u < v)
    (hnn : ∀ x ∈ Ioo u v, 0 ≤ f x)
    {t : ℝ} (ht : t ∈ Ioo u v) (hpos : 0 < f t) :
    0 < ∫ x in u..v, f x := by
  have hclosed := nonnegative_on_closed_of_open hf huv hnn
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => 0) (g := f) huv continuousOn_const hf.continuousOn
    (fun x hx => hclosed x ⟨le_of_lt hx.1, hx.2⟩)
    ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, hpos⟩
  simpa only [intervalIntegral.integral_zero] using h

/-- Negation preserves the vanishing shifted sine moments. -/
theorem moment_neg {S : ℝ → ℝ} {u v : ℝ}
    (hmom : ∀ a : ℝ, (∫ x in u..v, S x * Real.sin (x - a)) = 0) :
    ∀ a : ℝ, (∫ x in u..v, (-S x) * Real.sin (x - a)) = 0 := by
  intro a
  simp only [neg_mul, intervalIntegral.integral_neg, hmom a, neg_zero]

/-- A nonflat load with zero sine moments has a negative interior value. -/
theorem exists_negative_of_zero_moments {S : ℝ → ℝ}
    (hcont : Continuous S) {u v : ℝ} (huv : u < v) (hpi : v - u ≤ π)
    (hnf : ∃ t, u < t ∧ t < v ∧ S t ≠ 0)
    (hmom : ∀ a : ℝ, (∫ x in u..v, S x * Real.sin (x - a)) = 0) :
    ∃ q ∈ Ioo u v, S q < 0 := by
  by_contra hno
  push_neg at hno
  obtain ⟨t, hut, htv, htne⟩ := hnf
  have htpos : 0 < S t := lt_of_le_of_ne (hno t ⟨hut, htv⟩) (Ne.symm htne)
  have hspos : 0 < Real.sin (t - u) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hi := integral_positive_of_nonnegative_on_open
    (f := fun x => S x * Real.sin (x - u))
    (hcont.mul (Real.continuous_sin.comp (continuous_id.sub continuous_const)))
    huv (fun x hx => mul_nonneg (hno x hx)
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
        (by linarith [hx.2]))) ⟨hut, htv⟩ (mul_pos htpos hspos)
  rw [hmom u] at hi
  exact (lt_irrefl 0) hi

/-- The supremum separator forces a positive-before-negative pair.  The proof
does not require the separator itself to have zero load. -/
theorem exists_positive_before_negative_of_zero_moments {S : ℝ → ℝ}
    (hcont : Continuous S) {u v : ℝ} (huv : u < v) (hpi : v - u ≤ π)
    (hnf : ∃ t, u < t ∧ t < v ∧ S t ≠ 0)
    (hmom : ∀ a : ℝ, (∫ x in u..v, S x * Real.sin (x - a)) = 0) :
    ∃ p q : ℝ, u < p ∧ p < q ∧ q < v ∧ 0 < S p ∧ S q < 0 := by
  classical
  obtain ⟨q, hqI, hq⟩ := exists_negative_of_zero_moments hcont huv hpi hnf hmom
  have hnfNeg : ∃ t, u < t ∧ t < v ∧ -S t ≠ 0 := by
    simpa only [neg_ne_zero] using hnf
  obtain ⟨p, hpI, hpNeg⟩ := exists_negative_of_zero_moments
    hcont.neg huv hpi hnfNeg (moment_neg hmom)
  have hp : 0 < S p := by linarith
  by_contra hpair
  have hno : ∀ a b : ℝ, a ∈ Ioo u v → b ∈ Ioo u v →
      0 < S a → S b < 0 → b < a := by
    intro a b ha hb haPos hbNeg
    rcases lt_trichotomy a b with hab | hab | hba
    · exact False.elim (hpair ⟨a, b, ha.1, hab, hb.2, haPos, hbNeg⟩)
    · subst b
      exact False.elim ((not_lt_of_ge (le_of_lt haPos)) hbNeg)
    · exact hba
  let N : Set ℝ := {x | x ∈ Ioo u v ∧ S x < 0}
  have hNne : N.Nonempty := ⟨q, hqI, hq⟩
  have hNbdd : BddAbove N := ⟨v, fun x hx => le_of_lt hx.1.2⟩
  let z : ℝ := sSup N
  have hqz : q ≤ z := le_csSup hNbdd ⟨hqI, hq⟩
  have hzp : z ≤ p := csSup_le hNne
    (fun x hx => le_of_lt (hno p x hpI hx.1 hp hx.2))
  have huz : u < z := lt_of_lt_of_le hqI.1 hqz
  have hzv : z < v := lt_of_le_of_lt hzp hpI.2
  have hleft : ∀ x ∈ Ioo u v, x < z → S x ≤ 0 := by
    intro x hx hxz
    by_contra hxPos
    push_neg at hxPos
    have hzx : z ≤ x := csSup_le hNne
      (fun y hy => le_of_lt (hno x y hx hy.1 hxPos hy.2))
    exact (not_lt_of_ge hzx) hxz
  have hright : ∀ x ∈ Ioo u v, z < x → 0 ≤ S x := by
    intro x hx hzx
    by_contra hxNeg
    push_neg at hxNeg
    have hxz : x ≤ z := le_csSup hNbdd ⟨hx, hxNeg⟩
    exact (not_lt_of_ge hxz) hzx
  have hnonnegative : ∀ x ∈ Ioo u v, 0 ≤ S x * Real.sin (x - z) := by
    intro x hx
    rcases lt_trichotomy x z with hxz | hxz | hzx
    · have hs : Real.sin (x - z) ≤ 0 := by
        rw [show x - z = -(z - x) by ring, Real.sin_neg]
        exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith) (by linarith [hx.1]))
      exact mul_nonneg_of_nonpos_of_nonpos (hleft x hx hxz) hs
    · rw [hxz, sub_self, Real.sin_zero, mul_zero]
    · exact mul_nonneg (hright x hx hzx)
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hx.2]))
  have hstrict : ∃ t ∈ Ioo u v, 0 < S t * Real.sin (t - z) := by
    rcases lt_or_eq_of_le hqz with hqzStrict | hqzEq
    · refine ⟨q, hqI, mul_pos_of_neg_of_neg hq ?_⟩
      rw [show q - z = -(z - q) by ring, Real.sin_neg]
      exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi
        (by linarith) (by linarith [hqI.1]))
    · have hqp : q < p := hno p q hpI hqI hp hq
      refine ⟨p, hpI, mul_pos hp ?_⟩
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hpI.2])
  obtain ⟨t, htI, htpos⟩ := hstrict
  have hi := integral_positive_of_nonnegative_on_open
    (f := fun x => S x * Real.sin (x - z))
    (hcont.mul (Real.continuous_sin.comp (continuous_id.sub continuous_const)))
    huv hnonnegative htI htpos
  rw [hmom z] at hi
  exact (lt_irrefl 0) hi

/-- A nonflat continuous load with zero shifted sine moments on a gap of
length at most `π` has an alternating strict-sign triple in the open gap. -/
theorem exists_alternating_triple_of_zero_moments {S : ℝ → ℝ}
    (hcont : Continuous S) {u v : ℝ} (huv : u < v) (hpi : v - u ≤ π)
    (hnf : ∃ t, u < t ∧ t < v ∧ S t ≠ 0)
    (hmom : ∀ a : ℝ, (∫ x in u..v, S x * Real.sin (x - a)) = 0) :
    (∃ l p r : ℝ, u < l ∧ l < p ∧ p < r ∧ r < v ∧
      S l < 0 ∧ 0 < S p ∧ S r < 0) ∨
    (∃ l p r : ℝ, u < l ∧ l < p ∧ p < r ∧ r < v ∧
      0 < S l ∧ S p < 0 ∧ 0 < S r) := by
  obtain ⟨p, q, hup, hpq, hqv, hp, hq⟩ :=
    exists_positive_before_negative_of_zero_moments hcont huv hpi hnf hmom
  have hnfNeg : ∃ t, u < t ∧ t < v ∧ -S t ≠ 0 := by
    simpa only [neg_ne_zero] using hnf
  obtain ⟨a, b, hua, hab, hbv, haNeg, hbNeg⟩ :=
    exists_positive_before_negative_of_zero_moments
      hcont.neg huv hpi hnfNeg (moment_neg hmom)
  have ha : S a < 0 := by linarith
  have hb : 0 < S b := by linarith
  rcases lt_trichotomy a p with hap | hap | hpa
  · exact Or.inl ⟨a, p, q, hua, hap, hpq, hqv, ha, hp, hq⟩
  · subst a
    exact False.elim ((not_lt_of_ge (le_of_lt hp)) ha)
  · exact Or.inr ⟨p, a, b, hup, hpa, hab, hbv, hp, ha, hb⟩

end ShortGapAlternation

/-! Counting step: GapComponentSides. -/
namespace GapComponentSides

/-- A positive component is represented directly by its two zero endpoints. -/
def PositiveInterval (S : ℝ → ℝ) :=
  {lr : ℝ × ℝ // lr.1 < lr.2 ∧ S lr.1 = 0 ∧ S lr.2 = 0 ∧
    ∀ t ∈ Ioo lr.1 lr.2, 0 < S t}

/-- Side 0 is the right boundary and side 1 is the left boundary, matching
the half-open gap convention used in the finite component-side census. -/
def boundary {S : ℝ → ℝ} (C : PositiveInterval S) (side : Fin 2) : ℝ :=
  if side = 0 then C.val.2 else C.val.1

theorem positive_point_has_interval {S : ℝ → ℝ} (hS : Continuous S)
    (hperiod : Function.Periodic S π) {p q : ℝ} (hp : 0 < S p) (hq : S q < 0) :
    ∃ C : PositiveInterval S, p ∈ Ioo C.val.1 C.val.2 ∧ C.val.2 - C.val.1 < π := by
  obtain ⟨l, r, hlp, hpr, hlen, hl, hr, hpos⟩ :=
    PlainPositiveComponents.positive_point_in_short_interval hS hperiod hp hq
  exact ⟨⟨(l, r), hlp.trans hpr, hl, hr, hpos⟩, ⟨hlp, hpr⟩, hlen⟩

/-- A negative point to the right of an interior positive witness lies
strictly beyond the component's right endpoint. -/
theorem right_boundary_lt_negative {S : ℝ → ℝ} (C : PositiveInterval S)
    {p q : ℝ} (hp : p ∈ Ioo C.val.1 C.val.2) (hpq : p < q) (hq : S q < 0) :
    C.val.2 < q := by
  rcases lt_trichotomy C.val.2 q with hlt | heq | hgt
  · exact hlt
  · have hz := C.property.2.2.1
    rw [heq] at hz
    linarith only [hq, hz]
  · have hpos := C.property.2.2.2 q ⟨lt_trans hp.1 hpq, hgt⟩
    linarith only [hq, hpos]

/-- The corresponding left-endpoint exclusion. -/
theorem negative_lt_left_boundary {S : ℝ → ℝ} (C : PositiveInterval S)
    {p q : ℝ} (hp : p ∈ Ioo C.val.1 C.val.2) (hqp : q < p) (hq : S q < 0) :
    q < C.val.1 := by
  rcases lt_trichotomy q C.val.1 with hlt | heq | hgt
  · exact hlt
  · have hz := C.property.2.1
    rw [← heq] at hz
    linarith only [hq, hz]
  · have hpos := C.property.2.2.2 q ⟨hgt, lt_trans hqp hp.2⟩
    linarith only [hq, hpos]

/-- An N-P-N triple selects both sides of the component containing its
positive point. Both boundaries lie strictly within the triple. -/
theorem negative_positive_negative_interval {S : ℝ → ℝ}
    (hS : Continuous S) (hperiod : Function.Periodic S π)
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (ha : S a < 0) (hb : 0 < S b) (hc : S c < 0) :
    ∃ C : PositiveInterval S, a < C.val.1 ∧ C.val.2 < c ∧
      C.val.2 - C.val.1 < π := by
  obtain ⟨C, hbC, hlen⟩ := positive_point_has_interval hS hperiod hb ha
  exact ⟨C, negative_lt_left_boundary C hbC hab ha,
    right_boundary_lt_negative C hbC hbc hc, hlen⟩

/-- A P-N-P triple selects the right side of the first positive component
and the left side of the second. The components are strictly separated. -/
theorem positive_negative_positive_intervals {S : ℝ → ℝ}
    (hS : Continuous S) (hperiod : Function.Periodic S π)
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (ha : 0 < S a) (hb : S b < 0) (hc : 0 < S c) :
    ∃ C D : PositiveInterval S, C ≠ D ∧
      a < C.val.2 ∧ C.val.2 < b ∧ b < D.val.1 ∧ D.val.1 < c ∧
      C.val.2 - C.val.1 < π ∧ D.val.2 - D.val.1 < π := by
  obtain ⟨C, haC, hlenC⟩ := positive_point_has_interval hS hperiod ha hb
  obtain ⟨D, hcD, hlenD⟩ := positive_point_has_interval hS hperiod hc hb
  have hCb := right_boundary_lt_negative C haC hab hb
  have hbD := negative_lt_left_boundary D hcD hbc hb
  have hne : C ≠ D := by
    intro heq
    rw [← heq] at hbD
    have horder := C.property.1
    linarith only [hCb, hbD, horder]
  exact ⟨C, D, hne, haC.2, hCb, hbD, hcD.1, hlenC, hlenD⟩

/-- An alternating strict-sign triple supplies one right side and one left
side, both strictly inside the gap. Every selected interval is shorter than π.
No gap-length assumption is needed in this topological selection step. -/
theorem alternating_triple_component_sides {S : ℝ → ℝ}
    (hS : Continuous S) (hperiod : Function.Periodic S π)
    {u a b c v : ℝ} (hua : u < a) (hab : a < b) (hbc : b < c) (hcv : c < v)
    (hsign : (S a < 0 ∧ 0 < S b ∧ S c < 0) ∨
      (0 < S a ∧ S b < 0 ∧ 0 < S c)) :
    ∃ owner : Fin 2 → PositiveInterval S,
      (∀ side, boundary (owner side) side ∈ Ioo u v) ∧
      ∀ side, (owner side).val.2 - (owner side).val.1 < π := by
  rcases hsign with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · obtain ⟨C, haC, hCc, hlen⟩ :=
      negative_positive_negative_interval hS hperiod hab hbc ha hb hc
    refine ⟨fun _ => C, ?_, fun _ => hlen⟩
    intro side
    by_cases hs : side = 0
    · simpa only [boundary, if_pos hs] using
        (show C.val.2 ∈ Ioo u v from
          ⟨lt_trans hua (lt_trans haC C.property.1), lt_trans hCc hcv⟩)
    · simpa only [boundary, if_neg hs] using
        (show C.val.1 ∈ Ioo u v from
          ⟨lt_trans hua haC, lt_trans C.property.1 (lt_trans hCc hcv)⟩)
  · obtain ⟨C, D, _, haC, hCb, hbD, hDc, hlenC, hlenD⟩ :=
      positive_negative_positive_intervals hS hperiod hab hbc ha hb hc
    let owner : Fin 2 → PositiveInterval S := fun side => if side = 0 then C else D
    refine ⟨owner, ?_, ?_⟩
    · intro side
      by_cases hs : side = 0
      · simpa only [owner, boundary, if_pos hs] using
          (show C.val.2 ∈ Ioo u v from
            ⟨lt_trans hua haC, lt_trans hCb (lt_trans hbc hcv)⟩)
      · simpa only [owner, boundary, if_neg hs] using
          (show D.val.1 ∈ Ioo u v from
            ⟨lt_trans hua (lt_trans hab hbD), lt_trans hDc hcv⟩)
    · intro side
      by_cases hs : side = 0
      · simpa only [owner, if_pos hs] using hlenC
      · simpa only [owner, if_neg hs] using hlenD

/-- Existential-triple form, matching the conclusion of the short-gap
zero-moment sign-alternation theorem. -/
theorem alternating_signs_component_sides {S : ℝ → ℝ}
    (hS : Continuous S) (hperiod : Function.Periodic S π) {u v : ℝ}
    (htriple :
      (∃ a b c : ℝ, u < a ∧ a < b ∧ b < c ∧ c < v ∧ S a < 0 ∧ 0 < S b ∧ S c < 0) ∨
      (∃ a b c : ℝ, u < a ∧ a < b ∧ b < c ∧ c < v ∧ 0 < S a ∧ S b < 0 ∧ 0 < S c)) :
    ∃ owner : Fin 2 → PositiveInterval S,
      (∀ side, boundary (owner side) side ∈ Ioo u v) ∧
      ∀ side, (owner side).val.2 - (owner side).val.1 < π := by
  rcases htriple with ⟨a, b, c, hua, hab, hbc, hcv, ha, hb, hc⟩ |
    ⟨a, b, c, hua, hab, hbc, hcv, ha, hb, hc⟩
  · exact alternating_triple_component_sides hS hperiod hua hab hbc hcv (Or.inl ⟨ha, hb, hc⟩)
  · exact alternating_triple_component_sides hS hperiod hua hab hbc hcv (Or.inr ⟨ha, hb, hc⟩)

/-- Different boundary sides are distinct slots, even for one component. -/
theorem selected_component_sides_injective {S : ℝ → ℝ}
    (owner : Fin 2 → PositiveInterval S) :
    Function.Injective (fun side : Fin 2 => (owner side, side)) := by
  intro s t heq
  exact congrArg Prod.snd heq

end GapComponentSides

/-! Counting step: CyclicBoundarySlots. -/
namespace CyclicBoundarySlots

/-- The orientation bit of an integer multiple of `π`, also for negative turns. -/
def turnParity (k : ℤ) : Fin 2 :=
  ⟨(k % 2).toNat,
    (Int.toNat_lt' (by decide : (2 : ℕ) ≠ 0)).mpr
      (Int.emod_lt_of_pos k (by decide : (0 : ℤ) < 2))⟩

theorem turnParity_eq_imp_emod_eq {k l : ℤ} (h : turnParity k = turnParity l) :
    k % 2 = l % 2 := by
  have hnat : (k % 2).toNat = (l % 2).toNat := congrArg Fin.val h
  have hint := congrArg (fun a : ℕ => (a : ℤ)) hnat
  simpa only [Int.toNat_of_nonneg (Int.emod_nonneg k (by decide : (2 : ℤ) ≠ 0)),
    Int.toNat_of_nonneg (Int.emod_nonneg l (by decide : (2 : ℤ) ≠ 0))] using hint

/-- Equal parity is an exact even-difference statement over the integers. -/
theorem turnParity_eq_imp_even_difference {k l : ℤ}
    (h : turnParity k = turnParity l) : ∃ z : ℤ, k = l + z * 2 := by
  have hmod := turnParity_eq_imp_emod_eq h
  refine ⟨k / 2 - l / 2, ?_⟩
  have hk := Int.emod_add_ediv k 2
  have hl := Int.emod_add_ediv l 2
  linarith

/-- The corresponding geometric statement is an integer `2π` translation. -/
theorem turnParity_eq_imp_pi_shift {k l : ℤ} (h : turnParity k = turnParity l) :
    ∃ z : ℤ, (k : ℝ) * Real.pi = (l : ℝ) * Real.pi + (z : ℝ) * (2 * Real.pi) := by
  obtain ⟨z, hz⟩ := turnParity_eq_imp_even_difference h
  refine ⟨z, ?_⟩
  have hreal : (k : ℝ) = (l : ℝ) + (z : ℝ) * 2 := by exact_mod_cast hz
  rw [hreal]
  ring

/-- Periodic equality inside one left-closed/right-open lifted turn is ordinary
equality.  This includes both boundary cases allowed by the half-open interval. -/
theorem eq_of_mem_Ico_of_int_period {a T x y : ℝ} {z : ℤ}
    (hT : 0 < T) (hx : x ∈ Set.Ico a (a + T))
    (hy : y ∈ Set.Ico a (a + T)) (hxy : x = y + (z : ℝ) * T) : x = y := by
  have hzlo : (-1 : ℝ) < (z : ℝ) := (mul_lt_mul_right hT).mp (by
    nlinarith [hx.1, hy.2])
  have hzhi : (z : ℝ) < (1 : ℝ) := (mul_lt_mul_right hT).mp (by
    nlinarith [hx.2, hy.1])
  have hzloInt : (-1 : ℤ) < z := by exact_mod_cast hzlo
  have hzhiInt : z < (1 : ℤ) := by exact_mod_cast hzhi
  have hznonnegative : (0 : ℤ) ≤ z := by
    have hstep := Int.add_one_le_iff.mpr hzloInt
    linarith
  have hznonpositive : z ≤ (0 : ℤ) := Int.lt_add_one_iff.mp hzhiInt
  have hz : z = 0 := le_antisymm hznonpositive hznonnegative
  simpa only [hz, Int.cast_zero, zero_mul, add_zero] using hxy

/-- A gap of an increasing lifted partition lies in its containing full turn. -/
theorem gap_Ico_subset_turn {n : ℕ} {E : Fin (n + 1) → ℝ} {T : ℝ}
    (hE : StrictMono E) (hperiod : E (Fin.last n) = E 0 + T) (i : Fin n) :
    Set.Ico (E i.castSucc) (E i.succ) ⊆ Set.Ico (E 0) (E 0 + T) := by
  intro x hx
  refine ⟨le_trans (hE.monotone (Fin.zero_le i.castSucc)) hx.1, ?_⟩
  have hupper := hE.monotone (Fin.le_last i.succ)
  rw [hperiod] at hupper
  exact lt_of_lt_of_le hx.2 hupper

/-- Equal boundary positions modulo the period have the same gap owner.
The last gap is handled by `E (Fin.last n) = E 0 + T`, with no quotient model. -/
theorem cyclic_gap_Ico_unique {n : ℕ} {E : Fin (n + 1) → ℝ}
    {T x y : ℝ} {z : ℤ} {i j : Fin n}
    (hE : StrictMono E) (hT : 0 < T) (hperiod : E (Fin.last n) = E 0 + T)
    (hi : x ∈ Set.Ico (E i.castSucc) (E i.succ))
    (hj : y ∈ Set.Ico (E j.castSucc) (E j.succ))
    (hxy : x = y + (z : ℝ) * T) : i = j := by
  have heq : x = y := eq_of_mem_Ico_of_int_period hT
    (gap_Ico_subset_turn hE hperiod i hi) (gap_Ico_subset_turn hE hperiod j hj) hxy
  subst y
  rcases lt_trichotomy i j with hij | hij | hji
  · have hij' : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    exact False.elim ((not_lt_of_ge (le_trans (hE.monotone hij') hj.1)) hi.2)
  · exact hij
  · have hji' : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      exact hji
    exact False.elim ((not_lt_of_ge (le_trans (hE.monotone hji') hi.1)) hj.2)

end CyclicBoundarySlots

/-! Counting step: ChargeCensus. -/
namespace PlainCharges

/-- A selected gap side is attached either to a zero-load teacher knot or to
the corresponding boundary of a positive interval owning a teacher knot.
Side zero is the right boundary and side one is the left boundary. -/
structure Charge {m : ℕ} (S : ℝ → ℝ) (beta : Fin m → ℝ) (side : Fin 2) where
  teacher : Fin m
  turn : ℤ
  boundary : ℝ
  event :
    (S (beta teacher + turn * π) = 0 ∧ boundary = beta teacher + turn * π) ∨
    ∃ l r : ℝ, l < beta teacher + turn * π ∧ beta teacher + turn * π < r ∧
      S l = 0 ∧ S r = 0 ∧ (∀ t ∈ Ioo l r, 0 < S t) ∧
      boundary = if side = 0 then r else l

/-- Equal oriented teacher slots identify the selected boundary modulo one
full turn. The mixed zero/positive case is excluded by the load itself. -/
theorem charge_boundary_translate {m : ℕ} {S : ℝ → ℝ} {beta : Fin m → ℝ}
    (hperiod : Function.Periodic S π) {side : Fin 2}
    (A B : Charge S beta side) (hteacher : A.teacher = B.teacher)
    {z : ℤ} (hturn : (A.turn : ℝ) * π = (B.turn : ℝ) * π + z * (2 * π)) :
    A.boundary = B.boundary + z * (2 * π) := by
  let d : ℝ := z * (2 * π)
  have hd (x : ℝ) : S (x + d) = S x := by
    have h := hperiod.int_mul (2 * z) x
    convert h using 1; push_cast; ring
  have hk : beta A.teacher + A.turn * π = beta B.teacher + B.turn * π + d := by
    rw [hteacher, hturn]
    dsimp [d]
    ring
  rcases A.event with hAz | ⟨l, r, hl, hr, hSl, hSr, hp, hb⟩
  · rcases B.event with hBz | ⟨l', r', hl', hr', hSl', hSr', hp', hb'⟩
    · rw [hAz.2, hBz.2]
      exact hk
    · have hpositive := hp' (beta B.teacher + B.turn * π) ⟨hl', hr'⟩
      rw [hk, hd] at hAz
      exact False.elim ((ne_of_gt hpositive) hAz.1)
  · rcases B.event with hBz | ⟨l', r', hl', hr', hSl', hSr', hp', hb'⟩
    · have hpositive := hp (beta A.teacher + A.turn * π) ⟨hl, hr⟩
      rw [hk, hd, hBz.1] at hpositive
      exact False.elim ((lt_irrefl 0) hpositive)
    · have hSlshift : S (l' + d) = 0 := by rw [hd, hSl']
      have hSrshift : S (r' + d) = 0 := by rw [hd, hSr']
      have hpshift : ∀ t ∈ Ioo (l' + d) (r' + d), 0 < S t := by
        intro t ht
        have h := hp' (t - d) ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
        have heq : S t = S (t - d) := by
          simpa only [sub_add_cancel] using hd (t - d)
        rwa [heq]
      have hends := PositiveIntervals.positive_zero_intervals_eq_of_overlap
        hSl hSr hSlshift hSrshift hp hpshift ⟨hl, hr⟩
        (show beta A.teacher + A.turn * π ∈ Ioo (l' + d) (r' + d) from
          ⟨by linarith only [hk, hl'], by linarith only [hk, hr']⟩)
      rw [hb, hb']
      split_ifs
      · simpa only [d] using hends.2
      · simpa only [d] using hends.1

/-- The manuscript's final census: one selected right boundary per half-open
student gap injects directly into teacher index times orientation. No finite
type of positive components, quotient construction, or auxiliary tag tree
is needed. -/
theorem eq_ceiling_count {n m : ℕ} {S : ℝ → ℝ} {beta : Fin m → ℝ}
    (hperiod : Function.Periodic S π) (E : Fin (n + 1) → ℝ)
    (hE : StrictMono E) (hlast : E (Fin.last n) = E 0 + 2 * π)
    (charge : Fin n → Charge S beta 0)
    (hboundary : ∀ i, (charge i).boundary ∈ Ico (E i.castSucc) (E i.succ)) :
    n ≤ 2 * m := by
  let owner : Fin n → Fin m × Fin 2 := fun i =>
    ((charge i).teacher, CyclicBoundarySlots.turnParity (charge i).turn)
  have hinj : Function.Injective owner := by
    intro i j hij
    have ht : (charge i).teacher = (charge j).teacher := congrArg Prod.fst hij
    have hp : CyclicBoundarySlots.turnParity (charge i).turn =
        CyclicBoundarySlots.turnParity (charge j).turn := congrArg Prod.snd hij
    obtain ⟨z, hz⟩ := CyclicBoundarySlots.turnParity_eq_imp_pi_shift hp
    have hb := charge_boundary_translate hperiod (charge i) (charge j) ht hz
    exact CyclicBoundarySlots.cyclic_gap_Ico_unique hE
      (by linarith only [Real.pi_pos]) hlast (hboundary i) (hboundary j) hb
  have hcard := Fintype.card_le_of_injective owner hinj
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using hcard

end PlainCharges

/-! Counting step: PositiveGapCharges. -/
namespace PositiveGapCharges

/-- A positive interval of the explicit student-minus-teacher sine load owns
a teacher atom. Its selected endpoint therefore defines a genuine charge.
Teacher coefficients and directions are unrestricted. -/
theorem positive_interval_teacher_charge {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {l r : ℝ} (hlr : l < r) (hlen : r - l < π) (side : Fin 2)
    (hl : (∑ i, c i * |sin (l - theta i)|) - (∑ k, s k * |sin (l - beta k)|) = 0)
    (hr : (∑ i, c i * |sin (r - theta i)|) - (∑ k, s k * |sin (r - beta k)|) = 0)
    (hpos : ∀ t ∈ Ioo l r,
      0 < (∑ i, c i * |sin (t - theta i)|) - (∑ k, s k * |sin (t - beta k)|)) :
    ∃ A : PlainCharges.Charge
      (fun x => (∑ i, c i * |sin (x - theta i)|) - (∑ k, s k * |sin (x - beta k)|))
      beta side, A.boundary = if side = 0 then r else l := by
  let w : Fin n ⊕ Fin m → ℝ := Sum.elim c (fun k => -s k)
  let alpha : Fin n ⊕ Fin m → ℝ := Sum.elim theta beta
  have hload (t : ℝ) : (∑ i, w i * |sin (t - alpha i)|) =
      (∑ i, c i * |sin (t - theta i)|) - (∑ k, s k * |sin (t - beta k)|) := by
    simp only [w, alpha, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  obtain ⟨i, hi, q, hql, hqr, _⟩ := FreshDuhamel.positive_hump_owns_negative_atom
    w alpha hlr hlen (by rw [hload]; exact hl) (by rw [hload]; exact hr)
    (by intro t ht; rw [hload]; exact hpos t ht)
  cases i with
  | inl j =>
      have hij : c j < 0 := hi
      exact False.elim ((not_lt_of_ge (hc j).le) hij)
  | inr k =>
      have hlk : l < beta k + q * π := hql
      have hkr : beta k + q * π < r := hqr
      exact ⟨⟨k, q, if side = 0 then r else l,
        Or.inr ⟨l, r, hlk, hkr, hl, hr, hpos, rfl⟩⟩, rfl⟩

/-- The interval-subtype form used by the alternating-sign gap selection. -/
theorem positive_component_teacher_charge {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (C : GapComponentSides.PositiveInterval
      (fun x => (∑ i, c i * |sin (x - theta i)|) - (∑ k, s k * |sin (x - beta k)|)))
    (hlen : C.val.2 - C.val.1 < π) (side : Fin 2) :
    ∃ A : PlainCharges.Charge
      (fun x => (∑ i, c i * |sin (x - theta i)|) - (∑ k, s k * |sin (x - beta k)|))
      beta side, A.boundary = GapComponentSides.boundary C side :=
  positive_interval_teacher_charge c theta s beta hc C.property.1 hlen side
    C.property.2.1 C.property.2.2.1 C.property.2.2.2

/-- An alternating triple supplies the two teacher-owned side charges of
the actual gap. The load is given in one explicit formula in this statement. -/
theorem alternating_signs_teacher_charges {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (hc : ∀ i, 0 < c i) {u v : ℝ} :
    let S : ℝ → ℝ := fun x =>
      (∑ i, c i * |sin (x - theta i)|) - (∑ k, s k * |sin (x - beta k)|)
    ((∃ a b d : ℝ, u < a ∧ a < b ∧ b < d ∧ d < v ∧ S a < 0 ∧ 0 < S b ∧ S d < 0) ∨
      (∃ a b d : ℝ, u < a ∧ a < b ∧ b < d ∧ d < v ∧ 0 < S a ∧ S b < 0 ∧ 0 < S d)) →
    ∃ charge : (side : Fin 2) → PlainCharges.Charge S beta side,
      ∀ side, (charge side).boundary ∈ Ioo u v := by
  dsimp only
  intro htriple
  let S : ℝ → ℝ := fun x =>
    (∑ i, c i * |sin (x - theta i)|) - (∑ k, s k * |sin (x - beta k)|)
  have hS : Continuous S := by
    apply Continuous.sub
    · exact continuous_finset_sum _ fun i _ => continuous_const.mul
        ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).abs)
    · exact continuous_finset_sum _ fun i _ => continuous_const.mul
        ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).abs)
  have hperiod : Function.Periodic S π := by
    have hatom (a x : ℝ) : |sin (x + π - a)| = |sin (x - a)| := by
      rw [show x + π - a = (x - a) + π by ring, Real.sin_add_pi, abs_neg]
    intro x
    simp only [S, hatom]
  obtain ⟨owner, hboundary, hlen⟩ :=
    GapComponentSides.alternating_signs_component_sides hS hperiod htriple
  have hcharges : ∀ side : Fin 2, ∃ A : PlainCharges.Charge S beta side,
      A.boundary = GapComponentSides.boundary (owner side) side := by
    intro side
    exact positive_component_teacher_charge c theta s beta hc (owner side) (hlen side) side
  classical
  choose charge hcharge using hcharges
  refine ⟨charge, ?_⟩
  intro side
  rw [hcharge side]
  exact hboundary side

/-- A nonflat short interval with zero sine moments has a teacher-owned
right-boundary charge strictly inside it. This is the nonflat-gap input to
the final one-charge-per-gap count. -/
theorem nonflat_zero_moment_interval_teacher_charge {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {u v : ℝ} (huv : u < v) (hpi : v - u ≤ π) :
    let S : ℝ → ℝ := fun x =>
      (∑ i, c i * |sin (x - theta i)|) - (∑ k, s k * |sin (x - beta k)|)
    (¬ ∀ x ∈ Icc u v, S x = 0) →
    (∀ a : ℝ, (∫ x in u..v, S x * sin (x - a)) = 0) →
    ∃ A : PlainCharges.Charge S beta 0, A.boundary ∈ Ioo u v := by
  dsimp only
  intro hnotflat hmom
  let S : ℝ → ℝ := fun x =>
    (∑ i, c i * |sin (x - theta i)|) - (∑ k, s k * |sin (x - beta k)|)
  have hS : Continuous S := by
    apply Continuous.sub
    · exact continuous_finset_sum _ fun i _ => continuous_const.mul
        ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).abs)
    · exact continuous_finset_sum _ fun i _ => continuous_const.mul
        ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).abs)
  have hnonzero : ∃ t, u < t ∧ t < v ∧ S t ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply hnotflat
    have hzero : ∀ t ∈ Ioo u v, S t = 0 := fun t ht => hno t ht.1 ht.2
    have hclosed : IsClosed {t : ℝ | S t = 0} := isClosed_eq hS continuous_const
    have hclosure := closure_minimal hzero hclosed
    rw [closure_Ioo (ne_of_lt huv)] at hclosure
    exact hclosure
  have htriple := ShortGapAlternation.exists_alternating_triple_of_zero_moments
    hS huv hpi hnonzero hmom
  obtain ⟨charge, hboundary⟩ := alternating_signs_teacher_charges c theta s beta hc htriple
  exact ⟨charge 0, hboundary 0⟩

end PositiveGapCharges

/-! Counting step: FlatSineJump. -/
namespace FlatSineJump

/-- An arbitrarily small exact symmetric jump formula for a finite absolute-sine
sum. Only continuity and the sine addition formula enter the proof. -/
theorem abs_sine_sum_second_difference_nhd {ι : Type*} [Fintype ι]
    (w α : ι → ℝ) (x r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < π ∧ ρ ≤ r ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
      (∑ i, w i * |sin (x + δ - α i)|) + (∑ i, w i * |sin (x - δ - α i)|) -
        2 * cos δ * (∑ i, w i * |sin (x - α i)|) =
      2 * sin δ * ∑ i in Finset.univ.filter (fun i => sin (x - α i) = 0), w i := by
  classical
  have hsign : ∀ᶠ t in 𝓝 x, ∀ i,
      (0 < sin (x - α i) → 0 < sin (t - α i)) ∧
      (sin (x - α i) < 0 → sin (t - α i) < 0) := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℝ => sin (t - α i)) x :=
      (Real.continuous_sin.comp (continuous_id.sub continuous_const)).continuousAt
    have hp : ∀ᶠ t in 𝓝 x, 0 < sin (x - α i) → 0 < sin (t - α i) := by
      by_cases h : 0 < sin (x - α i)
      · filter_upwards [continuousAt_const.eventually_lt hc h] with t ht
        exact fun _ => ht
      · exact Filter.eventually_of_forall fun _ h' => False.elim (h h')
    have hn : ∀ᶠ t in 𝓝 x, sin (x - α i) < 0 → sin (t - α i) < 0 := by
      by_cases h : sin (x - α i) < 0
      · filter_upwards [hc.eventually_lt continuousAt_const h] with t ht
        exact fun _ => ht
      · exact Filter.eventually_of_forall fun _ h' => False.elim (h h')
    filter_upwards [hp, hn] with t hp' hn'
    exact ⟨hp', hn'⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hsign
  let ρ : ℝ := min (ε / 2) (min (r / 2) (π / 2))
  have hρ0 : 0 < ρ := lt_min (by linarith) (lt_min (by linarith) (by linarith [pi_pos]))
  have hρε : ρ ≤ ε / 2 := min_le_left _ _
  have hρr : ρ ≤ r / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρπ : ρ < π :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith [pi_pos])
  refine ⟨ρ, hρ0, hρπ, by linarith, ?_⟩
  intro δ hδ0 hδρ
  have hδε : δ ≤ ε / 2 := le_trans hδρ hρε
  have hδπ : δ < π := lt_of_le_of_lt hδρ hρπ
  have hp := hball (y := x + δ) (by
    rw [Real.dist_eq, show x + δ - x = δ by ring, abs_of_pos hδ0]
    linarith only [hδε, hε])
  have hm := hball (y := x - δ) (by
    rw [Real.dist_eq, show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδ0]
    linarith only [hδε, hε])
  have hsd : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ0 hδπ
  have hterm : ∀ i,
      w i * |sin (x + δ - α i)| + w i * |sin (x - δ - α i)| -
        2 * cos δ * (w i * |sin (x - α i)|) =
      if sin (x - α i) = 0 then 2 * sin δ * w i else 0 := by
    intro i
    by_cases hz : sin (x - α i) = 0
    · rcases sin_eq_zero_iff_cos_eq.mp hz with hc | hc
      all_goals
        rw [if_pos hz, show x + δ - α i = (x - α i) + δ by ring,
          show x - δ - α i = (x - α i) - δ by ring,
          sin_add (x - α i) δ, sin_sub (x - α i) δ, hz, hc]
        simp only [zero_mul, one_mul, neg_one_mul, zero_add, zero_sub, abs_neg,
          abs_zero, mul_zero, sub_zero, abs_of_pos hsd]
        ring
    · rw [if_neg hz]
      rcases lt_or_gt_of_ne hz with hn | hp'
      · rw [abs_of_neg ((hp i).2 hn), abs_of_neg ((hm i).2 hn), abs_of_neg hn,
          show x + δ - α i = (x - α i) + δ by ring,
          show x - δ - α i = (x - α i) - δ by ring,
          sin_add (x - α i) δ, sin_sub (x - α i) δ]
        ring
      · rw [abs_of_pos ((hp i).1 hp'), abs_of_pos ((hm i).1 hp'), abs_of_pos hp',
          show x + δ - α i = (x - α i) + δ by ring,
          show x - δ - α i = (x - α i) - δ by ring,
          sin_add (x - α i) δ, sin_sub (x - α i) δ]
        ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => hterm i

/-- Splitting a signed disjoint union into its student and teacher masses. -/
theorem abs_sine_difference_line_weight {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (x : ℝ) :
    (∑ q in Finset.univ.filter
      (fun q : Fin n ⊕ Fin m => sin (x - Sum.elim θ β q) = 0),
      Sum.elim c (fun k => -s k) q) =
    (∑ i in Finset.univ.filter (fun i => sin (x - θ i) = 0), c i) -
      ∑ k in Finset.univ.filter (fun k => sin (x - β k) = 0), s k := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hneg : (∑ k : Fin m, if sin (x - β k) = 0 then -s k else 0) =
      -(∑ k : Fin m, if sin (x - β k) = 0 then s k else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  rw [hneg, Finset.sum_filter, Finset.sum_filter, sub_eq_add_neg]

/-- A flat interval with positive left endpoint weight has a wholly positive
exterior left neighborhood. -/
theorem flat_abs_sine_sum_left_flank {ι : Type*} [Fintype ι]
    (w α : ι → ℝ) {u v : ℝ} (huv : u < v)
    (hflat : ∀ t ∈ Set.Icc u v, (∑ i, w i * |sin (t - α i)|) = 0)
    (hw : 0 < ∑ i in Finset.univ.filter (fun i => sin (u - α i) = 0), w i) :
    ∃ r : ℝ, 0 < r ∧ ∀ δ : ℝ, 0 < δ → δ ≤ r →
      0 < ∑ i, w i * |sin (u - δ - α i)| := by
  obtain ⟨r, hr0, hrπ, hrv, hsecond⟩ :=
    abs_sine_sum_second_difference_nhd w α u (v - u) (by linarith)
  refine ⟨r, hr0, ?_⟩
  intro δ hδ0 hδr
  have heq := hsecond δ hδ0 hδr
  rw [hflat (u + δ) ⟨by linarith, by linarith⟩,
    hflat u ⟨le_rfl, huv.le⟩] at heq
  have hp : 0 < 2 * sin δ *
      (∑ i in Finset.univ.filter (fun i => sin (u - α i) = 0), w i) :=
    mul_pos (mul_pos (by norm_num)
      (sin_pos_of_pos_of_lt_pi hδ0 (lt_of_le_of_lt hδr hrπ))) hw
  linarith only [heq, hp]

/-- The symmetric positive exterior neighborhood at a flat right endpoint. -/
theorem flat_abs_sine_sum_right_flank {ι : Type*} [Fintype ι]
    (w α : ι → ℝ) {u v : ℝ} (huv : u < v)
    (hflat : ∀ t ∈ Set.Icc u v, (∑ i, w i * |sin (t - α i)|) = 0)
    (hw : 0 < ∑ i in Finset.univ.filter (fun i => sin (v - α i) = 0), w i) :
    ∃ r : ℝ, 0 < r ∧ ∀ δ : ℝ, 0 < δ → δ ≤ r →
      0 < ∑ i, w i * |sin (v + δ - α i)| := by
  obtain ⟨r, hr0, hrπ, hrv, hsecond⟩ :=
    abs_sine_sum_second_difference_nhd w α v (v - u) (by linarith)
  refine ⟨r, hr0, ?_⟩
  intro δ hδ0 hδr
  have heq := hsecond δ hδ0 hδr
  rw [hflat (v - δ) ⟨by linarith, by linarith⟩,
    hflat v ⟨huv.le, le_rfl⟩] at heq
  have hp : 0 < 2 * sin δ *
      (∑ i in Finset.univ.filter (fun i => sin (v - α i) = 0), w i) :=
    mul_pos (mul_pos (by norm_num)
      (sin_pos_of_pos_of_lt_pi hδ0 (lt_of_le_of_lt hδr hrπ))) hw
  linarith only [heq, hp]

/-- Without a positive teacher on a student's line, that line has positive net
mass; negative and zero teacher coefficients are allowed. -/
theorem abs_sine_difference_line_mass_pos {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {x : ℝ} (i : Fin n) (hi : sin (x - θ i) = 0)
    (ht : ¬ ∃ k, 0 < s k ∧ sin (x - β k) = 0) :
    0 < (∑ i in Finset.univ.filter (fun i => sin (x - θ i) = 0), c i) -
      ∑ k in Finset.univ.filter (fun k => sin (x - β k) = 0), s k := by
  classical
  have hstudents : 0 < ∑ j in Finset.univ.filter (fun j => sin (x - θ j) = 0), c j :=
    Finset.sum_pos (fun j _ => hc j) ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hteachers : (∑ k in Finset.univ.filter (fun k => sin (x - β k) = 0), s k) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k hk
    exact not_lt.mp (fun hsk => ht ⟨k, hsk, (Finset.mem_filter.mp hk).2⟩)
  linarith only [hstudents, hteachers]

/-- At a student on a flat left endpoint, either a positive teacher shares the
line or the entire exterior left neighborhood has positive sine load. -/
theorem flat_abs_sine_difference_left_endpoint {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {u v : ℝ} (huv : u < v) (i : Fin n) (hi : sin (u - θ i) = 0)
    (hflat : ∀ t ∈ Set.Icc u v,
      (∑ j, c j * |sin (t - θ j)|) - (∑ k, s k * |sin (t - β k)|) = 0) :
    (∃ k, 0 < s k ∧ sin (u - β k) = 0) ∨
      ∃ r : ℝ, 0 < r ∧ ∀ δ : ℝ, 0 < δ → δ ≤ r →
        0 < (∑ j, c j * |sin (u - δ - θ j)|) -
          ∑ k, s k * |sin (u - δ - β k)| := by
  classical
  by_cases ht : ∃ k, 0 < s k ∧ sin (u - β k) = 0
  · exact Or.inl ht
  right
  have hw := abs_sine_difference_line_mass_pos c θ s β hc i hi ht
  rw [← abs_sine_difference_line_weight] at hw
  obtain ⟨r, hr, hflank⟩ := flat_abs_sine_sum_left_flank
    (Sum.elim c (fun k => -s k)) (Sum.elim θ β) huv (by
      intro t ht
      simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg] using hflat t ht) hw
  refine ⟨r, hr, ?_⟩
  intro δ hδ0 hδr
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg] using hflank δ hδ0 hδr

/-- The corresponding positive-teacher or positive-right-neighborhood
alternative at a flat right endpoint. -/
theorem flat_abs_sine_difference_right_endpoint {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {u v : ℝ} (huv : u < v) (i : Fin n) (hi : sin (v - θ i) = 0)
    (hflat : ∀ t ∈ Set.Icc u v,
      (∑ j, c j * |sin (t - θ j)|) - (∑ k, s k * |sin (t - β k)|) = 0) :
    (∃ k, 0 < s k ∧ sin (v - β k) = 0) ∨
      ∃ r : ℝ, 0 < r ∧ ∀ δ : ℝ, 0 < δ → δ ≤ r →
        0 < (∑ j, c j * |sin (v + δ - θ j)|) -
          ∑ k, s k * |sin (v + δ - β k)| := by
  classical
  by_cases ht : ∃ k, 0 < s k ∧ sin (v - β k) = 0
  · exact Or.inl ht
  right
  have hw := abs_sine_difference_line_mass_pos c θ s β hc i hi ht
  rw [← abs_sine_difference_line_weight] at hw
  obtain ⟨r, hr, hflank⟩ := flat_abs_sine_sum_right_flank
    (Sum.elim c (fun k => -s k)) (Sum.elim θ β) huv (by
      intro t ht
      simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg] using hflat t ht) hw
  refine ⟨r, hr, ?_⟩
  intro δ hδ0 hδr
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg] using hflank δ hδ0 hδr

end FlatSineJump

/-! Counting step: FlatGapCharges. -/
namespace FlatGapCharges

theorem sine_difference_continuous {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) :
    Continuous (fun t => (∑ i, c i * |sin (t - θ i)|) -
      (∑ k, s k * |sin (t - β k)|)) := by
  apply Continuous.sub
  · exact continuous_finset_sum _ fun i _ => continuous_const.mul
      ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).abs)
  · exact continuous_finset_sum _ fun i _ => continuous_const.mul
      ((Real.continuous_sin.comp (continuous_id.sub continuous_const)).abs)

theorem sine_difference_periodic {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) :
    Function.Periodic (fun t => (∑ i, c i * |sin (t - θ i)|) -
      (∑ k, s k * |sin (t - β k)|)) π := by
  have hatom (a t : ℝ) : |sin (t + π - a)| = |sin (t - a)| := by
    rw [show t + π - a = (t - a) + π by ring, Real.sin_add_pi, abs_neg]
  intro t
  simp only [hatom]

/-- A zero barrier less than a half-turn away bounds the component selected
by a positive left flank; no negative value is required. -/
theorem left_flank_positive_interval_of_zero_barrier {S : ℝ → ℝ}
    (hS : Continuous S) {a u : ℝ} (hau : a < u) (hlen : u - a < π)
    (ha : S a = 0) (hu : S u = 0)
    (hflank : ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε → 0 < S (u - δ)) :
    ∃ l : ℝ, a ≤ l ∧ l < u ∧ u - l < π ∧ S l = 0 ∧
      ∀ t ∈ Ioo l u, 0 < S t := by
  obtain ⟨ε, hε, hflank⟩ := hflank
  let δ : ℝ := min (ε / 2) ((u - a) / 2)
  have hδ0 : 0 < δ := lt_min (by linarith only [hε]) (by linarith only [hau])
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδa : δ ≤ (u - a) / 2 := min_le_right _ _
  have hp : 0 < S (u - δ) := hflank δ hδ0 (by linarith only [hδε, hε])
  obtain ⟨l, r, hal, hlp, hpr, hru, hl, hr, hpos⟩ :=
    PositiveIntervals.exists_positive_zero_interval hS
      (show a < u - δ by linarith only [hau, hδa])
      (show u - δ < u by linarith only [hδ0]) ha.le hp hu.le
  have hpositive : ∀ t ∈ Ioo (u - ε) u, 0 < S t := by
    intro t ht
    have h := hflank (u - t) (by linarith only [ht.2]) (by linarith only [ht.1])
    simpa only [sub_sub_cancel] using h
  have heq : r = u := PositiveIntervals.right_endpoints_eq_of_overlap
    hr hu hpos hpositive ⟨hlp, hpr⟩
      ⟨by linarith only [hδε, hε], by linarith only [hδ0]⟩
  subst r
  exact ⟨l, hal, hlp.trans hpr, by linarith only [hlen, hal], hl, hpos⟩

/-- The analogous zero-barrier construction for a positive right flank. -/
theorem right_flank_positive_interval_of_zero_barrier {S : ℝ → ℝ}
    (hS : Continuous S) {u b : ℝ} (hub : u < b) (hlen : b - u < π)
    (hu : S u = 0) (hb : S b = 0)
    (hflank : ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε → 0 < S (u + δ)) :
    ∃ r : ℝ, u < r ∧ r ≤ b ∧ r - u < π ∧ S r = 0 ∧
      ∀ t ∈ Ioo u r, 0 < S t := by
  obtain ⟨ε, hε, hflank⟩ := hflank
  let δ : ℝ := min (ε / 2) ((b - u) / 2)
  have hδ0 : 0 < δ := lt_min (by linarith only [hε]) (by linarith only [hub])
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδb : δ ≤ (b - u) / 2 := min_le_right _ _
  have hp : 0 < S (u + δ) := hflank δ hδ0 (by linarith only [hδε, hε])
  obtain ⟨l, r, hul, hlp, hpr, hrb, hl, hr, hpos⟩ :=
    PositiveIntervals.exists_positive_zero_interval hS
      (show u < u + δ by linarith only [hδ0])
      (show u + δ < b by linarith only [hub, hδb]) hu.le hp hb.le
  have hpositive : ∀ t ∈ Ioo u (u + ε), 0 < S t := by
    intro t ht
    have h := hflank (t - u) (by linarith only [ht.1]) (by linarith only [ht.2])
    simpa only [add_sub_cancel'_right] using h
  have heq : l = u := PositiveIntervals.left_endpoints_eq_of_overlap
    hl hu hpos hpositive ⟨hlp, hpr⟩
      ⟨by linarith only [hδ0], by linarith only [hδε, hε]⟩
  subst l
  exact ⟨r, hlp.trans hpr, hrb, by linarith only [hlen, hrb], hr, hpos⟩

/-- A zero-load teacher line itself supplies either side's zero-knot charge. -/
theorem zero_teacher_charge {m : ℕ} (S : ℝ → ℝ) (β : Fin m → ℝ)
    (side : Fin 2) {u : ℝ} (hu : S u = 0) (k : Fin m)
    (hk : sin (u - β k) = 0) : ∃ A : PlainCharges.Charge S β side, A.boundary = u := by
  obtain ⟨z, hz⟩ := sin_eq_zero_iff.mp hk
  have hpoint : β k + z * π = u := by linarith only [hz]
  refine ⟨⟨k, z, u, Or.inl ⟨?_, hpoint.symm⟩⟩, rfl⟩
  rw [hpoint]
  exact hu

/-- A flat gap charges its left student endpoint to either a zero teacher knot
or the right boundary of the adjacent positive component. Periodic zero
barriers make the component shorter than π without a negative-load witness. -/
theorem short_flat_gap_teacher_charge {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {u v : ℝ} (huv : u < v) (i : Fin n) (hi : θ i = u)
    (hflat : ∀ t ∈ Icc u v,
      (∑ j, c j * |sin (t - θ j)|) - (∑ k, s k * |sin (t - β k)|) = 0) :
    ∃ A : PlainCharges.Charge
      (fun t => (∑ j, c j * |sin (t - θ j)|) - (∑ k, s k * |sin (t - β k)|)) β 0,
      A.boundary ∈ Ico u v := by
  let S : ℝ → ℝ := fun t =>
    (∑ j, c j * |sin (t - θ j)|) - (∑ k, s k * |sin (t - β k)|)
  have hu : S u = 0 := hflat u ⟨le_rfl, huv.le⟩
  have hsi : sin (u - θ i) = 0 := by rw [hi, sub_self, sin_zero]
  rcases FlatSineJump.flat_abs_sine_difference_left_endpoint c θ s β hc huv i hsi hflat
    with ⟨k, _, hk⟩ | hflank
  · obtain ⟨A, hA⟩ := zero_teacher_charge S β 0 hu k hk
    exact ⟨A, by rw [hA]; exact ⟨le_rfl, huv⟩⟩
  · let η : ℝ := min ((v - u) / 2) (π / 2)
    have hη0 : 0 < η := lt_min (by linarith only [huv]) (by linarith only [pi_pos])
    have hηv : η ≤ (v - u) / 2 := min_le_left _ _
    have hηπ : η ≤ π / 2 := min_le_right _ _
    have hbarrier : S (u - π + η) = 0 := by
      have hz : S (u + η) = 0 := hflat (u + η)
        ⟨by linarith only [hη0], by linarith only [huv, hηv]⟩
      have hshift := sine_difference_periodic c θ s β (u - π + η)
      change S (u - π + η + π) = S (u - π + η) at hshift
      rw [show u - π + η + π = u + η by ring] at hshift
      exact hshift.symm.trans hz
    obtain ⟨l, _, hlu, hlen, hl, hpos⟩ := left_flank_positive_interval_of_zero_barrier
      (sine_difference_continuous c θ s β)
      (show u - π + η < u by linarith only [hηπ, pi_pos])
      (show u - (u - π + η) < π by linarith only [hη0]) hbarrier hu hflank
    obtain ⟨A, hA⟩ := PositiveGapCharges.positive_interval_teacher_charge
      c θ s β hc hlu hlen 0 hl hu hpos
    have hAu : A.boundary = u := by simpa only [if_pos rfl] using hA
    exact ⟨A, by rw [hAu]; exact ⟨le_rfl, huv⟩⟩

/-- The complementary flat core of a long gap supplies the same right-boundary
charge. Its midpoint is a zero barrier inside the gap, so a positive right
flank selects a teacher-owning component ending strictly before the next student. -/
theorem long_flat_core_teacher_charge {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {u v : ℝ} (hlong : π < v - u) (hlt : v - u < 2 * π)
    (i : Fin n) (hi : θ i = u)
    (hflatcore : ∀ t ∈ Icc (v - π) (u + π),
      (∑ j, c j * |sin (t - θ j)|) - (∑ k, s k * |sin (t - β k)|) = 0) :
    ∃ A : PlainCharges.Charge
      (fun t => (∑ j, c j * |sin (t - θ j)|) - (∑ k, s k * |sin (t - β k)|)) β 0,
      A.boundary ∈ Ico u v := by
  let S : ℝ → ℝ := fun t =>
    (∑ j, c j * |sin (t - θ j)|) - (∑ k, s k * |sin (t - β k)|)
  have huv : u < v := by linarith only [hlong, pi_pos]
  have hcorelen : v - 2 * π < u := by linarith only [hlt]
  have hprevious : ∀ t ∈ Icc (v - 2 * π) u, S t = 0 := by
    intro t ht
    have hz : S (t + π) = 0 := hflatcore (t + π)
      ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    exact (sine_difference_periodic c θ s β t).symm.trans hz
  have hu : S u = 0 := hprevious u ⟨hcorelen.le, le_rfl⟩
  have hsi : sin (u - θ i) = 0 := by rw [hi, sub_self, sin_zero]
  rcases FlatSineJump.flat_abs_sine_difference_right_endpoint
    c θ s β hc hcorelen i hsi hprevious with ⟨k, _, hk⟩ | hflank
  · obtain ⟨A, hA⟩ := zero_teacher_charge S β 0 hu k hk
    exact ⟨A, by rw [hA]; exact ⟨le_rfl, huv⟩⟩
  · have hb : S ((u + v) / 2) = 0 := hflatcore ((u + v) / 2)
      ⟨by linarith only [hlt], by linarith only [hlt]⟩
    obtain ⟨r, hur, hrmid, hlen, hr, hpos⟩ := right_flank_positive_interval_of_zero_barrier
      (sine_difference_continuous c θ s β)
      (show u < (u + v) / 2 by linarith only [huv])
      (show (u + v) / 2 - u < π by linarith only [hlt]) hu hb hflank
    obtain ⟨A, hA⟩ := PositiveGapCharges.positive_interval_teacher_charge
      c θ s β hc hur hlen 0 hu hr hpos
    have hAr : A.boundary = r := by simpa only [if_pos rfl] using hA
    exact ⟨A, by rw [hAr]; exact ⟨hur.le, by linarith only [hrmid, huv]⟩⟩

end FlatGapCharges

/-! Counting step: GapMoments. -/
namespace PlainGapMoments

/-- The Wronskian derivative proves all sinusoidal moments at once.  The
hypotheses are the direct first-order form of `R''+R=2S`. -/
theorem double_zero_sinusoidal_moment {R D S : ℝ → ℝ}
    (hR : ∀ x, HasDerivAt R (D x) x)
    (hD : ∀ x, HasDerivAt D (2 * S x - R x) x)
    (hS : Continuous S) {u v : ℝ}
    (hu : R u = 0 ∧ D u = 0) (hv : R v = 0 ∧ D v = 0) (a : ℝ) :
    (∫ x in u..v, S x * sin (x - a)) = 0 := by
  let W : ℝ → ℝ := fun x => D x * sin (x - a) - R x * cos (x - a)
  have hW (x : ℝ) : HasDerivAt W (2 * (S x * sin (x - a))) x := by
    have hs : HasDerivAt (fun t => sin (t - a)) (cos (x - a)) x := by
      simpa only [mul_one] using (hasDerivAt_sin (x - a)).comp x
        ((hasDerivAt_id x).sub_const a)
    have hc : HasDerivAt (fun t => cos (t - a)) (-sin (x - a)) x := by
      simpa only [mul_one] using (hasDerivAt_cos (x - a)).comp x
        ((hasDerivAt_id x).sub_const a)
    convert ((hD x).mul hs).sub ((hR x).mul hc) using 1
    ring
  have hint : IntervalIntegrable (fun x => 2 * (S x * sin (x - a)))
      MeasureTheory.volume u v :=
    (continuous_const.mul (hS.mul
      (Real.continuous_sin.comp (continuous_id.sub continuous_const)))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hW x) hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  dsimp [W] at hFTC
  rw [hu.1, hu.2, hv.1, hv.2] at hFTC
  linarith only [hFTC]

/-- An antiperiodic integrand has identical integrals on an interval and
its folded core.  This identity needs no interval-length assumption. -/
theorem antiperiodic_integral_fold {f : ℝ → ℝ} (hf : Continuous f)
    {p : ℝ} (hanti : ∀ x, f (x + p) = -f x) (u v : ℝ) :
    (∫ x in u..v, f x) = ∫ x in (v - p)..(u + p), f x := by
  have hcancel : (∫ x in u..(v - p), f x) +
      (∫ x in (u + p)..v, f x) = 0 := by
    have hshift := intervalIntegral.integral_comp_add_right
      (a := u) (b := v - p) f p
    rw [sub_add_cancel] at hshift
    have hneg : (∫ x in u..(v - p), f (x + p)) =
        -(∫ x in u..(v - p), f x) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun x _ => hanti x
    rw [← hshift, hneg]
    ring
  have hleft : (∫ x in u..(v - p), f x) +
      (∫ x in (v - p)..(u + p), f x) = ∫ x in u..(u + p), f x :=
    intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable u (v - p)) (hf.intervalIntegrable (v - p) (u + p))
  have hright : (∫ x in u..(u + p), f x) +
      (∫ x in (u + p)..v, f x) = ∫ x in u..v, f x :=
    intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable u (u + p)) (hf.intervalIntegrable (u + p) v)
  linarith only [hcancel, hleft, hright]

theorem periodic_sine_moment_fold {S : ℝ → ℝ}
    (hS : Continuous S) (hperiod : ∀ x, S (x + π) = S x) (u v a : ℝ) :
    (∫ x in u..v, S x * sin (x - a)) =
      ∫ x in (v - π)..(u + π), S x * sin (x - a) := by
  apply antiperiodic_integral_fold
    (hS.mul (Real.continuous_sin.comp (continuous_id.sub continuous_const)))
  intro x
  change S (x + π) * sin (x + π - a) = -(S x * sin (x - a))
  rw [hperiod, show x + π - a = (x - a) + π by ring, Real.sin_add_pi]
  ring

end PlainGapMoments

/-! Counting step: TourCount. -/
namespace PlainTourCount

/-- With at least two vertices, each gap of a strict full-turn tour has
length strictly smaller than a full turn. -/
theorem tour_gap_lt_two_pi {n : ℕ} (E : Fin (n + 1) → ℝ)
    (hE : StrictMono E) (hlast : E (Fin.last n) = E 0 + 2 * π)
    (hn : 2 ≤ n) (i : Fin n) : E i.succ - E i.castSucc < 2 * π := by
  have hleft : E 0 ≤ E i.castSucc := hE.monotone (Fin.zero_le _)
  have hright : E i.succ ≤ E (Fin.last n) := hE.monotone (Fin.le_last _)
  by_cases hi : i.val = 0
  · have hit : i.succ < Fin.last n := by
      change i.val + 1 < n
      rw [hi]
      exact hn
    have ht := hE hit
    rw [hlast] at ht
    linarith only [hleft, ht]
  · have hit : (0 : Fin (n + 1)) < i.castSucc := by
      change 0 < i.val
      exact Nat.pos_of_ne_zero hi
    have ht := hE hit
    rw [hlast] at hright
    linarith only [hright, ht]

/-- The plain-ReLU sharp census, reduced only to its direct sine moments on
an ordered student tour. Short gaps use their own moments; long gaps use the
folded core. Every case constructs one actual teacher-owned right boundary
inside the gap's half-open ownership interval. -/
theorem direct_sine_moment_tour_count {n m : ℕ}
    (c : Fin n → ℝ) (s beta : Fin m → ℝ) (E : Fin (n + 1) → ℝ)
    (hE : StrictMono E) (hlast : E (Fin.last n) = E 0 + 2 * π)
    (hn : 2 ≤ n) (hc : ∀ i, 0 < c i)
    (hmom : ∀ i : Fin n, ∀ a : ℝ,
      (∫ x in E i.castSucc..E i.succ,
        ((∑ j, c j * |sin (x - E j.castSucc)|) -
          (∑ k, s k * |sin (x - beta k)|)) * sin (x - a)) = 0) :
    n ≤ 2 * m := by
  let theta : Fin n → ℝ := fun i => E i.castSucc
  let S : ℝ → ℝ := fun x =>
    (∑ i, c i * |sin (x - theta i)|) - (∑ k, s k * |sin (x - beta k)|)
  have hS : Continuous S := FlatGapCharges.sine_difference_continuous c theta s beta
  have hperiod : Function.Periodic S π :=
    FlatGapCharges.sine_difference_periodic c theta s beta
  have hcharges : ∀ i : Fin n, ∃ A : PlainCharges.Charge S beta 0,
      A.boundary ∈ Ico (E i.castSucc) (E i.succ) := by
    intro i
    have huv : E i.castSucc < E i.succ := hE (Fin.castSucc_lt_succ i)
    have hlt := tour_gap_lt_two_pi E hE hlast hn i
    by_cases hshort : E i.succ - E i.castSucc ≤ π
    · by_cases hflat : ∀ x ∈ Icc (E i.castSucc) (E i.succ), S x = 0
      · exact FlatGapCharges.short_flat_gap_teacher_charge
          c theta s beta hc huv i rfl hflat
      · obtain ⟨A, hA⟩ := PositiveGapCharges.nonflat_zero_moment_interval_teacher_charge
          c theta s beta hc huv hshort hflat (hmom i)
        exact ⟨A, hA.1.le, hA.2⟩
    · have hlong : π < E i.succ - E i.castSucc := lt_of_not_ge hshort
      by_cases hflat : ∀ x ∈ Icc (E i.succ - π) (E i.castSucc + π), S x = 0
      · exact FlatGapCharges.long_flat_core_teacher_charge
          c theta s beta hc hlong hlt i rfl hflat
      · have hcore : E i.succ - π < E i.castSucc + π := by linarith only [hlt]
        have hcorelen : (E i.castSucc + π) - (E i.succ - π) ≤ π := by
          linarith only [hlong]
        have hcoremom : ∀ a : ℝ,
            (∫ x in (E i.succ - π)..(E i.castSucc + π), S x * sin (x - a)) = 0 := by
          intro a
          rw [← PlainGapMoments.periodic_sine_moment_fold hS hperiod]
          exact hmom i a
        obtain ⟨A, hA⟩ := PositiveGapCharges.nonflat_zero_moment_interval_teacher_charge
          c theta s beta hc hcore hcorelen hflat hcoremom
        exact ⟨A, by linarith only [hA.1, hlong],
          by linarith only [hA.2, hlong]⟩
  classical
  choose charge hcharge using hcharges
  exact PlainCharges.eq_ceiling_count hperiod E hE hlast charge hcharge

end PlainTourCount

open Real
open scoped BigOperators
noncomputable section

namespace PaperLeanFormalization.Plain

/-- Close an increasing list of oriented representatives by one full turn.
The fibre aggregate is already sorted, so no second sort or mass permutation
is needed in the counting proof. -/
def closeTour {n : ℕ} (θ : Fin n → ℝ) (hn : 0 < n) : Fin (n + 1) → ℝ :=
  Fin.lastCases (θ ⟨0, hn⟩ + 2 * π) θ

theorem closeTour_castSucc {n : ℕ} (θ : Fin n → ℝ) (hn : 0 < n) (i : Fin n) :
    closeTour θ hn i.castSucc = θ i := by
  simp only [closeTour, Fin.lastCases_castSucc]

theorem closeTour_last {n : ℕ} (θ : Fin n → ℝ) (hn : 0 < n) :
    closeTour θ hn (Fin.last n) = closeTour θ hn 0 + 2 * π := by
  change Fin.lastCases (θ ⟨0, hn⟩ + 2 * π) θ (Fin.last n) =
    Fin.lastCases (θ ⟨0, hn⟩ + 2 * π) θ (Fin.castSucc ⟨0, hn⟩) + 2 * π
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closeTour_strictMono {n : ℕ} (θ : Fin n → ℝ) (hn : 0 < n)
    (hθ : StrictMono θ) (hwindow : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) :
    StrictMono (closeTour θ hn) := by
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro h
    exact False.elim ((not_lt_of_ge (Fin.le_last j)) h)
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · intro _
      simp only [closeTour, Fin.lastCases_castSucc, Fin.lastCases_last]
      linarith only [(hwindow a).2, (hwindow ⟨0, hn⟩).1]
    · intro hab
      simp only [closeTour_castSucc]
      exact hθ hab

theorem full_turn_kernelResidual (f : ℝ → ℝ)
    (hf : ∀ x (k : ℤ), f (x + (k : ℝ) * (2 * π)) = f x)
    {n m : ℕ} (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (x : ℝ) :
    PaperLeanFormalization.kernelResidual f c β s θ (x + 2 * π) =
      PaperLeanFormalization.kernelResidual f c β s θ x := by
  have harg (y : ℝ) : x + 2 * π - y =
      (x - y) + ((1 : ℤ) : ℝ) * (2 * π) := by norm_num; ring
  simp only [PaperLeanFormalization.kernelResidual, harg, hf]

open PaperLeanFormalization

theorem plain_kernel_zero : phiCosJ 0 = π := by
  simp only [phiCosJ, reluPhi, orthantPhi, Real.cos_zero, Real.arcsin_one,
    one_mul, one_pow, sub_self, Real.sqrt_zero, add_zero]
  ring

theorem finite_kernel_loss_continuous {n m : ℕ} (K : ℝ → ℝ) (hK : Continuous K)
    (β s : Fin m → ℝ) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ kernelMassLoss K p.1 β s p.2) := by
  unfold kernelMassLoss
  apply Continuous.sub
  · apply continuous_const.mul
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact (((continuous_apply i).comp continuous_fst).mul
      ((continuous_apply j).comp continuous_fst)).mul
      (hK.comp (((continuous_apply i).comp continuous_snd).sub
        ((continuous_apply j).comp continuous_snd)))
  · apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro k _
    exact (((continuous_apply i).comp continuous_fst).mul continuous_const).mul
      (hK.comp (((continuous_apply i).comp continuous_snd).sub continuous_const))


/-- Full-turn periodicity is immediate from the literal cosine kernel. -/
theorem plain_kernel_full_turn (x : ℝ) (k : ℤ) :
    phiCosJ (x + (k : ℝ) * (2 * π)) = phiCosJ x := by
  simp only [phiCosJ, Real.cos_add_int_mul_two_pi]

/-- `eq:sine-load-identity`, in the literal finite-sum form. -/
theorem eq_sine_load_identity {n m : ℕ} (c θ : Fin n → ℝ) (s β : Fin m → ℝ)
    (x : ℝ) : residualCurvatureJ c β s θ x =
      2 * ((∑ i, c i * |sin (x - θ i)|) - ∑ k, s k * |sin (x - β k)|) -
        residualPotentialJ c β s θ x := by
  have h := SeedCertificate.eq_sine_load_identity phiCosJ c θ s β x
  change residualCurvatureJ c β s θ x + residualPotentialJ c β s θ x = _ at h
  linarith only [h]

theorem closeTour_double_zeros {n m : ℕ}
    {c θ : Fin n → ℝ} {s β : Fin m → ℝ} (hn : 0 < n)
    (hcrit : IsSignedMassCriticalNoncentered β s c θ)
    (hc : ∀ i, 0 < c i) (i : Fin (n + 1)) :
    residualPotentialJ c β s θ (closeTour θ hn i) = 0 ∧
      massTorqueFieldJ c β s θ (closeTour θ hn i) = 0 := by
  have hzero := (critical_iff_student_double_zeros
    (fun i => ne_of_gt (hc i))).mp hcrit
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [closeTour, Fin.lastCases_last]
    have hp (x : ℝ) (k : ℤ) : couplingHJ (x + (k : ℝ) * (2 * π)) =
        couplingHJ x := by
      simp only [couplingHJ, couplingH, Real.sin_add_int_mul_two_pi,
        Real.cos_add_int_mul_two_pi]
    change kernelResidual phiCosJ c β s θ (θ ⟨0, hn⟩ + 2 * π) = 0 ∧
      kernelResidual couplingHJ c β s θ (θ ⟨0, hn⟩ + 2 * π) = 0
    rw [full_turn_kernelResidual phiCosJ plain_kernel_full_turn,
      full_turn_kernelResidual couplingHJ hp]
    exact hzero ⟨0, hn⟩
  · rw [closeTour_castSucc]
    exact hzero j

theorem eq_gap_orthogonality {n m : ℕ}
    {c θ : Fin n → ℝ} {s β : Fin m → ℝ} (hn : 0 < n)
    (hcrit : IsSignedMassCriticalNoncentered β s c θ)
    (hc : ∀ i, 0 < c i) (j : Fin n) (a : ℝ) :
    (∫ x in closeTour θ hn j.castSucc..closeTour θ hn j.succ,
      ((∑ i, c i * |sin (x - θ i)|) - ∑ k, s k * |sin (x - β k)|) *
        sin (x - a)) = 0 := by
  apply PlainGapMoments.double_zero_sinusoidal_moment
    (R := residualPotentialJ c β s θ)
    (D := fun x => -massTorqueFieldJ c β s θ x)
  · exact fun x => (LocalKernelCalculus.residual_derivative_chain c β s θ x).1
  · intro x
    rw [← eq_sine_load_identity]
    exact (LocalKernelCalculus.residual_derivative_chain c β s θ x).2
  · apply Continuous.sub <;> apply continuous_finset_sum
    · intro i _
      exact continuous_const.mul ((Real.continuous_sin.comp
        (continuous_id.sub continuous_const)).abs)
    · intro k _
      exact continuous_const.mul ((Real.continuous_sin.comp
        (continuous_id.sub continuous_const)).abs)
  · obtain ⟨hR, hT⟩ := closeTour_double_zeros hn hcrit hc j.castSucc
    exact ⟨hR, by rw [hT, neg_zero]⟩
  · obtain ⟨hR, hT⟩ := closeTour_double_zeros hn hcrit hc j.succ
    exact ⟨hR, by rw [hT, neg_zero]⟩

/-- The single-student case cannot be obtained from a full-circle sine
moment, which vanishes by antiperiodicity. Its mass equation supplies the
missing information directly. -/
theorem one_student_requires_teacher {m : ℕ}
    {c θ : Fin 1 → ℝ} {s β : Fin m → ℝ}
    (hcrit : IsSignedMassCriticalNoncentered β s c θ) (hc : 0 < c 0) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  have hzero := ((critical_iff_student_double_zeros
    (fun i => by fin_cases i; exact ne_of_gt hc)).mp hcrit 0).1
  simp only [residualPotentialJ, kernelResidual, Fin.sum_univ_one,
    Fin.sum_univ_zero, sub_zero, sub_self, plain_kernel_zero] at hzero
  exact (ne_of_gt (mul_pos hc Real.pi_pos)) hzero

end PaperLeanFormalization.Plain

noncomputable section
open scoped BigOperators

namespace PaperLeanFormalization.Plain
open Real Complex

/-- The explicit regular teacher ring. -/
def RingTeacherAngle (m : ℕ) (j : Fin m) : ℝ := 2 * (j : ℝ) * Real.pi / m

def RingTeacherMass (m : ℕ) : Fin m → ℝ := fun _ ↦ 2

def RingStudentMass (m : ℕ) : Fin (m + m) → ℝ := fun _ ↦ 1

/-- One student on each teacher orientation and one on its antipode. -/
def RingStudentAngle (m : ℕ) : Fin (m + m) → ℝ :=
  Fin.append (RingTeacherAngle m) (fun j ↦ RingTeacherAngle m j + Real.pi)

def RingDirection (theta : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  ![Real.cos theta, Real.sin theta]

def RingRoot (m : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / m)

/-- The `j`th direction is the `j`th power of one primitive root of unity. -/
theorem ring_root_power (m : ℕ) (j : Fin m) :
    RingRoot m ^ (j : ℕ) = Complex.exp ((RingTeacherAngle m j : ℂ) * Complex.I) := by
  rw [RingRoot, ← Complex.exp_nat_mul]
  congr 1
  unfold RingTeacherAngle
  push_cast
  ring

/-- Both coordinates of the first moment vanish by one geometric sum. -/
theorem regular_ring_complex_moment_zero (m : ℕ) (hm : 2 ≤ m) :
    (∑ j : Fin m, Complex.exp ((RingTeacherAngle m j : ℂ) * Complex.I)) = 0 := by
  have hprimitive : IsPrimitiveRoot (RingRoot m) m :=
    Complex.isPrimitiveRoot_exp m (by omega (config := {}))
  have hsum := hprimitive.geom_sum_eq_zero (by omega (config := {}) : 1 < m)
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ RingRoot m ^ j) m] at hsum
  simpa only [ring_root_power] using hsum

/-- The regular ring has vanishing cosine moment in every probe direction. -/
theorem regular_ring_shifted_cosine_sum (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    (∑ j : Fin m, Real.cos (x - RingTeacherAngle m j)) = 0 := by
  have hmoment := regular_ring_complex_moment_zero m hm
  have hcos := congrArg Complex.re hmoment
  have hsin := congrArg Complex.im hmoment
  simp only [Complex.re_sum, Complex.exp_ofReal_mul_I_re, Complex.zero_re] at hcos
  simp only [Complex.im_sum, Complex.exp_ofReal_mul_I_im, Complex.zero_im] at hsin
  simp_rw [Real.cos_sub, Finset.sum_add_distrib, ← Finset.mul_sum, hcos, hsin,
    mul_zero, add_zero]

/-- Odd-order roots cannot meet their antipodal copy: the `m`th powers
would have to be both `1` and `-1`. -/
theorem odd_root_powers_disjoint_from_negatives {m : ℕ} {z : ℂ}
    (hz : IsPrimitiveRoot z m) (hodd : Odd m) (a b : Fin m) :
    z ^ (a : ℕ) ≠ -(z ^ (b : ℕ)) := by
  intro h
  have hp (j : Fin m) : (z ^ (j : ℕ)) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm (j : ℕ) m, pow_mul, hz.pow_eq_one, one_pow]
  have hm := congrArg (fun w : ℂ ↦ w ^ m) h
  dsimp only at hm
  rw [hodd.neg_pow, hp, hp] at hm
  norm_num at hm

/-- The two appended lists of roots and negative roots are injective. -/
theorem odd_root_antipodal_append_injective {m : ℕ} {z : ℂ}
    (hz : IsPrimitiveRoot z m) (hodd : Odd m) :
    Function.Injective (Fin.append (fun j : Fin m ↦ z ^ (j : ℕ))
      (fun j : Fin m ↦ -(z ^ (j : ℕ)))) := by
  intro i
  refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) i
  · intro j
    refine Fin.addCases (fun b ↦ ?_) (fun b ↦ ?_) j
    · intro h
      simp only [Fin.append_left] at h
      have hab : a = b := Fin.ext (hz.pow_inj a.isLt b.isLt h)
      exact congrArg (Fin.castAdd m) hab
    · intro h
      simp only [Fin.append_left, Fin.append_right] at h
      exact False.elim (odd_root_powers_disjoint_from_negatives hz hodd a b h)
  · intro j
    refine Fin.addCases (fun b ↦ ?_) (fun b ↦ ?_) j
    · intro h
      simp only [Fin.append_left, Fin.append_right] at h
      exact False.elim (odd_root_powers_disjoint_from_negatives hz hodd b a h.symm)
    · intro h
      simp only [Fin.append_right, neg_inj] at h
      have hab : a = b := Fin.ext (hz.pow_inj a.isLt b.isLt h)
      exact congrArg (Fin.natAdd m) hab

/-- Exponentials turn the appended angular ring into the preceding root list. -/
theorem ring_student_exponential (m : ℕ) (i : Fin (m + m)) :
    Complex.exp ((RingStudentAngle m i : ℂ) * Complex.I) =
      Fin.append (fun j : Fin m ↦ RingRoot m ^ (j : ℕ))
        (fun j : Fin m ↦ -(RingRoot m ^ (j : ℕ))) i := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp only [RingStudentAngle, Fin.append_left, ring_root_power]
  · simp only [RingStudentAngle, Fin.append_right, Complex.ofReal_add, add_mul,
      Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one, ring_root_power]

/-- Equality of the two real coordinates gives equality of the complex
unit-circle points, with no angle-modulo wrapper. -/
theorem ring_direction_eq_implies_exp_eq {a b : ℝ}
    (h : RingDirection a = RingDirection b) :
    Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) := by
  apply Complex.ext
  · have hc := congrArg (fun w : EuclideanSpace ℝ (Fin 2) ↦ w 0) h
    simpa only [RingDirection, Matrix.cons_val_zero, Complex.exp_ofReal_mul_I_re] using hc
  · have hs := congrArg (fun w : EuclideanSpace ℝ (Fin 2) ↦ w 1) h
    simpa only [RingDirection, Matrix.cons_val_one, Matrix.cons_val_zero,
      Complex.exp_ofReal_mul_I_im] using hs

/-- The odd-ring equality witness has exactly `2m` distinct oriented
directions. Distinctness uses oddness only through the antipodal obstruction. -/
theorem regular_odd_ring_student_directions_injective
    (m : ℕ) (hm : 0 < m) (hodd : Odd m) :
    Function.Injective (fun i : Fin (m + m) ↦ RingDirection (RingStudentAngle m i)) := by
  intro i j hij
  have hexp := ring_direction_eq_implies_exp_eq hij
  rw [ring_student_exponential, ring_student_exponential] at hexp
  exact odd_root_antipodal_append_injective
    (Complex.isPrimitiveRoot_exp m (by omega (config := {}))) hodd hexp


end PaperLeanFormalization.Plain

noncomputable section
open scoped BigOperators

namespace PaperLeanFormalization.Plain.SortedFibres

/-- The occupied oriented angles, counted before any masses are merged. -/
def count {n : ℕ} (q : Fin n → ℝ) : ℕ := (Finset.univ.image q).card

/-- Increasing enumeration of the occupied angles. -/
def angle {n : ℕ} (q : Fin n → ℝ) : Fin (count q) → ℝ :=
  (Finset.univ.image q).orderEmbOfFin rfl

/-- All coefficients at the displayed angle are added in this one sum. -/
def mass {n : ℕ} (q c : Fin n → ℝ) (j : Fin (count q)) : ℝ :=
  ∑ i in Finset.univ.filter (fun i => q i = angle q j), c i

theorem angle_strictMono {n : ℕ} (q : Fin n → ℝ) : StrictMono (angle q) :=
  ((Finset.univ.image q).orderEmbOfFin rfl).strictMono

theorem angle_injective {n : ℕ} (q : Fin n → ℝ) : Function.Injective (angle q) :=
  (angle_strictMono q).injective

theorem angle_has_preimage {n : ℕ} (q : Fin n → ℝ) (j : Fin (count q)) :
    ∃ i, q i = angle q j := by
  have hj : angle q j ∈ Finset.univ.image q :=
    Finset.orderEmbOfFin_mem _ rfl j
  simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hj

theorem raw_angle_is_enumerated {n : ℕ} (q : Fin n → ℝ) (i : Fin n) :
    ∃ j : Fin (count q), angle q j = q i := by
  have hm : q i ∈ Finset.univ.image q := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hr : q i ∈ Set.range ((Finset.univ.image q).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hm
  exact hr

theorem mass_positive {n : ℕ} (q c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (j : Fin (count q)) : 0 < mass q c j := by
  obtain ⟨i, hi⟩ := angle_has_preimage q j
  exact Finset.sum_pos' (fun k _ => (hc k).le)
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hc i⟩

/-- A raw angle appears exactly once in the sorted image, so the inner
indicator sum contains exactly one copy of its observable. -/
theorem indicator_sum {n : ℕ} (q : Fin n → ℝ) (i : Fin n) (v : ℝ) :
    (∑ j : Fin (count q), if q i = angle q j then v else 0) = v := by
  classical
  obtain ⟨j, hj⟩ := raw_angle_is_enumerated q i
  rw [Finset.sum_eq_single j]
  · rw [if_pos hj.symm]
  · intro k _ hkj
    apply if_neg
    intro hk
    exact hkj ((angle_injective q) (hk.symm.trans hj.symm))
  · intro h
    exact (h (Finset.mem_univ j)).elim

/-- Exchanging two finite sums proves aggregation for every observable.
This proof uses no model-specific residual or old aggregation theorem. -/
theorem weighted_observable {n : ℕ} (q c : Fin n → ℝ) (f : ℝ → ℝ) :
    (∑ i, c i * f (q i)) = ∑ j, mass q c j * f (angle q j) := by
  classical
  symm
  calc
    (∑ j, mass q c j * f (angle q j)) =
        ∑ j, ∑ i, if q i = angle q j then c i * f (q i) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [mass, Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : q i = angle q j
      · simp only [if_pos h, h]
      · simp only [if_neg h]
    _ = ∑ i, ∑ j, if q i = angle q j then c i * f (q i) else 0 := Finset.sum_comm
    _ = ∑ i, c i * f (q i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact indicator_sum q i _

end PaperLeanFormalization.Plain.SortedFibres

noncomputable section
open scoped BigOperators

namespace PaperLeanFormalization.Plain

/-- Literal finite kernel objective; the omitted teacher self-energy is
constant throughout the relabeling argument. -/
def reindexKernelLoss {n m : ℕ} (K : ℝ → ℝ) (c : Fin n → ℝ)
    (beta s : Fin m → ℝ) (theta : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, c i * c j * K (theta i - theta j)) -
    ∑ i, ∑ k, c i * s k * K (theta i - beta k)

/-- Relabeling both finite sums is the complete loss-invariance proof. -/
theorem kernel_loss_reindex {n p m : ℕ} {kf : ℝ → ℝ} (e : Fin p ≃ Fin n)
    (c theta : Fin n → ℝ) (beta s : Fin m → ℝ) :
    reindexKernelLoss kf (fun i => c (e i)) beta s (fun i => theta (e i)) =
      reindexKernelLoss kf c beta s theta := by
  have hself : (∑ i : Fin p, ∑ j : Fin p,
      c (e i) * c (e j) * kf (theta (e i) - theta (e j))) =
      ∑ i : Fin n, ∑ j : Fin n, c i * c j * kf (theta i - theta j) := by
    have hinner (i : Fin p) : (∑ j : Fin p,
        c (e i) * c (e j) * kf (theta (e i) - theta (e j))) =
        ∑ j : Fin n, c (e i) * c j * kf (theta (e i) - theta j) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    simp_rw [hinner]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hcross : (∑ i : Fin p, ∑ k : Fin m,
      c (e i) * s k * kf (theta (e i) - beta k)) =
      ∑ i : Fin n, ∑ k : Fin m, c i * s k * kf (theta i - beta k) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  exact congrArg₂ (fun A B : ℝ => (1 / 2 : ℝ) * A - B) hself hcross

/-- Local minima transport through the inverse coordinate permutation.
Only Mathlib's continuous composition principle is needed. -/
theorem local_minimum_reindex {n p m : ℕ} {kf : ℝ → ℝ} (e : Fin p ≃ Fin n)
    {beta s : Fin m → ℝ} {c theta : Fin n → ℝ}
    (hmin : IsLocalMin (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      reindexKernelLoss kf q.1 beta s q.2) (c, theta)) :
    IsLocalMin (fun q : (Fin p → ℝ) × (Fin p → ℝ) =>
      reindexKernelLoss kf q.1 beta s q.2) ((fun i => c (e i)), (fun i => theta (e i))) := by
  let pull : ((Fin p → ℝ) × (Fin p → ℝ)) → ((Fin n → ℝ) × (Fin n → ℝ)) :=
    fun q => ((fun i => q.1 (e.symm i)), (fun i => q.2 (e.symm i)))
  have hcont : Continuous pull :=
    (continuous_pi (fun i => (continuous_apply (e.symm i)).comp continuous_fst)).prod_mk
      (continuous_pi (fun i => (continuous_apply (e.symm i)).comp continuous_snd))
  have hpoint : pull ((fun i => c (e i)), (fun i => theta (e i))) = (c, theta) := by
    simp [pull]
  have hlocal : IsLocalMin (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      reindexKernelLoss kf q.1 beta s q.2)
      (pull ((fun i => c (e i)), (fun i => theta (e i)))) := by
    rw [hpoint]
    exact hmin
  apply (hlocal.comp_continuous hcont.continuousAt).congr
  apply Filter.eventually_of_forall
  intro q
  exact kernel_loss_reindex e.symm q.1 q.2 beta s

end PaperLeanFormalization.Plain


open Real Filter
open scoped Topology BigOperators RealInnerProductSpace

noncomputable section

namespace PaperLeanFormalization.Plain.CircleChart

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def circle (t : ℝ) : Plane := ![cos t, sin t]

def radial (t : ℝ) (w : Plane) : ℝ := cos t * w 0 + sin t * w 1

def transverse (t : ℝ) (w : Plane) : ℝ := cos t * w 1 - sin t * w 0

/-- A globally continuous expression which is the angle inverse on the open
hemicircle facing the base point. No choice of a global argument is needed. -/
def inverseAngle (t : ℝ) (w : Plane) : ℝ := t + arcsin (transverse t w)

theorem radial_base (t : ℝ) : radial t (circle t) = 1 := by
  change cos t * cos t + sin t * sin t = 1
  nlinarith only [sin_sq_add_cos_sq t]

theorem inverseAngle_base (t : ℝ) : inverseAngle t (circle t) = t := by
  change t + arcsin (cos t * sin t - sin t * cos t) = t
  rw [show cos t * sin t - sin t * cos t = 0 by ring, arcsin_zero, add_zero]

theorem continuous_radial (t : ℝ) : Continuous (radial t) :=
  (continuous_const.mul (continuous_apply 0)).add
    (continuous_const.mul (continuous_apply 1))

theorem continuous_inverseAngle (t : ℝ) : Continuous (inverseAngle t) :=
  continuous_const.add (continuous_arcsin.comp
    ((continuous_const.mul (continuous_apply 1)).sub
      (continuous_const.mul (continuous_apply 0))))

theorem circle_inverseAngle {t : ℝ} {w : Plane}
    (hw : ‖w‖ = 1) (hr : 0 < radial t w) : circle (inverseAngle t w) = w := by
  have hunit : w 0 ^ 2 + w 1 ^ 2 = 1 := by
    have h := real_inner_self_eq_norm_sq w
    rw [PiLp.inner_apply, Fin.sum_univ_two, hw] at h
    change w 0 * w 0 + w 1 * w 1 = (1 : ℝ) ^ 2 at h
    nlinarith only [h]
  have hrot : radial t w ^ 2 + transverse t w ^ 2 = 1 := by
    calc
      _ = (sin t ^ 2 + cos t ^ 2) * (w 0 ^ 2 + w 1 ^ 2) := by
        unfold radial transverse
        ring
      _ = 1 := by rw [sin_sq_add_cos_sq, hunit, one_mul]
  have hlo : -1 ≤ transverse t w := by
    nlinarith only [hrot, sq_nonneg (radial t w), sq_nonneg (transverse t w + 1)]
  have hhi : transverse t w ≤ 1 := by
    nlinarith only [hrot, sq_nonneg (radial t w), sq_nonneg (transverse t w - 1)]
  have hs : sin (arcsin (transverse t w)) = transverse t w := sin_arcsin hlo hhi
  have hc : cos (arcsin (transverse t w)) = radial t w := by
    rw [cos_arcsin, show 1 - transverse t w ^ 2 = radial t w ^ 2 by linarith only [hrot],
      sqrt_sq_eq_abs, abs_of_pos hr]
  funext i
  fin_cases i
  · change cos (t + arcsin (transverse t w)) = w 0
    rw [cos_add, hs, hc]
    calc
      _ = (sin t ^ 2 + cos t ^ 2) * w 0 := by unfold radial transverse; ring
      _ = w 0 := by rw [sin_sq_add_cos_sq, one_mul]
  · change sin (t + arcsin (transverse t w)) = w 1
    rw [sin_add, hs, hc]
    calc
      _ = (sin t ^ 2 + cos t ^ 2) * w 1 := by unfold radial transverse; ring
      _ = w 1 := by rw [sin_sq_add_cos_sq, one_mul]

variable {n : ℕ}

def chart (z : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → Plane) :=
  (z.1, fun i => circle (z.2 i))

def inverse (theta : Fin n → ℝ) (q : (Fin n → ℝ) × (Fin n → Plane)) :
    (Fin n → ℝ) × (Fin n → ℝ) := (q.1, fun i => inverseAngle (theta i) (q.2 i))

theorem inverse_base (c theta : Fin n → ℝ) : inverse theta (chart (c, theta)) = (c, theta) := by
  refine Prod.ext rfl ?_
  funext i
  exact inverseAngle_base (theta i)

theorem continuous_inverse (theta : Fin n → ℝ) : Continuous (inverse theta) := by
  refine continuous_fst.prod_mk (continuous_pi fun i => ?_)
  exact (continuous_inverseAngle (theta i)).comp ((continuous_apply i).comp continuous_snd)

/-- The only neighborhood restriction is positive radial coordinate. This is
automatic near each of the finitely many base directions. -/
theorem eventually_chart_inverse (c theta : Fin n → ℝ) :
    ∀ᶠ q in 𝓝[{q : (Fin n → ℝ) × (Fin n → Plane) | ∀ i, ‖q.2 i‖ = 1}]
      (chart (c, theta)), chart (inverse theta q) = q := by
  have hrad : ∀ᶠ q in 𝓝 (chart (c, theta)), ∀ i, 0 < radial (theta i) (q.2 i) := by
    apply eventually_all.mpr
    intro i
    have hopen : IsOpen {q : (Fin n → ℝ) × (Fin n → Plane) |
        0 < radial (theta i) (q.2 i)} :=
      isOpen_lt continuous_const
        ((continuous_radial (theta i)).comp ((continuous_apply i).comp continuous_snd))
    apply hopen.mem_nhds
    change 0 < radial (theta i) (circle (theta i))
    rw [radial_base]
    exact one_pos
  filter_upwards [hrad.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hr hq
  refine Prod.ext rfl ?_
  funext i
  exact circle_inverseAngle (hq i) (hr i)

theorem local_minimum_to_sphere
    (F : (Fin n → ℝ) → (Fin n → Plane) → ℝ) {c theta : Fin n → ℝ}
    (hmin : IsLocalMin (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      F z.1 (fun i => circle (z.2 i))) (c, theta)) :
    IsLocalMinOn (fun q : (Fin n → ℝ) × (Fin n → Plane) => F q.1 q.2)
      {q | ∀ i, ‖q.2 i‖ = 1} (c, fun i => circle (theta i)) := by
  have ht : Tendsto (inverse theta) (𝓝 (chart (c, theta))) (𝓝 (c, theta)) := by
    have h := ((continuous_inverse theta).continuousAt (x := chart (c, theta))).tendsto
    rw [inverse_base] at h
    exact h
  have hm := (ht.eventually hmin).filter_mono
    (nhdsWithin_le_nhds (s := {q : (Fin n → ℝ) × (Fin n → Plane) | ∀ i, ‖q.2 i‖ = 1}))
  filter_upwards [hm, eventually_chart_inverse c theta] with q hq heq
  change F c (fun i => circle (theta i)) ≤ F (chart (inverse theta q)).1
    (chart (inverse theta q)).2 at hq
  rw [heq] at hq
  exact hq

theorem strict_minimum_to_sphere
    (F : (Fin n → ℝ) → (Fin n → Plane) → ℝ) {c theta : Fin n → ℝ}
    (hmin : ∀ᶠ z : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (c, theta),
      z ≠ (c, theta) → F c (fun i => circle (theta i)) <
        F z.1 (fun i => circle (z.2 i))) :
    ∀ᶠ q : (Fin n → ℝ) × (Fin n → Plane) in
      𝓝[{q | ∀ i, ‖q.2 i‖ = 1}] (c, fun i => circle (theta i)),
      q ≠ (c, fun i => circle (theta i)) →
        F c (fun i => circle (theta i)) < F q.1 q.2 := by
  have ht : Tendsto (inverse theta) (𝓝 (chart (c, theta))) (𝓝 (c, theta)) := by
    have h := ((continuous_inverse theta).continuousAt (x := chart (c, theta))).tendsto
    rw [inverse_base] at h
    exact h
  have hm := (ht.eventually hmin).filter_mono
    (nhdsWithin_le_nhds (s := {q : (Fin n → ℝ) × (Fin n → Plane) | ∀ i, ‖q.2 i‖ = 1}))
  filter_upwards [hm, eventually_chart_inverse c theta] with q hq heq hne
  have hi : inverse theta q ≠ (c, theta) := by
    intro h
    apply hne
    change q = chart (c, theta)
    rw [← heq, h]
  have hlt := hq hi
  change F c (fun i => circle (theta i)) < F (chart (inverse theta q)).1
    (chart (inverse theta q)).2 at hlt
  rw [heq] at hlt
  exact hlt

end PaperLeanFormalization.Plain.CircleChart

/-! Fresh numerical certificate component: SeedNumerics. -/

open Real
open scoped BigOperators

noncomputable section

namespace PaperLeanFormalization.SeedNumerics

def cosTaylor (x : ℝ) : ℝ :=
  1-x^2/2+x^4/24-x^6/720+x^8/40320-x^10/3628800+x^12/479001600

def sinTaylor (x : ℝ) : ℝ :=
  x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800+x^13/6227020800

theorem trig_taylor_bound {x : ℝ} (hx : |x| ≤ 1) :
    |cos x-cosTaylor x| ≤ |x|^14*(15/(87178291200*14)) ∧
    |sin x-sinTaylor x| ≤ |x|^14*(15/(87178291200*14)) := by
  have hexp := Complex.exp_bound (x := (x : ℂ)*Complex.I)
    (by simpa using hx) (by norm_num : 0 < 14)
  have hre := (Complex.abs_re_le_abs _).trans hexp
  have him := (Complex.abs_im_le_abs _).trans hexp
  have hreal : (∑ m in Finset.range 14, ((x : ℂ)*Complex.I)^m/(m.factorial : ℂ)).re =
      cosTaylor x := by
    norm_num [Finset.sum_range_succ, pow_succ, Complex.mul_re, Complex.mul_im, Nat.factorial,
      cosTaylor]
    ring
  have himag : (∑ m in Finset.range 14, ((x : ℂ)*Complex.I)^m/(m.factorial : ℂ)).im =
      sinTaylor x := by
    norm_num [Finset.sum_range_succ, pow_succ, Complex.mul_re, Complex.mul_im, Nat.factorial,
      sinTaylor]
    ring
  constructor
  · rw [Complex.sub_re,hreal] at hre
    norm_num [Complex.exp_re,Nat.factorial] at hre ⊢
    exact hre
  · rw [Complex.sub_im,himag] at him
    norm_num [Complex.exp_im,Nat.factorial] at him ⊢
    exact him

theorem bound_add {x y a b r s : ℝ} (hx : |x-a| ≤ r) (hy : |y-b| ≤ s) :
    |x+y-(a+b)| ≤ r+s := by
  calc
    _ = |(x-a)+(y-b)| := by congr 1; ring
    _ ≤ |x-a|+|y-b| := abs_add _ _
    _ ≤ r+s := add_le_add hx hy

theorem bound_neg {x a r : ℝ} (hx : |x-a| ≤ r) : |-x- -a| ≤ r := by
  simpa only [neg_sub_neg, abs_sub_comm] using hx

theorem bound_sub {x y a b r s : ℝ} (hx : |x-a| ≤ r) (hy : |y-b| ≤ s) :
    |x-y-(a-b)| ≤ r+s := by
  simpa only [sub_eq_add_neg] using bound_add hx (bound_neg hy)

theorem bound_mul {x y a b r s : ℝ} (hx : |x-a| ≤ r) (hy : |y-b| ≤ s) :
    |x*y-a*b| ≤ r*|b|+(|a|+r)*s := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hx
  have hxa : |x| ≤ |a|+r := by
    have h := abs_sub_le x a 0
    simp only [sub_zero] at h
    linarith only [h,hx]
  calc
    _ = |(x-a)*b+x*(y-b)| := by congr 1; ring
    _ ≤ |(x-a)*b|+|x*(y-b)| := abs_add _ _
    _ = |x-a| * |b| + |x| * |y-b| := by rw [abs_mul,abs_mul]
    _ ≤ r*|b|+(|a|+r)*s := add_le_add
      (mul_le_mul_of_nonneg_right hx (abs_nonneg b))
      (mul_le_mul hxa hy (abs_nonneg _) (add_nonneg (abs_nonneg a) hr))

theorem bound_abs {x a r : ℝ} (hx : |x-a| ≤ r) : abs (abs x-abs a) ≤ r :=
  (abs_abs_sub_abs_le_abs_sub x a).trans hx

theorem bound_round {x a b r s : ℝ} (hx : |x-a| ≤ r)
    (h : r+|a-b| ≤ s) : |x-b| ≤ s :=
  (abs_sub_le x a b).trans ((add_le_add_right hx _).trans h)

theorem bound_cos {x a r : ℝ} (hx : |x| ≤ 1) (hp : |cosTaylor x-a| ≤ r) :
    |cos x-a| ≤ (15/(87178291200*14))+r := by
  have ht := (trig_taylor_bound hx).1
  have hpow : |x|^14 ≤ (1 : ℝ) := pow_le_one _ (abs_nonneg _) hx
  have hscale := mul_le_mul_of_nonneg_right hpow
    (by norm_num : (0 : ℝ) ≤ 15/(87178291200*14))
  have htri := abs_sub_le (cos x) (cosTaylor x) a
  linarith only [ht,hscale,htri,hp]

theorem bound_sin {x a r : ℝ} (hx : |x| ≤ 1) (hp : |sinTaylor x-a| ≤ r) :
    |sin x-a| ≤ (15/(87178291200*14))+r := by
  have ht := (trig_taylor_bound hx).2
  have hpow : |x|^14 ≤ (1 : ℝ) := pow_le_one _ (abs_nonneg _) hx
  have hscale := mul_le_mul_of_nonneg_right hpow
    (by norm_num : (0 : ℝ) ≤ 15/(87178291200*14))
  have htri := abs_sub_le (sin x) (sinTaylor x) a
  linarith only [ht,hscale,htri,hp]

/-- The exact Gram quadratic form is the sum of squares of its row forms. -/
theorem finite_gram_quadratic_eq_sum_sq {n k : ℕ} (B : Fin k → Fin n → ℝ)
    (x : Fin n → ℝ) :
    (∑ i, ∑ j, (∑ l, B l i*B l j)*x i*x j) = ∑ l, (∑ i, B l i*x i)^2 := by
  simp only [Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ l, B l i*B l j*x i*x j) =
        ∑ i, ∑ l, ∑ j, B l i*B l j*x i*x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ l, ∑ i, ∑ j, B l i*B l j*x i*x j := by rw [Finset.sum_comm]
    _ = ∑ l, (∑ i, B l i*x i)^2 := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem finite_gram_quadratic_nonneg {n k : ℕ} (B : Fin k → Fin n → ℝ)
    (x : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, (∑ l, B l i*B l j)*x i*x j := by
  rw [finite_gram_quadratic_eq_sum_sq]
  exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- Entrywise enclosure retains the full Gram part in the quadratic lower bound. -/
theorem gram_lower_bound_of_enclosure {n k : ℕ}
    (H : Fin n → Fin n → ℝ) (B : Fin k → Fin n → ℝ) (μ ε : ℝ) (hε : 0 ≤ ε)
    (hH : ∀ i j, |H i j - (∑ l, B l i*B l j) - (if i = j then μ else 0)| ≤ ε)
    (x : Fin n → ℝ) :
    (∑ i, ∑ j, (∑ l, B l i*B l j)*x i*x j) + (μ-n*ε)*(∑ i, x i^2) ≤
      ∑ i, ∑ j, H i j*x i*x j := by
  classical
  let E (i j : Fin n) := H i j - (∑ l, B l i*B l j) - (if i=j then μ else 0)
  have hprod (i j : Fin n) : -ε*(|x i| * |x j|) ≤ E i j*x i*x j := by
    have h := mul_le_mul_of_nonneg_right (hH i j) (abs_nonneg (x i*x j))
    have hneg := neg_abs_le_self (E i j*x i*x j)
    rw [abs_mul] at h
    dsimp [E] at hneg ⊢
    rw [abs_mul,abs_mul] at hneg
    nlinarith only [h,hneg]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hprod i j))
  have herr : -ε*(∑ i, |x i|)^2 ≤ ∑ i, ∑ j, E i j*x i*x j := by
    convert hsum using 1
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc : (∑ i, |x i|)^2 ≤ (n : ℝ)*∑ i, x i^2 := by
    simpa only [Finset.card_univ,Fintype.card_fin,sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|))
  have herr' := mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr hε)
  have hid : (∑ i, ∑ j, H i j*x i*x j) =
      (∑ i, ∑ j, E i j*x i*x j) +
      (∑ i, ∑ j, (∑ l, B l i*B l j)*x i*x j) + μ*(∑ i, x i^2) := by
    have hp (i j : Fin n) : H i j*x i*x j = E i j*x i*x j +
        (∑ l, B l i*B l j)*x i*x j + (if i=j then μ*x i*x i else 0) := by
      dsimp [E]
      split_ifs with h
      · subst j
        ring
      · ring
    simp only [hp,Finset.sum_add_distrib,Finset.sum_ite_eq, Finset.mem_univ,if_true]
    simp only [Finset.mul_sum,pow_two,mul_assoc]
  rw [hid]
  nlinarith only [herr,herr']

/-- The scalar Hessian floor follows by discarding the nonnegative Gram part. -/
theorem hessian_floor_of_gram_enclosure {n k : ℕ}
    (H : Fin n → Fin n → ℝ) (B : Fin k → Fin n → ℝ) (μ ε : ℝ) (hε : 0 ≤ ε)
    (hH : ∀ i j, |H i j - (∑ l, B l i*B l j) - (if i = j then μ else 0)| ≤ ε)
    (x : Fin n → ℝ) :
    (μ-n*ε)*(∑ i, x i^2) ≤ ∑ i, ∑ j, H i j*x i*x j := by
  have h := gram_lower_bound_of_enclosure H B μ ε hε hH x
  have hg := finite_gram_quadratic_nonneg B x
  linarith only [h, hg]

structure RationalBall where
  center : ℚ
  radius : ℚ
  deriving DecidableEq, Repr

inductive Certificate where
  | atom (index : ℕ)
  | const (q : ℚ)
  | add (left right : Certificate) (out : RationalBall)
  | mul (left right : Certificate) (out : RationalBall)
  | abs (arg : Certificate)
  deriving Repr

namespace Certificate

def ball (input : ℕ → RationalBall) : Certificate → RationalBall
  | .atom i => input i
  | .const q => ⟨q,0⟩
  | .add _ _ out => out
  | .mul _ _ out => out
  | .abs e => ⟨|(ball input e).center|,(ball input e).radius⟩

def eval (input : ℕ → ℝ) : Certificate → ℝ
  | .atom i => input i
  | .const q => q
  | .add a b _ => eval input a+eval input b
  | .mul a b _ => eval input a*eval input b
  | .abs e => |eval input e|

def check (input : ℕ → RationalBall) : Certificate → Bool
  | .atom _ => true
  | .const _ => true
  | .add a b out => check input a && check input b &&
      decide ((ball input a).radius+(ball input b).radius+
        |(ball input a).center+(ball input b).center-out.center| ≤ out.radius)
  | .mul a b out => check input a && check input b &&
      decide ((ball input a).radius*|(ball input b).center|+
        (|(ball input a).center|+(ball input a).radius)*(ball input b).radius+
        |(ball input a).center*(ball input b).center-out.center| ≤ out.radius)
  | .abs e => check input e

/-- The arithmetic artifact is merely data: this theorem independently checks
every exact rational rounding bound and propagates it to the real expression. -/
theorem sound (e : Certificate) (input : ℕ → RationalBall) (values : ℕ → ℝ)
    (hinput : ∀ i, |values i-(input i).center| ≤ (input i).radius)
    (hcheck : check input e = true) :
    |eval values e-(ball input e).center| ≤ (ball input e).radius := by
  induction e with
  | atom i => exact hinput i
  | const q => simp only [eval,ball,sub_self,abs_zero,Rat.cast_zero,le_refl]
  | add a b out iha ihb =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hcheck
      have ha := iha hcheck.1.1
      have hb := ihb hcheck.1.2
      have hround : ((ball input a).radius : ℝ)+(ball input b).radius+
          |((ball input a).center : ℝ)+(ball input b).center-out.center| ≤ out.radius := by
        exact_mod_cast hcheck.2
      exact bound_round (bound_add ha hb) hround
  | mul a b out iha ihb =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hcheck
      have ha := iha hcheck.1.1
      have hb := ihb hcheck.1.2
      have hround : ((ball input a).radius : ℝ)*|(ball input b).center|+
          (|(ball input a).center|+((ball input a).radius : ℝ))*(ball input b).radius+
          |((ball input a).center : ℝ)*(ball input b).center-out.center| ≤ out.radius := by
        exact_mod_cast hcheck.2
      apply bound_round (bound_mul ha hb)
      simpa only [ball,Rat.cast_abs] using hround
  | abs e ih =>
      simpa only [eval,ball,Rat.cast_abs] using bound_abs (ih hcheck)

end Certificate

end PaperLeanFormalization.SeedNumerics


/-! Fresh numerical certificate component: SeedModel. -/

open Real
open scoped BigOperators
noncomputable section

namespace PaperLeanFormalization.SeedNumerics

def J (t : ℝ) : ℝ := (π-arccos (cos t))*cos t+|sin t|
def J1 (t : ℝ) : ℝ := -(π-arccos (cos t))*sin t
def J2 (t : ℝ) : ℝ := 2*|sin t|-J t

theorem J_neg (t : ℝ) : J (-t) = J t := by simp [J]
theorem J1_neg (t : ℝ) : J1 (-t) = -J1 t := by simp [J1]
theorem J2_neg (t : ℝ) : J2 (-t) = J2 t := by simp [J2,J_neg]
@[simp] theorem J_zero : J 0 = π := by simp [J]
@[simp] theorem J1_zero : J1 0 = 0 := by simp [J1]
@[simp] theorem J2_zero : J2 0 = -π := by simp [J2]

theorem J_sub_comm (x y : ℝ) : J (x-y) = J (y-x) := by
  rw [show x-y = -(y-x) by ring,J_neg]
theorem J1_sub_comm (x y : ℝ) : J1 (x-y) = -J1 (y-x) := by
  rw [show x-y = -(y-x) by ring,J1_neg]
theorem J2_sub_comm (x y : ℝ) : J2 (x-y) = J2 (y-x) := by
  rw [show x-y = -(y-x) by ring,J2_neg]

def seedMass : Fin 3 → ℝ :=
  ![1000437388123/1000000000000,695398940163/500000000000,604352649479/1000000000000]
def seedAngle : Fin 3 → ℝ :=
  ![(222166734523/125000000000)*π,(66013352661/62500000000)*π,
    (363169886907/1000000000000)*π]

theorem append_three {α : Type*} (f g : Fin 3 → α) :
    Fin.append f g = ![f 0,f 1,f 2,g 0,g 1,g 2] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem append_three_0 {α : Type*} (f g : Fin 3 → α) : Fin.append f g 0 = f 0 := rfl
@[simp] theorem append_three_1 {α : Type*} (f g : Fin 3 → α) : Fin.append f g 1 = f 1 := rfl
@[simp] theorem append_three_2 {α : Type*} (f g : Fin 3 → α) : Fin.append f g 2 = f 2 := rfl
@[simp] theorem append_three_3 {α : Type*} (f g : Fin 3 → α) : Fin.append f g 3 = g 0 := rfl
@[simp] theorem append_three_4 {α : Type*} (f g : Fin 3 → α) : Fin.append f g 4 = g 1 := rfl
@[simp] theorem append_three_5 {α : Type*} (f g : Fin 3 → α) : Fin.append f g 5 = g 2 := rfl

def teacherAngle : Fin 3 → ℝ := ![0,(5/6)*π,(4/3)*π]

def gradient (c θ : Fin 3 → ℝ) : Fin 6 → ℝ :=
  Fin.append
    (fun i => ∑ j, c j*J (θ i-θ j)-∑ k, J (θ i-teacherAngle k))
    (fun i => c i*(∑ j, c j*J1 (θ i-θ j)-∑ k, J1 (θ i-teacherAngle k)))

def mixed (c θ : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = j then ∑ k, c k*J1 (θ i-θ k)-∑ k, J1 (θ i-teacherAngle k)
  else -c j*J1 (θ i-θ j)

def angular (c θ : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = j then c i*(∑ k, (if k = i then 0 else c k*J2 (θ i-θ k))-
      ∑ k, J2 (θ i-teacherAngle k))
  else -c i*c j*J2 (θ i-θ j)

def hessian (c θ : Fin 3 → ℝ) : Fin 6 → Fin 6 → ℝ :=
  Fin.append
    (fun i => Fin.append (fun j => J (θ i-θ j)) (mixed c θ i))
    (fun i => Fin.append (fun j => mixed c θ j i) (angular c θ i))

theorem linear_form_sq_bound {n : ℕ} (g v : Fin n → ℝ) {ε : ℝ}
    (_he : 0 ≤ ε) (hg : ∀ i, |g i| ≤ ε) :
    (∑ i, g i*v i)^2 ≤ (n : ℝ)*ε^2*(∑ i, v i^2) := by
  have hsum : |∑ i, g i*v i| ≤ ε*(∑ i, |v i|) := by
    calc
      _ ≤ ∑ i, |g i*v i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |g i| * |v i| := by simp only [abs_mul]
      _ ≤ ∑ i, ε*|v i| := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_right (hg i) (abs_nonneg _))
      _ = _ := by rw [Finset.mul_sum]
  have hsquare := mul_self_le_mul_self (abs_nonneg _) hsum
  have hcauchy := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |v i|)
  simp only [Finset.card_univ,Fintype.card_fin,sq_abs] at hcauchy
  have hscale := mul_le_mul_of_nonneg_left hcauchy (sq_nonneg ε)
  have habssq : |∑ i, g i*v i| * |∑ i, g i*v i| = (∑ i, g i*v i)^2 := by
    rw [← pow_two,sq_abs]
  rw [habssq] at hsquare
  have hproduct : (ε*(∑ i, |v i|))*(ε*(∑ i, |v i|)) = ε^2*(∑ i, |v i|)^2 := by ring
  rw [hproduct] at hsquare
  nlinarith only [hsquare,hscale]

end PaperLeanFormalization.SeedNumerics


/-! Fresh numerical certificate component: SeedPi. -/

/-! Generated exact certificate data. Do not edit emitted source.
Producer: the certificate generator of this development, part: pi
Schema SHA256: 2b5eb7e44659fd32230111f5fe08b24c5356d826efe455d063986973dcd2ccc2
A generator run is not proof: compile this file and audit its declarations. -/

open Real
noncomputable section

namespace PaperLeanFormalization.SeedNumerics

theorem seed_pi_lower : ((3141592653589 / 1000000000000) : ℝ) < π := by
  pi_lower_bound [14142135623730950488016887242096980785697 / 10000000000000000000000000000000000000000,
      18477590650225735122563663787935765736449 / 10000000000000000000000000000000000000000,
      19615705608064608982523644722684780739479 / 10000000000000000000000000000000000000000,
      1990369453344393772489673906218959843151 / 1000000000000000000000000000000000000000,
      3995181824820689570859086419036402777773 / 2000000000000000000000000000000000000000,
      9996988186962042201157656496661721968501 / 5000000000000000000000000000000000000000,
      19998494036782890818432929823927664487013 / 10000000000000000000000000000000000000000,
      19999623505652022853139808754571354323479 / 10000000000000000000000000000000000000000,
      999995293809576171511580125700119899553 / 500000000000000000000000000000000000000,
      9999988234517019099290257101715260190483 / 5000000000000000000000000000000000000000,
      9999997058628822191602282177387656771163 / 5000000000000000000000000000000000000000,
      3999999705862871404578925922829551427793 / 2000000000000000000000000000000000000000,
      9999999816164292938083469154029097145051 / 5000000000000000000000000000000000000000,
      19999999908082146257819438662792122979179 / 10000000000000000000000000000000000000000,
      4999999994255134137813366538972770542003 / 2500000000000000000000000000000000000000,
      19999999994255134136988279444372835521783 / 10000000000000000000000000000000000000000,
      1999999999856378353419550191767700980521 / 1000000000000000000000000000000000000000,
      19999999999640945883545652482955682147593 / 10000000000000000000000000000000000000000,
      19999999999910236470886211683459946488831 / 10000000000000000000000000000000000000000,
      9999999999988779558860770165517525365039 / 5000000000000000000000000000000000000000,
      19999999999994389779430384295894391689041 / 10000000000000000000000000000000000000000,
      3999999999999719488971519204958914947033 / 2000000000000000000000000000000000000000]

theorem seed_pi_upper : π < ((314159265359 / 100000000000) : ℝ) := by
  pi_upper_bound [441941738241592202750527726315530649553 / 312500000000000000000000000000000000000,
      18044522119361069455628577917906021227 / 9765625000000000000000000000000000000,
      9807852804032304491261822361342390369739 / 5000000000000000000000000000000000000000,
      19903694533443937724896739062189598431509 / 10000000000000000000000000000000000000000,
      19975909124103447854295432095182013888863 / 10000000000000000000000000000000000000000,
      19993976373924084402315312993323443937 / 10000000000000000000000000000000000000,
      19998494036782890818432929823927664487011 / 10000000000000000000000000000000000000000,
      9999811752826011426569904377285677161739 / 5000000000000000000000000000000000000000,
      19999905876191523430231602514002397991059 / 10000000000000000000000000000000000000000,
      3999995293806807639716102840686104076193 / 2000000000000000000000000000000000000000,
      799999764690305775328182574191012541693 / 400000000000000000000000000000000000000,
      19999998529314357022894629614147757138963 / 10000000000000000000000000000000000000000,
      19999999632328585876166938308058194290101 / 10000000000000000000000000000000000000000,
      19999999908082146257819438662792122979177 / 10000000000000000000000000000000000000000,
      1999999997702053655125346615589108216801 / 1000000000000000000000000000000000000000,
      19999999994255134136988279444372835521781 / 10000000000000000000000000000000000000000,
      19999999998563783534195501917677009805209 / 10000000000000000000000000000000000000000,
      2499999999955118235443206560369460268449 / 1250000000000000000000000000000000000000,
      1999999999991023647088621168345994648883 / 1000000000000000000000000000000000000000,
      4999999999994389779430385082758762682519 / 2500000000000000000000000000000000000000,
      249999999999929872242879803698679896113 / 125000000000000000000000000000000000000,
      4999999999999649361214399006198643683791 / 2500000000000000000000000000000000000000]

end PaperLeanFormalization.SeedNumerics


/-! Fresh numerical certificate component: SeedCenterPairs. -/

/-! Generated exact certificate data. Do not edit emitted source.
Producer: the certificate generator of this development, part: center-pairs
Schema SHA256: 52d78277f3f1ad2146ecf733e1e7238c78f6c1192abbdf0157de3ea8fb3d301a
A generator run is not proof: compile this file and audit its declarations. -/

open Real
noncomputable section

namespace PaperLeanFormalization.SeedNumerics

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private def centerSS01TaylorInput : ℕ → RationalBall := fun _ => ⟨(173667425365721714933979 / 250000000000000000000000), (27640029201 / 250000000000000000000000)⟩
private def centerSS01TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.const (1 / 6227020800)) ⟨(31 / 400000000000), (1 / 100000000000000)⟩) ⟨(-2497461 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-120519 / 10000000000000), (1 / 50000000000000)⟩) ⟨(137184001 / 50000000000000), (3 / 100000000000000)⟩) ⟨(33100167 / 25000000000000), (1 / 50000000000000)⟩) ⟨(-19708869173 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-4755415023 / 50000000000000), (1 / 50000000000000)⟩) ⟨(823822503287 / 100000000000000), (3 / 100000000000000)⟩) ⟨(198774362643 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-16269117941381 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-785092307301 / 10000000000000), (1 / 20000000000000)⟩) ⟨(9214907692699 / 10000000000000), (1 / 20000000000000)⟩) ⟨(64013171758953 / 100000000000000), (7 / 50000000000000)⟩)
private def centerSS01TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1 / 6250000000000)⟩) (.const (1 / 479001600)) ⟨(12593 / 12500000000000), (1 / 100000000000000)⟩) ⟨(-1098263 / 4000000000000), (1 / 50000000000000)⟩) ⟨(-13249609 / 100000000000000), (1 / 50000000000000)⟩) ⟨(2466909121 / 100000000000000), (3 / 100000000000000)⟩) ⟨(297611613 / 25000000000000), (1 / 50000000000000)⟩) ⟨(-137698442437 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-13289717153 / 20000000000000), (1 / 50000000000000)⟩) ⟨(2050109040451 / 50000000000000), (3 / 100000000000000)⟩) ⟨(989312907181 / 50000000000000), (3 / 100000000000000)⟩) ⟨(-24010687092819 / 50000000000000), (3 / 100000000000000)⟩) ⟨(-23173482173407 / 100000000000000), (1 / 10000000000000)⟩) ⟨(76826517826593 / 100000000000000), (1 / 10000000000000)⟩)

theorem centerSS01Taylor {x : ℝ}
    (hx : |x-((173667425365721714933979 / 250000000000000000000000) : ℝ)| ≤ (27640029201 / 250000000000000000000000)) :
    |sin x-((64013171758953 / 100000000000000) : ℝ)| ≤ (311 / 25000000000000) ∧
    |cos x-((76826517826593 / 100000000000000) : ℝ)| ≤ (31 / 2500000000000) := by
  have hs := Certificate.sound centerSS01TaylorSin centerSS01TaylorInput (fun _ => x)
    (by intro i; simpa [centerSS01TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerSS01TaylorInput,centerSS01TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerSS01TaylorCos centerSS01TaylorInput (fun _ => x)
    (by intro i; simpa [centerSS01TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerSS01TaylorInput,centerSS01TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerSS01TaylorSin-
      ((64013171758953 / 100000000000000) : ℝ)| ≤ (7 / 50000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerSS01TaylorInput,centerSS01TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerSS01TaylorCos-
      ((76826517826593 / 100000000000000) : ℝ)| ≤ (1 / 10000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerSS01TaylorInput,centerSS01TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerSS01TaylorSin = sinTaylor x := by
    norm_num [centerSS01TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerSS01TaylorCos = cosTaylor x := by
    norm_num [centerSS01TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((173667425365721714933979 / 250000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerSS01Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(566366507064409214933979 / 250000000000000000000000), (90140029201 / 250000000000000000000000)⟩, ⟨(76826517826593 / 100000000000000), (31 / 2500000000000)⟩, ⟨(-64013171758953 / 100000000000000), (311 / 25000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerSS01J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-56636650706441 / 25000000000000), (37 / 100000000000000)⟩) ⟨(43806331266593 / 50000000000000), (87 / 100000000000000)⟩) (.atom 3) ⟨(-1402091103749 / 2500000000000), (573 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(20742873676633 / 100000000000000), (1193 / 50000000000000)⟩)
private def centerSS01First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-56636650706441 / 25000000000000), (37 / 100000000000000)⟩) ⟨(43806331266593 / 50000000000000), (87 / 100000000000000)⟩) ⟨(-43806331266593 / 50000000000000), (87 / 100000000000000)⟩) (.atom 2) ⟨(-67309757799411 / 100000000000000), (577 / 50000000000000)⟩)
private def centerSS01Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(76826517826593 / 50000000000000), (31 / 1250000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-56636650706441 / 25000000000000), (37 / 100000000000000)⟩) ⟨(43806331266593 / 50000000000000), (87 / 100000000000000)⟩) (.atom 3) ⟨(-1402091103749 / 2500000000000), (573 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(20742873676633 / 100000000000000), (1193 / 50000000000000)⟩) ⟨(-20742873676633 / 100000000000000), (1193 / 50000000000000)⟩) ⟨(132910161976553 / 100000000000000), (2433 / 50000000000000)⟩)

theorem centerSS01 {t : ℝ}
    (ht : |t-((90140029201 / 125000000000) : ℝ)*π| ≤ 0) :
    |J t-((20742873676633 / 100000000000000) : ℝ)| ≤ (1193 / 50000000000000) ∧
    |J1 t-((-67309757799411 / 100000000000000) : ℝ)| ≤ (577 / 50000000000000) ∧
    |J2 t-((132910161976553 / 100000000000000) : ℝ)| ≤ (2433 / 50000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((1 / 2) : ℝ)*π-((173667425365721714933979 / 250000000000000000000000) : ℝ)| ≤ (27640029201 / 250000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerSS01Taylor hred
  have hreduced : t-((1 / 2) : ℝ)*π = t-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((76826517826593 / 100000000000000) : ℝ)| ≤ (31 / 2500000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hc : |cos t-((-64013171758953 / 100000000000000) : ℝ)| ≤ (311 / 25000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((566366507064409214933979 / 250000000000000000000000) : ℝ)| ≤ (90140029201 / 250000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerSS01Input i).center : ℝ)| ≤ ((centerSS01Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerSS01Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerSS01Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerSS01Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerSS01Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerSS01Input i).center : ℝ)| ≤ ((centerSS01Input i).radius : ℝ) := by
    intro i
    simpa [centerSS01Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerSS01J centerSS01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS01Input,centerSS01J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS01J = J t := by
    norm_num [centerSS01J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((20742873676633 / 100000000000000) : ℝ)| ≤ (1193 / 50000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerSS01Input,centerSS01J,Fin.ofNat]
  have hFirst := Certificate.sound centerSS01First centerSS01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS01Input,centerSS01First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS01First = J1 t := by
    norm_num [centerSS01First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-67309757799411 / 100000000000000) : ℝ)| ≤ (577 / 50000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerSS01Input,centerSS01First,Fin.ofNat]
  have hSecond := Certificate.sound centerSS01Second centerSS01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS01Input,centerSS01Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS01Second = J2 t := by
    norm_num [centerSS01Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((132910161976553 / 100000000000000) : ℝ)| ≤ (2433 / 50000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerSS01Input,centerSS01Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerSS02TaylorInput : ℕ → RationalBall := fun _ => ⟨(-539323561401612692880417 / 2000000000000000000000000), (85836010723 / 2000000000000000000000000)⟩
private def centerSS02TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(73 / 6250000000000), (1 / 100000000000000)⟩) ⟨(-2504043 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-22761 / 12500000000000), (1 / 100000000000000)⟩) ⟨(2151493 / 781250000000), (1 / 50000000000000)⟩) ⟨(10012873 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-3964248819 / 20000000000000), (1 / 50000000000000)⟩) ⟨(-1441350841 / 100000000000000), (1 / 100000000000000)⟩) ⟨(207972995623 / 25000000000000), (1 / 50000000000000)⟩) ⟨(60493085247 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-830308679071 / 5000000000000), (1 / 50000000000000)⟩) ⟨(-1207559028373 / 100000000000000), (1 / 100000000000000)⟩) ⟨(98792440971627 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-6660136388047 / 25000000000000), (1 / 20000000000000)⟩)
private def centerSS02TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (3 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(15181 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-13771069 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-400559 / 20000000000000), (1 / 100000000000000)⟩) ⟨(495631187 / 20000000000000), (1 / 50000000000000)⟩) ⟨(36041049 / 20000000000000), (1 / 100000000000000)⟩) ⟨(-34677170911 / 25000000000000), (1 / 50000000000000)⟩) ⟨(-1008654537 / 10000000000000), (1 / 100000000000000)⟩) ⟨(4156580121297 / 100000000000000), (1 / 50000000000000)⟩) ⟨(302256015091 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-49697743984909 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1806947252011 / 50000000000000), (1 / 50000000000000)⟩) ⟨(48193052747989 / 50000000000000), (1 / 50000000000000)⟩)

theorem centerSS02Taylor {x : ℝ}
    (hx : |x-((-539323561401612692880417 / 2000000000000000000000000) : ℝ)| ≤ (85836010723 / 2000000000000000000000000)) :
    |sin x-((-6660136388047 / 25000000000000) : ℝ)| ≤ (247 / 20000000000000) ∧
    |cos x-((48193052747989 / 50000000000000) : ℝ)| ≤ (77 / 6250000000000) := by
  have hs := Certificate.sound centerSS02TaylorSin centerSS02TaylorInput (fun _ => x)
    (by intro i; simpa [centerSS02TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerSS02TaylorInput,centerSS02TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerSS02TaylorCos centerSS02TaylorInput (fun _ => x)
    (by intro i; simpa [centerSS02TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerSS02TaylorInput,centerSS02TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerSS02TaylorSin-
      ((-6660136388047 / 25000000000000) : ℝ)| ≤ (1 / 20000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerSS02TaylorInput,centerSS02TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerSS02TaylorCos-
      ((48193052747989 / 50000000000000) : ℝ)| ≤ (1 / 50000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerSS02TaylorInput,centerSS02TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerSS02TaylorSin = sinTaylor x := by
    norm_num [centerSS02TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerSS02TaylorCos = cosTaylor x := by
    norm_num [centerSS02TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-539323561401612692880417 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerSS02Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(8885454399366887307119583 / 2000000000000000000000000), (1414163989277 / 2000000000000000000000000)⟩, ⟨(-48193052747989 / 50000000000000), (77 / 6250000000000)⟩, ⟨(-6660136388047 / 25000000000000), (247 / 20000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerSS02J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-55534089996043 / 12500000000000), (9 / 12500000000000)⟩) ⟨(46011452687389 / 25000000000000), (43 / 25000000000000)⟩) ⟨(-46011452687389 / 25000000000000), (43 / 25000000000000)⟩) ⟨(65056727304697 / 50000000000000), (111 / 50000000000000)⟩) (.atom 3) ⟨(-34662934144741 / 100000000000000), (1667 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(61723171351237 / 100000000000000), (2899 / 100000000000000)⟩)
private def centerSS02First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-55534089996043 / 12500000000000), (9 / 12500000000000)⟩) ⟨(46011452687389 / 25000000000000), (43 / 25000000000000)⟩) ⟨(-46011452687389 / 25000000000000), (43 / 25000000000000)⟩) ⟨(65056727304697 / 50000000000000), (111 / 50000000000000)⟩) ⟨(-65056727304697 / 50000000000000), (111 / 50000000000000)⟩) (.atom 2) ⟨(7838205726517 / 6250000000000), (909 / 50000000000000)⟩)
private def centerSS02Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(48193052747989 / 25000000000000), (77 / 3125000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-55534089996043 / 12500000000000), (9 / 12500000000000)⟩) ⟨(46011452687389 / 25000000000000), (43 / 25000000000000)⟩) ⟨(-46011452687389 / 25000000000000), (43 / 25000000000000)⟩) ⟨(65056727304697 / 50000000000000), (111 / 50000000000000)⟩) (.atom 3) ⟨(-34662934144741 / 100000000000000), (1667 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(61723171351237 / 100000000000000), (2899 / 100000000000000)⟩) ⟨(-61723171351237 / 100000000000000), (2899 / 100000000000000)⟩) ⟨(131049039640719 / 100000000000000), (5363 / 100000000000000)⟩)

theorem centerSS02 {t : ℝ}
    (ht : |t-((1414163989277 / 1000000000000) : ℝ)*π| ≤ 0) :
    |J t-((61723171351237 / 100000000000000) : ℝ)| ≤ (2899 / 100000000000000) ∧
    |J1 t-((7838205726517 / 6250000000000) : ℝ)| ≤ (909 / 50000000000000) ∧
    |J2 t-((131049039640719 / 100000000000000) : ℝ)| ≤ (5363 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((3 / 2) : ℝ)*π-((-539323561401612692880417 / 2000000000000000000000000) : ℝ)| ≤ (85836010723 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerSS02Taylor hred
  have hreduced : t-((3 / 2) : ℝ)*π = (t-π)-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-48193052747989 / 50000000000000) : ℝ)| ≤ (77 / 6250000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hc : |cos t-((-6660136388047 / 25000000000000) : ℝ)| ≤ (247 / 20000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((8885454399366887307119583 / 2000000000000000000000000) : ℝ)| ≤ (1414163989277 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerSS02Input i).center : ℝ)| ≤ ((centerSS02Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerSS02Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerSS02Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerSS02Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerSS02Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerSS02Input i).center : ℝ)| ≤ ((centerSS02Input i).radius : ℝ) := by
    intro i
    simpa [centerSS02Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = 2*π-t := by
    have ht0 : 0 ≤ 2*π-t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : 2*π-t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (2*π-t) = cos t := by rw [show 2*π-t = -(t-2*π) by ring,cos_neg,cos_sub_two_pi]
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerSS02J centerSS02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS02Input,centerSS02J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS02J = J t := by
    norm_num [centerSS02J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((61723171351237 / 100000000000000) : ℝ)| ≤ (2899 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerSS02Input,centerSS02J,Fin.ofNat]
  have hFirst := Certificate.sound centerSS02First centerSS02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS02Input,centerSS02First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS02First = J1 t := by
    norm_num [centerSS02First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((7838205726517 / 6250000000000) : ℝ)| ≤ (909 / 50000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerSS02Input,centerSS02First,Fin.ofNat]
  have hSecond := Certificate.sound centerSS02Second centerSS02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS02Input,centerSS02Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS02Second = J2 t := by
    norm_num [centerSS02Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((131049039640719 / 100000000000000) : ℝ)| ≤ (5363 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerSS02Input,centerSS02Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerSS12TaylorInput : ℕ → RationalBall := fun _ => ⟨(1212929689262113587647751 / 2000000000000000000000000), (193043755669 / 2000000000000000000000000)⟩
private def centerSS12TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.const (1 / 6227020800)) ⟨(5907 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-312413 / 12500000000000), (1 / 50000000000000)⟩) ⟨(-919243 / 100000000000000), (1 / 100000000000000)⟩) ⟨(274653949 / 100000000000000), (1 / 50000000000000)⟩) ⟨(20203523 / 20000000000000), (1 / 50000000000000)⟩) ⟨(-9870126113 / 50000000000000), (3 / 100000000000000)⟩) ⟨(-3630228513 / 50000000000000), (1 / 50000000000000)⟩) ⟨(826072876307 / 100000000000000), (3 / 100000000000000)⟩) ⟨(151914639949 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-16362837386769 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-6018245172913 / 100000000000000), (1 / 25000000000000)⟩) ⟨(93981754827087 / 100000000000000), (1 / 25000000000000)⟩) ⟨(56996630339363 / 100000000000000), (3 / 25000000000000)⟩)
private def centerSS12TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (3 / 25000000000000)⟩) (.const (1 / 479001600)) ⟨(15357 / 20000000000000), (1 / 100000000000000)⟩) ⟨(-13740267 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-1010733 / 10000000000000), (1 / 50000000000000)⟩) ⟨(12350257 / 500000000000), (3 / 100000000000000)⟩) ⟨(28390123 / 3125000000000), (1 / 50000000000000)⟩) ⟨(-137980404953 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-25374569411 / 50000000000000), (1 / 50000000000000)⟩) ⟨(823183505569 / 20000000000000), (3 / 100000000000000)⟩) ⟨(1513832852369 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-48486167147631 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-17833193259333 / 100000000000000), (7 / 100000000000000)⟩) ⟨(82166806740667 / 100000000000000), (7 / 100000000000000)⟩)

theorem centerSS12Taylor {x : ℝ}
    (hx : |x-((1212929689262113587647751 / 2000000000000000000000000) : ℝ)| ≤ (193043755669 / 2000000000000000000000000)) :
    |sin x-((56996630339363 / 100000000000000) : ℝ)| ≤ (621 / 50000000000000) ∧
    |cos x-((82166806740667 / 100000000000000) : ℝ)| ≤ (1237 / 100000000000000) := by
  have hs := Certificate.sound centerSS12TaylorSin centerSS12TaylorInput (fun _ => x)
    (by intro i; simpa [centerSS12TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerSS12TaylorInput,centerSS12TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerSS12TaylorCos centerSS12TaylorInput (fun _ => x)
    (by intro i; simpa [centerSS12TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerSS12TaylorInput,centerSS12TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerSS12TaylorSin-
      ((56996630339363 / 100000000000000) : ℝ)| ≤ (3 / 25000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerSS12TaylorInput,centerSS12TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerSS12TaylorCos-
      ((82166806740667 / 100000000000000) : ℝ)| ≤ (7 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerSS12TaylorInput,centerSS12TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerSS12TaylorSin = sinTaylor x := by
    norm_num [centerSS12TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerSS12TaylorCos = cosTaylor x := by
    norm_num [centerSS12TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((1212929689262113587647751 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerSS12Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(4354522342851613587647751 / 2000000000000000000000000), (693043755669 / 2000000000000000000000000)⟩, ⟨(82166806740667 / 100000000000000), (1237 / 100000000000000)⟩, ⟨(-56996630339363 / 100000000000000), (621 / 50000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerSS12J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-217726117142581 / 100000000000000), (7 / 20000000000000)⟩) ⟨(96433148216369 / 100000000000000), (17 / 20000000000000)⟩) (.atom 3) ⟨(-27481822506747 / 50000000000000), (1247 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(27203161727173 / 100000000000000), (621 / 25000000000000)⟩)
private def centerSS12First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-217726117142581 / 100000000000000), (7 / 20000000000000)⟩) ⟨(96433148216369 / 100000000000000), (17 / 20000000000000)⟩) ⟨(-96433148216369 / 100000000000000), (17 / 20000000000000)⟩) (.atom 2) ⟨(-15847207705777 / 20000000000000), (1263 / 100000000000000)⟩)
private def centerSS12Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(82166806740667 / 50000000000000), (1237 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-217726117142581 / 100000000000000), (7 / 20000000000000)⟩) ⟨(96433148216369 / 100000000000000), (17 / 20000000000000)⟩) (.atom 3) ⟨(-27481822506747 / 50000000000000), (1247 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(27203161727173 / 100000000000000), (621 / 25000000000000)⟩) ⟨(-27203161727173 / 100000000000000), (621 / 25000000000000)⟩) ⟨(137130451754161 / 100000000000000), (2479 / 50000000000000)⟩)

theorem centerSS12 {t : ℝ}
    (ht : |t-((693043755669 / 1000000000000) : ℝ)*π| ≤ 0) :
    |J t-((27203161727173 / 100000000000000) : ℝ)| ≤ (621 / 25000000000000) ∧
    |J1 t-((-15847207705777 / 20000000000000) : ℝ)| ≤ (1263 / 100000000000000) ∧
    |J2 t-((137130451754161 / 100000000000000) : ℝ)| ≤ (2479 / 50000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((1 / 2) : ℝ)*π-((1212929689262113587647751 / 2000000000000000000000000) : ℝ)| ≤ (193043755669 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerSS12Taylor hred
  have hreduced : t-((1 / 2) : ℝ)*π = t-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((82166806740667 / 100000000000000) : ℝ)| ≤ (1237 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hc : |cos t-((-56996630339363 / 100000000000000) : ℝ)| ≤ (621 / 50000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((4354522342851613587647751 / 2000000000000000000000000) : ℝ)| ≤ (693043755669 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerSS12Input i).center : ℝ)| ≤ ((centerSS12Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerSS12Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerSS12Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerSS12Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerSS12Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerSS12Input i).center : ℝ)| ≤ ((centerSS12Input i).radius : ℝ) := by
    intro i
    simpa [centerSS12Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerSS12J centerSS12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS12Input,centerSS12J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS12J = J t := by
    norm_num [centerSS12J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((27203161727173 / 100000000000000) : ℝ)| ≤ (621 / 25000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerSS12Input,centerSS12J,Fin.ofNat]
  have hFirst := Certificate.sound centerSS12First centerSS12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS12Input,centerSS12First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS12First = J1 t := by
    norm_num [centerSS12First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-15847207705777 / 20000000000000) : ℝ)| ≤ (1263 / 100000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerSS12Input,centerSS12First,Fin.ofNat]
  have hSecond := Certificate.sound centerSS12Second centerSS12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerSS12Input,centerSS12Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerSS12Second = J2 t := by
    norm_num [centerSS12Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((137130451754161 / 100000000000000) : ℝ)| ≤ (2479 / 50000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerSS12Input,centerSS12Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST00TaylorInput : ℕ → RationalBall := fun _ => ⟨(-174881564695898900959383 / 250000000000000000000000), (27833265477 / 250000000000000000000000)⟩
private def centerST00TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.const (1 / 6227020800)) ⟨(3929 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-2497353 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-1222047 / 100000000000000), (1 / 50000000000000)⟩) ⟨(54870229 / 20000000000000), (3 / 100000000000000)⟩) ⟨(134250163 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-9853509839 / 50000000000000), (3 / 100000000000000)⟩) ⟨(-9643373627 / 100000000000000), (1 / 50000000000000)⟩) ⟨(411844979853 / 50000000000000), (3 / 100000000000000)⟩) ⟨(629784317 / 156250000000), (3 / 100000000000000)⟩) ⟨(-16263604703787 / 100000000000000), (1 / 25000000000000)⟩) ⟨(-7958383319083 / 100000000000000), (1 / 20000000000000)⟩) ⟨(92041616680917 / 100000000000000), (1 / 20000000000000)⟩) ⟨(-16096381942299 / 25000000000000), (3 / 20000000000000)⟩)
private def centerST00TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (1 / 6250000000000)⟩) (.const (1 / 479001600)) ⟨(51079 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-27455161 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-6717413 / 50000000000000), (1 / 50000000000000)⟩) ⟨(38542561 / 1562500000000), (3 / 100000000000000)⟩) ⟨(603529621 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-137681829647 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-67372811647 / 100000000000000), (1 / 50000000000000)⟩) ⟨(204964692751 / 5000000000000), (3 / 100000000000000)⟩) ⟨(2005936102727 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-47994063897273 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-2935658826039 / 12500000000000), (1 / 10000000000000)⟩) ⟨(9564341173961 / 12500000000000), (1 / 10000000000000)⟩)

theorem centerST00Taylor {x : ℝ}
    (hx : |x-((-174881564695898900959383 / 250000000000000000000000) : ℝ)| ≤ (27833265477 / 250000000000000000000000)) :
    |sin x-((-16096381942299 / 25000000000000) : ℝ)| ≤ (249 / 20000000000000) ∧
    |cos x-((9564341173961 / 12500000000000) : ℝ)| ≤ (31 / 2500000000000) := by
  have hs := Certificate.sound centerST00TaylorSin centerST00TaylorInput (fun _ => x)
    (by intro i; simpa [centerST00TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST00TaylorInput,centerST00TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST00TaylorCos centerST00TaylorInput (fun _ => x)
    (by intro i; simpa [centerST00TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST00TaylorInput,centerST00TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST00TaylorSin-
      ((-16096381942299 / 25000000000000) : ℝ)| ≤ (3 / 20000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST00TaylorInput,centerST00TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST00TaylorCos-
      ((9564341173961 / 12500000000000) : ℝ)| ≤ (1 / 10000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST00TaylorInput,centerST00TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST00TaylorSin = sinTaylor x := by
    norm_num [centerST00TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST00TaylorCos = cosTaylor x := by
    norm_num [centerST00TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-174881564695898900959383 / 250000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST00Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(1395914762098851099040617 / 250000000000000000000000), (222166734523 / 250000000000000000000000)⟩, ⟨(-16096381942299 / 25000000000000), (249 / 20000000000000)⟩, ⟨(9564341173961 / 12500000000000), (31 / 2500000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST00J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-27918295241977 / 5000000000000), (9 / 10000000000000)⟩) ⟨(1748815646959 / 2500000000000), (19 / 10000000000000)⟩) ⟨(-1748815646959 / 2500000000000), (19 / 10000000000000)⟩) ⟨(24420663948059 / 10000000000000), (3 / 1250000000000)⟩) (.atom 3) ⟨(186854049355109 / 100000000000000), (3213 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(50247915424861 / 20000000000000), (2229 / 50000000000000)⟩)
private def centerST00First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-27918295241977 / 5000000000000), (9 / 10000000000000)⟩) ⟨(1748815646959 / 2500000000000), (19 / 10000000000000)⟩) ⟨(-1748815646959 / 2500000000000), (19 / 10000000000000)⟩) ⟨(24420663948059 / 10000000000000), (3 / 1250000000000)⟩) ⟨(-24420663948059 / 10000000000000), (3 / 1250000000000)⟩) (.atom 2) ⟨(39308433419249 / 25000000000000), (799 / 25000000000000)⟩)
private def centerST00Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(16096381942299 / 12500000000000), (249 / 10000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-27918295241977 / 5000000000000), (9 / 10000000000000)⟩) ⟨(1748815646959 / 2500000000000), (19 / 10000000000000)⟩) ⟨(-1748815646959 / 2500000000000), (19 / 10000000000000)⟩) ⟨(24420663948059 / 10000000000000), (3 / 1250000000000)⟩) (.atom 3) ⟨(186854049355109 / 100000000000000), (3213 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(50247915424861 / 20000000000000), (2229 / 50000000000000)⟩) ⟨(-50247915424861 / 20000000000000), (2229 / 50000000000000)⟩) ⟨(-122468521585913 / 100000000000000), (1737 / 25000000000000)⟩)

theorem centerST00 {t : ℝ}
    (ht : |t-((222166734523 / 125000000000) : ℝ)*π| ≤ 0) :
    |J t-((50247915424861 / 20000000000000) : ℝ)| ≤ (2229 / 50000000000000) ∧
    |J1 t-((39308433419249 / 25000000000000) : ℝ)| ≤ (799 / 25000000000000) ∧
    |J2 t-((-122468521585913 / 100000000000000) : ℝ)| ≤ (1737 / 25000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-(2 : ℝ)*π-((-174881564695898900959383 / 250000000000000000000000) : ℝ)| ≤ (27833265477 / 250000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST00Taylor hred
  have hreduced : t-(2 : ℝ)*π = t-2*π := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-16096381942299 / 25000000000000) : ℝ)| ≤ (249 / 20000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hc : |cos t-((9564341173961 / 12500000000000) : ℝ)| ≤ (31 / 2500000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((1395914762098851099040617 / 250000000000000000000000) : ℝ)| ≤ (222166734523 / 250000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST00Input i).center : ℝ)| ≤ ((centerST00Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST00Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST00Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST00Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST00Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST00Input i).center : ℝ)| ≤ ((centerST00Input i).radius : ℝ) := by
    intro i
    simpa [centerST00Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = 2*π-t := by
    have ht0 : 0 ≤ 2*π-t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : 2*π-t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (2*π-t) = cos t := by rw [show 2*π-t = -(t-2*π) by ring,cos_neg,cos_sub_two_pi]
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST00J centerST00Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST00Input,centerST00J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST00J = J t := by
    norm_num [centerST00J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((50247915424861 / 20000000000000) : ℝ)| ≤ (2229 / 50000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST00Input,centerST00J,Fin.ofNat]
  have hFirst := Certificate.sound centerST00First centerST00Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST00Input,centerST00First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST00First = J1 t := by
    norm_num [centerST00First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((39308433419249 / 25000000000000) : ℝ)| ≤ (799 / 25000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST00Input,centerST00First,Fin.ofNat]
  have hSecond := Certificate.sound centerST00Second centerST00Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST00Input,centerST00Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST00Second = J2 t := by
    norm_num [centerST00Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((-122468521585913 / 100000000000000) : ℝ)| ≤ (1737 / 25000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST00Input,centerST00Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST01TaylorInput : ℕ → RationalBall := fun _ => ⟨(-43981870796336400959383 / 250000000000000000000000), (20999796431 / 750000000000000000000000)⟩
private def centerST01TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(497 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1252357 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-38761 / 50000000000000), (1 / 100000000000000)⟩) ⟨(27549567 / 10000000000000), (1 / 50000000000000)⟩) ⟨(8526723 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-9916371559 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-306916453 / 50000000000000), (1 / 100000000000000)⟩) ⟨(832719500427 / 100000000000000), (1 / 50000000000000)⟩) ⟨(12886533847 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-16640893598973 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-515043633533 / 100000000000000), (1 / 100000000000000)⟩) ⟨(99484956366467 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-4375534497089 / 25000000000000), (1 / 25000000000000)⟩)
private def centerST01TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(6461 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-13775429 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-106589 / 12500000000000), (1 / 100000000000000)⟩) ⟨(1239653009 / 50000000000000), (1 / 50000000000000)⟩) ⟨(7673571 / 10000000000000), (1 / 100000000000000)⟩) ⟨(-138812153179 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-4296302679 / 100000000000000), (1 / 100000000000000)⟩) ⟨(1040592590997 / 25000000000000), (1 / 50000000000000)⟩) ⟨(32206839489 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-12467793160511 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-385884174629 / 25000000000000), (1 / 100000000000000)⟩) ⟨(24614115825371 / 25000000000000), (1 / 100000000000000)⟩)

theorem centerST01Taylor {x : ℝ}
    (hx : |x-((-43981870796336400959383 / 250000000000000000000000) : ℝ)| ≤ (20999796431 / 750000000000000000000000)) :
    |sin x-((-4375534497089 / 25000000000000) : ℝ)| ≤ (617 / 50000000000000) ∧
    |cos x-((24614115825371 / 25000000000000) : ℝ)| ≤ (1231 / 100000000000000) := by
  have hs := Certificate.sound centerST01TaylorSin centerST01TaylorInput (fun _ => x)
    (by intro i; simpa [centerST01TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST01TaylorInput,centerST01TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST01TaylorCos centerST01TaylorInput (fun _ => x)
    (by intro i; simpa [centerST01TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST01TaylorInput,centerST01TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST01TaylorSin-
      ((-4375534497089 / 25000000000000) : ℝ)| ≤ (1 / 25000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST01TaylorInput,centerST01TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST01TaylorCos-
      ((24614115825371 / 25000000000000) : ℝ)| ≤ (1 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST01TaylorInput,centerST01TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST01TaylorSin = sinTaylor x := by
    norm_num [centerST01TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST01TaylorCos = cosTaylor x := by
    norm_num [centerST01TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-43981870796336400959383 / 250000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST01Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(741416292601038599040617 / 250000000000000000000000), (354000203569 / 750000000000000000000000)⟩, ⟨(4375534497089 / 25000000000000), (617 / 50000000000000)⟩, ⟨(-24614115825371 / 25000000000000), (1231 / 100000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST01J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-59313303408083 / 20000000000000), (3 / 6250000000000)⟩) ⟨(3518549663707 / 20000000000000), (49 / 50000000000000)⟩) (.atom 3) ⟨(-17321197791961 / 100000000000000), (157 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(36188039279 / 20000000000000), (387 / 25000000000000)⟩)
private def centerST01First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-59313303408083 / 20000000000000), (3 / 6250000000000)⟩) ⟨(3518549663707 / 20000000000000), (49 / 50000000000000)⟩) ⟨(-3518549663707 / 20000000000000), (49 / 50000000000000)⟩) (.atom 2) ⟨(-1539553543327 / 50000000000000), (47 / 20000000000000)⟩)
private def centerST01Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(4375534497089 / 12500000000000), (617 / 25000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-59313303408083 / 20000000000000), (3 / 6250000000000)⟩) ⟨(3518549663707 / 20000000000000), (49 / 50000000000000)⟩) (.atom 3) ⟨(-17321197791961 / 100000000000000), (157 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(36188039279 / 20000000000000), (387 / 25000000000000)⟩) ⟨(-36188039279 / 20000000000000), (387 / 25000000000000)⟩) ⟨(34823335780317 / 100000000000000), (251 / 6250000000000)⟩)

theorem centerST01 {t : ℝ}
    (ht : |t-((354000203569 / 375000000000) : ℝ)*π| ≤ 0) :
    |J t-((36188039279 / 20000000000000) : ℝ)| ≤ (387 / 25000000000000) ∧
    |J1 t-((-1539553543327 / 50000000000000) : ℝ)| ≤ (47 / 20000000000000) ∧
    |J2 t-((34823335780317 / 100000000000000) : ℝ)| ≤ (251 / 6250000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-(1 : ℝ)*π-((-43981870796336400959383 / 250000000000000000000000) : ℝ)| ≤ (20999796431 / 750000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST01Taylor hred
  have hreduced : t-(1 : ℝ)*π = t-π := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((4375534497089 / 25000000000000) : ℝ)| ≤ (617 / 50000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hc : |cos t-((-24614115825371 / 25000000000000) : ℝ)| ≤ (1231 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((741416292601038599040617 / 250000000000000000000000) : ℝ)| ≤ (354000203569 / 750000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST01Input i).center : ℝ)| ≤ ((centerST01Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST01Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST01Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST01Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST01Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST01Input i).center : ℝ)| ≤ ((centerST01Input i).radius : ℝ) := by
    intro i
    simpa [centerST01Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST01J centerST01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST01Input,centerST01J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST01J = J t := by
    norm_num [centerST01J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((36188039279 / 20000000000000) : ℝ)| ≤ (387 / 25000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST01Input,centerST01J,Fin.ofNat]
  have hFirst := Certificate.sound centerST01First centerST01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST01Input,centerST01First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST01First = J1 t := by
    norm_num [centerST01First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-1539553543327 / 50000000000000) : ℝ)| ≤ (47 / 20000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST01Input,centerST01First,Fin.ofNat]
  have hSecond := Certificate.sound centerST01Second centerST01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST01Input,centerST01Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST01Second = J2 t := by
    norm_num [centerST01Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((34823335780317 / 100000000000000) : ℝ)| ≤ (251 / 6250000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST01Input,centerST01Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST02TaylorInput : ℕ → RationalBall := fun _ => ⟨(-43981870796336400959383 / 250000000000000000000000), (20999796431 / 750000000000000000000000)⟩
private def centerST02TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(497 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1252357 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-38761 / 50000000000000), (1 / 100000000000000)⟩) ⟨(27549567 / 10000000000000), (1 / 50000000000000)⟩) ⟨(8526723 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-9916371559 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-306916453 / 50000000000000), (1 / 100000000000000)⟩) ⟨(832719500427 / 100000000000000), (1 / 50000000000000)⟩) ⟨(12886533847 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-16640893598973 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-515043633533 / 100000000000000), (1 / 100000000000000)⟩) ⟨(99484956366467 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-4375534497089 / 25000000000000), (1 / 25000000000000)⟩)
private def centerST02TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (1 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(6461 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-13775429 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-106589 / 12500000000000), (1 / 100000000000000)⟩) ⟨(1239653009 / 50000000000000), (1 / 50000000000000)⟩) ⟨(7673571 / 10000000000000), (1 / 100000000000000)⟩) ⟨(-138812153179 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-4296302679 / 100000000000000), (1 / 100000000000000)⟩) ⟨(1040592590997 / 25000000000000), (1 / 50000000000000)⟩) ⟨(32206839489 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-12467793160511 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-385884174629 / 25000000000000), (1 / 100000000000000)⟩) ⟨(24614115825371 / 25000000000000), (1 / 100000000000000)⟩)

theorem centerST02Taylor {x : ℝ}
    (hx : |x-((-43981870796336400959383 / 250000000000000000000000) : ℝ)| ≤ (20999796431 / 750000000000000000000000)) :
    |sin x-((-4375534497089 / 25000000000000) : ℝ)| ≤ (617 / 50000000000000) ∧
    |cos x-((24614115825371 / 25000000000000) : ℝ)| ≤ (1231 / 100000000000000) := by
  have hs := Certificate.sound centerST02TaylorSin centerST02TaylorInput (fun _ => x)
    (by intro i; simpa [centerST02TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST02TaylorInput,centerST02TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST02TaylorCos centerST02TaylorInput (fun _ => x)
    (by intro i; simpa [centerST02TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST02TaylorInput,centerST02TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST02TaylorSin-
      ((-4375534497089 / 25000000000000) : ℝ)| ≤ (1 / 25000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST02TaylorInput,centerST02TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST02TaylorCos-
      ((24614115825371 / 25000000000000) : ℝ)| ≤ (1 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST02TaylorInput,centerST02TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST02TaylorSin = sinTaylor x := by
    norm_num [centerST02TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST02TaylorCos = cosTaylor x := by
    norm_num [centerST02TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-43981870796336400959383 / 250000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST02Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(348717210902351099040617 / 250000000000000000000000), (166500203569 / 750000000000000000000000)⟩, ⟨(24614115825371 / 25000000000000), (1231 / 100000000000000)⟩, ⟨(4375534497089 / 25000000000000), (617 / 50000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST02J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-6974344218047 / 5000000000000), (23 / 100000000000000)⟩) ⟨(17467238099801 / 10000000000000), (73 / 100000000000000)⟩) (.atom 3) ⟨(30571401149819 / 100000000000000), (2169 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(129027864451303 / 100000000000000), (17 / 500000000000)⟩)
private def centerST02First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-6974344218047 / 5000000000000), (23 / 100000000000000)⟩) ⟨(17467238099801 / 10000000000000), (73 / 100000000000000)⟩) ⟨(-17467238099801 / 10000000000000), (73 / 100000000000000)⟩) (.atom 2) ⟨(-85988124347567 / 50000000000000), (2223 / 100000000000000)⟩)
private def centerST02Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(24614115825371 / 12500000000000), (1231 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-6974344218047 / 5000000000000), (23 / 100000000000000)⟩) ⟨(17467238099801 / 10000000000000), (73 / 100000000000000)⟩) (.atom 3) ⟨(30571401149819 / 100000000000000), (2169 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(129027864451303 / 100000000000000), (17 / 500000000000)⟩) ⟨(-129027864451303 / 100000000000000), (17 / 500000000000)⟩) ⟨(13577012430333 / 20000000000000), (2931 / 50000000000000)⟩)

theorem centerST02 {t : ℝ}
    (ht : |t-((166500203569 / 375000000000) : ℝ)*π| ≤ 0) :
    |J t-((129027864451303 / 100000000000000) : ℝ)| ≤ (17 / 500000000000) ∧
    |J1 t-((-85988124347567 / 50000000000000) : ℝ)| ≤ (2223 / 100000000000000) ∧
    |J2 t-((13577012430333 / 20000000000000) : ℝ)| ≤ (2931 / 50000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((1 / 2) : ℝ)*π-((-43981870796336400959383 / 250000000000000000000000) : ℝ)| ≤ (20999796431 / 750000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST02Taylor hred
  have hreduced : t-((1 / 2) : ℝ)*π = t-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((24614115825371 / 25000000000000) : ℝ)| ≤ (1231 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hc : |cos t-((4375534497089 / 25000000000000) : ℝ)| ≤ (617 / 50000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((348717210902351099040617 / 250000000000000000000000) : ℝ)| ≤ (166500203569 / 750000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST02Input i).center : ℝ)| ≤ ((centerST02Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST02Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST02Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST02Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST02Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST02Input i).center : ℝ)| ≤ ((centerST02Input i).radius : ℝ) := by
    intro i
    simpa [centerST02Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST02J centerST02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST02Input,centerST02J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST02J = J t := by
    norm_num [centerST02J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((129027864451303 / 100000000000000) : ℝ)| ≤ (17 / 500000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST02Input,centerST02J,Fin.ofNat]
  have hFirst := Certificate.sound centerST02First centerST02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST02Input,centerST02First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST02First = J1 t := by
    norm_num [centerST02First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-85988124347567 / 50000000000000) : ℝ)| ≤ (2223 / 100000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST02Input,centerST02First,Fin.ofNat]
  have hSecond := Certificate.sound centerST02Second centerST02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST02Input,centerST02Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST02Second = J2 t := by
    norm_num [centerST02Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((13577012430333 / 20000000000000) : ℝ)| ≤ (2931 / 50000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST02Input,centerST02Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST10TaylorInput : ℕ → RationalBall := fun _ => ⟨(22075045818533442053319 / 125000000000000000000000), (3513352661 / 125000000000000000000000)⟩
private def centerST10TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.const (1 / 6227020800)) ⟨(501 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-250471 / 10000000000000), (1 / 50000000000000)⟩) ⟨(-19529 / 25000000000000), (1 / 100000000000000)⟩) ⟨(68873769 / 25000000000000), (1 / 50000000000000)⟩) ⟨(1718411 / 20000000000000), (1 / 100000000000000)⟩) ⟨(-9916338893 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-154633849 / 25000000000000), (1 / 100000000000000)⟩) ⟨(832714797937 / 100000000000000), (1 / 50000000000000)⟩) ⟨(25970450531 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-2080087027017 / 12500000000000), (1 / 50000000000000)⟩) ⟨(-51898486607 / 10000000000000), (1 / 100000000000000)⟩) ⟨(9948101513393 / 10000000000000), (1 / 100000000000000)⟩) ⟨(8784191868623 / 50000000000000), (1 / 25000000000000)⟩)
private def centerST10TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (1 / 50000000000000)⟩) (.const (1 / 479001600)) ⟨(6511 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-3443851 / 12500000000000), (1 / 50000000000000)⟩) ⟨(-429623 / 50000000000000), (1 / 100000000000000)⟩) ⟨(619824871 / 25000000000000), (1 / 50000000000000)⟩) ⟨(38661811 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-138811565267 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-541151499 / 12500000000000), (1 / 100000000000000)⟩) ⟨(166493498187 / 4000000000000), (1 / 50000000000000)⟩) ⟨(25962737597 / 20000000000000), (1 / 100000000000000)⟩) ⟨(-9974037262403 / 20000000000000), (1 / 100000000000000)⟩) ⟨(-77766794213 / 5000000000000), (1 / 50000000000000)⟩) ⟨(4922233205787 / 5000000000000), (1 / 50000000000000)⟩)

theorem centerST10Taylor {x : ℝ}
    (hx : |x-((22075045818533442053319 / 125000000000000000000000) : ℝ)| ≤ (3513352661 / 125000000000000000000000)) :
    |sin x-((8784191868623 / 50000000000000) : ℝ)| ≤ (617 / 50000000000000) ∧
    |cos x-((4922233205787 / 5000000000000) : ℝ)| ≤ (77 / 6250000000000) := by
  have hs := Certificate.sound centerST10TaylorSin centerST10TaylorInput (fun _ => x)
    (by intro i; simpa [centerST10TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST10TaylorInput,centerST10TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST10TaylorCos centerST10TaylorInput (fun _ => x)
    (by intro i; simpa [centerST10TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST10TaylorInput,centerST10TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST10TaylorSin-
      ((8784191868623 / 50000000000000) : ℝ)| ≤ (1 / 25000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST10TaylorInput,centerST10TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST10TaylorCos-
      ((4922233205787 / 5000000000000) : ℝ)| ≤ (1 / 50000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST10TaylorInput,centerST10TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST10TaylorSin = sinTaylor x := by
    norm_num [centerST10TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST10TaylorCos = cosTaylor x := by
    norm_num [centerST10TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((22075045818533442053319 / 125000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST10Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(414774127517220942053319 / 125000000000000000000000), (66013352661 / 125000000000000000000000)⟩, ⟨(-8784191868623 / 50000000000000), (617 / 50000000000000)⟩, ⟨(-4922233205787 / 5000000000000), (77 / 6250000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST10J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-331819302013777 / 100000000000000), (27 / 50000000000000)⟩) ⟨(296499228704123 / 100000000000000), (77 / 50000000000000)⟩) ⟨(-296499228704123 / 100000000000000), (77 / 50000000000000)⟩) ⟨(17660036654827 / 100000000000000), (51 / 25000000000000)⟩) (.atom 3) ⟨(-17385363767561 / 100000000000000), (419 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(36603993937 / 20000000000000), (1653 / 100000000000000)⟩)
private def centerST10First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-331819302013777 / 100000000000000), (27 / 50000000000000)⟩) ⟨(296499228704123 / 100000000000000), (77 / 50000000000000)⟩) ⟨(-296499228704123 / 100000000000000), (77 / 50000000000000)⟩) ⟨(17660036654827 / 100000000000000), (51 / 25000000000000)⟩) ⟨(-17660036654827 / 100000000000000), (51 / 25000000000000)⟩) (.atom 2) ⟨(1551291503829 / 50000000000000), (51 / 20000000000000)⟩)
private def centerST10Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(8784191868623 / 25000000000000), (617 / 25000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-331819302013777 / 100000000000000), (27 / 50000000000000)⟩) ⟨(296499228704123 / 100000000000000), (77 / 50000000000000)⟩) ⟨(-296499228704123 / 100000000000000), (77 / 50000000000000)⟩) ⟨(17660036654827 / 100000000000000), (51 / 25000000000000)⟩) (.atom 3) ⟨(-17385363767561 / 100000000000000), (419 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(36603993937 / 20000000000000), (1653 / 100000000000000)⟩) ⟨(-36603993937 / 20000000000000), (1653 / 100000000000000)⟩) ⟨(34953747504807 / 100000000000000), (4121 / 100000000000000)⟩)

theorem centerST10 {t : ℝ}
    (ht : |t-((66013352661 / 62500000000) : ℝ)*π| ≤ 0) :
    |J t-((36603993937 / 20000000000000) : ℝ)| ≤ (1653 / 100000000000000) ∧
    |J1 t-((1551291503829 / 50000000000000) : ℝ)| ≤ (51 / 20000000000000) ∧
    |J2 t-((34953747504807 / 100000000000000) : ℝ)| ≤ (4121 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-(1 : ℝ)*π-((22075045818533442053319 / 125000000000000000000000) : ℝ)| ≤ (3513352661 / 125000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST10Taylor hred
  have hreduced : t-(1 : ℝ)*π = t-π := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-8784191868623 / 50000000000000) : ℝ)| ≤ (617 / 50000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hc : |cos t-((-4922233205787 / 5000000000000) : ℝ)| ≤ (77 / 6250000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((414774127517220942053319 / 125000000000000000000000) : ℝ)| ≤ (66013352661 / 125000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST10Input i).center : ℝ)| ≤ ((centerST10Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST10Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST10Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST10Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST10Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST10Input i).center : ℝ)| ≤ ((centerST10Input i).radius : ℝ) := by
    intro i
    simpa [centerST10Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = 2*π-t := by
    have ht0 : 0 ≤ 2*π-t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : 2*π-t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (2*π-t) = cos t := by rw [show 2*π-t = -(t-2*π) by ring,cos_neg,cos_sub_two_pi]
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST10J centerST10Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST10Input,centerST10J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST10J = J t := by
    norm_num [centerST10J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((36603993937 / 20000000000000) : ℝ)| ≤ (1653 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST10Input,centerST10J,Fin.ofNat]
  have hFirst := Certificate.sound centerST10First centerST10Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST10Input,centerST10First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST10First = J1 t := by
    norm_num [centerST10First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((1551291503829 / 50000000000000) : ℝ)| ≤ (51 / 20000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST10Input,centerST10First,Fin.ofNat]
  have hSecond := Certificate.sound centerST10Second centerST10Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST10Input,centerST10Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST10Second = J2 t := by
    norm_num [centerST10Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((34953747504807 / 100000000000000) : ℝ)| ≤ (4121 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST10Input,centerST10Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST11TaylorInput : ℕ → RationalBall := fun _ => ⟨(87524892768314692053319 / 125000000000000000000000), (41790057983 / 375000000000000000000000)⟩
private def centerST11TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.const (1 / 6227020800)) ⟨(7873 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1248669 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-153049 / 12500000000000), (1 / 50000000000000)⟩) ⟨(42867 / 15625000000), (3 / 100000000000000)⟩) ⟨(134507411 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-1970676243 / 10000000000000), (3 / 100000000000000)⟩) ⟨(-4830904299 / 50000000000000), (1 / 50000000000000)⟩) ⟨(164734304947 / 20000000000000), (3 / 100000000000000)⟩) ⟨(403828718587 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-203285474351 / 1250000000000), (3 / 100000000000000)⟩) ⟨(-1594665060509 / 20000000000000), (1 / 20000000000000)⟩) ⟨(18405334939491 / 20000000000000), (1 / 20000000000000)⟩) ⟨(12887399735551 / 20000000000000), (3 / 20000000000000)⟩)
private def centerST11TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.const (1 / 479001600)) ⟨(51177 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-5490993 / 20000000000000), (1 / 50000000000000)⟩) ⟨(-3365147 / 25000000000000), (1 / 50000000000000)⟩) ⟨(1233349071 / 50000000000000), (3 / 100000000000000)⟩) ⟨(12093699 / 1000000000000), (1 / 50000000000000)⟩) ⟨(-137679518989 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-33750677339 / 50000000000000), (1 / 50000000000000)⟩) ⟨(4099165311989 / 100000000000000), (3 / 100000000000000)⟩) ⟨(251216751081 / 12500000000000), (3 / 100000000000000)⟩) ⟨(-5998783248919 / 12500000000000), (3 / 100000000000000)⟩) ⟨(-4705722375471 / 20000000000000), (1 / 10000000000000)⟩) ⟨(15294277624529 / 20000000000000), (1 / 10000000000000)⟩)

theorem centerST11Taylor {x : ℝ}
    (hx : |x-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (41790057983 / 375000000000000000000000)) :
    |sin x-((12887399735551 / 20000000000000) : ℝ)| ≤ (249 / 20000000000000) ∧
    |cos x-((15294277624529 / 20000000000000) : ℝ)| ≤ (31 / 2500000000000) := by
  have hs := Certificate.sound centerST11TaylorSin centerST11TaylorInput (fun _ => x)
    (by intro i; simpa [centerST11TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST11TaylorInput,centerST11TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST11TaylorCos centerST11TaylorInput (fun _ => x)
    (by intro i; simpa [centerST11TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST11TaylorInput,centerST11TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST11TaylorSin-
      ((12887399735551 / 20000000000000) : ℝ)| ≤ (3 / 20000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST11TaylorInput,centerST11TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST11TaylorCos-
      ((15294277624529 / 20000000000000) : ℝ)| ≤ (1 / 10000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST11TaylorInput,centerST11TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST11TaylorSin = sinTaylor x := by
    norm_num [centerST11TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST11TaylorCos = cosTaylor x := by
    norm_num [centerST11TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((87524892768314692053319 / 125000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST11Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(87524892768314692053319 / 125000000000000000000000), (41790057983 / 375000000000000000000000)⟩, ⟨(12887399735551 / 20000000000000), (249 / 20000000000000)⟩, ⟨(15294277624529 / 20000000000000), (31 / 2500000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST11J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-17504978553663 / 25000000000000), (3 / 25000000000000)⟩) ⟨(122069675572149 / 50000000000000), (31 / 50000000000000)⟩) (.atom 3) ⟨(186696750773663 / 100000000000000), (769 / 25000000000000)⟩) (.abs (.atom 2)) ⟨(125566874725709 / 50000000000000), (4321 / 100000000000000)⟩)
private def centerST11First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-17504978553663 / 25000000000000), (3 / 25000000000000)⟩) ⟨(122069675572149 / 50000000000000), (31 / 50000000000000)⟩) ⟨(-122069675572149 / 50000000000000), (31 / 50000000000000)⟩) (.atom 2) ⟨(-157316070468731 / 100000000000000), (77 / 2500000000000)⟩)
private def centerST11Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(12887399735551 / 10000000000000), (249 / 10000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-17504978553663 / 25000000000000), (3 / 25000000000000)⟩) ⟨(122069675572149 / 50000000000000), (31 / 50000000000000)⟩) (.atom 3) ⟨(186696750773663 / 100000000000000), (769 / 25000000000000)⟩) (.abs (.atom 2)) ⟨(125566874725709 / 50000000000000), (4321 / 100000000000000)⟩) ⟨(-125566874725709 / 50000000000000), (4321 / 100000000000000)⟩) ⟨(-30564938023977 / 25000000000000), (6811 / 100000000000000)⟩)

theorem centerST11 {t : ℝ}
    (ht : |t-((41790057983 / 187500000000) : ℝ)*π| ≤ 0) :
    |J t-((125566874725709 / 50000000000000) : ℝ)| ≤ (4321 / 100000000000000) ∧
    |J1 t-((-157316070468731 / 100000000000000) : ℝ)| ≤ (77 / 2500000000000) ∧
    |J2 t-((-30564938023977 / 25000000000000) : ℝ)| ≤ (6811 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-(0 : ℝ)*π-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (41790057983 / 375000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST11Taylor hred
  have hreduced : t-(0 : ℝ)*π = t := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((12887399735551 / 20000000000000) : ℝ)| ≤ (249 / 20000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hc : |cos t-((15294277624529 / 20000000000000) : ℝ)| ≤ (31 / 2500000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (41790057983 / 375000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST11Input i).center : ℝ)| ≤ ((centerST11Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST11Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST11Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST11Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST11Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST11Input i).center : ℝ)| ≤ ((centerST11Input i).radius : ℝ) := by
    intro i
    simpa [centerST11Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST11J centerST11Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST11Input,centerST11J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST11J = J t := by
    norm_num [centerST11J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((125566874725709 / 50000000000000) : ℝ)| ≤ (4321 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST11Input,centerST11J,Fin.ofNat]
  have hFirst := Certificate.sound centerST11First centerST11Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST11Input,centerST11First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST11First = J1 t := by
    norm_num [centerST11First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-157316070468731 / 100000000000000) : ℝ)| ≤ (77 / 2500000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST11Input,centerST11First,Fin.ofNat]
  have hSecond := Certificate.sound centerST11Second centerST11Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST11Input,centerST11Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST11Second = J2 t := by
    norm_num [centerST11Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((-30564938023977 / 25000000000000) : ℝ)| ≤ (6811 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST11Input,centerST11Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST12TaylorInput : ℕ → RationalBall := fun _ => ⟨(87524892768314692053319 / 125000000000000000000000), (41790057983 / 375000000000000000000000)⟩
private def centerST12TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.const (1 / 6227020800)) ⟨(7873 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1248669 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-153049 / 12500000000000), (1 / 50000000000000)⟩) ⟨(42867 / 15625000000), (3 / 100000000000000)⟩) ⟨(134507411 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-1970676243 / 10000000000000), (3 / 100000000000000)⟩) ⟨(-4830904299 / 50000000000000), (1 / 50000000000000)⟩) ⟨(164734304947 / 20000000000000), (3 / 100000000000000)⟩) ⟨(403828718587 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-203285474351 / 1250000000000), (3 / 100000000000000)⟩) ⟨(-1594665060509 / 20000000000000), (1 / 20000000000000)⟩) ⟨(18405334939491 / 20000000000000), (1 / 20000000000000)⟩) ⟨(12887399735551 / 20000000000000), (3 / 20000000000000)⟩)
private def centerST12TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (1 / 6250000000000)⟩) (.const (1 / 479001600)) ⟨(51177 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-5490993 / 20000000000000), (1 / 50000000000000)⟩) ⟨(-3365147 / 25000000000000), (1 / 50000000000000)⟩) ⟨(1233349071 / 50000000000000), (3 / 100000000000000)⟩) ⟨(12093699 / 1000000000000), (1 / 50000000000000)⟩) ⟨(-137679518989 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-33750677339 / 50000000000000), (1 / 50000000000000)⟩) ⟨(4099165311989 / 100000000000000), (3 / 100000000000000)⟩) ⟨(251216751081 / 12500000000000), (3 / 100000000000000)⟩) ⟨(-5998783248919 / 12500000000000), (3 / 100000000000000)⟩) ⟨(-4705722375471 / 20000000000000), (1 / 10000000000000)⟩) ⟨(15294277624529 / 20000000000000), (1 / 10000000000000)⟩)

theorem centerST12Taylor {x : ℝ}
    (hx : |x-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (41790057983 / 375000000000000000000000)) :
    |sin x-((12887399735551 / 20000000000000) : ℝ)| ≤ (249 / 20000000000000) ∧
    |cos x-((15294277624529 / 20000000000000) : ℝ)| ≤ (31 / 2500000000000) := by
  have hs := Certificate.sound centerST12TaylorSin centerST12TaylorInput (fun _ => x)
    (by intro i; simpa [centerST12TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST12TaylorInput,centerST12TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST12TaylorCos centerST12TaylorInput (fun _ => x)
    (by intro i; simpa [centerST12TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST12TaylorInput,centerST12TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST12TaylorSin-
      ((12887399735551 / 20000000000000) : ℝ)| ≤ (3 / 20000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST12TaylorInput,centerST12TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST12TaylorCos-
      ((15294277624529 / 20000000000000) : ℝ)| ≤ (1 / 10000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST12TaylorInput,centerST12TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST12TaylorSin = sinTaylor x := by
    norm_num [centerST12TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST12TaylorCos = cosTaylor x := by
    norm_num [centerST12TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((87524892768314692053319 / 125000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST12Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(-108824648081029057946681 / 125000000000000000000000), (51959942017 / 375000000000000000000000)⟩, ⟨(-15294277624529 / 20000000000000), (31 / 2500000000000)⟩, ⟨(12887399735551 / 20000000000000), (249 / 20000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST12J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(87059718464823 / 100000000000000), (3 / 20000000000000)⟩) ⟨(-87059718464823 / 100000000000000), (3 / 20000000000000)⟩) ⟨(227099546894127 / 100000000000000), (13 / 20000000000000)⟩) (.atom 3) ⟨(36584033007339 / 25000000000000), (287 / 10000000000000)⟩) (.abs (.atom 2)) ⟨(222807520152001 / 100000000000000), (411 / 10000000000000)⟩)
private def centerST12First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(87059718464823 / 100000000000000), (3 / 20000000000000)⟩) ⟨(-87059718464823 / 100000000000000), (3 / 20000000000000)⟩) ⟨(227099546894127 / 100000000000000), (13 / 20000000000000)⟩) ⟨(-227099546894127 / 100000000000000), (13 / 20000000000000)⟩) (.atom 2) ⟨(2713533998909 / 1562500000000), (1433 / 50000000000000)⟩)
private def centerST12Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(15294277624529 / 10000000000000), (31 / 1250000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(87059718464823 / 100000000000000), (3 / 20000000000000)⟩) ⟨(-87059718464823 / 100000000000000), (3 / 20000000000000)⟩) ⟨(227099546894127 / 100000000000000), (13 / 20000000000000)⟩) (.atom 3) ⟨(36584033007339 / 25000000000000), (287 / 10000000000000)⟩) (.abs (.atom 2)) ⟨(222807520152001 / 100000000000000), (411 / 10000000000000)⟩) ⟨(-222807520152001 / 100000000000000), (411 / 10000000000000)⟩) ⟨(-69864743906711 / 100000000000000), (659 / 10000000000000)⟩)

theorem centerST12 {t : ℝ}
    (ht : |t-((-51959942017 / 187500000000) : ℝ)*π| ≤ 0) :
    |J t-((222807520152001 / 100000000000000) : ℝ)| ≤ (411 / 10000000000000) ∧
    |J1 t-((2713533998909 / 1562500000000) : ℝ)| ≤ (1433 / 50000000000000) ∧
    |J2 t-((-69864743906711 / 100000000000000) : ℝ)| ≤ (659 / 10000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((-1 / 2) : ℝ)*π-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (41790057983 / 375000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST12Taylor hred
  have hreduced : t-((-1 / 2) : ℝ)*π = t+π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-15294277624529 / 20000000000000) : ℝ)| ≤ (31 / 2500000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hc : |cos t-((12887399735551 / 20000000000000) : ℝ)| ≤ (249 / 20000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((-108824648081029057946681 / 125000000000000000000000) : ℝ)| ≤ (51959942017 / 375000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST12Input i).center : ℝ)| ≤ ((centerST12Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST12Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST12Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST12Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST12Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST12Input i).center : ℝ)| ≤ ((centerST12Input i).radius : ℝ) := by
    intro i
    simpa [centerST12Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = -t := by
    have ht0 : 0 ≤ -t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : -t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (-t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST12J centerST12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST12Input,centerST12J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST12J = J t := by
    norm_num [centerST12J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eJ] at hJ
  have bJ : |J t-((222807520152001 / 100000000000000) : ℝ)| ≤ (411 / 10000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST12Input,centerST12J,Fin.ofNat]
  have hFirst := Certificate.sound centerST12First centerST12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST12Input,centerST12First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST12First = J1 t := by
    norm_num [centerST12First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((2713533998909 / 1562500000000) : ℝ)| ≤ (1433 / 50000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST12Input,centerST12First,Fin.ofNat]
  have hSecond := Certificate.sound centerST12Second centerST12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST12Input,centerST12Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST12Second = J2 t := by
    norm_num [centerST12Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((-69864743906711 / 100000000000000) : ℝ)| ≤ (659 / 10000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST12Input,centerST12Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST20TaylorInput : ℕ → RationalBall := fun _ => ⟨(-859728956165578514794647 / 2000000000000000000000000), (136830113093 / 2000000000000000000000000)⟩
private def centerST20TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(2967 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-625561 / 25000000000000), (1 / 50000000000000)⟩) ⟨(-462373 / 100000000000000), (1 / 100000000000000)⟩) ⟨(275110819 / 100000000000000), (1 / 50000000000000)⟩) ⟨(12708983 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-19790433909 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-3656945041 / 100000000000000), (1 / 100000000000000)⟩) ⟨(207419097073 / 25000000000000), (1 / 50000000000000)⟩) ⟨(30662096321 / 20000000000000), (1 / 100000000000000)⟩) ⟨(-8256678092531 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-762848812313 / 25000000000000), (1 / 50000000000000)⟩) ⟨(24237151187687 / 25000000000000), (1 / 50000000000000)⟩) ⟨(-8334952276407 / 20000000000000), (1 / 12500000000000)⟩)
private def centerST20TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (7 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(38577 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-13759371 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-5085009 / 100000000000000), (1 / 100000000000000)⟩) ⟨(2475073721 / 100000000000000), (1 / 50000000000000)⟩) ⟨(457352709 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-6921576809 / 5000000000000), (1 / 50000000000000)⟩) ⟨(-12789929773 / 50000000000000), (1 / 100000000000000)⟩) ⟨(4141086807121 / 100000000000000), (1 / 50000000000000)⟩) ⟨(765204387793 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-49234795612207 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-9097776354203 / 100000000000000), (1 / 25000000000000)⟩) ⟨(90902223645797 / 100000000000000), (1 / 25000000000000)⟩)

theorem centerST20Taylor {x : ℝ}
    (hx : |x-((-859728956165578514794647 / 2000000000000000000000000) : ℝ)| ≤ (136830113093 / 2000000000000000000000000)) :
    |sin x-((-8334952276407 / 20000000000000) : ℝ)| ≤ (619 / 50000000000000) ∧
    |cos x-((90902223645797 / 100000000000000) : ℝ)| ≤ (617 / 50000000000000) := by
  have hs := Certificate.sound centerST20TaylorSin centerST20TaylorInput (fun _ => x)
    (by intro i; simpa [centerST20TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST20TaylorInput,centerST20TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST20TaylorCos centerST20TaylorInput (fun _ => x)
    (by intro i; simpa [centerST20TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST20TaylorInput,centerST20TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST20TaylorSin-
      ((-8334952276407 / 20000000000000) : ℝ)| ≤ (1 / 12500000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST20TaylorInput,centerST20TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST20TaylorCos-
      ((90902223645797 / 100000000000000) : ℝ)| ≤ (1 / 25000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST20TaylorInput,centerST20TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST20TaylorSin = sinTaylor x := by
    norm_num [centerST20TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST20TaylorCos = cosTaylor x := by
    norm_num [centerST20TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-859728956165578514794647 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST20Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(2281863697423921485205353 / 2000000000000000000000000), (363169886907 / 2000000000000000000000000)⟩, ⟨(90902223645797 / 100000000000000), (617 / 50000000000000)⟩, ⟨(8334952276407 / 20000000000000), (619 / 50000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST20J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-28523296217799 / 25000000000000), (19 / 100000000000000)⟩) ⟨(100033040243877 / 50000000000000), (69 / 100000000000000)⟩) (.atom 3) ⟨(41688530824831 / 50000000000000), (2507 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(174279285295459 / 100000000000000), (3741 / 100000000000000)⟩)
private def centerST20First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-28523296217799 / 25000000000000), (19 / 100000000000000)⟩) ⟨(100033040243877 / 50000000000000), (69 / 100000000000000)⟩) ⟨(-100033040243877 / 50000000000000), (69 / 100000000000000)⟩) (.atom 2) ⟨(-90932257962179 / 50000000000000), (633 / 25000000000000)⟩)
private def centerST20Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(90902223645797 / 50000000000000), (617 / 25000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-28523296217799 / 25000000000000), (19 / 100000000000000)⟩) ⟨(100033040243877 / 50000000000000), (69 / 100000000000000)⟩) (.atom 3) ⟨(41688530824831 / 50000000000000), (2507 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(174279285295459 / 100000000000000), (3741 / 100000000000000)⟩) ⟨(-174279285295459 / 100000000000000), (3741 / 100000000000000)⟩) ⟨(1505032399227 / 20000000000000), (6209 / 100000000000000)⟩)

theorem centerST20 {t : ℝ}
    (ht : |t-((363169886907 / 1000000000000) : ℝ)*π| ≤ 0) :
    |J t-((174279285295459 / 100000000000000) : ℝ)| ≤ (3741 / 100000000000000) ∧
    |J1 t-((-90932257962179 / 50000000000000) : ℝ)| ≤ (633 / 25000000000000) ∧
    |J2 t-((1505032399227 / 20000000000000) : ℝ)| ≤ (6209 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((1 / 2) : ℝ)*π-((-859728956165578514794647 / 2000000000000000000000000) : ℝ)| ≤ (136830113093 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST20Taylor hred
  have hreduced : t-((1 / 2) : ℝ)*π = t-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((90902223645797 / 100000000000000) : ℝ)| ≤ (617 / 50000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hc : |cos t-((8334952276407 / 20000000000000) : ℝ)| ≤ (619 / 50000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((2281863697423921485205353 / 2000000000000000000000000) : ℝ)| ≤ (363169886907 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST20Input i).center : ℝ)| ≤ ((centerST20Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST20Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST20Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST20Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST20Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST20Input i).center : ℝ)| ≤ ((centerST20Input i).radius : ℝ) := by
    intro i
    simpa [centerST20Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST20J centerST20Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST20Input,centerST20J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST20J = J t := by
    norm_num [centerST20J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((174279285295459 / 100000000000000) : ℝ)| ≤ (3741 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST20Input,centerST20J,Fin.ofNat]
  have hFirst := Certificate.sound centerST20First centerST20Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST20Input,centerST20First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST20First = J1 t := by
    norm_num [centerST20First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-90932257962179 / 50000000000000) : ℝ)| ≤ (633 / 25000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST20Input,centerST20First,Fin.ofNat]
  have hSecond := Certificate.sound centerST20Second centerST20Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST20Input,centerST20Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST20Second = J2 t := by
    norm_num [centerST20Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((1505032399227 / 20000000000000) : ℝ)| ≤ (6209 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST20Input,centerST20Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST21TaylorInput : ℕ → RationalBall := fun _ => ⟨(187468595030921485205353 / 2000000000000000000000000), (89509660721 / 6000000000000000000000000)⟩
private def centerST21TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(141 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-250507 / 10000000000000), (1 / 50000000000000)⟩) ⟨(-2201 / 10000000000000), (1 / 100000000000000)⟩) ⟨(137775591 / 50000000000000), (1 / 50000000000000)⟩) ⟨(96841 / 4000000000000), (1 / 100000000000000)⟩) ⟨(-1239928051 / 6250000000000), (1 / 50000000000000)⟩) ⟨(-174306477 / 100000000000000), (1 / 100000000000000)⟩) ⟨(104144878357 / 12500000000000), (1 / 50000000000000)⟩) ⟨(1464046793 / 20000000000000), (1 / 100000000000000)⟩) ⟨(-8329673216351 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-73185496201 / 50000000000000), (1 / 100000000000000)⟩) ⟨(49926814503799 / 50000000000000), (1 / 100000000000000)⟩) ⟨(9359709769397 / 100000000000000), (1 / 50000000000000)⟩)
private def centerST21TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(917 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-5511097 / 20000000000000), (1 / 50000000000000)⟩) ⟨(-121053 / 50000000000000), (1 / 100000000000000)⟩) ⟨(154994789 / 6250000000000), (1 / 50000000000000)⟩) ⟨(21788841 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-8679193753 / 6250000000000), (1 / 50000000000000)⟩) ⟨(-1220102801 / 100000000000000), (1 / 100000000000000)⟩) ⟨(2082723281933 / 50000000000000), (1 / 50000000000000)⟩) ⟨(9149526811 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-12490850473189 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-109746092807 / 25000000000000), (1 / 100000000000000)⟩) ⟨(24890253907193 / 25000000000000), (1 / 100000000000000)⟩)

theorem centerST21Taylor {x : ℝ}
    (hx : |x-((187468595030921485205353 / 2000000000000000000000000) : ℝ)| ≤ (89509660721 / 6000000000000000000000000)) :
    |sin x-((9359709769397 / 100000000000000) : ℝ)| ≤ (77 / 6250000000000) ∧
    |cos x-((24890253907193 / 25000000000000) : ℝ)| ≤ (1231 / 100000000000000) := by
  have hs := Certificate.sound centerST21TaylorSin centerST21TaylorInput (fun _ => x)
    (by intro i; simpa [centerST21TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST21TaylorInput,centerST21TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST21TaylorCos centerST21TaylorInput (fun _ => x)
    (by intro i; simpa [centerST21TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST21TaylorInput,centerST21TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST21TaylorSin-
      ((9359709769397 / 100000000000000) : ℝ)| ≤ (1 / 50000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST21TaylorInput,centerST21TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST21TaylorCos-
      ((24890253907193 / 25000000000000) : ℝ)| ≤ (1 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST21TaylorInput,centerST21TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST21TaylorSin = sinTaylor x := by
    norm_num [centerST21TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST21TaylorCos = cosTaylor x := by
    norm_num [centerST21TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((187468595030921485205353 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST21Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(-2954124058558578514794647 / 2000000000000000000000000), (1410490339279 / 6000000000000000000000000)⟩, ⟨(-24890253907193 / 25000000000000), (1231 / 100000000000000)⟩, ⟨(9359709769397 / 100000000000000), (77 / 6250000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST21J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(147706202927929 / 100000000000000), (3 / 12500000000000)⟩) ⟨(-147706202927929 / 100000000000000), (3 / 12500000000000)⟩) ⟨(166453062431021 / 100000000000000), (37 / 50000000000000)⟩) (.atom 3) ⟨(15579523545817 / 100000000000000), (1029 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(115140539174589 / 100000000000000), (3289 / 100000000000000)⟩)
private def centerST21First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(147706202927929 / 100000000000000), (3 / 12500000000000)⟩) ⟨(-147706202927929 / 100000000000000), (3 / 12500000000000)⟩) ⟨(166453062431021 / 100000000000000), (37 / 50000000000000)⟩) ⟨(-166453062431021 / 100000000000000), (37 / 50000000000000)⟩) (.atom 2) ⟨(82861179750759 / 50000000000000), (531 / 25000000000000)⟩)
private def centerST21Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(24890253907193 / 12500000000000), (1231 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(147706202927929 / 100000000000000), (3 / 12500000000000)⟩) ⟨(-147706202927929 / 100000000000000), (3 / 12500000000000)⟩) ⟨(166453062431021 / 100000000000000), (37 / 50000000000000)⟩) (.atom 3) ⟨(15579523545817 / 100000000000000), (1029 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(115140539174589 / 100000000000000), (3289 / 100000000000000)⟩) ⟨(-115140539174589 / 100000000000000), (3289 / 100000000000000)⟩) ⟨(16796298416591 / 20000000000000), (5751 / 100000000000000)⟩)

theorem centerST21 {t : ℝ}
    (ht : |t-((-1410490339279 / 3000000000000) : ℝ)*π| ≤ 0) :
    |J t-((115140539174589 / 100000000000000) : ℝ)| ≤ (3289 / 100000000000000) ∧
    |J1 t-((82861179750759 / 50000000000000) : ℝ)| ≤ (531 / 25000000000000) ∧
    |J2 t-((16796298416591 / 20000000000000) : ℝ)| ≤ (5751 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((-1 / 2) : ℝ)*π-((187468595030921485205353 / 2000000000000000000000000) : ℝ)| ≤ (89509660721 / 6000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST21Taylor hred
  have hreduced : t-((-1 / 2) : ℝ)*π = t+π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-24890253907193 / 25000000000000) : ℝ)| ≤ (1231 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hc : |cos t-((9359709769397 / 100000000000000) : ℝ)| ≤ (77 / 6250000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((-2954124058558578514794647 / 2000000000000000000000000) : ℝ)| ≤ (1410490339279 / 6000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST21Input i).center : ℝ)| ≤ ((centerST21Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST21Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST21Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST21Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST21Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST21Input i).center : ℝ)| ≤ ((centerST21Input i).radius : ℝ) := by
    intro i
    simpa [centerST21Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = -t := by
    have ht0 : 0 ≤ -t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : -t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (-t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST21J centerST21Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST21Input,centerST21J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST21J = J t := by
    norm_num [centerST21J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eJ] at hJ
  have bJ : |J t-((115140539174589 / 100000000000000) : ℝ)| ≤ (3289 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST21Input,centerST21J,Fin.ofNat]
  have hFirst := Certificate.sound centerST21First centerST21Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST21Input,centerST21First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST21First = J1 t := by
    norm_num [centerST21First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((82861179750759 / 50000000000000) : ℝ)| ≤ (531 / 25000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST21Input,centerST21First,Fin.ofNat]
  have hSecond := Certificate.sound centerST21Second centerST21Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST21Input,centerST21Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST21Second = J2 t := by
    norm_num [centerST21Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((16796298416591 / 20000000000000) : ℝ)| ≤ (5751 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST21Input,centerST21Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def centerST22TaylorInput : ℕ → RationalBall := fun _ => ⟨(187468595030921485205353 / 2000000000000000000000000), (89509660721 / 6000000000000000000000000)⟩
private def centerST22TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(141 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-250507 / 10000000000000), (1 / 50000000000000)⟩) ⟨(-2201 / 10000000000000), (1 / 100000000000000)⟩) ⟨(137775591 / 50000000000000), (1 / 50000000000000)⟩) ⟨(96841 / 4000000000000), (1 / 100000000000000)⟩) ⟨(-1239928051 / 6250000000000), (1 / 50000000000000)⟩) ⟨(-174306477 / 100000000000000), (1 / 100000000000000)⟩) ⟨(104144878357 / 12500000000000), (1 / 50000000000000)⟩) ⟨(1464046793 / 20000000000000), (1 / 100000000000000)⟩) ⟨(-8329673216351 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-73185496201 / 50000000000000), (1 / 100000000000000)⟩) ⟨(49926814503799 / 50000000000000), (1 / 100000000000000)⟩) ⟨(9359709769397 / 100000000000000), (1 / 50000000000000)⟩)
private def centerST22TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (1 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(917 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-5511097 / 20000000000000), (1 / 50000000000000)⟩) ⟨(-121053 / 50000000000000), (1 / 100000000000000)⟩) ⟨(154994789 / 6250000000000), (1 / 50000000000000)⟩) ⟨(21788841 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-8679193753 / 6250000000000), (1 / 50000000000000)⟩) ⟨(-1220102801 / 100000000000000), (1 / 100000000000000)⟩) ⟨(2082723281933 / 50000000000000), (1 / 50000000000000)⟩) ⟨(9149526811 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-12490850473189 / 25000000000000), (1 / 100000000000000)⟩) ⟨(-109746092807 / 25000000000000), (1 / 100000000000000)⟩) ⟨(24890253907193 / 25000000000000), (1 / 100000000000000)⟩)

theorem centerST22Taylor {x : ℝ}
    (hx : |x-((187468595030921485205353 / 2000000000000000000000000) : ℝ)| ≤ (89509660721 / 6000000000000000000000000)) :
    |sin x-((9359709769397 / 100000000000000) : ℝ)| ≤ (77 / 6250000000000) ∧
    |cos x-((24890253907193 / 25000000000000) : ℝ)| ≤ (1231 / 100000000000000) := by
  have hs := Certificate.sound centerST22TaylorSin centerST22TaylorInput (fun _ => x)
    (by intro i; simpa [centerST22TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST22TaylorInput,centerST22TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound centerST22TaylorCos centerST22TaylorInput (fun _ => x)
    (by intro i; simpa [centerST22TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,centerST22TaylorInput,centerST22TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) centerST22TaylorSin-
      ((9359709769397 / 100000000000000) : ℝ)| ≤ (1 / 50000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,centerST22TaylorInput,centerST22TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) centerST22TaylorCos-
      ((24890253907193 / 25000000000000) : ℝ)| ≤ (1 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,centerST22TaylorInput,centerST22TaylorCos]
  have hsin : Certificate.eval (fun _ => x) centerST22TaylorSin = sinTaylor x := by
    norm_num [centerST22TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) centerST22TaylorCos = cosTaylor x := by
    norm_num [centerST22TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((187468595030921485205353 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def centerST22Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(-6095716712148078514794647 / 2000000000000000000000000), (2910490339279 / 6000000000000000000000000)⟩, ⟨(-9359709769397 / 100000000000000), (77 / 6250000000000)⟩, ⟨(-24890253907193 / 25000000000000), (1231 / 100000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def centerST22J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(76196458901851 / 25000000000000), (49 / 100000000000000)⟩) ⟨(-76196458901851 / 25000000000000), (49 / 100000000000000)⟩) ⟨(4686714875773 / 50000000000000), (99 / 100000000000000)⟩) (.atom 3) ⟨(-9332281859889 / 100000000000000), (43 / 20000000000000)⟩) (.abs (.atom 2)) ⟨(6856977377 / 25000000000000), (1447 / 100000000000000)⟩)
private def centerST22First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(76196458901851 / 25000000000000), (49 / 100000000000000)⟩) ⟨(-76196458901851 / 25000000000000), (49 / 100000000000000)⟩) ⟨(4686714875773 / 50000000000000), (99 / 100000000000000)⟩) ⟨(-4686714875773 / 50000000000000), (99 / 100000000000000)⟩) (.atom 2) ⟨(877325820183 / 100000000000000), (1 / 800000000000)⟩)
private def centerST22Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(9359709769397 / 50000000000000), (77 / 3125000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(76196458901851 / 25000000000000), (49 / 100000000000000)⟩) ⟨(-76196458901851 / 25000000000000), (49 / 100000000000000)⟩) ⟨(4686714875773 / 50000000000000), (99 / 100000000000000)⟩) (.atom 3) ⟨(-9332281859889 / 100000000000000), (43 / 20000000000000)⟩) (.abs (.atom 2)) ⟨(6856977377 / 25000000000000), (1447 / 100000000000000)⟩) ⟨(-6856977377 / 25000000000000), (1447 / 100000000000000)⟩) ⟨(9345995814643 / 50000000000000), (3911 / 100000000000000)⟩)

theorem centerST22 {t : ℝ}
    (ht : |t-((-2910490339279 / 3000000000000) : ℝ)*π| ≤ 0) :
    |J t-((6856977377 / 25000000000000) : ℝ)| ≤ (1447 / 100000000000000) ∧
    |J1 t-((877325820183 / 100000000000000) : ℝ)| ≤ (1 / 800000000000) ∧
    |J2 t-((9345995814643 / 50000000000000) : ℝ)| ≤ (3911 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((-1) : ℝ)*π-((187468595030921485205353 / 2000000000000000000000000) : ℝ)| ≤ (89509660721 / 6000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := centerST22Taylor hred
  have hreduced : t-((-1) : ℝ)*π = t+π := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-9359709769397 / 100000000000000) : ℝ)| ≤ (77 / 6250000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hc : |cos t-((-24890253907193 / 25000000000000) : ℝ)| ≤ (1231 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((-6095716712148078514794647 / 2000000000000000000000000) : ℝ)| ≤ (2910490339279 / 6000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((centerST22Input i).center : ℝ)| ≤ ((centerST22Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [centerST22Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [centerST22Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [centerST22Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [centerST22Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((centerST22Input i).center : ℝ)| ≤ ((centerST22Input i).radius : ℝ) := by
    intro i
    simpa [centerST22Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = -t := by
    have ht0 : 0 ≤ -t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : -t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (-t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound centerST22J centerST22Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST22Input,centerST22J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST22J = J t := by
    norm_num [centerST22J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eJ] at hJ
  have bJ : |J t-((6856977377 / 25000000000000) : ℝ)| ≤ (1447 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,centerST22Input,centerST22J,Fin.ofNat]
  have hFirst := Certificate.sound centerST22First centerST22Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST22Input,centerST22First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST22First = J1 t := by
    norm_num [centerST22First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((877325820183 / 100000000000000) : ℝ)| ≤ (1 / 800000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,centerST22Input,centerST22First,Fin.ofNat]
  have hSecond := Certificate.sound centerST22Second centerST22Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,centerST22Input,centerST22Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) centerST22Second = J2 t := by
    norm_num [centerST22Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((9345995814643 / 50000000000000) : ℝ)| ≤ (3911 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,centerST22Input,centerST22Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

end PaperLeanFormalization.SeedNumerics


/-! Fresh numerical certificate component: SeedBoxPairs. -/

/-! Generated exact certificate data. Do not edit emitted source.
Producer: the certificate generator of this development, part: box-pairs
Schema SHA256: 52d78277f3f1ad2146ecf733e1e7238c78f6c1192abbdf0157de3ea8fb3d301a
A generator run is not proof: compile this file and audit its declarations. -/

open Real
noncomputable section

namespace PaperLeanFormalization.SeedNumerics

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private def boxSS01TaylorInput : ℕ → RationalBall := fun _ => ⟨(173667425365721714933979 / 250000000000000000000000), (10000000027640029201 / 250000000000000000000000)⟩
private def boxSS01TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.const (1 / 6227020800)) ⟨(31 / 400000000000), (1 / 50000000000000)⟩) ⟨(-2497461 / 100000000000000), (3 / 100000000000000)⟩) ⟨(-120519 / 10000000000000), (141 / 100000000000000)⟩) ⟨(137184001 / 50000000000000), (71 / 50000000000000)⟩) ⟨(33100167 / 25000000000000), (15317 / 100000000000000)⟩) ⟨(-19708869173 / 100000000000000), (7659 / 50000000000000)⟩) ⟨(-4755415023 / 50000000000000), (551359 / 50000000000000)⟩) ⟨(823822503287 / 100000000000000), (1102719 / 100000000000000)⟩) ⟨(198774362643 / 50000000000000), (23158139 / 50000000000000)⟩) ⟨(-16269117941381 / 100000000000000), (46316279 / 100000000000000)⟩) ⟨(-785092307301 / 10000000000000), (463256167 / 50000000000000)⟩) ⟨(9214907692699 / 10000000000000), (463256167 / 50000000000000)⟩) ⟨(64013171758953 / 100000000000000), (865924039 / 20000000000000)⟩)
private def boxSS01TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(24128299706527 / 50000000000000), (1389379407 / 25000000000000)⟩) (.const (1 / 479001600)) ⟨(12593 / 12500000000000), (3 / 25000000000000)⟩) ⟨(-1098263 / 4000000000000), (13 / 100000000000000)⟩) ⟨(-13249609 / 100000000000000), (1533 / 100000000000000)⟩) ⟨(2466909121 / 100000000000000), (767 / 50000000000000)⟩) ⟨(297611613 / 25000000000000), (1723 / 1250000000000)⟩) ⟨(-137698442437 / 100000000000000), (137841 / 100000000000000)⟩) ⟨(-13289717153 / 20000000000000), (7719141 / 100000000000000)⟩) ⟨(2050109040451 / 50000000000000), (3859571 / 50000000000000)⟩) ⟨(989312907181 / 50000000000000), (28949471 / 12500000000000)⟩) ⟨(-24010687092819 / 50000000000000), (28949471 / 12500000000000)⟩) ⟨(-23173482173407 / 100000000000000), (2780569449 / 100000000000000)⟩) ⟨(76826517826593 / 100000000000000), (2780569449 / 100000000000000)⟩)

theorem boxSS01Taylor {x : ℝ}
    (hx : |x-((173667425365721714933979 / 250000000000000000000000) : ℝ)| ≤ (10000000027640029201 / 250000000000000000000000)) :
    |sin x-((64013171758953 / 100000000000000) : ℝ)| ≤ (173184857 / 4000000000000) ∧
    |cos x-((76826517826593 / 100000000000000) : ℝ)| ≤ (2780570679 / 100000000000000) := by
  have hs := Certificate.sound boxSS01TaylorSin boxSS01TaylorInput (fun _ => x)
    (by intro i; simpa [boxSS01TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxSS01TaylorInput,boxSS01TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxSS01TaylorCos boxSS01TaylorInput (fun _ => x)
    (by intro i; simpa [boxSS01TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxSS01TaylorInput,boxSS01TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxSS01TaylorSin-
      ((64013171758953 / 100000000000000) : ℝ)| ≤ (865924039 / 20000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxSS01TaylorInput,boxSS01TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxSS01TaylorCos-
      ((76826517826593 / 100000000000000) : ℝ)| ≤ (2780569449 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxSS01TaylorInput,boxSS01TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxSS01TaylorSin = sinTaylor x := by
    norm_num [boxSS01TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxSS01TaylorCos = cosTaylor x := by
    norm_num [boxSS01TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((173667425365721714933979 / 250000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxSS01Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(566366507064409214933979 / 250000000000000000000000), (10000000090140029201 / 250000000000000000000000)⟩, ⟨(76826517826593 / 100000000000000), (2780570679 / 100000000000000)⟩, ⟨(-64013171758953 / 100000000000000), (173184857 / 4000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxSS01J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-56636650706441 / 25000000000000), (4000000037 / 100000000000000)⟩) ⟨(43806331266593 / 50000000000000), (4000000087 / 100000000000000)⟩) (.atom 3) ⟨(-1402091103749 / 2500000000000), (79424959 / 1250000000000)⟩) (.abs (.atom 2)) ⟨(20742873676633 / 100000000000000), (9134567399 / 100000000000000)⟩)
private def boxSS01First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-56636650706441 / 25000000000000), (4000000037 / 100000000000000)⟩) ⟨(43806331266593 / 50000000000000), (4000000087 / 100000000000000)⟩) ⟨(-43806331266593 / 50000000000000), (4000000087 / 100000000000000)⟩) (.atom 2) ⟨(-67309757799411 / 100000000000000), (5509304009 / 100000000000000)⟩)
private def boxSS01Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(76826517826593 / 50000000000000), (2780570679 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-56636650706441 / 25000000000000), (4000000037 / 100000000000000)⟩) ⟨(43806331266593 / 50000000000000), (4000000087 / 100000000000000)⟩) (.atom 3) ⟨(-1402091103749 / 2500000000000), (79424959 / 1250000000000)⟩) (.abs (.atom 2)) ⟨(20742873676633 / 100000000000000), (9134567399 / 100000000000000)⟩) ⟨(-20742873676633 / 100000000000000), (9134567399 / 100000000000000)⟩) ⟨(132910161976553 / 100000000000000), (14695708757 / 100000000000000)⟩)

theorem boxSS01 {t : ℝ}
    (ht : |t-((90140029201 / 125000000000) : ℝ)*π| ≤ (1 / 25000)) :
    |J t-((20742873676633 / 100000000000000) : ℝ)| ≤ (9134567399 / 100000000000000) ∧
    |J1 t-((-67309757799411 / 100000000000000) : ℝ)| ≤ (5509304009 / 100000000000000) ∧
    |J2 t-((132910161976553 / 100000000000000) : ℝ)| ≤ (14695708757 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((1 / 2) : ℝ)*π-((173667425365721714933979 / 250000000000000000000000) : ℝ)| ≤ (10000000027640029201 / 250000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxSS01Taylor hred
  have hreduced : t-((1 / 2) : ℝ)*π = t-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((76826517826593 / 100000000000000) : ℝ)| ≤ (2780570679 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hc : |cos t-((-64013171758953 / 100000000000000) : ℝ)| ≤ (173184857 / 4000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((566366507064409214933979 / 250000000000000000000000) : ℝ)| ≤ (10000000090140029201 / 250000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxSS01Input i).center : ℝ)| ≤ ((boxSS01Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxSS01Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxSS01Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxSS01Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxSS01Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxSS01Input i).center : ℝ)| ≤ ((boxSS01Input i).radius : ℝ) := by
    intro i
    simpa [boxSS01Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxSS01J boxSS01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS01Input,boxSS01J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS01J = J t := by
    norm_num [boxSS01J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((20742873676633 / 100000000000000) : ℝ)| ≤ (9134567399 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxSS01Input,boxSS01J,Fin.ofNat]
  have hFirst := Certificate.sound boxSS01First boxSS01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS01Input,boxSS01First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS01First = J1 t := by
    norm_num [boxSS01First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-67309757799411 / 100000000000000) : ℝ)| ≤ (5509304009 / 100000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxSS01Input,boxSS01First,Fin.ofNat]
  have hSecond := Certificate.sound boxSS01Second boxSS01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS01Input,boxSS01Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS01Second = J2 t := by
    norm_num [boxSS01Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((132910161976553 / 100000000000000) : ℝ)| ≤ (14695708757 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxSS01Input,boxSS01Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxSS02TaylorInput : ℕ → RationalBall := fun _ => ⟨(-539323561401612692880417 / 2000000000000000000000000), (80000000085836010723 / 2000000000000000000000000)⟩
private def boxSS02TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.const (1 / 6227020800)) ⟨(73 / 6250000000000), (1 / 100000000000000)⟩) ⟨(-2504043 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-22761 / 12500000000000), (11 / 20000000000000)⟩) ⟨(2151493 / 781250000000), (7 / 12500000000000)⟩) ⟨(10012873 / 50000000000000), (2973 / 50000000000000)⟩) ⟨(-3964248819 / 20000000000000), (5947 / 100000000000000)⟩) ⟨(-1441350841 / 100000000000000), (107017 / 25000000000000)⟩) ⟨(207972995623 / 25000000000000), (428069 / 100000000000000)⟩) ⟨(60493085247 / 100000000000000), (17978827 / 100000000000000)⟩) ⟨(-830308679071 / 5000000000000), (4494707 / 25000000000000)⟩) ⟨(-1207559028373 / 100000000000000), (359578361 / 100000000000000)⟩) ⟨(98792440971627 / 100000000000000), (359578361 / 100000000000000)⟩) ⟨(-6660136388047 / 25000000000000), (506084571 / 12500000000000)⟩)
private def boxSS02TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(7271747597073 / 100000000000000), (269681781 / 12500000000000)⟩) (.const (1 / 479001600)) ⟨(15181 / 100000000000000), (1 / 20000000000000)⟩) ⟨(-13771069 / 50000000000000), (3 / 50000000000000)⟩) ⟨(-400559 / 20000000000000), (119 / 20000000000000)⟩) ⟨(495631187 / 20000000000000), (149 / 25000000000000)⟩) ⟨(36041049 / 20000000000000), (53509 / 100000000000000)⟩) ⟨(-34677170911 / 25000000000000), (5351 / 10000000000000)⟩) ⟨(-1008654537 / 10000000000000), (2996469 / 100000000000000)⟩) ⟨(4156580121297 / 100000000000000), (299647 / 10000000000000)⟩) ⟨(302256015091 / 100000000000000), (3595771 / 4000000000000)⟩) ⟨(-49697743984909 / 100000000000000), (3595771 / 4000000000000)⟩) ⟨(-1806947252011 / 50000000000000), (539372457 / 50000000000000)⟩) ⟨(48193052747989 / 50000000000000), (539372457 / 50000000000000)⟩)

theorem boxSS02Taylor {x : ℝ}
    (hx : |x-((-539323561401612692880417 / 2000000000000000000000000) : ℝ)| ≤ (80000000085836010723 / 2000000000000000000000000)) :
    |sin x-((-6660136388047 / 25000000000000) : ℝ)| ≤ (2024338899 / 50000000000000) ∧
    |cos x-((48193052747989 / 50000000000000) : ℝ)| ≤ (33710817 / 3125000000000) := by
  have hs := Certificate.sound boxSS02TaylorSin boxSS02TaylorInput (fun _ => x)
    (by intro i; simpa [boxSS02TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxSS02TaylorInput,boxSS02TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxSS02TaylorCos boxSS02TaylorInput (fun _ => x)
    (by intro i; simpa [boxSS02TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxSS02TaylorInput,boxSS02TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxSS02TaylorSin-
      ((-6660136388047 / 25000000000000) : ℝ)| ≤ (506084571 / 12500000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxSS02TaylorInput,boxSS02TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxSS02TaylorCos-
      ((48193052747989 / 50000000000000) : ℝ)| ≤ (539372457 / 50000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxSS02TaylorInput,boxSS02TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxSS02TaylorSin = sinTaylor x := by
    norm_num [boxSS02TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxSS02TaylorCos = cosTaylor x := by
    norm_num [boxSS02TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-539323561401612692880417 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxSS02Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(8885454399366887307119583 / 2000000000000000000000000), (80000001414163989277 / 2000000000000000000000000)⟩, ⟨(-48193052747989 / 50000000000000), (33710817 / 3125000000000)⟩, ⟨(-6660136388047 / 25000000000000), (2024338899 / 50000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxSS02J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-55534089996043 / 12500000000000), (500000009 / 12500000000000)⟩) ⟨(46011452687389 / 25000000000000), (1000000043 / 25000000000000)⟩) ⟨(-46011452687389 / 25000000000000), (1000000043 / 25000000000000)⟩) ⟨(65056727304697 / 50000000000000), (2000000111 / 50000000000000)⟩) (.atom 3) ⟨(-34662934144741 / 100000000000000), (3166829189 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(61723171351237 / 100000000000000), (3706202261 / 50000000000000)⟩)
private def boxSS02First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-55534089996043 / 12500000000000), (500000009 / 12500000000000)⟩) ⟨(46011452687389 / 25000000000000), (1000000043 / 25000000000000)⟩) ⟨(-46011452687389 / 25000000000000), (1000000043 / 25000000000000)⟩) ⟨(65056727304697 / 50000000000000), (2000000111 / 50000000000000)⟩) ⟨(-65056727304697 / 50000000000000), (2000000111 / 50000000000000)⟩) (.atom 2) ⟨(7838205726517 / 6250000000000), (5259081459 / 100000000000000)⟩)
private def boxSS02Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(48193052747989 / 25000000000000), (33710817 / 1562500000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-55534089996043 / 12500000000000), (500000009 / 12500000000000)⟩) ⟨(46011452687389 / 25000000000000), (1000000043 / 25000000000000)⟩) ⟨(-46011452687389 / 25000000000000), (1000000043 / 25000000000000)⟩) ⟨(65056727304697 / 50000000000000), (2000000111 / 50000000000000)⟩) (.atom 3) ⟨(-34662934144741 / 100000000000000), (3166829189 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(61723171351237 / 100000000000000), (3706202261 / 50000000000000)⟩) ⟨(-61723171351237 / 100000000000000), (3706202261 / 50000000000000)⟩) ⟨(131049039640719 / 100000000000000), (956989681 / 10000000000000)⟩)

theorem boxSS02 {t : ℝ}
    (ht : |t-((1414163989277 / 1000000000000) : ℝ)*π| ≤ (1 / 25000)) :
    |J t-((61723171351237 / 100000000000000) : ℝ)| ≤ (3706202261 / 50000000000000) ∧
    |J1 t-((7838205726517 / 6250000000000) : ℝ)| ≤ (5259081459 / 100000000000000) ∧
    |J2 t-((131049039640719 / 100000000000000) : ℝ)| ≤ (956989681 / 10000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((3 / 2) : ℝ)*π-((-539323561401612692880417 / 2000000000000000000000000) : ℝ)| ≤ (80000000085836010723 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxSS02Taylor hred
  have hreduced : t-((3 / 2) : ℝ)*π = (t-π)-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-48193052747989 / 50000000000000) : ℝ)| ≤ (33710817 / 3125000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hc : |cos t-((-6660136388047 / 25000000000000) : ℝ)| ≤ (2024338899 / 50000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((8885454399366887307119583 / 2000000000000000000000000) : ℝ)| ≤ (80000001414163989277 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxSS02Input i).center : ℝ)| ≤ ((boxSS02Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxSS02Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxSS02Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxSS02Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxSS02Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxSS02Input i).center : ℝ)| ≤ ((boxSS02Input i).radius : ℝ) := by
    intro i
    simpa [boxSS02Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = 2*π-t := by
    have ht0 : 0 ≤ 2*π-t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : 2*π-t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (2*π-t) = cos t := by rw [show 2*π-t = -(t-2*π) by ring,cos_neg,cos_sub_two_pi]
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxSS02J boxSS02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS02Input,boxSS02J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS02J = J t := by
    norm_num [boxSS02J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((61723171351237 / 100000000000000) : ℝ)| ≤ (3706202261 / 50000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxSS02Input,boxSS02J,Fin.ofNat]
  have hFirst := Certificate.sound boxSS02First boxSS02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS02Input,boxSS02First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS02First = J1 t := by
    norm_num [boxSS02First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((7838205726517 / 6250000000000) : ℝ)| ≤ (5259081459 / 100000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxSS02Input,boxSS02First,Fin.ofNat]
  have hSecond := Certificate.sound boxSS02Second boxSS02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS02Input,boxSS02Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS02Second = J2 t := by
    norm_num [boxSS02Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((131049039640719 / 100000000000000) : ℝ)| ≤ (956989681 / 10000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxSS02Input,boxSS02Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxSS12TaylorInput : ℕ → RationalBall := fun _ => ⟨(1212929689262113587647751 / 2000000000000000000000000), (80000000193043755669 / 2000000000000000000000000)⟩
private def boxSS12TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(5907 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-312413 / 12500000000000), (3 / 100000000000000)⟩) ⟨(-919243 / 100000000000000), (123 / 100000000000000)⟩) ⟨(274653949 / 100000000000000), (31 / 25000000000000)⟩) ⟨(20203523 / 20000000000000), (3343 / 25000000000000)⟩) ⟨(-9870126113 / 50000000000000), (13373 / 100000000000000)⟩) ⟨(-3630228513 / 50000000000000), (962693 / 100000000000000)⟩) ⟨(826072876307 / 100000000000000), (481347 / 50000000000000)⟩) ⟨(151914639949 / 50000000000000), (2021709 / 5000000000000)⟩) ⟨(-16362837386769 / 100000000000000), (40434181 / 100000000000000)⟩) ⟨(-6018245172913 / 100000000000000), (808778671 / 100000000000000)⟩) ⟨(93981754827087 / 100000000000000), (808778671 / 100000000000000)⟩) ⟨(56996630339363 / 100000000000000), (849959677 / 20000000000000)⟩)
private def boxSS12TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(36779960777337 / 100000000000000), (4851878769 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(15357 / 20000000000000), (11 / 100000000000000)⟩) ⟨(-13740267 / 50000000000000), (3 / 25000000000000)⟩) ⟨(-1010733 / 10000000000000), (1339 / 100000000000000)⟩) ⟨(12350257 / 500000000000), (67 / 5000000000000)⟩) ⟨(28390123 / 3125000000000), (120337 / 100000000000000)⟩) ⟨(-137980404953 / 100000000000000), (60169 / 50000000000000)⟩) ⟨(-25374569411 / 50000000000000), (6738909 / 100000000000000)⟩) ⟨(823183505569 / 20000000000000), (673891 / 10000000000000)⟩) ⟨(1513832852369 / 100000000000000), (8087129 / 4000000000000)⟩) ⟨(-48486167147631 / 100000000000000), (8087129 / 4000000000000)⟩) ⟨(-17833193259333 / 100000000000000), (606715233 / 25000000000000)⟩) ⟨(82166806740667 / 100000000000000), (606715233 / 25000000000000)⟩)

theorem boxSS12Taylor {x : ℝ}
    (hx : |x-((1212929689262113587647751 / 2000000000000000000000000) : ℝ)| ≤ (80000000193043755669 / 2000000000000000000000000)) :
    |sin x-((56996630339363 / 100000000000000) : ℝ)| ≤ (849959923 / 20000000000000) ∧
    |cos x-((82166806740667 / 100000000000000) : ℝ)| ≤ (1213431081 / 50000000000000) := by
  have hs := Certificate.sound boxSS12TaylorSin boxSS12TaylorInput (fun _ => x)
    (by intro i; simpa [boxSS12TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxSS12TaylorInput,boxSS12TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxSS12TaylorCos boxSS12TaylorInput (fun _ => x)
    (by intro i; simpa [boxSS12TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxSS12TaylorInput,boxSS12TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxSS12TaylorSin-
      ((56996630339363 / 100000000000000) : ℝ)| ≤ (849959677 / 20000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxSS12TaylorInput,boxSS12TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxSS12TaylorCos-
      ((82166806740667 / 100000000000000) : ℝ)| ≤ (606715233 / 25000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxSS12TaylorInput,boxSS12TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxSS12TaylorSin = sinTaylor x := by
    norm_num [boxSS12TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxSS12TaylorCos = cosTaylor x := by
    norm_num [boxSS12TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((1212929689262113587647751 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxSS12Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(4354522342851613587647751 / 2000000000000000000000000), (80000000693043755669 / 2000000000000000000000000)⟩, ⟨(82166806740667 / 100000000000000), (1213431081 / 50000000000000)⟩, ⟨(-56996630339363 / 100000000000000), (849959923 / 20000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxSS12J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-217726117142581 / 100000000000000), (800000007 / 20000000000000)⟩) ⟨(96433148216369 / 100000000000000), (800000017 / 20000000000000)⟩) (.atom 3) ⟨(-27481822506747 / 50000000000000), (99660169 / 1562500000000)⟩) (.abs (.atom 2)) ⟨(27203161727173 / 100000000000000), (4402556489 / 50000000000000)⟩)
private def boxSS12First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-217726117142581 / 100000000000000), (800000007 / 20000000000000)⟩) ⟨(96433148216369 / 100000000000000), (800000017 / 20000000000000)⟩) ⟨(-96433148216369 / 100000000000000), (800000017 / 20000000000000)⟩) (.atom 2) ⟨(-15847207705777 / 20000000000000), (5627069 / 100000000000)⟩)
private def boxSS12Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(82166806740667 / 50000000000000), (1213431081 / 25000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-217726117142581 / 100000000000000), (800000007 / 20000000000000)⟩) ⟨(96433148216369 / 100000000000000), (800000017 / 20000000000000)⟩) (.atom 3) ⟨(-27481822506747 / 50000000000000), (99660169 / 1562500000000)⟩) (.abs (.atom 2)) ⟨(27203161727173 / 100000000000000), (4402556489 / 50000000000000)⟩) ⟨(-27203161727173 / 100000000000000), (4402556489 / 50000000000000)⟩) ⟨(137130451754161 / 100000000000000), (6829418651 / 50000000000000)⟩)

theorem boxSS12 {t : ℝ}
    (ht : |t-((693043755669 / 1000000000000) : ℝ)*π| ≤ (1 / 25000)) :
    |J t-((27203161727173 / 100000000000000) : ℝ)| ≤ (4402556489 / 50000000000000) ∧
    |J1 t-((-15847207705777 / 20000000000000) : ℝ)| ≤ (5627069 / 100000000000) ∧
    |J2 t-((137130451754161 / 100000000000000) : ℝ)| ≤ (6829418651 / 50000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((1 / 2) : ℝ)*π-((1212929689262113587647751 / 2000000000000000000000000) : ℝ)| ≤ (80000000193043755669 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxSS12Taylor hred
  have hreduced : t-((1 / 2) : ℝ)*π = t-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((82166806740667 / 100000000000000) : ℝ)| ≤ (1213431081 / 50000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hc : |cos t-((-56996630339363 / 100000000000000) : ℝ)| ≤ (849959923 / 20000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((4354522342851613587647751 / 2000000000000000000000000) : ℝ)| ≤ (80000000693043755669 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxSS12Input i).center : ℝ)| ≤ ((boxSS12Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxSS12Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxSS12Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxSS12Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxSS12Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxSS12Input i).center : ℝ)| ≤ ((boxSS12Input i).radius : ℝ) := by
    intro i
    simpa [boxSS12Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxSS12J boxSS12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS12Input,boxSS12J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS12J = J t := by
    norm_num [boxSS12J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((27203161727173 / 100000000000000) : ℝ)| ≤ (4402556489 / 50000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxSS12Input,boxSS12J,Fin.ofNat]
  have hFirst := Certificate.sound boxSS12First boxSS12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS12Input,boxSS12First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS12First = J1 t := by
    norm_num [boxSS12First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-15847207705777 / 20000000000000) : ℝ)| ≤ (5627069 / 100000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxSS12Input,boxSS12First,Fin.ofNat]
  have hSecond := Certificate.sound boxSS12Second boxSS12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxSS12Input,boxSS12Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxSS12Second = J2 t := by
    norm_num [boxSS12Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((137130451754161 / 100000000000000) : ℝ)| ≤ (6829418651 / 50000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxSS12Input,boxSS12Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST00TaylorInput : ℕ → RationalBall := fun _ => ⟨(-174881564695898900959383 / 250000000000000000000000), (5000000027833265477 / 250000000000000000000000)⟩
private def boxST00TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.const (1 / 6227020800)) ⟨(3929 / 50000000000000), (1 / 100000000000000)⟩) ⟨(-2497353 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-1222047 / 100000000000000), (9 / 12500000000000)⟩) ⟨(54870229 / 20000000000000), (73 / 100000000000000)⟩) ⟨(134250163 / 100000000000000), (7713 / 100000000000000)⟩) ⟨(-9853509839 / 50000000000000), (3857 / 50000000000000)⟩) ⟨(-9643373627 / 100000000000000), (555207 / 100000000000000)⟩) ⟨(411844979853 / 50000000000000), (69401 / 12500000000000)⟩) ⟨(629784317 / 156250000000), (1165987 / 5000000000000)⟩) ⟨(-16263604703787 / 100000000000000), (23319741 / 100000000000000)⟩) ⟨(-7958383319083 / 100000000000000), (93298223 / 20000000000000)⟩) ⟨(92041616680917 / 100000000000000), (93298223 / 20000000000000)⟩) ⟨(-16096381942299 / 25000000000000), (2167164459 / 100000000000000)⟩)
private def boxST00TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(48933698672777 / 100000000000000), (699536263 / 25000000000000)⟩) (.const (1 / 479001600)) ⟨(51079 / 50000000000000), (7 / 100000000000000)⟩) ⟨(-27455161 / 100000000000000), (1 / 12500000000000)⟩) ⟨(-6717413 / 50000000000000), (773 / 100000000000000)⟩) ⟨(38542561 / 1562500000000), (387 / 50000000000000)⟩) ⟨(603529621 / 50000000000000), (34701 / 50000000000000)⟩) ⟨(-137681829647 / 100000000000000), (69403 / 100000000000000)⟩) ⟨(-67372811647 / 100000000000000), (1943251 / 50000000000000)⟩) ⟨(204964692751 / 5000000000000), (3886503 / 100000000000000)⟩) ⟨(2005936102727 / 100000000000000), (116606107 / 100000000000000)⟩) ⟨(-47994063897273 / 100000000000000), (116606107 / 100000000000000)⟩) ⟨(-2935658826039 / 12500000000000), (1400006469 / 100000000000000)⟩) ⟨(9564341173961 / 12500000000000), (1400006469 / 100000000000000)⟩)

theorem boxST00Taylor {x : ℝ}
    (hx : |x-((-174881564695898900959383 / 250000000000000000000000) : ℝ)| ≤ (5000000027833265477 / 250000000000000000000000)) :
    |sin x-((-16096381942299 / 25000000000000) : ℝ)| ≤ (2167165689 / 100000000000000) ∧
    |cos x-((9564341173961 / 12500000000000) : ℝ)| ≤ (1400007699 / 100000000000000) := by
  have hs := Certificate.sound boxST00TaylorSin boxST00TaylorInput (fun _ => x)
    (by intro i; simpa [boxST00TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST00TaylorInput,boxST00TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST00TaylorCos boxST00TaylorInput (fun _ => x)
    (by intro i; simpa [boxST00TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST00TaylorInput,boxST00TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST00TaylorSin-
      ((-16096381942299 / 25000000000000) : ℝ)| ≤ (2167164459 / 100000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST00TaylorInput,boxST00TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST00TaylorCos-
      ((9564341173961 / 12500000000000) : ℝ)| ≤ (1400006469 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST00TaylorInput,boxST00TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST00TaylorSin = sinTaylor x := by
    norm_num [boxST00TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST00TaylorCos = cosTaylor x := by
    norm_num [boxST00TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-174881564695898900959383 / 250000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST00Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(1395914762098851099040617 / 250000000000000000000000), (5000000222166734523 / 250000000000000000000000)⟩, ⟨(-16096381942299 / 25000000000000), (2167165689 / 100000000000000)⟩, ⟨(9564341173961 / 12500000000000), (1400007699 / 100000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST00J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-27918295241977 / 5000000000000), (200000009 / 10000000000000)⟩) ⟨(1748815646959 / 2500000000000), (200000019 / 10000000000000)⟩) ⟨(-1748815646959 / 2500000000000), (200000019 / 10000000000000)⟩) ⟨(24420663948059 / 10000000000000), (25000003 / 1250000000000)⟩) (.atom 3) ⟨(186854049355109 / 100000000000000), (4949234527 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(50247915424861 / 20000000000000), (889550027 / 12500000000000)⟩)
private def boxST00First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-27918295241977 / 5000000000000), (200000009 / 10000000000000)⟩) ⟨(1748815646959 / 2500000000000), (200000019 / 10000000000000)⟩) ⟨(-1748815646959 / 2500000000000), (200000019 / 10000000000000)⟩) ⟨(24420663948059 / 10000000000000), (25000003 / 1250000000000)⟩) ⟨(-24420663948059 / 10000000000000), (25000003 / 1250000000000)⟩) (.atom 2) ⟨(39308433419249 / 25000000000000), (1316023311 / 20000000000000)⟩)
private def boxST00Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(16096381942299 / 12500000000000), (2167165689 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-27918295241977 / 5000000000000), (200000009 / 10000000000000)⟩) ⟨(1748815646959 / 2500000000000), (200000019 / 10000000000000)⟩) ⟨(-1748815646959 / 2500000000000), (200000019 / 10000000000000)⟩) ⟨(24420663948059 / 10000000000000), (25000003 / 1250000000000)⟩) (.atom 3) ⟨(186854049355109 / 100000000000000), (4949234527 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(50247915424861 / 20000000000000), (889550027 / 12500000000000)⟩) ⟨(-50247915424861 / 20000000000000), (889550027 / 12500000000000)⟩) ⟨(-122468521585913 / 100000000000000), (5725365797 / 50000000000000)⟩)

theorem boxST00 {t : ℝ}
    (ht : |t-((222166734523 / 125000000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((50247915424861 / 20000000000000) : ℝ)| ≤ (889550027 / 12500000000000) ∧
    |J1 t-((39308433419249 / 25000000000000) : ℝ)| ≤ (1316023311 / 20000000000000) ∧
    |J2 t-((-122468521585913 / 100000000000000) : ℝ)| ≤ (5725365797 / 50000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-(2 : ℝ)*π-((-174881564695898900959383 / 250000000000000000000000) : ℝ)| ≤ (5000000027833265477 / 250000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST00Taylor hred
  have hreduced : t-(2 : ℝ)*π = t-2*π := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-16096381942299 / 25000000000000) : ℝ)| ≤ (2167165689 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hc : |cos t-((9564341173961 / 12500000000000) : ℝ)| ≤ (1400007699 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((1395914762098851099040617 / 250000000000000000000000) : ℝ)| ≤ (5000000222166734523 / 250000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST00Input i).center : ℝ)| ≤ ((boxST00Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST00Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST00Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST00Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST00Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST00Input i).center : ℝ)| ≤ ((boxST00Input i).radius : ℝ) := by
    intro i
    simpa [boxST00Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = 2*π-t := by
    have ht0 : 0 ≤ 2*π-t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : 2*π-t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (2*π-t) = cos t := by rw [show 2*π-t = -(t-2*π) by ring,cos_neg,cos_sub_two_pi]
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST00J boxST00Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST00Input,boxST00J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST00J = J t := by
    norm_num [boxST00J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((50247915424861 / 20000000000000) : ℝ)| ≤ (889550027 / 12500000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST00Input,boxST00J,Fin.ofNat]
  have hFirst := Certificate.sound boxST00First boxST00Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST00Input,boxST00First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST00First = J1 t := by
    norm_num [boxST00First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((39308433419249 / 25000000000000) : ℝ)| ≤ (1316023311 / 20000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST00Input,boxST00First,Fin.ofNat]
  have hSecond := Certificate.sound boxST00Second boxST00Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST00Input,boxST00Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST00Second = J2 t := by
    norm_num [boxST00Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((-122468521585913 / 100000000000000) : ℝ)| ≤ (5725365797 / 50000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST00Input,boxST00Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST01TaylorInput : ℕ → RationalBall := fun _ => ⟨(-43981870796336400959383 / 250000000000000000000000), (15000000020999796431 / 750000000000000000000000)⟩
private def boxST01TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.const (1 / 6227020800)) ⟨(497 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1252357 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-38761 / 50000000000000), (9 / 50000000000000)⟩) ⟨(27549567 / 10000000000000), (19 / 100000000000000)⟩) ⟨(8526723 / 100000000000000), (97 / 5000000000000)⟩) ⟨(-9916371559 / 50000000000000), (1941 / 100000000000000)⟩) ⟨(-306916453 / 50000000000000), (69817 / 50000000000000)⟩) ⟨(832719500427 / 100000000000000), (27927 / 20000000000000)⟩) ⟨(12886533847 / 50000000000000), (2932293 / 50000000000000)⟩) ⟨(-16640893598973 / 100000000000000), (5864587 / 100000000000000)⟩) ⟨(-515043633533 / 100000000000000), (117291831 / 100000000000000)⟩) ⟨(99484956366467 / 100000000000000), (117291831 / 100000000000000)⟩) ⟨(-4375534497089 / 25000000000000), (1005168167 / 50000000000000)⟩)
private def boxST01TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.const (1 / 479001600)) ⟨(6461 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-13775429 / 50000000000000), (3 / 100000000000000)⟩) ⟨(-106589 / 12500000000000), (39 / 20000000000000)⟩) ⟨(1239653009 / 50000000000000), (49 / 25000000000000)⟩) ⟨(7673571 / 10000000000000), (3491 / 20000000000000)⟩) ⟨(-138812153179 / 100000000000000), (1091 / 6250000000000)⟩) ⟨(-4296302679 / 100000000000000), (977431 / 100000000000000)⟩) ⟨(1040592590997 / 25000000000000), (122179 / 12500000000000)⟩) ⟨(32206839489 / 25000000000000), (14661469 / 50000000000000)⟩) ⟨(-12467793160511 / 25000000000000), (14661469 / 50000000000000)⟩) ⟨(-385884174629 / 25000000000000), (351876111 / 100000000000000)⟩) ⟨(24614115825371 / 25000000000000), (351876111 / 100000000000000)⟩)

theorem boxST01Taylor {x : ℝ}
    (hx : |x-((-43981870796336400959383 / 250000000000000000000000) : ℝ)| ≤ (15000000020999796431 / 750000000000000000000000)) :
    |sin x-((-4375534497089 / 25000000000000) : ℝ)| ≤ (502584391 / 25000000000000) ∧
    |cos x-((24614115825371 / 25000000000000) : ℝ)| ≤ (351877341 / 100000000000000) := by
  have hs := Certificate.sound boxST01TaylorSin boxST01TaylorInput (fun _ => x)
    (by intro i; simpa [boxST01TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST01TaylorInput,boxST01TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST01TaylorCos boxST01TaylorInput (fun _ => x)
    (by intro i; simpa [boxST01TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST01TaylorInput,boxST01TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST01TaylorSin-
      ((-4375534497089 / 25000000000000) : ℝ)| ≤ (1005168167 / 50000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST01TaylorInput,boxST01TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST01TaylorCos-
      ((24614115825371 / 25000000000000) : ℝ)| ≤ (351876111 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST01TaylorInput,boxST01TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST01TaylorSin = sinTaylor x := by
    norm_num [boxST01TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST01TaylorCos = cosTaylor x := by
    norm_num [boxST01TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-43981870796336400959383 / 250000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST01Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(741416292601038599040617 / 250000000000000000000000), (15000000354000203569 / 750000000000000000000000)⟩, ⟨(4375534497089 / 25000000000000), (502584391 / 25000000000000)⟩, ⟨(-24614115825371 / 25000000000000), (351877341 / 100000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST01J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-59313303408083 / 20000000000000), (125000003 / 6250000000000)⟩) ⟨(3518549663707 / 20000000000000), (1000000049 / 50000000000000)⟩) (.atom 3) ⟨(-17321197791961 / 100000000000000), (126940081 / 6250000000000)⟩) (.abs (.atom 2)) ⟨(36188039279 / 20000000000000), (202068943 / 5000000000000)⟩)
private def boxST01First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-59313303408083 / 20000000000000), (125000003 / 6250000000000)⟩) ⟨(3518549663707 / 20000000000000), (1000000049 / 50000000000000)⟩) ⟨(-3518549663707 / 20000000000000), (1000000049 / 50000000000000)⟩) (.atom 2) ⟨(-1539553543327 / 50000000000000), (175939153 / 25000000000000)⟩)
private def boxST01Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(4375534497089 / 12500000000000), (502584391 / 12500000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-59313303408083 / 20000000000000), (125000003 / 6250000000000)⟩) ⟨(3518549663707 / 20000000000000), (1000000049 / 50000000000000)⟩) (.atom 3) ⟨(-17321197791961 / 100000000000000), (126940081 / 6250000000000)⟩) (.abs (.atom 2)) ⟨(36188039279 / 20000000000000), (202068943 / 5000000000000)⟩) ⟨(-36188039279 / 20000000000000), (202068943 / 5000000000000)⟩) ⟨(34823335780317 / 100000000000000), (2015513497 / 25000000000000)⟩)

theorem boxST01 {t : ℝ}
    (ht : |t-((354000203569 / 375000000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((36188039279 / 20000000000000) : ℝ)| ≤ (202068943 / 5000000000000) ∧
    |J1 t-((-1539553543327 / 50000000000000) : ℝ)| ≤ (175939153 / 25000000000000) ∧
    |J2 t-((34823335780317 / 100000000000000) : ℝ)| ≤ (2015513497 / 25000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-(1 : ℝ)*π-((-43981870796336400959383 / 250000000000000000000000) : ℝ)| ≤ (15000000020999796431 / 750000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST01Taylor hred
  have hreduced : t-(1 : ℝ)*π = t-π := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((4375534497089 / 25000000000000) : ℝ)| ≤ (502584391 / 25000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hc : |cos t-((-24614115825371 / 25000000000000) : ℝ)| ≤ (351877341 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((741416292601038599040617 / 250000000000000000000000) : ℝ)| ≤ (15000000354000203569 / 750000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST01Input i).center : ℝ)| ≤ ((boxST01Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST01Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST01Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST01Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST01Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST01Input i).center : ℝ)| ≤ ((boxST01Input i).radius : ℝ) := by
    intro i
    simpa [boxST01Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST01J boxST01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST01Input,boxST01J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST01J = J t := by
    norm_num [boxST01J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((36188039279 / 20000000000000) : ℝ)| ≤ (202068943 / 5000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST01Input,boxST01J,Fin.ofNat]
  have hFirst := Certificate.sound boxST01First boxST01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST01Input,boxST01First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST01First = J1 t := by
    norm_num [boxST01First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-1539553543327 / 50000000000000) : ℝ)| ≤ (175939153 / 25000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST01Input,boxST01First,Fin.ofNat]
  have hSecond := Certificate.sound boxST01Second boxST01Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST01Input,boxST01Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST01Second = J2 t := by
    norm_num [boxST01Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((34823335780317 / 100000000000000) : ℝ)| ≤ (2015513497 / 25000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST01Input,boxST01Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST02TaylorInput : ℕ → RationalBall := fun _ => ⟨(-43981870796336400959383 / 250000000000000000000000), (15000000020999796431 / 750000000000000000000000)⟩
private def boxST02TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.const (1 / 6227020800)) ⟨(497 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1252357 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-38761 / 50000000000000), (9 / 50000000000000)⟩) ⟨(27549567 / 10000000000000), (19 / 100000000000000)⟩) ⟨(8526723 / 100000000000000), (97 / 5000000000000)⟩) ⟨(-9916371559 / 50000000000000), (1941 / 100000000000000)⟩) ⟨(-306916453 / 50000000000000), (69817 / 50000000000000)⟩) ⟨(832719500427 / 100000000000000), (27927 / 20000000000000)⟩) ⟨(12886533847 / 50000000000000), (2932293 / 50000000000000)⟩) ⟨(-16640893598973 / 100000000000000), (5864587 / 100000000000000)⟩) ⟨(-515043633533 / 100000000000000), (117291831 / 100000000000000)⟩) ⟨(99484956366467 / 100000000000000), (117291831 / 100000000000000)⟩) ⟨(-4375534497089 / 25000000000000), (1005168167 / 50000000000000)⟩)
private def boxST02TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(3095047933993 / 100000000000000), (351874967 / 50000000000000)⟩) (.const (1 / 479001600)) ⟨(6461 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-13775429 / 50000000000000), (3 / 100000000000000)⟩) ⟨(-106589 / 12500000000000), (39 / 20000000000000)⟩) ⟨(1239653009 / 50000000000000), (49 / 25000000000000)⟩) ⟨(7673571 / 10000000000000), (3491 / 20000000000000)⟩) ⟨(-138812153179 / 100000000000000), (1091 / 6250000000000)⟩) ⟨(-4296302679 / 100000000000000), (977431 / 100000000000000)⟩) ⟨(1040592590997 / 25000000000000), (122179 / 12500000000000)⟩) ⟨(32206839489 / 25000000000000), (14661469 / 50000000000000)⟩) ⟨(-12467793160511 / 25000000000000), (14661469 / 50000000000000)⟩) ⟨(-385884174629 / 25000000000000), (351876111 / 100000000000000)⟩) ⟨(24614115825371 / 25000000000000), (351876111 / 100000000000000)⟩)

theorem boxST02Taylor {x : ℝ}
    (hx : |x-((-43981870796336400959383 / 250000000000000000000000) : ℝ)| ≤ (15000000020999796431 / 750000000000000000000000)) :
    |sin x-((-4375534497089 / 25000000000000) : ℝ)| ≤ (502584391 / 25000000000000) ∧
    |cos x-((24614115825371 / 25000000000000) : ℝ)| ≤ (351877341 / 100000000000000) := by
  have hs := Certificate.sound boxST02TaylorSin boxST02TaylorInput (fun _ => x)
    (by intro i; simpa [boxST02TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST02TaylorInput,boxST02TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST02TaylorCos boxST02TaylorInput (fun _ => x)
    (by intro i; simpa [boxST02TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST02TaylorInput,boxST02TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST02TaylorSin-
      ((-4375534497089 / 25000000000000) : ℝ)| ≤ (1005168167 / 50000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST02TaylorInput,boxST02TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST02TaylorCos-
      ((24614115825371 / 25000000000000) : ℝ)| ≤ (351876111 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST02TaylorInput,boxST02TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST02TaylorSin = sinTaylor x := by
    norm_num [boxST02TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST02TaylorCos = cosTaylor x := by
    norm_num [boxST02TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-43981870796336400959383 / 250000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST02Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(348717210902351099040617 / 250000000000000000000000), (15000000166500203569 / 750000000000000000000000)⟩, ⟨(24614115825371 / 25000000000000), (351877341 / 100000000000000)⟩, ⟨(4375534497089 / 25000000000000), (502584391 / 25000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST02J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-6974344218047 / 5000000000000), (2000000023 / 100000000000000)⟩) ⟨(17467238099801 / 10000000000000), (2000000073 / 100000000000000)⟩) (.atom 3) ⟨(30571401149819 / 100000000000000), (3861587469 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(129027864451303 / 100000000000000), (421346481 / 10000000000000)⟩)
private def boxST02First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-6974344218047 / 5000000000000), (2000000023 / 100000000000000)⟩) ⟨(17467238099801 / 10000000000000), (2000000073 / 100000000000000)⟩) ⟨(-17467238099801 / 10000000000000), (2000000073 / 100000000000000)⟩) (.atom 2) ⟨(-85988124347567 / 50000000000000), (1291884453 / 50000000000000)⟩)
private def boxST02Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(24614115825371 / 12500000000000), (351877341 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-6974344218047 / 5000000000000), (2000000023 / 100000000000000)⟩) ⟨(17467238099801 / 10000000000000), (2000000073 / 100000000000000)⟩) (.atom 3) ⟨(30571401149819 / 100000000000000), (3861587469 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(129027864451303 / 100000000000000), (421346481 / 10000000000000)⟩) ⟨(-129027864451303 / 100000000000000), (421346481 / 10000000000000)⟩) ⟨(13577012430333 / 20000000000000), (1229304873 / 25000000000000)⟩)

theorem boxST02 {t : ℝ}
    (ht : |t-((166500203569 / 375000000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((129027864451303 / 100000000000000) : ℝ)| ≤ (421346481 / 10000000000000) ∧
    |J1 t-((-85988124347567 / 50000000000000) : ℝ)| ≤ (1291884453 / 50000000000000) ∧
    |J2 t-((13577012430333 / 20000000000000) : ℝ)| ≤ (1229304873 / 25000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((1 / 2) : ℝ)*π-((-43981870796336400959383 / 250000000000000000000000) : ℝ)| ≤ (15000000020999796431 / 750000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST02Taylor hred
  have hreduced : t-((1 / 2) : ℝ)*π = t-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((24614115825371 / 25000000000000) : ℝ)| ≤ (351877341 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hc : |cos t-((4375534497089 / 25000000000000) : ℝ)| ≤ (502584391 / 25000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((348717210902351099040617 / 250000000000000000000000) : ℝ)| ≤ (15000000166500203569 / 750000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST02Input i).center : ℝ)| ≤ ((boxST02Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST02Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST02Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST02Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST02Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST02Input i).center : ℝ)| ≤ ((boxST02Input i).radius : ℝ) := by
    intro i
    simpa [boxST02Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST02J boxST02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST02Input,boxST02J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST02J = J t := by
    norm_num [boxST02J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((129027864451303 / 100000000000000) : ℝ)| ≤ (421346481 / 10000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST02Input,boxST02J,Fin.ofNat]
  have hFirst := Certificate.sound boxST02First boxST02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST02Input,boxST02First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST02First = J1 t := by
    norm_num [boxST02First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-85988124347567 / 50000000000000) : ℝ)| ≤ (1291884453 / 50000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST02Input,boxST02First,Fin.ofNat]
  have hSecond := Certificate.sound boxST02Second boxST02Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST02Input,boxST02Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST02Second = J2 t := by
    norm_num [boxST02Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((13577012430333 / 20000000000000) : ℝ)| ≤ (1229304873 / 25000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST02Input,boxST02Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST10TaylorInput : ℕ → RationalBall := fun _ => ⟨(22075045818533442053319 / 125000000000000000000000), (2500000003513352661 / 125000000000000000000000)⟩
private def boxST10TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.const (1 / 6227020800)) ⟨(501 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-250471 / 10000000000000), (1 / 50000000000000)⟩) ⟨(-19529 / 25000000000000), (9 / 50000000000000)⟩) ⟨(68873769 / 25000000000000), (19 / 100000000000000)⟩) ⟨(1718411 / 20000000000000), (1947 / 100000000000000)⟩) ⟨(-9916338893 / 50000000000000), (487 / 25000000000000)⟩) ⟨(-154633849 / 25000000000000), (17521 / 12500000000000)⟩) ⟨(832714797937 / 100000000000000), (140169 / 100000000000000)⟩) ⟨(25970450531 / 100000000000000), (735877 / 12500000000000)⟩) ⟨(-2080087027017 / 12500000000000), (5887017 / 100000000000000)⟩) ⟨(-51898486607 / 10000000000000), (117740423 / 100000000000000)⟩) ⟨(9948101513393 / 10000000000000), (117740423 / 100000000000000)⟩) ⟨(8784191868623 / 50000000000000), (2010415663 / 100000000000000)⟩)
private def boxST10TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1559384473249 / 50000000000000), (176610367 / 25000000000000)⟩) (.const (1 / 479001600)) ⟨(6511 / 100000000000000), (1 / 50000000000000)⟩) ⟨(-3443851 / 12500000000000), (3 / 100000000000000)⟩) ⟨(-429623 / 50000000000000), (39 / 20000000000000)⟩) ⟨(619824871 / 25000000000000), (49 / 25000000000000)⟩) ⟨(38661811 / 50000000000000), (8761 / 50000000000000)⟩) ⟨(-138811565267 / 100000000000000), (17523 / 100000000000000)⟩) ⟨(-541151499 / 12500000000000), (98117 / 10000000000000)⟩) ⟨(166493498187 / 4000000000000), (981171 / 100000000000000)⟩) ⟨(25962737597 / 20000000000000), (14717543 / 50000000000000)⟩) ⟨(-9974037262403 / 20000000000000), (14717543 / 50000000000000)⟩) ⟨(-77766794213 / 5000000000000), (353221897 / 100000000000000)⟩) ⟨(4922233205787 / 5000000000000), (353221897 / 100000000000000)⟩)

theorem boxST10Taylor {x : ℝ}
    (hx : |x-((22075045818533442053319 / 125000000000000000000000) : ℝ)| ≤ (2500000003513352661 / 125000000000000000000000)) :
    |sin x-((8784191868623 / 50000000000000) : ℝ)| ≤ (2010416893 / 100000000000000) ∧
    |cos x-((4922233205787 / 5000000000000) : ℝ)| ≤ (353223127 / 100000000000000) := by
  have hs := Certificate.sound boxST10TaylorSin boxST10TaylorInput (fun _ => x)
    (by intro i; simpa [boxST10TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST10TaylorInput,boxST10TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST10TaylorCos boxST10TaylorInput (fun _ => x)
    (by intro i; simpa [boxST10TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST10TaylorInput,boxST10TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST10TaylorSin-
      ((8784191868623 / 50000000000000) : ℝ)| ≤ (2010415663 / 100000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST10TaylorInput,boxST10TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST10TaylorCos-
      ((4922233205787 / 5000000000000) : ℝ)| ≤ (353221897 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST10TaylorInput,boxST10TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST10TaylorSin = sinTaylor x := by
    norm_num [boxST10TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST10TaylorCos = cosTaylor x := by
    norm_num [boxST10TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((22075045818533442053319 / 125000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST10Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(414774127517220942053319 / 125000000000000000000000), (2500000066013352661 / 125000000000000000000000)⟩, ⟨(-8784191868623 / 50000000000000), (2010416893 / 100000000000000)⟩, ⟨(-4922233205787 / 5000000000000), (353223127 / 100000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST10J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-331819302013777 / 100000000000000), (1000000027 / 50000000000000)⟩) ⟨(296499228704123 / 100000000000000), (1000000077 / 50000000000000)⟩) ⟨(-296499228704123 / 100000000000000), (1000000077 / 50000000000000)⟩) ⟨(17660036654827 / 100000000000000), (500000051 / 25000000000000)⟩) (.atom 3) ⟨(-17385363767561 / 100000000000000), (1015639941 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(36603993937 / 20000000000000), (161667871 / 4000000000000)⟩)
private def boxST10First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-331819302013777 / 100000000000000), (1000000027 / 50000000000000)⟩) ⟨(296499228704123 / 100000000000000), (1000000077 / 50000000000000)⟩) ⟨(-296499228704123 / 100000000000000), (1000000077 / 50000000000000)⟩) ⟨(17660036654827 / 100000000000000), (500000051 / 25000000000000)⟩) ⟨(-17660036654827 / 100000000000000), (500000051 / 25000000000000)⟩) (.atom 2) ⟨(1551291503829 / 50000000000000), (17661207 / 2500000000000)⟩)
private def boxST10Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(8784191868623 / 25000000000000), (2010416893 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.add (.mul (.atom 0) (.const 2) ⟨(6283185307179 / 1000000000000), (1 / 1000000000000)⟩) (.mul (.const (-1)) (.atom 1) ⟨(-331819302013777 / 100000000000000), (1000000027 / 50000000000000)⟩) ⟨(296499228704123 / 100000000000000), (1000000077 / 50000000000000)⟩) ⟨(-296499228704123 / 100000000000000), (1000000077 / 50000000000000)⟩) ⟨(17660036654827 / 100000000000000), (500000051 / 25000000000000)⟩) (.atom 3) ⟨(-17385363767561 / 100000000000000), (1015639941 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(36603993937 / 20000000000000), (161667871 / 4000000000000)⟩) ⟨(-36603993937 / 20000000000000), (161667871 / 4000000000000)⟩) ⟨(34953747504807 / 100000000000000), (8062530561 / 100000000000000)⟩)

theorem boxST10 {t : ℝ}
    (ht : |t-((66013352661 / 62500000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((36603993937 / 20000000000000) : ℝ)| ≤ (161667871 / 4000000000000) ∧
    |J1 t-((1551291503829 / 50000000000000) : ℝ)| ≤ (17661207 / 2500000000000) ∧
    |J2 t-((34953747504807 / 100000000000000) : ℝ)| ≤ (8062530561 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-(1 : ℝ)*π-((22075045818533442053319 / 125000000000000000000000) : ℝ)| ≤ (2500000003513352661 / 125000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST10Taylor hred
  have hreduced : t-(1 : ℝ)*π = t-π := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-8784191868623 / 50000000000000) : ℝ)| ≤ (2010416893 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hc : |cos t-((-4922233205787 / 5000000000000) : ℝ)| ≤ (353223127 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((414774127517220942053319 / 125000000000000000000000) : ℝ)| ≤ (2500000066013352661 / 125000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST10Input i).center : ℝ)| ≤ ((boxST10Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST10Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST10Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST10Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST10Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST10Input i).center : ℝ)| ≤ ((boxST10Input i).radius : ℝ) := by
    intro i
    simpa [boxST10Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = 2*π-t := by
    have ht0 : 0 ≤ 2*π-t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : 2*π-t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (2*π-t) = cos t := by rw [show 2*π-t = -(t-2*π) by ring,cos_neg,cos_sub_two_pi]
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST10J boxST10Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST10Input,boxST10J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST10J = J t := by
    norm_num [boxST10J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((36603993937 / 20000000000000) : ℝ)| ≤ (161667871 / 4000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST10Input,boxST10J,Fin.ofNat]
  have hFirst := Certificate.sound boxST10First boxST10Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST10Input,boxST10First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST10First = J1 t := by
    norm_num [boxST10First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((1551291503829 / 50000000000000) : ℝ)| ≤ (17661207 / 2500000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST10Input,boxST10First,Fin.ofNat]
  have hSecond := Certificate.sound boxST10Second boxST10Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST10Input,boxST10Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST10Second = J2 t := by
    norm_num [boxST10Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((34953747504807 / 100000000000000) : ℝ)| ≤ (8062530561 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST10Input,boxST10Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST11TaylorInput : ℕ → RationalBall := fun _ => ⟨(87524892768314692053319 / 125000000000000000000000), (7500000041790057983 / 375000000000000000000000)⟩
private def boxST11TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.const (1 / 6227020800)) ⟨(7873 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1248669 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-153049 / 12500000000000), (71 / 100000000000000)⟩) ⟨(42867 / 15625000000), (9 / 12500000000000)⟩) ⟨(134507411 / 100000000000000), (193 / 2500000000000)⟩) ⟨(-1970676243 / 10000000000000), (7721 / 100000000000000)⟩) ⟨(-4830904299 / 50000000000000), (27787 / 5000000000000)⟩) ⟨(164734304947 / 20000000000000), (555741 / 100000000000000)⟩) ⟨(403828718587 / 100000000000000), (11671089 / 50000000000000)⟩) ⟨(-203285474351 / 1250000000000), (23342179 / 100000000000000)⟩) ⟨(-1594665060509 / 20000000000000), (233470173 / 50000000000000)⟩) ⟨(18405334939491 / 20000000000000), (233470173 / 50000000000000)⟩) ⟨(12887399735551 / 20000000000000), (1083747037 / 50000000000000)⟩)
private def boxST11TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.const (1 / 479001600)) ⟨(51177 / 50000000000000), (7 / 100000000000000)⟩) ⟨(-5490993 / 20000000000000), (1 / 12500000000000)⟩) ⟨(-3365147 / 25000000000000), (387 / 50000000000000)⟩) ⟨(1233349071 / 50000000000000), (31 / 4000000000000)⟩) ⟨(12093699 / 1000000000000), (69469 / 100000000000000)⟩) ⟨(-137679518989 / 100000000000000), (6947 / 10000000000000)⟩) ⟨(-33750677339 / 50000000000000), (3890241 / 100000000000000)⟩) ⟨(4099165311989 / 100000000000000), (1945121 / 50000000000000)⟩) ⟨(251216751081 / 12500000000000), (23343667 / 20000000000000)⟩) ⟨(-5998783248919 / 12500000000000), (23343667 / 20000000000000)⟩) ⟨(-4705722375471 / 20000000000000), (1401356727 / 100000000000000)⟩) ⟨(15294277624529 / 20000000000000), (1401356727 / 100000000000000)⟩)

theorem boxST11Taylor {x : ℝ}
    (hx : |x-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (7500000041790057983 / 375000000000000000000000)) :
    |sin x-((12887399735551 / 20000000000000) : ℝ)| ≤ (270936913 / 12500000000000) ∧
    |cos x-((15294277624529 / 20000000000000) : ℝ)| ≤ (1401357957 / 100000000000000) := by
  have hs := Certificate.sound boxST11TaylorSin boxST11TaylorInput (fun _ => x)
    (by intro i; simpa [boxST11TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST11TaylorInput,boxST11TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST11TaylorCos boxST11TaylorInput (fun _ => x)
    (by intro i; simpa [boxST11TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST11TaylorInput,boxST11TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST11TaylorSin-
      ((12887399735551 / 20000000000000) : ℝ)| ≤ (1083747037 / 50000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST11TaylorInput,boxST11TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST11TaylorCos-
      ((15294277624529 / 20000000000000) : ℝ)| ≤ (1401356727 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST11TaylorInput,boxST11TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST11TaylorSin = sinTaylor x := by
    norm_num [boxST11TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST11TaylorCos = cosTaylor x := by
    norm_num [boxST11TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((87524892768314692053319 / 125000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST11Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(87524892768314692053319 / 125000000000000000000000), (7500000041790057983 / 375000000000000000000000)⟩, ⟨(12887399735551 / 20000000000000), (270936913 / 12500000000000)⟩, ⟨(15294277624529 / 20000000000000), (1401357957 / 100000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST11J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-17504978553663 / 25000000000000), (500000003 / 25000000000000)⟩) ⟨(122069675572149 / 50000000000000), (1000000031 / 50000000000000)⟩) (.atom 3) ⟨(186696750773663 / 100000000000000), (4950722061 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(125566874725709 / 50000000000000), (1423643473 / 20000000000000)⟩)
private def boxST11First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-17504978553663 / 25000000000000), (500000003 / 25000000000000)⟩) ⟨(122069675572149 / 50000000000000), (1000000031 / 50000000000000)⟩) ⟨(-122069675572149 / 50000000000000), (1000000031 / 50000000000000)⟩) (.atom 2) ⟨(-157316070468731 / 100000000000000), (1316098467 / 20000000000000)⟩)
private def boxST11Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(12887399735551 / 10000000000000), (270936913 / 6250000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-17504978553663 / 25000000000000), (500000003 / 25000000000000)⟩) ⟨(122069675572149 / 50000000000000), (1000000031 / 50000000000000)⟩) (.atom 3) ⟨(186696750773663 / 100000000000000), (4950722061 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(125566874725709 / 50000000000000), (1423643473 / 20000000000000)⟩) ⟨(-125566874725709 / 50000000000000), (1423643473 / 20000000000000)⟩) ⟨(-30564938023977 / 25000000000000), (11453207973 / 100000000000000)⟩)

theorem boxST11 {t : ℝ}
    (ht : |t-((41790057983 / 187500000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((125566874725709 / 50000000000000) : ℝ)| ≤ (1423643473 / 20000000000000) ∧
    |J1 t-((-157316070468731 / 100000000000000) : ℝ)| ≤ (1316098467 / 20000000000000) ∧
    |J2 t-((-30564938023977 / 25000000000000) : ℝ)| ≤ (11453207973 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-(0 : ℝ)*π-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (7500000041790057983 / 375000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST11Taylor hred
  have hreduced : t-(0 : ℝ)*π = t := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((12887399735551 / 20000000000000) : ℝ)| ≤ (270936913 / 12500000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hc : |cos t-((15294277624529 / 20000000000000) : ℝ)| ≤ (1401357957 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (7500000041790057983 / 375000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST11Input i).center : ℝ)| ≤ ((boxST11Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST11Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST11Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST11Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST11Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST11Input i).center : ℝ)| ≤ ((boxST11Input i).radius : ℝ) := by
    intro i
    simpa [boxST11Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST11J boxST11Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST11Input,boxST11J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST11J = J t := by
    norm_num [boxST11J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((125566874725709 / 50000000000000) : ℝ)| ≤ (1423643473 / 20000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST11Input,boxST11J,Fin.ofNat]
  have hFirst := Certificate.sound boxST11First boxST11Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST11Input,boxST11First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST11First = J1 t := by
    norm_num [boxST11First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-157316070468731 / 100000000000000) : ℝ)| ≤ (1316098467 / 20000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST11Input,boxST11First,Fin.ofNat]
  have hSecond := Certificate.sound boxST11Second boxST11Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST11Input,boxST11Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST11Second = J2 t := by
    norm_num [boxST11Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((-30564938023977 / 25000000000000) : ℝ)| ≤ (11453207973 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST11Input,boxST11Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST12TaylorInput : ℕ → RationalBall := fun _ => ⟨(87524892768314692053319 / 125000000000000000000000), (7500000041790057983 / 375000000000000000000000)⟩
private def boxST12TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.const (1 / 6227020800)) ⟨(7873 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-1248669 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-153049 / 12500000000000), (71 / 100000000000000)⟩) ⟨(42867 / 15625000000), (9 / 12500000000000)⟩) ⟨(134507411 / 100000000000000), (193 / 2500000000000)⟩) ⟨(-1970676243 / 10000000000000), (7721 / 100000000000000)⟩) ⟨(-4830904299 / 50000000000000), (27787 / 5000000000000)⟩) ⟨(164734304947 / 20000000000000), (555741 / 100000000000000)⟩) ⟨(403828718587 / 100000000000000), (11671089 / 50000000000000)⟩) ⟨(-203285474351 / 1250000000000), (23342179 / 100000000000000)⟩) ⟨(-1594665060509 / 20000000000000), (233470173 / 50000000000000)⟩) ⟨(18405334939491 / 20000000000000), (233470173 / 50000000000000)⟩) ⟨(12887399735551 / 20000000000000), (1083747037 / 50000000000000)⟩)
private def boxST12TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(1532121370821 / 3125000000000), (560167317 / 20000000000000)⟩) (.const (1 / 479001600)) ⟨(51177 / 50000000000000), (7 / 100000000000000)⟩) ⟨(-5490993 / 20000000000000), (1 / 12500000000000)⟩) ⟨(-3365147 / 25000000000000), (387 / 50000000000000)⟩) ⟨(1233349071 / 50000000000000), (31 / 4000000000000)⟩) ⟨(12093699 / 1000000000000), (69469 / 100000000000000)⟩) ⟨(-137679518989 / 100000000000000), (6947 / 10000000000000)⟩) ⟨(-33750677339 / 50000000000000), (3890241 / 100000000000000)⟩) ⟨(4099165311989 / 100000000000000), (1945121 / 50000000000000)⟩) ⟨(251216751081 / 12500000000000), (23343667 / 20000000000000)⟩) ⟨(-5998783248919 / 12500000000000), (23343667 / 20000000000000)⟩) ⟨(-4705722375471 / 20000000000000), (1401356727 / 100000000000000)⟩) ⟨(15294277624529 / 20000000000000), (1401356727 / 100000000000000)⟩)

theorem boxST12Taylor {x : ℝ}
    (hx : |x-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (7500000041790057983 / 375000000000000000000000)) :
    |sin x-((12887399735551 / 20000000000000) : ℝ)| ≤ (270936913 / 12500000000000) ∧
    |cos x-((15294277624529 / 20000000000000) : ℝ)| ≤ (1401357957 / 100000000000000) := by
  have hs := Certificate.sound boxST12TaylorSin boxST12TaylorInput (fun _ => x)
    (by intro i; simpa [boxST12TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST12TaylorInput,boxST12TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST12TaylorCos boxST12TaylorInput (fun _ => x)
    (by intro i; simpa [boxST12TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST12TaylorInput,boxST12TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST12TaylorSin-
      ((12887399735551 / 20000000000000) : ℝ)| ≤ (1083747037 / 50000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST12TaylorInput,boxST12TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST12TaylorCos-
      ((15294277624529 / 20000000000000) : ℝ)| ≤ (1401356727 / 100000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST12TaylorInput,boxST12TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST12TaylorSin = sinTaylor x := by
    norm_num [boxST12TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST12TaylorCos = cosTaylor x := by
    norm_num [boxST12TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((87524892768314692053319 / 125000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST12Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(-108824648081029057946681 / 125000000000000000000000), (7500000051959942017 / 375000000000000000000000)⟩, ⟨(-15294277624529 / 20000000000000), (1401357957 / 100000000000000)⟩, ⟨(12887399735551 / 20000000000000), (270936913 / 12500000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST12J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(87059718464823 / 100000000000000), (400000003 / 20000000000000)⟩) ⟨(-87059718464823 / 100000000000000), (400000003 / 20000000000000)⟩) ⟨(227099546894127 / 100000000000000), (400000013 / 20000000000000)⟩) (.atom 3) ⟨(36584033007339 / 25000000000000), (310557769 / 5000000000000)⟩) (.abs (.atom 2)) ⟨(222807520152001 / 100000000000000), (7612513337 / 100000000000000)⟩)
private def boxST12First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(87059718464823 / 100000000000000), (400000003 / 20000000000000)⟩) ⟨(-87059718464823 / 100000000000000), (400000003 / 20000000000000)⟩) ⟨(227099546894127 / 100000000000000), (400000013 / 20000000000000)⟩) ⟨(-227099546894127 / 100000000000000), (400000013 / 20000000000000)⟩) (.atom 2) ⟨(2713533998909 / 1562500000000), (4711933411 / 100000000000000)⟩)
private def boxST12Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(15294277624529 / 10000000000000), (1401357957 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(87059718464823 / 100000000000000), (400000003 / 20000000000000)⟩) ⟨(-87059718464823 / 100000000000000), (400000003 / 20000000000000)⟩) ⟨(227099546894127 / 100000000000000), (400000013 / 20000000000000)⟩) (.atom 3) ⟨(36584033007339 / 25000000000000), (310557769 / 5000000000000)⟩) (.abs (.atom 2)) ⟨(222807520152001 / 100000000000000), (7612513337 / 100000000000000)⟩) ⟨(-222807520152001 / 100000000000000), (7612513337 / 100000000000000)⟩) ⟨(-69864743906711 / 100000000000000), (10415229251 / 100000000000000)⟩)

theorem boxST12 {t : ℝ}
    (ht : |t-((-51959942017 / 187500000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((222807520152001 / 100000000000000) : ℝ)| ≤ (7612513337 / 100000000000000) ∧
    |J1 t-((2713533998909 / 1562500000000) : ℝ)| ≤ (4711933411 / 100000000000000) ∧
    |J2 t-((-69864743906711 / 100000000000000) : ℝ)| ≤ (10415229251 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((-1 / 2) : ℝ)*π-((87524892768314692053319 / 125000000000000000000000) : ℝ)| ≤ (7500000041790057983 / 375000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST12Taylor hred
  have hreduced : t-((-1 / 2) : ℝ)*π = t+π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-15294277624529 / 20000000000000) : ℝ)| ≤ (1401357957 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hc : |cos t-((12887399735551 / 20000000000000) : ℝ)| ≤ (270936913 / 12500000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((-108824648081029057946681 / 125000000000000000000000) : ℝ)| ≤ (7500000051959942017 / 375000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST12Input i).center : ℝ)| ≤ ((boxST12Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST12Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST12Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST12Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST12Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST12Input i).center : ℝ)| ≤ ((boxST12Input i).radius : ℝ) := by
    intro i
    simpa [boxST12Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = -t := by
    have ht0 : 0 ≤ -t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : -t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (-t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST12J boxST12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST12Input,boxST12J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST12J = J t := by
    norm_num [boxST12J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eJ] at hJ
  have bJ : |J t-((222807520152001 / 100000000000000) : ℝ)| ≤ (7612513337 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST12Input,boxST12J,Fin.ofNat]
  have hFirst := Certificate.sound boxST12First boxST12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST12Input,boxST12First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST12First = J1 t := by
    norm_num [boxST12First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((2713533998909 / 1562500000000) : ℝ)| ≤ (4711933411 / 100000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST12Input,boxST12First,Fin.ofNat]
  have hSecond := Certificate.sound boxST12Second boxST12Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST12Input,boxST12Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST12Second = J2 t := by
    norm_num [boxST12Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((-69864743906711 / 100000000000000) : ℝ)| ≤ (10415229251 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST12Input,boxST12Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST20TaylorInput : ℕ → RationalBall := fun _ => ⟨(-859728956165578514794647 / 2000000000000000000000000), (40000000136830113093 / 2000000000000000000000000)⟩
private def boxST20TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(2967 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-625561 / 25000000000000), (1 / 50000000000000)⟩) ⟨(-462373 / 100000000000000), (11 / 25000000000000)⟩) ⟨(275110819 / 100000000000000), (9 / 20000000000000)⟩) ⟨(12708983 / 25000000000000), (237 / 5000000000000)⟩) ⟨(-19790433909 / 100000000000000), (4741 / 100000000000000)⟩) ⟨(-3656945041 / 100000000000000), (341173 / 100000000000000)⟩) ⟨(207419097073 / 25000000000000), (170587 / 50000000000000)⟩) ⟨(30662096321 / 20000000000000), (7164659 / 50000000000000)⟩) ⟨(-8256678092531 / 50000000000000), (14329319 / 100000000000000)⟩) ⟨(-762848812313 / 25000000000000), (71648721 / 25000000000000)⟩) ⟨(24237151187687 / 25000000000000), (71648721 / 25000000000000)⟩) ⟨(-8334952276407 / 20000000000000), (1031087397 / 50000000000000)⟩)
private def boxST20TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(18478346951739 / 100000000000000), (1719497919 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(38577 / 100000000000000), (1 / 25000000000000)⟩) ⟨(-13759371 / 50000000000000), (1 / 20000000000000)⟩) ⟨(-5085009 / 100000000000000), (19 / 4000000000000)⟩) ⟨(2475073721 / 100000000000000), (119 / 25000000000000)⟩) ⟨(457352709 / 100000000000000), (5331 / 12500000000000)⟩) ⟨(-6921576809 / 5000000000000), (42649 / 100000000000000)⟩) ⟨(-12789929773 / 50000000000000), (2388209 / 100000000000000)⟩) ⟨(4141086807121 / 100000000000000), (238821 / 10000000000000)⟩) ⟨(765204387793 / 100000000000000), (14329449 / 20000000000000)⟩) ⟨(-49234795612207 / 100000000000000), (14329449 / 20000000000000)⟩) ⟨(-9097776354203 / 100000000000000), (171966349 / 20000000000000)⟩) ⟨(90902223645797 / 100000000000000), (171966349 / 20000000000000)⟩)

theorem boxST20Taylor {x : ℝ}
    (hx : |x-((-859728956165578514794647 / 2000000000000000000000000) : ℝ)| ≤ (40000000136830113093 / 2000000000000000000000000)) :
    |sin x-((-8334952276407 / 20000000000000) : ℝ)| ≤ (257772003 / 12500000000000) ∧
    |cos x-((90902223645797 / 100000000000000) : ℝ)| ≤ (34393319 / 4000000000000) := by
  have hs := Certificate.sound boxST20TaylorSin boxST20TaylorInput (fun _ => x)
    (by intro i; simpa [boxST20TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST20TaylorInput,boxST20TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST20TaylorCos boxST20TaylorInput (fun _ => x)
    (by intro i; simpa [boxST20TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST20TaylorInput,boxST20TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST20TaylorSin-
      ((-8334952276407 / 20000000000000) : ℝ)| ≤ (1031087397 / 50000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST20TaylorInput,boxST20TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST20TaylorCos-
      ((90902223645797 / 100000000000000) : ℝ)| ≤ (171966349 / 20000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST20TaylorInput,boxST20TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST20TaylorSin = sinTaylor x := by
    norm_num [boxST20TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST20TaylorCos = cosTaylor x := by
    norm_num [boxST20TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((-859728956165578514794647 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST20Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(2281863697423921485205353 / 2000000000000000000000000), (40000000363169886907 / 2000000000000000000000000)⟩, ⟨(90902223645797 / 100000000000000), (34393319 / 4000000000000)⟩, ⟨(8334952276407 / 20000000000000), (257772003 / 12500000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST20J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-28523296217799 / 25000000000000), (2000000019 / 100000000000000)⟩) ⟨(100033040243877 / 50000000000000), (2000000069 / 100000000000000)⟩) (.atom 3) ⟨(41688530824831 / 50000000000000), (991850249 / 20000000000000)⟩) (.abs (.atom 2)) ⟨(174279285295459 / 100000000000000), (290954211 / 5000000000000)⟩)
private def boxST20First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-28523296217799 / 25000000000000), (2000000019 / 100000000000000)⟩) ⟨(100033040243877 / 50000000000000), (2000000069 / 100000000000000)⟩) ⟨(-100033040243877 / 50000000000000), (2000000069 / 100000000000000)⟩) (.atom 2) ⟨(-90932257962179 / 50000000000000), (707659173 / 20000000000000)⟩)
private def boxST20Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(90902223645797 / 50000000000000), (34393319 / 2000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.atom 1) ⟨(-28523296217799 / 25000000000000), (2000000019 / 100000000000000)⟩) ⟨(100033040243877 / 50000000000000), (2000000069 / 100000000000000)⟩) (.atom 3) ⟨(41688530824831 / 50000000000000), (991850249 / 20000000000000)⟩) (.abs (.atom 2)) ⟨(174279285295459 / 100000000000000), (290954211 / 5000000000000)⟩) ⟨(-174279285295459 / 100000000000000), (290954211 / 5000000000000)⟩) ⟨(1505032399227 / 20000000000000), (753875017 / 10000000000000)⟩)

theorem boxST20 {t : ℝ}
    (ht : |t-((363169886907 / 1000000000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((174279285295459 / 100000000000000) : ℝ)| ≤ (290954211 / 5000000000000) ∧
    |J1 t-((-90932257962179 / 50000000000000) : ℝ)| ≤ (707659173 / 20000000000000) ∧
    |J2 t-((1505032399227 / 20000000000000) : ℝ)| ≤ (753875017 / 10000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((1 / 2) : ℝ)*π-((-859728956165578514794647 / 2000000000000000000000000) : ℝ)| ≤ (40000000136830113093 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST20Taylor hred
  have hreduced : t-((1 / 2) : ℝ)*π = t-π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((90902223645797 / 100000000000000) : ℝ)| ≤ (34393319 / 4000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.2
  have hc : |cos t-((8334952276407 / 20000000000000) : ℝ)| ≤ (257772003 / 12500000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((2281863697423921485205353 / 2000000000000000000000000) : ℝ)| ≤ (40000000363169886907 / 2000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST20Input i).center : ℝ)| ≤ ((boxST20Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST20Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST20Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST20Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST20Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST20Input i).center : ℝ)| ≤ ((boxST20Input i).radius : ℝ) := by
    intro i
    simpa [boxST20Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = t := by
    have ht0 : 0 ≤ t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST20J boxST20Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST20Input,boxST20J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST20J = J t := by
    norm_num [boxST20J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eJ] at hJ
  have bJ : |J t-((174279285295459 / 100000000000000) : ℝ)| ≤ (290954211 / 5000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST20Input,boxST20J,Fin.ofNat]
  have hFirst := Certificate.sound boxST20First boxST20Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST20Input,boxST20First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST20First = J1 t := by
    norm_num [boxST20First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf; simp
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((-90932257962179 / 50000000000000) : ℝ)| ≤ (707659173 / 20000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST20Input,boxST20First,Fin.ofNat]
  have hSecond := Certificate.sound boxST20Second boxST20Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST20Input,boxST20Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST20Second = J2 t := by
    norm_num [boxST20Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((1505032399227 / 20000000000000) : ℝ)| ≤ (753875017 / 10000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST20Input,boxST20Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST21TaylorInput : ℕ → RationalBall := fun _ => ⟨(187468595030921485205353 / 2000000000000000000000000), (120000000089509660721 / 6000000000000000000000000)⟩
private def boxST21TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(141 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-250507 / 10000000000000), (1 / 50000000000000)⟩) ⟨(-2201 / 10000000000000), (1 / 10000000000000)⟩) ⟨(137775591 / 50000000000000), (11 / 100000000000000)⟩) ⟨(96841 / 4000000000000), (517 / 50000000000000)⟩) ⟨(-1239928051 / 6250000000000), (207 / 20000000000000)⟩) ⟨(-174306477 / 100000000000000), (74401 / 100000000000000)⟩) ⟨(104144878357 / 12500000000000), (37201 / 50000000000000)⟩) ⟨(1464046793 / 20000000000000), (3124811 / 100000000000000)⟩) ⟨(-8329673216351 / 50000000000000), (781203 / 25000000000000)⟩) ⟨(-73185496201 / 50000000000000), (62496217 / 100000000000000)⟩) ⟨(49926814503799 / 50000000000000), (62496217 / 100000000000000)⟩) ⟨(9359709769397 / 100000000000000), (2002931871 / 100000000000000)⟩)
private def boxST21TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(917 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-5511097 / 20000000000000), (3 / 100000000000000)⟩) ⟨(-121053 / 50000000000000), (13 / 12500000000000)⟩) ⟨(154994789 / 6250000000000), (21 / 20000000000000)⟩) ⟨(21788841 / 100000000000000), (9301 / 100000000000000)⟩) ⟨(-8679193753 / 6250000000000), (4651 / 50000000000000)⟩) ⟨(-1220102801 / 100000000000000), (260401 / 50000000000000)⟩) ⟨(2082723281933 / 50000000000000), (520803 / 100000000000000)⟩) ⟨(9149526811 / 25000000000000), (15624053 / 100000000000000)⟩) ⟨(-12490850473189 / 25000000000000), (15624053 / 100000000000000)⟩) ⟨(-109746092807 / 25000000000000), (37497739 / 20000000000000)⟩) ⟨(24890253907193 / 25000000000000), (37497739 / 20000000000000)⟩)

theorem boxST21Taylor {x : ℝ}
    (hx : |x-((187468595030921485205353 / 2000000000000000000000000) : ℝ)| ≤ (120000000089509660721 / 6000000000000000000000000)) :
    |sin x-((9359709769397 / 100000000000000) : ℝ)| ≤ (2002933101 / 100000000000000) ∧
    |cos x-((24890253907193 / 25000000000000) : ℝ)| ≤ (7499597 / 4000000000000) := by
  have hs := Certificate.sound boxST21TaylorSin boxST21TaylorInput (fun _ => x)
    (by intro i; simpa [boxST21TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST21TaylorInput,boxST21TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST21TaylorCos boxST21TaylorInput (fun _ => x)
    (by intro i; simpa [boxST21TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST21TaylorInput,boxST21TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST21TaylorSin-
      ((9359709769397 / 100000000000000) : ℝ)| ≤ (2002931871 / 100000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST21TaylorInput,boxST21TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST21TaylorCos-
      ((24890253907193 / 25000000000000) : ℝ)| ≤ (37497739 / 20000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST21TaylorInput,boxST21TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST21TaylorSin = sinTaylor x := by
    norm_num [boxST21TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST21TaylorCos = cosTaylor x := by
    norm_num [boxST21TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((187468595030921485205353 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST21Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(-2954124058558578514794647 / 2000000000000000000000000), (120000001410490339279 / 6000000000000000000000000)⟩, ⟨(-24890253907193 / 25000000000000), (7499597 / 4000000000000)⟩, ⟨(9359709769397 / 100000000000000), (2002933101 / 100000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST21J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(147706202927929 / 100000000000000), (250000003 / 12500000000000)⟩) ⟨(-147706202927929 / 100000000000000), (250000003 / 12500000000000)⟩) ⟨(166453062431021 / 100000000000000), (1000000037 / 50000000000000)⟩) (.atom 3) ⟨(15579523545817 / 100000000000000), (3521177747 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(115140539174589 / 100000000000000), (463583459 / 12500000000000)⟩)
private def boxST21First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(147706202927929 / 100000000000000), (250000003 / 12500000000000)⟩) ⟨(-147706202927929 / 100000000000000), (250000003 / 12500000000000)⟩) ⟨(166453062431021 / 100000000000000), (1000000037 / 50000000000000)⟩) ⟨(-166453062431021 / 100000000000000), (1000000037 / 50000000000000)⟩) (.atom 2) ⟨(82861179750759 / 50000000000000), (2303306859 / 100000000000000)⟩)
private def boxST21Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(24890253907193 / 12500000000000), (7499597 / 2000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(147706202927929 / 100000000000000), (250000003 / 12500000000000)⟩) ⟨(-147706202927929 / 100000000000000), (250000003 / 12500000000000)⟩) ⟨(166453062431021 / 100000000000000), (1000000037 / 50000000000000)⟩) (.atom 3) ⟨(15579523545817 / 100000000000000), (3521177747 / 100000000000000)⟩) (.abs (.atom 2)) ⟨(115140539174589 / 100000000000000), (463583459 / 12500000000000)⟩) ⟨(-115140539174589 / 100000000000000), (463583459 / 12500000000000)⟩) ⟨(16796298416591 / 20000000000000), (2041823761 / 50000000000000)⟩)

theorem boxST21 {t : ℝ}
    (ht : |t-((-1410490339279 / 3000000000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((115140539174589 / 100000000000000) : ℝ)| ≤ (463583459 / 12500000000000) ∧
    |J1 t-((82861179750759 / 50000000000000) : ℝ)| ≤ (2303306859 / 100000000000000) ∧
    |J2 t-((16796298416591 / 20000000000000) : ℝ)| ≤ (2041823761 / 50000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((-1 / 2) : ℝ)*π-((187468595030921485205353 / 2000000000000000000000000) : ℝ)| ≤ (120000000089509660721 / 6000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST21Taylor hred
  have hreduced : t-((-1 / 2) : ℝ)*π = t+π/2 := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-24890253907193 / 25000000000000) : ℝ)| ≤ (7499597 / 4000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hc : |cos t-((9359709769397 / 100000000000000) : ℝ)| ≤ (2002933101 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using htrig.1
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((-2954124058558578514794647 / 2000000000000000000000000) : ℝ)| ≤ (120000001410490339279 / 6000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST21Input i).center : ℝ)| ≤ ((boxST21Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST21Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST21Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST21Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST21Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST21Input i).center : ℝ)| ≤ ((boxST21Input i).radius : ℝ) := by
    intro i
    simpa [boxST21Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = -t := by
    have ht0 : 0 ≤ -t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : -t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (-t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST21J boxST21Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST21Input,boxST21J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST21J = J t := by
    norm_num [boxST21J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eJ] at hJ
  have bJ : |J t-((115140539174589 / 100000000000000) : ℝ)| ≤ (463583459 / 12500000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST21Input,boxST21J,Fin.ofNat]
  have hFirst := Certificate.sound boxST21First boxST21Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST21Input,boxST21First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST21First = J1 t := by
    norm_num [boxST21First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((82861179750759 / 50000000000000) : ℝ)| ≤ (2303306859 / 100000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST21Input,boxST21First,Fin.ofNat]
  have hSecond := Certificate.sound boxST21Second boxST21Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST21Input,boxST21Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST21Second = J2 t := by
    norm_num [boxST21Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((16796298416591 / 20000000000000) : ℝ)| ≤ (2041823761 / 50000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST21Input,boxST21Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

private def boxST22TaylorInput : ℕ → RationalBall := fun _ => ⟨(187468595030921485205353 / 2000000000000000000000000), (120000000089509660721 / 6000000000000000000000000)⟩
private def boxST22TaylorSin : Certificate := (.mul (.atom 0) (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 6)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (1 / 120)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 5040)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (1 / 362880)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 39916800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.const (1 / 6227020800)) ⟨(141 / 100000000000000), (1 / 100000000000000)⟩) ⟨(-250507 / 10000000000000), (1 / 50000000000000)⟩) ⟨(-2201 / 10000000000000), (1 / 10000000000000)⟩) ⟨(137775591 / 50000000000000), (11 / 100000000000000)⟩) ⟨(96841 / 4000000000000), (517 / 50000000000000)⟩) ⟨(-1239928051 / 6250000000000), (207 / 20000000000000)⟩) ⟨(-174306477 / 100000000000000), (74401 / 100000000000000)⟩) ⟨(104144878357 / 12500000000000), (37201 / 50000000000000)⟩) ⟨(1464046793 / 20000000000000), (3124811 / 100000000000000)⟩) ⟨(-8329673216351 / 50000000000000), (781203 / 25000000000000)⟩) ⟨(-73185496201 / 50000000000000), (62496217 / 100000000000000)⟩) ⟨(49926814503799 / 50000000000000), (62496217 / 100000000000000)⟩) ⟨(9359709769397 / 100000000000000), (2002931871 / 100000000000000)⟩)
private def boxST22TaylorCos : Certificate := (.add (.const 1) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 2)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (1 / 24)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 720)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (1 / 40320)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.add (.const (-1 / 3628800)) (.mul (.mul (.atom 0) (.atom 0) ⟨(54913240817 / 6250000000000), (374977191 / 100000000000000)⟩) (.const (1 / 479001600)) ⟨(917 / 50000000000000), (1 / 50000000000000)⟩) ⟨(-5511097 / 20000000000000), (3 / 100000000000000)⟩) ⟨(-121053 / 50000000000000), (13 / 12500000000000)⟩) ⟨(154994789 / 6250000000000), (21 / 20000000000000)⟩) ⟨(21788841 / 100000000000000), (9301 / 100000000000000)⟩) ⟨(-8679193753 / 6250000000000), (4651 / 50000000000000)⟩) ⟨(-1220102801 / 100000000000000), (260401 / 50000000000000)⟩) ⟨(2082723281933 / 50000000000000), (520803 / 100000000000000)⟩) ⟨(9149526811 / 25000000000000), (15624053 / 100000000000000)⟩) ⟨(-12490850473189 / 25000000000000), (15624053 / 100000000000000)⟩) ⟨(-109746092807 / 25000000000000), (37497739 / 20000000000000)⟩) ⟨(24890253907193 / 25000000000000), (37497739 / 20000000000000)⟩)

theorem boxST22Taylor {x : ℝ}
    (hx : |x-((187468595030921485205353 / 2000000000000000000000000) : ℝ)| ≤ (120000000089509660721 / 6000000000000000000000000)) :
    |sin x-((9359709769397 / 100000000000000) : ℝ)| ≤ (2002933101 / 100000000000000) ∧
    |cos x-((24890253907193 / 25000000000000) : ℝ)| ≤ (7499597 / 4000000000000) := by
  have hs := Certificate.sound boxST22TaylorSin boxST22TaylorInput (fun _ => x)
    (by intro i; simpa [boxST22TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST22TaylorInput,boxST22TaylorSin,abs_of_nonneg])
  have hc := Certificate.sound boxST22TaylorCos boxST22TaylorInput (fun _ => x)
    (by intro i; simpa [boxST22TaylorInput] using hx)
    (by norm_num [Certificate.check,Certificate.ball,boxST22TaylorInput,boxST22TaylorCos,abs_of_nonneg])
  have hs' : |Certificate.eval (fun _ => x) boxST22TaylorSin-
      ((9359709769397 / 100000000000000) : ℝ)| ≤ (2002931871 / 100000000000000) := by
    convert hs using 1 <;> norm_num [Certificate.ball,boxST22TaylorInput,boxST22TaylorSin]
  have hc' : |Certificate.eval (fun _ => x) boxST22TaylorCos-
      ((24890253907193 / 25000000000000) : ℝ)| ≤ (37497739 / 20000000000000) := by
    convert hc using 1 <;> norm_num [Certificate.ball,boxST22TaylorInput,boxST22TaylorCos]
  have hsin : Certificate.eval (fun _ => x) boxST22TaylorSin = sinTaylor x := by
    norm_num [boxST22TaylorSin,Certificate.eval,sinTaylor]; ring_nf
  have hcos : Certificate.eval (fun _ => x) boxST22TaylorCos = cosTaylor x := by
    norm_num [boxST22TaylorCos,Certificate.eval,cosTaylor]; ring_nf
  rw [hsin] at hs'
  rw [hcos] at hc'
  have hxabs : |x| ≤ 1 := by
    have ht := abs_sub_le x ((187468595030921485205353 / 2000000000000000000000000) : ℝ) 0
    norm_num [abs_of_nonneg] at ht hx
    linarith only [ht,hx]
  constructor
  · exact (bound_sin hxabs hs').trans (by norm_num)
  · exact (bound_cos hxabs hc').trans (by norm_num)

private def boxST22Input : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(-6095716712148078514794647 / 2000000000000000000000000), (120000002910490339279 / 6000000000000000000000000)⟩, ⟨(-9359709769397 / 100000000000000), (2002933101 / 100000000000000)⟩, ⟨(-24890253907193 / 25000000000000), (7499597 / 4000000000000)⟩] : Fin 4 → RationalBall) (Fin.ofNat i)
private def boxST22J : Certificate := (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(76196458901851 / 25000000000000), (2000000049 / 100000000000000)⟩) ⟨(-76196458901851 / 25000000000000), (2000000049 / 100000000000000)⟩) ⟨(4686714875773 / 50000000000000), (2000000099 / 100000000000000)⟩) (.atom 3) ⟨(-9332281859889 / 100000000000000), (1004399199 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(6856977377 / 25000000000000), (4011731499 / 100000000000000)⟩)
private def boxST22First : Certificate := (.mul (.mul (.const (-1)) (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(76196458901851 / 25000000000000), (2000000049 / 100000000000000)⟩) ⟨(-76196458901851 / 25000000000000), (2000000049 / 100000000000000)⟩) ⟨(4686714875773 / 50000000000000), (2000000099 / 100000000000000)⟩) ⟨(-4686714875773 / 50000000000000), (2000000099 / 100000000000000)⟩) (.atom 2) ⟨(877325820183 / 100000000000000), (374977791 / 100000000000000)⟩)
private def boxST22Second : Certificate := (.add (.mul (.abs (.atom 2)) (.const 2) ⟨(9359709769397 / 50000000000000), (2002933101 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.mul (.add (.atom 0) (.mul (.const (-1)) (.mul (.const (-1)) (.atom 1) ⟨(76196458901851 / 25000000000000), (2000000049 / 100000000000000)⟩) ⟨(-76196458901851 / 25000000000000), (2000000049 / 100000000000000)⟩) ⟨(4686714875773 / 50000000000000), (2000000099 / 100000000000000)⟩) (.atom 3) ⟨(-9332281859889 / 100000000000000), (1004399199 / 50000000000000)⟩) (.abs (.atom 2)) ⟨(6856977377 / 25000000000000), (4011731499 / 100000000000000)⟩) ⟨(-6856977377 / 25000000000000), (4011731499 / 100000000000000)⟩) ⟨(9345995814643 / 50000000000000), (8017597701 / 100000000000000)⟩)

theorem boxST22 {t : ℝ}
    (ht : |t-((-2910490339279 / 3000000000000) : ℝ)*π| ≤ (1 / 50000)) :
    |J t-((6856977377 / 25000000000000) : ℝ)| ≤ (4011731499 / 100000000000000) ∧
    |J1 t-((877325820183 / 100000000000000) : ℝ)| ≤ (374977791 / 100000000000000) ∧
    |J2 t-((9345995814643 / 50000000000000) : ℝ)| ≤ (8017597701 / 100000000000000) := by
  have hp0 := seed_pi_lower
  have hp1 := seed_pi_upper
  have hred : |t-((-1) : ℝ)*π-((187468595030921485205353 / 2000000000000000000000000) : ℝ)| ≤ (120000000089509660721 / 6000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have htrig := boxST22Taylor hred
  have hreduced : t-((-1) : ℝ)*π = t+π := by ring
  rw [hreduced] at htrig
  try simp only [sin_add_pi,cos_add_pi,sin_add_pi_div_two,cos_add_pi_div_two,
    sin_sub_pi_div_two,cos_sub_pi_div_two,sin_sub_pi,cos_sub_pi,
    sin_sub_two_pi,cos_sub_two_pi,neg_neg] at htrig

  have hs : |sin t-((-9359709769397 / 100000000000000) : ℝ)| ≤ (2002933101 / 100000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.1
  have hc : |cos t-((-24890253907193 / 25000000000000) : ℝ)| ≤ (7499597 / 4000000000000) := by
    simpa only [neg_neg,neg_div] using bound_neg htrig.2
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [hp0,hp1]
  have ht' : |t-((-6095716712148078514794647 / 2000000000000000000000000) : ℝ)| ≤ (120000002910490339279 / 6000000000000000000000000) := by
    rw [abs_le] at ht ⊢
    constructor <;> nlinarith only [ht.1,ht.2,hp0,hp1]
  have hin4 : ∀ i : Fin 4, |(![π,t,sin t,cos t] : Fin 4 → ℝ) i-
      ((boxST22Input i).center : ℝ)| ≤ ((boxST22Input i).radius : ℝ) := by
    intro i
    fin_cases i
    · convert hpi using 1 <;> norm_num [boxST22Input,Fin.ofNat]
    · convert ht' using 1 <;> norm_num [boxST22Input,Fin.ofNat]
    · convert hs using 1 <;> norm_num [boxST22Input,Fin.ofNat]
    · convert hc using 1 <;> norm_num [boxST22Input,Fin.ofNat]
  have hin : ∀ i : ℕ, |(![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)-
      ((boxST22Input i).center : ℝ)| ≤ ((boxST22Input i).radius : ℝ) := by
    intro i
    simpa [boxST22Input,Fin.ofNat,Nat.mod_mod] using hin4 (Fin.ofNat i)
  have ha : arccos (cos t) = -t := by
    have ht0 : 0 ≤ -t := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have htpi : -t ≤ π := by
      rw [abs_le] at ht
      nlinarith only [ht.1,ht.2,hp0,hp1]
    have heq : cos (-t) = cos t := by simp
    rw [← heq]
    exact arccos_cos ht0 htpi
  have hJ := Certificate.sound boxST22J boxST22Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST22Input,boxST22J,Fin.ofNat,abs_of_nonneg])
  have eJ : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST22J = J t := by
    norm_num [boxST22J,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eJ] at hJ
  have bJ : |J t-((6856977377 / 25000000000000) : ℝ)| ≤ (4011731499 / 100000000000000) := by
    convert hJ using 1 <;> norm_num [Certificate.ball,boxST22Input,boxST22J,Fin.ofNat]
  have hFirst := Certificate.sound boxST22First boxST22Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST22Input,boxST22First,Fin.ofNat,abs_of_nonneg])
  have eFirst : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST22First = J1 t := by
    norm_num [boxST22First,Certificate.eval,Fin.ofNat,J,J1,J2,ha]
  rw [eFirst] at hFirst
  have bFirst : |J1 t-((877325820183 / 100000000000000) : ℝ)| ≤ (374977791 / 100000000000000) := by
    convert hFirst using 1 <;> norm_num [Certificate.ball,boxST22Input,boxST22First,Fin.ofNat]
  have hSecond := Certificate.sound boxST22Second boxST22Input
    (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) hin
    (by norm_num [Certificate.check,Certificate.ball,boxST22Input,boxST22Second,Fin.ofNat,abs_of_nonneg])
  have eSecond : Certificate.eval
      (fun i => (![π,t,sin t,cos t] : Fin 4 → ℝ) (Fin.ofNat i)) boxST22Second = J2 t := by
    norm_num [boxST22Second,Certificate.eval,Fin.ofNat,J,J1,J2,ha]; ring_nf
  rw [eSecond] at hSecond
  have bSecond : |J2 t-((9345995814643 / 50000000000000) : ℝ)| ≤ (8017597701 / 100000000000000) := by
    convert hSecond using 1 <;> norm_num [Certificate.ball,boxST22Input,boxST22Second,Fin.ofNat]

  exact ⟨bJ,bFirst,bSecond⟩

end PaperLeanFormalization.SeedNumerics


/-! Fresh numerical certificate component: SeedCenterModel. -/

/-! Generated exact certificate data. Do not edit emitted source.
Producer: the certificate generator of this development, part: center-model
Schema SHA256: 52d78277f3f1ad2146ecf733e1e7238c78f6c1192abbdf0157de3ea8fb3d301a
A generator run is not proof: compile this file and audit its declarations. -/

open Real
noncomputable section

namespace PaperLeanFormalization.SeedNumerics

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

private def centerInput : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(1000437388123 / 1000000000000), 0⟩, ⟨(695398940163 / 500000000000), 0⟩, ⟨(604352649479 / 1000000000000), 0⟩, ⟨(20742873676633 / 100000000000000), (1193 / 50000000000000)⟩, ⟨(-67309757799411 / 100000000000000), (577 / 50000000000000)⟩, ⟨(132910161976553 / 100000000000000), (2433 / 50000000000000)⟩, ⟨(61723171351237 / 100000000000000), (2899 / 100000000000000)⟩, ⟨(7838205726517 / 6250000000000), (909 / 50000000000000)⟩, ⟨(131049039640719 / 100000000000000), (5363 / 100000000000000)⟩, ⟨(27203161727173 / 100000000000000), (621 / 25000000000000)⟩, ⟨(-15847207705777 / 20000000000000), (1263 / 100000000000000)⟩, ⟨(137130451754161 / 100000000000000), (2479 / 50000000000000)⟩, ⟨(50247915424861 / 20000000000000), (2229 / 50000000000000)⟩, ⟨(39308433419249 / 25000000000000), (799 / 25000000000000)⟩, ⟨(-122468521585913 / 100000000000000), (1737 / 25000000000000)⟩, ⟨(36188039279 / 20000000000000), (387 / 25000000000000)⟩, ⟨(-1539553543327 / 50000000000000), (47 / 20000000000000)⟩, ⟨(34823335780317 / 100000000000000), (251 / 6250000000000)⟩, ⟨(129027864451303 / 100000000000000), (17 / 500000000000)⟩, ⟨(-85988124347567 / 50000000000000), (2223 / 100000000000000)⟩, ⟨(13577012430333 / 20000000000000), (2931 / 50000000000000)⟩, ⟨(36603993937 / 20000000000000), (1653 / 100000000000000)⟩, ⟨(1551291503829 / 50000000000000), (51 / 20000000000000)⟩, ⟨(34953747504807 / 100000000000000), (4121 / 100000000000000)⟩, ⟨(125566874725709 / 50000000000000), (4321 / 100000000000000)⟩, ⟨(-157316070468731 / 100000000000000), (77 / 2500000000000)⟩, ⟨(-30564938023977 / 25000000000000), (6811 / 100000000000000)⟩, ⟨(222807520152001 / 100000000000000), (411 / 10000000000000)⟩, ⟨(2713533998909 / 1562500000000), (1433 / 50000000000000)⟩, ⟨(-69864743906711 / 100000000000000), (659 / 10000000000000)⟩, ⟨(174279285295459 / 100000000000000), (3741 / 100000000000000)⟩, ⟨(-90932257962179 / 50000000000000), (633 / 25000000000000)⟩, ⟨(1505032399227 / 20000000000000), (6209 / 100000000000000)⟩, ⟨(115140539174589 / 100000000000000), (3289 / 100000000000000)⟩, ⟨(82861179750759 / 50000000000000), (531 / 25000000000000)⟩, ⟨(16796298416591 / 20000000000000), (5751 / 100000000000000)⟩, ⟨(6856977377 / 25000000000000), (1447 / 100000000000000)⟩, ⟨(877325820183 / 100000000000000), (1 / 800000000000)⟩, ⟨(9345995814643 / 50000000000000), (3911 / 100000000000000)⟩] : Fin 40 → RationalBall) (Fin.ofNat i)
private def centerValues (c θ : Fin 3 → ℝ) : ℕ → ℝ :=
  fun i => (![π, c 0, c 1, c 2, J (θ 0-θ 1), J1 (θ 0-θ 1), J2 (θ 0-θ 1), J (θ 0-θ 2), J1 (θ 0-θ 2), J2 (θ 0-θ 2), J (θ 1-θ 2), J1 (θ 1-θ 2), J2 (θ 1-θ 2), J (θ 0-(0 : ℝ)*π), J1 (θ 0-(0 : ℝ)*π), J2 (θ 0-(0 : ℝ)*π), J (θ 0-((5 / 6) : ℝ)*π), J1 (θ 0-((5 / 6) : ℝ)*π), J2 (θ 0-((5 / 6) : ℝ)*π), J (θ 0-((4 / 3) : ℝ)*π), J1 (θ 0-((4 / 3) : ℝ)*π), J2 (θ 0-((4 / 3) : ℝ)*π), J (θ 1-(0 : ℝ)*π), J1 (θ 1-(0 : ℝ)*π), J2 (θ 1-(0 : ℝ)*π), J (θ 1-((5 / 6) : ℝ)*π), J1 (θ 1-((5 / 6) : ℝ)*π), J2 (θ 1-((5 / 6) : ℝ)*π), J (θ 1-((4 / 3) : ℝ)*π), J1 (θ 1-((4 / 3) : ℝ)*π), J2 (θ 1-((4 / 3) : ℝ)*π), J (θ 2-(0 : ℝ)*π), J1 (θ 2-(0 : ℝ)*π), J2 (θ 2-(0 : ℝ)*π), J (θ 2-((5 / 6) : ℝ)*π), J1 (θ 2-((5 / 6) : ℝ)*π), J2 (θ 2-((5 / 6) : ℝ)*π), J (θ 2-((4 / 3) : ℝ)*π), J1 (θ 2-((4 / 3) : ℝ)*π), J2 (θ 2-((4 / 3) : ℝ)*π)] : Fin 40 → ℝ) (Fin.ofNat i)

theorem center_inputs {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ (0 : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ (0 : ℝ)) :
    ∀ i, |centerValues c θ i-((centerInput i).center : ℝ)| ≤
      ((centerInput i).radius : ℝ) := by
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤
      (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [seed_pi_lower,seed_pi_upper]
  have centerSS01Arg : |(θ 0-θ 1)-((90140029201 / 125000000000) : ℝ)*π| ≤
      0 := by
    have h := bound_sub (ht 0) (ht 1)
    convert h using 1 <;> norm_num [seedAngle]; congr 1; ring
  have hcenterSS01 := centerSS01 centerSS01Arg
  have centerSS02Arg : |(θ 0-θ 2)-((1414163989277 / 1000000000000) : ℝ)*π| ≤
      0 := by
    have h := bound_sub (ht 0) (ht 2)
    convert h using 1 <;> norm_num [seedAngle]; congr 1; ring
  have hcenterSS02 := centerSS02 centerSS02Arg
  have centerSS12Arg : |(θ 1-θ 2)-((693043755669 / 1000000000000) : ℝ)*π| ≤
      0 := by
    have h := bound_sub (ht 1) (ht 2)
    convert h using 1 <;> norm_num [seedAngle]; congr 1; ring
  have hcenterSS12 := centerSS12 centerSS12Arg
  have centerST00Arg : |(θ 0-(0 : ℝ)*π)-((222166734523 / 125000000000) : ℝ)*π| ≤
      0 := by
    have h := ht 0
    convert h using 1; norm_num [seedAngle]
  have hcenterST00 := centerST00 centerST00Arg
  have centerST01Arg : |(θ 0-((5 / 6) : ℝ)*π)-((354000203569 / 375000000000) : ℝ)*π| ≤
      0 := by
    have h := ht 0
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hcenterST01 := centerST01 centerST01Arg
  have centerST02Arg : |(θ 0-((4 / 3) : ℝ)*π)-((166500203569 / 375000000000) : ℝ)*π| ≤
      0 := by
    have h := ht 0
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hcenterST02 := centerST02 centerST02Arg
  have centerST10Arg : |(θ 1-(0 : ℝ)*π)-((66013352661 / 62500000000) : ℝ)*π| ≤
      0 := by
    have h := ht 1
    convert h using 1; norm_num [seedAngle]
  have hcenterST10 := centerST10 centerST10Arg
  have centerST11Arg : |(θ 1-((5 / 6) : ℝ)*π)-((41790057983 / 187500000000) : ℝ)*π| ≤
      0 := by
    have h := ht 1
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hcenterST11 := centerST11 centerST11Arg
  have centerST12Arg : |(θ 1-((4 / 3) : ℝ)*π)-((-51959942017 / 187500000000) : ℝ)*π| ≤
      0 := by
    have h := ht 1
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hcenterST12 := centerST12 centerST12Arg
  have centerST20Arg : |(θ 2-(0 : ℝ)*π)-((363169886907 / 1000000000000) : ℝ)*π| ≤
      0 := by
    have h := ht 2
    convert h using 1; norm_num [seedAngle]
  have hcenterST20 := centerST20 centerST20Arg
  have centerST21Arg : |(θ 2-((5 / 6) : ℝ)*π)-((-1410490339279 / 3000000000000) : ℝ)*π| ≤
      0 := by
    have h := ht 2
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hcenterST21 := centerST21 centerST21Arg
  have centerST22Arg : |(θ 2-((4 / 3) : ℝ)*π)-((-2910490339279 / 3000000000000) : ℝ)*π| ≤
      0 := by
    have h := ht 2
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hcenterST22 := centerST22 centerST22Arg
  have hfin : ∀ i : Fin 40, |centerValues c θ i-
      ((centerInput i).center : ℝ)| ≤ ((centerInput i).radius : ℝ) := by
    intro i
    fin_cases i
    · change |π-(((6283185307179 / 2000000000000) : ℚ) : ℝ)| ≤
        (((1 / 2000000000000) : ℚ) : ℝ)
      convert hpi using 1 <;> norm_num [seedMass]
    · change |c 0-(((1000437388123 / 1000000000000) : ℚ) : ℝ)| ≤
        ((0 : ℚ) : ℝ)
      convert hc 0 using 1 <;> norm_num [seedMass]
    · change |c 1-(((695398940163 / 500000000000) : ℚ) : ℝ)| ≤
        ((0 : ℚ) : ℝ)
      convert hc 1 using 1 <;> norm_num [seedMass]
    · change |c 2-(((604352649479 / 1000000000000) : ℚ) : ℝ)| ≤
        ((0 : ℚ) : ℝ)
      convert hc 2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-θ 1)-(((20742873676633 / 100000000000000) : ℚ) : ℝ)| ≤
        (((1193 / 50000000000000) : ℚ) : ℝ)
      convert hcenterSS01.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-θ 1)-(((-67309757799411 / 100000000000000) : ℚ) : ℝ)| ≤
        (((577 / 50000000000000) : ℚ) : ℝ)
      convert hcenterSS01.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-θ 1)-(((132910161976553 / 100000000000000) : ℚ) : ℝ)| ≤
        (((2433 / 50000000000000) : ℚ) : ℝ)
      convert hcenterSS01.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-θ 2)-(((61723171351237 / 100000000000000) : ℚ) : ℝ)| ≤
        (((2899 / 100000000000000) : ℚ) : ℝ)
      convert hcenterSS02.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-θ 2)-(((7838205726517 / 6250000000000) : ℚ) : ℝ)| ≤
        (((909 / 50000000000000) : ℚ) : ℝ)
      convert hcenterSS02.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-θ 2)-(((131049039640719 / 100000000000000) : ℚ) : ℝ)| ≤
        (((5363 / 100000000000000) : ℚ) : ℝ)
      convert hcenterSS02.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 1-θ 2)-(((27203161727173 / 100000000000000) : ℚ) : ℝ)| ≤
        (((621 / 25000000000000) : ℚ) : ℝ)
      convert hcenterSS12.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 1-θ 2)-(((-15847207705777 / 20000000000000) : ℚ) : ℝ)| ≤
        (((1263 / 100000000000000) : ℚ) : ℝ)
      convert hcenterSS12.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 1-θ 2)-(((137130451754161 / 100000000000000) : ℚ) : ℝ)| ≤
        (((2479 / 50000000000000) : ℚ) : ℝ)
      convert hcenterSS12.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-(0 : ℝ)*π)-(((50247915424861 / 20000000000000) : ℚ) : ℝ)| ≤
        (((2229 / 50000000000000) : ℚ) : ℝ)
      convert hcenterST00.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-(0 : ℝ)*π)-(((39308433419249 / 25000000000000) : ℚ) : ℝ)| ≤
        (((799 / 25000000000000) : ℚ) : ℝ)
      convert hcenterST00.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-(0 : ℝ)*π)-(((-122468521585913 / 100000000000000) : ℚ) : ℝ)| ≤
        (((1737 / 25000000000000) : ℚ) : ℝ)
      convert hcenterST00.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-((5 / 6) : ℝ)*π)-(((36188039279 / 20000000000000) : ℚ) : ℝ)| ≤
        (((387 / 25000000000000) : ℚ) : ℝ)
      convert hcenterST01.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-((5 / 6) : ℝ)*π)-(((-1539553543327 / 50000000000000) : ℚ) : ℝ)| ≤
        (((47 / 20000000000000) : ℚ) : ℝ)
      convert hcenterST01.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-((5 / 6) : ℝ)*π)-(((34823335780317 / 100000000000000) : ℚ) : ℝ)| ≤
        (((251 / 6250000000000) : ℚ) : ℝ)
      convert hcenterST01.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-((4 / 3) : ℝ)*π)-(((129027864451303 / 100000000000000) : ℚ) : ℝ)| ≤
        (((17 / 500000000000) : ℚ) : ℝ)
      convert hcenterST02.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-((4 / 3) : ℝ)*π)-(((-85988124347567 / 50000000000000) : ℚ) : ℝ)| ≤
        (((2223 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST02.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-((4 / 3) : ℝ)*π)-(((13577012430333 / 20000000000000) : ℚ) : ℝ)| ≤
        (((2931 / 50000000000000) : ℚ) : ℝ)
      convert hcenterST02.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 1-(0 : ℝ)*π)-(((36603993937 / 20000000000000) : ℚ) : ℝ)| ≤
        (((1653 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST10.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 1-(0 : ℝ)*π)-(((1551291503829 / 50000000000000) : ℚ) : ℝ)| ≤
        (((51 / 20000000000000) : ℚ) : ℝ)
      convert hcenterST10.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 1-(0 : ℝ)*π)-(((34953747504807 / 100000000000000) : ℚ) : ℝ)| ≤
        (((4121 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST10.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 1-((5 / 6) : ℝ)*π)-(((125566874725709 / 50000000000000) : ℚ) : ℝ)| ≤
        (((4321 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST11.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 1-((5 / 6) : ℝ)*π)-(((-157316070468731 / 100000000000000) : ℚ) : ℝ)| ≤
        (((77 / 2500000000000) : ℚ) : ℝ)
      convert hcenterST11.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 1-((5 / 6) : ℝ)*π)-(((-30564938023977 / 25000000000000) : ℚ) : ℝ)| ≤
        (((6811 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST11.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 1-((4 / 3) : ℝ)*π)-(((222807520152001 / 100000000000000) : ℚ) : ℝ)| ≤
        (((411 / 10000000000000) : ℚ) : ℝ)
      convert hcenterST12.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 1-((4 / 3) : ℝ)*π)-(((2713533998909 / 1562500000000) : ℚ) : ℝ)| ≤
        (((1433 / 50000000000000) : ℚ) : ℝ)
      convert hcenterST12.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 1-((4 / 3) : ℝ)*π)-(((-69864743906711 / 100000000000000) : ℚ) : ℝ)| ≤
        (((659 / 10000000000000) : ℚ) : ℝ)
      convert hcenterST12.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 2-(0 : ℝ)*π)-(((174279285295459 / 100000000000000) : ℚ) : ℝ)| ≤
        (((3741 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST20.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 2-(0 : ℝ)*π)-(((-90932257962179 / 50000000000000) : ℚ) : ℝ)| ≤
        (((633 / 25000000000000) : ℚ) : ℝ)
      convert hcenterST20.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 2-(0 : ℝ)*π)-(((1505032399227 / 20000000000000) : ℚ) : ℝ)| ≤
        (((6209 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST20.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 2-((5 / 6) : ℝ)*π)-(((115140539174589 / 100000000000000) : ℚ) : ℝ)| ≤
        (((3289 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST21.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 2-((5 / 6) : ℝ)*π)-(((82861179750759 / 50000000000000) : ℚ) : ℝ)| ≤
        (((531 / 25000000000000) : ℚ) : ℝ)
      convert hcenterST21.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 2-((5 / 6) : ℝ)*π)-(((16796298416591 / 20000000000000) : ℚ) : ℝ)| ≤
        (((5751 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST21.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 2-((4 / 3) : ℝ)*π)-(((6856977377 / 25000000000000) : ℚ) : ℝ)| ≤
        (((1447 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST22.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 2-((4 / 3) : ℝ)*π)-(((877325820183 / 100000000000000) : ℚ) : ℝ)| ≤
        (((1 / 800000000000) : ℚ) : ℝ)
      convert hcenterST22.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 2-((4 / 3) : ℝ)*π)-(((9345995814643 / 50000000000000) : ℚ) : ℝ)| ≤
        (((3911 / 100000000000000) : ℚ) : ℝ)
      convert hcenterST22.2.2 using 1 <;> norm_num [seedMass]
  intro i
  simpa [centerInput,centerValues,Fin.ofNat,Nat.mod_mod] using hfin (Fin.ofNat i)

private def centerG0Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.atom 0) ⟨(78574168722587 / 25000000000000), (51 / 100000000000000)⟩) ⟨(78574168722587 / 25000000000000), (51 / 100000000000000)⟩) (.mul (.atom 2) (.atom 4) ⟨(28849144741331 / 100000000000000), (3319 / 100000000000000)⟩) ⟨(343145819631679 / 100000000000000), (337 / 10000000000000)⟩) (.mul (.atom 3) (.atom 7) ⟨(18651281070183 / 50000000000000), (1753 / 100000000000000)⟩) ⟨(76089676354409 / 20000000000000), (5123 / 100000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 13) ⟨(50247915424861 / 20000000000000), (2229 / 50000000000000)⟩) (.atom 16) ⟨(2514205173207 / 1000000000000), (3003 / 50000000000000)⟩) (.atom 19) ⟨(380448381772003 / 100000000000000), (4703 / 50000000000000)⟩) ⟨(-380448381772003 / 100000000000000), (4703 / 50000000000000)⟩) ⟨(21 / 50000000000000), (14529 / 100000000000000)⟩)

theorem centerG0 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ (0 : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ (0 : ℝ)) :
    |gradient c θ 0-((21 / 50000000000000) : ℝ)| ≤ (14529 / 100000000000000) := by
  have hs := Certificate.sound centerG0Expr centerInput (centerValues c θ)
    (center_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,centerInput,centerG0Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (centerValues c θ) centerG0Expr = gradient c θ 0 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [centerG0Expr,Certificate.eval,centerValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,centerInput,centerG0Expr,Fin.ofNat]

private def centerG1Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.atom 4) ⟨(1296996647701 / 6250000000000), (597 / 25000000000000)⟩) ⟨(1296996647701 / 6250000000000), (597 / 25000000000000)⟩) (.mul (.atom 2) (.atom 0) ⟨(436932040346001 / 100000000000000), (7 / 10000000000000)⟩) ⟨(457683986709217 / 100000000000000), (1229 / 50000000000000)⟩) (.mul (.atom 3) (.atom 10) ⟨(16440302864023 / 100000000000000), (751 / 50000000000000)⟩) ⟨(11853107239331 / 2500000000000), (99 / 2500000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 22) ⟨(36603993937 / 20000000000000), (1653 / 100000000000000)⟩) (.atom 25) ⟨(251316769421103 / 100000000000000), (2987 / 50000000000000)⟩) (.atom 28) ⟨(29632768098319 / 6250000000000), (2521 / 25000000000000)⟩) ⟨(-29632768098319 / 6250000000000), (2521 / 25000000000000)⟩) ⟨(17 / 12500000000000), (3511 / 25000000000000)⟩)

theorem centerG1 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ (0 : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ (0 : ℝ)) :
    |gradient c θ 1-((17 / 12500000000000) : ℝ)| ≤ (3511 / 25000000000000) := by
  have hs := Certificate.sound centerG1Expr centerInput (centerValues c θ)
    (center_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,centerInput,centerG1Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (centerValues c θ) centerG1Expr = gradient c θ 1 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [centerG1Expr,Certificate.eval,centerValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,centerInput,centerG1Expr,Fin.ofNat]

private def centerG2Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.atom 7) ⟨(617501683333 / 1000000000000), (2901 / 100000000000000)⟩) ⟨(617501683333 / 1000000000000), (2901 / 100000000000000)⟩) (.mul (.atom 2) (.atom 10) ⟨(18917049834159 / 50000000000000), (27 / 781250000000)⟩) ⟨(49792134000809 / 50000000000000), (6357 / 100000000000000)⟩) (.mul (.atom 3) (.atom 0) ⟨(94931492189029 / 50000000000000), (31 / 100000000000000)⟩) ⟨(72361813094919 / 25000000000000), (1597 / 25000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 31) ⟨(174279285295459 / 100000000000000), (3741 / 100000000000000)⟩) (.atom 34) ⟨(9044369514689 / 3125000000000), (703 / 10000000000000)⟩) (.atom 37) ⟨(72361813094889 / 25000000000000), (8477 / 100000000000000)⟩) ⟨(-72361813094889 / 25000000000000), (8477 / 100000000000000)⟩) ⟨(3 / 2500000000000), (2973 / 20000000000000)⟩)

theorem centerG2 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ (0 : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ (0 : ℝ)) :
    |gradient c θ 2-((3 / 2500000000000) : ℝ)| ≤ (2973 / 20000000000000) := by
  have hs := Certificate.sound centerG2Expr centerInput (centerValues c θ)
    (center_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,centerInput,centerG2Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (centerValues c θ) centerG2Expr = gradient c θ 2 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [centerG2Expr,Certificate.eval,centerValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,centerInput,centerG2Expr,Fin.ofNat]

private def centerG3Expr : Certificate := (.mul (.atom 1) (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.const 0) ⟨0, 0⟩) ⟨0, 0⟩) (.mul (.atom 2) (.atom 5) ⟨(-93614268472677 / 100000000000000), (803 / 50000000000000)⟩) ⟨(-93614268472677 / 100000000000000), (803 / 50000000000000)⟩) (.mul (.atom 3) (.atom 8) ⟨(2368520198991 / 3125000000000), (11 / 1000000000000)⟩) ⟨(-3564324420993 / 20000000000000), (1353 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 14) ⟨(39308433419249 / 25000000000000), (799 / 25000000000000)⟩) (.atom 17) ⟨(77077313295171 / 50000000000000), (3431 / 100000000000000)⟩) (.atom 20) ⟨(-2227702763099 / 12500000000000), (2827 / 50000000000000)⟩) ⟨(2227702763099 / 12500000000000), (2827 / 50000000000000)⟩) ⟨(-173 / 100000000000000), (209 / 2500000000000)⟩) ⟨(-173 / 100000000000000), (2091 / 25000000000000)⟩)

theorem centerG3 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ (0 : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ (0 : ℝ)) :
    |gradient c θ 3-((-173 / 100000000000000) : ℝ)| ≤ (2091 / 25000000000000) := by
  have hs := Certificate.sound centerG3Expr centerInput (centerValues c θ)
    (center_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,centerInput,centerG3Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (centerValues c θ) centerG3Expr = gradient c θ 3 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [centerG3Expr,Certificate.eval,centerValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf; simp
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,centerInput,centerG3Expr,Fin.ofNat]

private def centerG4Expr : Certificate := (.mul (.atom 2) (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.mul (.const (-1)) (.atom 5) ⟨(67309757799411 / 100000000000000), (577 / 50000000000000)⟩) ⟨(33669599144017 / 50000000000000), (231 / 20000000000000)⟩) ⟨(33669599144017 / 50000000000000), (231 / 20000000000000)⟩) (.mul (.atom 2) (.const 0) ⟨0, 0⟩) ⟨(33669599144017 / 50000000000000), (231 / 20000000000000)⟩) (.mul (.atom 3) (.atom 11) ⟨(-2992906863697 / 6250000000000), (191 / 25000000000000)⟩) ⟨(9726344234441 / 50000000000000), (1919 / 100000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 23) ⟨(1551291503829 / 50000000000000), (51 / 20000000000000)⟩) (.atom 26) ⟨(-154213487461073 / 100000000000000), (667 / 20000000000000)⟩) (.atom 29) ⟨(19452688469103 / 100000000000000), (6201 / 100000000000000)⟩) ⟨(-19452688469103 / 100000000000000), (6201 / 100000000000000)⟩) ⟨(-221 / 100000000000000), (203 / 2500000000000)⟩) ⟨(-307 / 100000000000000), (5647 / 50000000000000)⟩)

theorem centerG4 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ (0 : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ (0 : ℝ)) :
    |gradient c θ 4-((-307 / 100000000000000) : ℝ)| ≤ (5647 / 50000000000000) := by
  have hs := Certificate.sound centerG4Expr centerInput (centerValues c θ)
    (center_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,centerInput,centerG4Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (centerValues c θ) centerG4Expr = gradient c θ 4 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [centerG4Expr,Certificate.eval,centerValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf; simp
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,centerInput,centerG4Expr,Fin.ofNat]

private def centerG5Expr : Certificate := (.mul (.atom 3) (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.mul (.const (-1)) (.atom 8) ⟨(-7838205726517 / 6250000000000), (909 / 50000000000000)⟩) ⟨(-125466145033719 / 100000000000000), (91 / 5000000000000)⟩) ⟨(-125466145033719 / 100000000000000), (91 / 5000000000000)⟩) (.mul (.atom 2) (.mul (.const (-1)) (.atom 11) ⟨(15847207705777 / 20000000000000), (1263 / 100000000000000)⟩) ⟨(110201314431403 / 100000000000000), (879 / 50000000000000)⟩) ⟨(-3816207650579 / 25000000000000), (1789 / 50000000000000)⟩) (.mul (.atom 3) (.const 0) ⟨0, 0⟩) ⟨(-3816207650579 / 25000000000000), (1789 / 50000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 32) ⟨(-90932257962179 / 50000000000000), (633 / 25000000000000)⟩) (.atom 35) ⟨(-403553910571 / 2500000000000), (291 / 6250000000000)⟩) (.atom 38) ⟨(-15264830602657 / 100000000000000), (4781 / 100000000000000)⟩) ⟨(15264830602657 / 100000000000000), (4781 / 100000000000000)⟩) ⟨(341 / 100000000000000), (8359 / 100000000000000)⟩) ⟨(103 / 50000000000000), (1263 / 25000000000000)⟩)

theorem centerG5 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ (0 : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ (0 : ℝ)) :
    |gradient c θ 5-((103 / 50000000000000) : ℝ)| ≤ (1263 / 25000000000000) := by
  have hs := Certificate.sound centerG5Expr centerInput (centerValues c θ)
    (center_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,centerInput,centerG5Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (centerValues c θ) centerG5Expr = gradient c θ 5 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [centerG5Expr,Certificate.eval,centerValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf; simp
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,centerInput,centerG5Expr,Fin.ofNat]

end PaperLeanFormalization.SeedNumerics


/-! Fresh numerical certificate component: SeedBoxModel. -/

/-! Generated exact certificate data. Do not edit emitted source.
Producer: the certificate generator of this development, part: box-model
Schema SHA256: 52d78277f3f1ad2146ecf733e1e7238c78f6c1192abbdf0157de3ea8fb3d301a
A generator run is not proof: compile this file and audit its declarations. -/

open Real
noncomputable section

namespace PaperLeanFormalization.SeedNumerics

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

private def boxInput : ℕ → RationalBall :=
  fun i => (![⟨(6283185307179 / 2000000000000), (1 / 2000000000000)⟩, ⟨(1000437388123 / 1000000000000), (1 / 50000)⟩, ⟨(695398940163 / 500000000000), (1 / 50000)⟩, ⟨(604352649479 / 1000000000000), (1 / 50000)⟩, ⟨(20742873676633 / 100000000000000), (9134567399 / 100000000000000)⟩, ⟨(-67309757799411 / 100000000000000), (5509304009 / 100000000000000)⟩, ⟨(132910161976553 / 100000000000000), (14695708757 / 100000000000000)⟩, ⟨(61723171351237 / 100000000000000), (3706202261 / 50000000000000)⟩, ⟨(7838205726517 / 6250000000000), (5259081459 / 100000000000000)⟩, ⟨(131049039640719 / 100000000000000), (956989681 / 10000000000000)⟩, ⟨(27203161727173 / 100000000000000), (4402556489 / 50000000000000)⟩, ⟨(-15847207705777 / 20000000000000), (5627069 / 100000000000)⟩, ⟨(137130451754161 / 100000000000000), (6829418651 / 50000000000000)⟩, ⟨(50247915424861 / 20000000000000), (889550027 / 12500000000000)⟩, ⟨(39308433419249 / 25000000000000), (1316023311 / 20000000000000)⟩, ⟨(-122468521585913 / 100000000000000), (5725365797 / 50000000000000)⟩, ⟨(36188039279 / 20000000000000), (202068943 / 5000000000000)⟩, ⟨(-1539553543327 / 50000000000000), (175939153 / 25000000000000)⟩, ⟨(34823335780317 / 100000000000000), (2015513497 / 25000000000000)⟩, ⟨(129027864451303 / 100000000000000), (421346481 / 10000000000000)⟩, ⟨(-85988124347567 / 50000000000000), (1291884453 / 50000000000000)⟩, ⟨(13577012430333 / 20000000000000), (1229304873 / 25000000000000)⟩, ⟨(36603993937 / 20000000000000), (161667871 / 4000000000000)⟩, ⟨(1551291503829 / 50000000000000), (17661207 / 2500000000000)⟩, ⟨(34953747504807 / 100000000000000), (8062530561 / 100000000000000)⟩, ⟨(125566874725709 / 50000000000000), (1423643473 / 20000000000000)⟩, ⟨(-157316070468731 / 100000000000000), (1316098467 / 20000000000000)⟩, ⟨(-30564938023977 / 25000000000000), (11453207973 / 100000000000000)⟩, ⟨(222807520152001 / 100000000000000), (7612513337 / 100000000000000)⟩, ⟨(2713533998909 / 1562500000000), (4711933411 / 100000000000000)⟩, ⟨(-69864743906711 / 100000000000000), (10415229251 / 100000000000000)⟩, ⟨(174279285295459 / 100000000000000), (290954211 / 5000000000000)⟩, ⟨(-90932257962179 / 50000000000000), (707659173 / 20000000000000)⟩, ⟨(1505032399227 / 20000000000000), (753875017 / 10000000000000)⟩, ⟨(115140539174589 / 100000000000000), (463583459 / 12500000000000)⟩, ⟨(82861179750759 / 50000000000000), (2303306859 / 100000000000000)⟩, ⟨(16796298416591 / 20000000000000), (2041823761 / 50000000000000)⟩, ⟨(6856977377 / 25000000000000), (4011731499 / 100000000000000)⟩, ⟨(877325820183 / 100000000000000), (374977791 / 100000000000000)⟩, ⟨(9345995814643 / 50000000000000), (8017597701 / 100000000000000)⟩] : Fin 40 → RationalBall) (Fin.ofNat i)
private def boxValues (c θ : Fin 3 → ℝ) : ℕ → ℝ :=
  fun i => (![π, c 0, c 1, c 2, J (θ 0-θ 1), J1 (θ 0-θ 1), J2 (θ 0-θ 1), J (θ 0-θ 2), J1 (θ 0-θ 2), J2 (θ 0-θ 2), J (θ 1-θ 2), J1 (θ 1-θ 2), J2 (θ 1-θ 2), J (θ 0-(0 : ℝ)*π), J1 (θ 0-(0 : ℝ)*π), J2 (θ 0-(0 : ℝ)*π), J (θ 0-((5 / 6) : ℝ)*π), J1 (θ 0-((5 / 6) : ℝ)*π), J2 (θ 0-((5 / 6) : ℝ)*π), J (θ 0-((4 / 3) : ℝ)*π), J1 (θ 0-((4 / 3) : ℝ)*π), J2 (θ 0-((4 / 3) : ℝ)*π), J (θ 1-(0 : ℝ)*π), J1 (θ 1-(0 : ℝ)*π), J2 (θ 1-(0 : ℝ)*π), J (θ 1-((5 / 6) : ℝ)*π), J1 (θ 1-((5 / 6) : ℝ)*π), J2 (θ 1-((5 / 6) : ℝ)*π), J (θ 1-((4 / 3) : ℝ)*π), J1 (θ 1-((4 / 3) : ℝ)*π), J2 (θ 1-((4 / 3) : ℝ)*π), J (θ 2-(0 : ℝ)*π), J1 (θ 2-(0 : ℝ)*π), J2 (θ 2-(0 : ℝ)*π), J (θ 2-((5 / 6) : ℝ)*π), J1 (θ 2-((5 / 6) : ℝ)*π), J2 (θ 2-((5 / 6) : ℝ)*π), J (θ 2-((4 / 3) : ℝ)*π), J1 (θ 2-((4 / 3) : ℝ)*π), J2 (θ 2-((4 / 3) : ℝ)*π)] : Fin 40 → ℝ) (Fin.ofNat i)

theorem box_inputs {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    ∀ i, |boxValues c θ i-((boxInput i).center : ℝ)| ≤
      ((boxInput i).radius : ℝ) := by
  have hpi : |π-((6283185307179 / 2000000000000) : ℝ)| ≤
      (1 / 2000000000000) := by
    rw [abs_le]
    constructor <;> linarith only [seed_pi_lower,seed_pi_upper]
  have boxSS01Arg : |(θ 0-θ 1)-((90140029201 / 125000000000) : ℝ)*π| ≤
      (1 / 25000) := by
    have h := bound_sub (ht 0) (ht 1)
    convert h using 1 <;> norm_num [seedAngle]; congr 1; ring
  have hboxSS01 := boxSS01 boxSS01Arg
  have boxSS02Arg : |(θ 0-θ 2)-((1414163989277 / 1000000000000) : ℝ)*π| ≤
      (1 / 25000) := by
    have h := bound_sub (ht 0) (ht 2)
    convert h using 1 <;> norm_num [seedAngle]; congr 1; ring
  have hboxSS02 := boxSS02 boxSS02Arg
  have boxSS12Arg : |(θ 1-θ 2)-((693043755669 / 1000000000000) : ℝ)*π| ≤
      (1 / 25000) := by
    have h := bound_sub (ht 1) (ht 2)
    convert h using 1 <;> norm_num [seedAngle]; congr 1; ring
  have hboxSS12 := boxSS12 boxSS12Arg
  have boxST00Arg : |(θ 0-(0 : ℝ)*π)-((222166734523 / 125000000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 0
    convert h using 1; norm_num [seedAngle]
  have hboxST00 := boxST00 boxST00Arg
  have boxST01Arg : |(θ 0-((5 / 6) : ℝ)*π)-((354000203569 / 375000000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 0
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hboxST01 := boxST01 boxST01Arg
  have boxST02Arg : |(θ 0-((4 / 3) : ℝ)*π)-((166500203569 / 375000000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 0
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hboxST02 := boxST02 boxST02Arg
  have boxST10Arg : |(θ 1-(0 : ℝ)*π)-((66013352661 / 62500000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 1
    convert h using 1; norm_num [seedAngle]
  have hboxST10 := boxST10 boxST10Arg
  have boxST11Arg : |(θ 1-((5 / 6) : ℝ)*π)-((41790057983 / 187500000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 1
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hboxST11 := boxST11 boxST11Arg
  have boxST12Arg : |(θ 1-((4 / 3) : ℝ)*π)-((-51959942017 / 187500000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 1
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hboxST12 := boxST12 boxST12Arg
  have boxST20Arg : |(θ 2-(0 : ℝ)*π)-((363169886907 / 1000000000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 2
    convert h using 1; norm_num [seedAngle]
  have hboxST20 := boxST20 boxST20Arg
  have boxST21Arg : |(θ 2-((5 / 6) : ℝ)*π)-((-1410490339279 / 3000000000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 2
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hboxST21 := boxST21 boxST21Arg
  have boxST22Arg : |(θ 2-((4 / 3) : ℝ)*π)-((-2910490339279 / 3000000000000) : ℝ)*π| ≤
      (1 / 50000) := by
    have h := ht 2
    convert h using 1; norm_num [seedAngle]; congr 1; ring
  have hboxST22 := boxST22 boxST22Arg
  have hfin : ∀ i : Fin 40, |boxValues c θ i-
      ((boxInput i).center : ℝ)| ≤ ((boxInput i).radius : ℝ) := by
    intro i
    fin_cases i
    · change |π-(((6283185307179 / 2000000000000) : ℚ) : ℝ)| ≤
        (((1 / 2000000000000) : ℚ) : ℝ)
      convert hpi using 1 <;> norm_num [seedMass]
    · change |c 0-(((1000437388123 / 1000000000000) : ℚ) : ℝ)| ≤
        (((1 / 50000) : ℚ) : ℝ)
      convert hc 0 using 1 <;> norm_num [seedMass]
    · change |c 1-(((695398940163 / 500000000000) : ℚ) : ℝ)| ≤
        (((1 / 50000) : ℚ) : ℝ)
      convert hc 1 using 1 <;> norm_num [seedMass]
    · change |c 2-(((604352649479 / 1000000000000) : ℚ) : ℝ)| ≤
        (((1 / 50000) : ℚ) : ℝ)
      convert hc 2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-θ 1)-(((20742873676633 / 100000000000000) : ℚ) : ℝ)| ≤
        (((9134567399 / 100000000000000) : ℚ) : ℝ)
      convert hboxSS01.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-θ 1)-(((-67309757799411 / 100000000000000) : ℚ) : ℝ)| ≤
        (((5509304009 / 100000000000000) : ℚ) : ℝ)
      convert hboxSS01.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-θ 1)-(((132910161976553 / 100000000000000) : ℚ) : ℝ)| ≤
        (((14695708757 / 100000000000000) : ℚ) : ℝ)
      convert hboxSS01.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-θ 2)-(((61723171351237 / 100000000000000) : ℚ) : ℝ)| ≤
        (((3706202261 / 50000000000000) : ℚ) : ℝ)
      convert hboxSS02.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-θ 2)-(((7838205726517 / 6250000000000) : ℚ) : ℝ)| ≤
        (((5259081459 / 100000000000000) : ℚ) : ℝ)
      convert hboxSS02.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-θ 2)-(((131049039640719 / 100000000000000) : ℚ) : ℝ)| ≤
        (((956989681 / 10000000000000) : ℚ) : ℝ)
      convert hboxSS02.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 1-θ 2)-(((27203161727173 / 100000000000000) : ℚ) : ℝ)| ≤
        (((4402556489 / 50000000000000) : ℚ) : ℝ)
      convert hboxSS12.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 1-θ 2)-(((-15847207705777 / 20000000000000) : ℚ) : ℝ)| ≤
        (((5627069 / 100000000000) : ℚ) : ℝ)
      convert hboxSS12.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 1-θ 2)-(((137130451754161 / 100000000000000) : ℚ) : ℝ)| ≤
        (((6829418651 / 50000000000000) : ℚ) : ℝ)
      convert hboxSS12.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-(0 : ℝ)*π)-(((50247915424861 / 20000000000000) : ℚ) : ℝ)| ≤
        (((889550027 / 12500000000000) : ℚ) : ℝ)
      convert hboxST00.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-(0 : ℝ)*π)-(((39308433419249 / 25000000000000) : ℚ) : ℝ)| ≤
        (((1316023311 / 20000000000000) : ℚ) : ℝ)
      convert hboxST00.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-(0 : ℝ)*π)-(((-122468521585913 / 100000000000000) : ℚ) : ℝ)| ≤
        (((5725365797 / 50000000000000) : ℚ) : ℝ)
      convert hboxST00.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-((5 / 6) : ℝ)*π)-(((36188039279 / 20000000000000) : ℚ) : ℝ)| ≤
        (((202068943 / 5000000000000) : ℚ) : ℝ)
      convert hboxST01.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-((5 / 6) : ℝ)*π)-(((-1539553543327 / 50000000000000) : ℚ) : ℝ)| ≤
        (((175939153 / 25000000000000) : ℚ) : ℝ)
      convert hboxST01.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-((5 / 6) : ℝ)*π)-(((34823335780317 / 100000000000000) : ℚ) : ℝ)| ≤
        (((2015513497 / 25000000000000) : ℚ) : ℝ)
      convert hboxST01.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 0-((4 / 3) : ℝ)*π)-(((129027864451303 / 100000000000000) : ℚ) : ℝ)| ≤
        (((421346481 / 10000000000000) : ℚ) : ℝ)
      convert hboxST02.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 0-((4 / 3) : ℝ)*π)-(((-85988124347567 / 50000000000000) : ℚ) : ℝ)| ≤
        (((1291884453 / 50000000000000) : ℚ) : ℝ)
      convert hboxST02.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 0-((4 / 3) : ℝ)*π)-(((13577012430333 / 20000000000000) : ℚ) : ℝ)| ≤
        (((1229304873 / 25000000000000) : ℚ) : ℝ)
      convert hboxST02.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 1-(0 : ℝ)*π)-(((36603993937 / 20000000000000) : ℚ) : ℝ)| ≤
        (((161667871 / 4000000000000) : ℚ) : ℝ)
      convert hboxST10.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 1-(0 : ℝ)*π)-(((1551291503829 / 50000000000000) : ℚ) : ℝ)| ≤
        (((17661207 / 2500000000000) : ℚ) : ℝ)
      convert hboxST10.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 1-(0 : ℝ)*π)-(((34953747504807 / 100000000000000) : ℚ) : ℝ)| ≤
        (((8062530561 / 100000000000000) : ℚ) : ℝ)
      convert hboxST10.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 1-((5 / 6) : ℝ)*π)-(((125566874725709 / 50000000000000) : ℚ) : ℝ)| ≤
        (((1423643473 / 20000000000000) : ℚ) : ℝ)
      convert hboxST11.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 1-((5 / 6) : ℝ)*π)-(((-157316070468731 / 100000000000000) : ℚ) : ℝ)| ≤
        (((1316098467 / 20000000000000) : ℚ) : ℝ)
      convert hboxST11.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 1-((5 / 6) : ℝ)*π)-(((-30564938023977 / 25000000000000) : ℚ) : ℝ)| ≤
        (((11453207973 / 100000000000000) : ℚ) : ℝ)
      convert hboxST11.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 1-((4 / 3) : ℝ)*π)-(((222807520152001 / 100000000000000) : ℚ) : ℝ)| ≤
        (((7612513337 / 100000000000000) : ℚ) : ℝ)
      convert hboxST12.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 1-((4 / 3) : ℝ)*π)-(((2713533998909 / 1562500000000) : ℚ) : ℝ)| ≤
        (((4711933411 / 100000000000000) : ℚ) : ℝ)
      convert hboxST12.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 1-((4 / 3) : ℝ)*π)-(((-69864743906711 / 100000000000000) : ℚ) : ℝ)| ≤
        (((10415229251 / 100000000000000) : ℚ) : ℝ)
      convert hboxST12.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 2-(0 : ℝ)*π)-(((174279285295459 / 100000000000000) : ℚ) : ℝ)| ≤
        (((290954211 / 5000000000000) : ℚ) : ℝ)
      convert hboxST20.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 2-(0 : ℝ)*π)-(((-90932257962179 / 50000000000000) : ℚ) : ℝ)| ≤
        (((707659173 / 20000000000000) : ℚ) : ℝ)
      convert hboxST20.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 2-(0 : ℝ)*π)-(((1505032399227 / 20000000000000) : ℚ) : ℝ)| ≤
        (((753875017 / 10000000000000) : ℚ) : ℝ)
      convert hboxST20.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 2-((5 / 6) : ℝ)*π)-(((115140539174589 / 100000000000000) : ℚ) : ℝ)| ≤
        (((463583459 / 12500000000000) : ℚ) : ℝ)
      convert hboxST21.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 2-((5 / 6) : ℝ)*π)-(((82861179750759 / 50000000000000) : ℚ) : ℝ)| ≤
        (((2303306859 / 100000000000000) : ℚ) : ℝ)
      convert hboxST21.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 2-((5 / 6) : ℝ)*π)-(((16796298416591 / 20000000000000) : ℚ) : ℝ)| ≤
        (((2041823761 / 50000000000000) : ℚ) : ℝ)
      convert hboxST21.2.2 using 1 <;> norm_num [seedMass]
    · change |J (θ 2-((4 / 3) : ℝ)*π)-(((6856977377 / 25000000000000) : ℚ) : ℝ)| ≤
        (((4011731499 / 100000000000000) : ℚ) : ℝ)
      convert hboxST22.1 using 1 <;> norm_num [seedMass]
    · change |J1 (θ 2-((4 / 3) : ℝ)*π)-(((877325820183 / 100000000000000) : ℚ) : ℝ)| ≤
        (((374977791 / 100000000000000) : ℚ) : ℝ)
      convert hboxST22.2.1 using 1 <;> norm_num [seedMass]
    · change |J2 (θ 2-((4 / 3) : ℝ)*π)-(((9345995814643 / 50000000000000) : ℚ) : ℝ)| ≤
        (((8017597701 / 100000000000000) : ℚ) : ℝ)
      convert hboxST22.2.2 using 1 <;> norm_num [seedMass]
  intro i
  simpa [boxInput,boxValues,Fin.ofNat,Nat.mod_mod] using hfin (Fin.ofNat i)

private def boxH00Expr : Certificate := (.atom 0)

theorem boxH00 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 0 0-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
  have hs := Certificate.sound boxH00Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH00Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH00Expr = hessian c θ 0 0 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH00Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH00Expr,Fin.ofNat]

private def boxH01Expr : Certificate := (.atom 4)

theorem boxH01 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 0 1-((20742873676633 / 100000000000000) : ℝ)| ≤ (9134567399 / 100000000000000) := by
  have hs := Certificate.sound boxH01Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH01Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH01Expr = hessian c θ 0 1 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH01Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH01Expr,Fin.ofNat]

private def boxH02Expr : Certificate := (.atom 7)

theorem boxH02 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 0 2-((61723171351237 / 100000000000000) : ℝ)| ≤ (3706202261 / 50000000000000) := by
  have hs := Certificate.sound boxH02Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH02Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH02Expr = hessian c θ 0 2 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH02Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH02Expr,Fin.ofNat]

private def boxH03Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.const 0) ⟨0, 0⟩) ⟨0, 0⟩) (.mul (.atom 2) (.atom 5) ⟨(-93614268472677 / 100000000000000), (9008633681 / 100000000000000)⟩) ⟨(-93614268472677 / 100000000000000), (9008633681 / 100000000000000)⟩) (.mul (.atom 3) (.atom 8) ⟨(2368520198991 / 3125000000000), (1421667707 / 25000000000000)⟩) ⟨(-3564324420993 / 20000000000000), (14695304509 / 100000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 14) ⟨(39308433419249 / 25000000000000), (1316023311 / 20000000000000)⟩) (.atom 17) ⟨(77077313295171 / 50000000000000), (7283873167 / 100000000000000)⟩) (.atom 20) ⟨(-2227702763099 / 12500000000000), (9867642073 / 100000000000000)⟩) ⟨(2227702763099 / 12500000000000), (9867642073 / 100000000000000)⟩) ⟨(-173 / 100000000000000), (12281473291 / 50000000000000)⟩)

theorem boxH03 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 0 3-((-173 / 100000000000000) : ℝ)| ≤ (12281473291 / 50000000000000) := by
  have hs := Certificate.sound boxH03Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH03Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH03Expr = hessian c θ 0 3 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH03Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH03Expr,Fin.ofNat]

private def boxH04Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 2) ⟨(-695398940163 / 500000000000), (1 / 50000)⟩) (.atom 5) ⟨(93614268472677 / 100000000000000), (9008633681 / 100000000000000)⟩)

theorem boxH04 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 0 4-((93614268472677 / 100000000000000) : ℝ)| ≤ (9008633681 / 100000000000000) := by
  have hs := Certificate.sound boxH04Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH04Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH04Expr = hessian c θ 0 4 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH04Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH04Expr,Fin.ofNat]

private def boxH05Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 3) ⟨(-604352649479 / 1000000000000), (1 / 50000)⟩) (.atom 8) ⟨(-2368520198991 / 3125000000000), (1421667707 / 25000000000000)⟩)

theorem boxH05 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 0 5-((-2368520198991 / 3125000000000) : ℝ)| ≤ (1421667707 / 25000000000000) := by
  have hs := Certificate.sound boxH05Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH05Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH05Expr = hessian c θ 0 5 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH05Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH05Expr,Fin.ofNat]

private def boxH10Expr : Certificate := (.atom 4)

theorem boxH10 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 1 0-((20742873676633 / 100000000000000) : ℝ)| ≤ (9134567399 / 100000000000000) := by
  have hs := Certificate.sound boxH10Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH10Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH10Expr = hessian c θ 1 0 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH10Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH10Expr,Fin.ofNat]

private def boxH11Expr : Certificate := (.atom 0)

theorem boxH11 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 1 1-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
  have hs := Certificate.sound boxH11Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH11Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH11Expr = hessian c θ 1 1 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH11Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH11Expr,Fin.ofNat]

private def boxH12Expr : Certificate := (.atom 10)

theorem boxH12 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 1 2-((27203161727173 / 100000000000000) : ℝ)| ≤ (4402556489 / 50000000000000) := by
  have hs := Certificate.sound boxH12Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH12Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH12Expr = hessian c θ 1 2 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH12Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH12Expr,Fin.ofNat]

private def boxH13Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 1) ⟨(-1000437388123 / 1000000000000), (1 / 50000)⟩) (.mul (.const (-1)) (.atom 5) ⟨(67309757799411 / 100000000000000), (5509304009 / 100000000000000)⟩) ⟨(-33669599144017 / 50000000000000), (428626191 / 6250000000000)⟩)

theorem boxH13 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 1 3-((-33669599144017 / 50000000000000) : ℝ)| ≤ (428626191 / 6250000000000) := by
  have hs := Certificate.sound boxH13Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH13Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH13Expr = hessian c θ 1 3 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH13Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH13Expr,Fin.ofNat]

private def boxH14Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.mul (.const (-1)) (.atom 5) ⟨(67309757799411 / 100000000000000), (5509304009 / 100000000000000)⟩) ⟨(33669599144017 / 50000000000000), (428626191 / 6250000000000)⟩) ⟨(33669599144017 / 50000000000000), (428626191 / 6250000000000)⟩) (.mul (.atom 2) (.const 0) ⟨0, 0⟩) ⟨(33669599144017 / 50000000000000), (428626191 / 6250000000000)⟩) (.mul (.atom 3) (.atom 11) ⟨(-2992906863697 / 6250000000000), (1246391843 / 25000000000000)⟩) ⟨(9726344234441 / 50000000000000), (2960896607 / 25000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 23) ⟨(1551291503829 / 50000000000000), (17661207 / 2500000000000)⟩) (.atom 26) ⟨(-154213487461073 / 100000000000000), (1457388123 / 20000000000000)⟩) (.atom 29) ⟨(19452688469103 / 100000000000000), (5999437013 / 50000000000000)⟩) ⟨(-19452688469103 / 100000000000000), (5999437013 / 50000000000000)⟩) ⟨(-221 / 100000000000000), (11921230227 / 50000000000000)⟩)

theorem boxH14 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 1 4-((-221 / 100000000000000) : ℝ)| ≤ (11921230227 / 50000000000000) := by
  have hs := Certificate.sound boxH14Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH14Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH14Expr = hessian c θ 1 4 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH14Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH14Expr,Fin.ofNat]

private def boxH15Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 3) ⟨(-604352649479 / 1000000000000), (1 / 50000)⟩) (.atom 11) ⟨(2992906863697 / 6250000000000), (1246391843 / 25000000000000)⟩)

theorem boxH15 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 1 5-((2992906863697 / 6250000000000) : ℝ)| ≤ (1246391843 / 25000000000000) := by
  have hs := Certificate.sound boxH15Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH15Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH15Expr = hessian c θ 1 5 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH15Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH15Expr,Fin.ofNat]

private def boxH20Expr : Certificate := (.atom 7)

theorem boxH20 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 2 0-((61723171351237 / 100000000000000) : ℝ)| ≤ (3706202261 / 50000000000000) := by
  have hs := Certificate.sound boxH20Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH20Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH20Expr = hessian c θ 2 0 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH20Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH20Expr,Fin.ofNat]

private def boxH21Expr : Certificate := (.atom 10)

theorem boxH21 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 2 1-((27203161727173 / 100000000000000) : ℝ)| ≤ (4402556489 / 50000000000000) := by
  have hs := Certificate.sound boxH21Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH21Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH21Expr = hessian c θ 2 1 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH21Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH21Expr,Fin.ofNat]

private def boxH22Expr : Certificate := (.atom 0)

theorem boxH22 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 2 2-((6283185307179 / 2000000000000) : ℝ)| ≤ (1 / 2000000000000) := by
  have hs := Certificate.sound boxH22Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH22Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH22Expr = hessian c θ 2 2 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH22Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH22Expr,Fin.ofNat]

private def boxH23Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 1) ⟨(-1000437388123 / 1000000000000), (1 / 50000)⟩) (.mul (.const (-1)) (.atom 8) ⟨(-7838205726517 / 6250000000000), (5259081459 / 100000000000000)⟩) ⟨(125466145033719 / 100000000000000), (3884856367 / 50000000000000)⟩)

theorem boxH23 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 2 3-((125466145033719 / 100000000000000) : ℝ)| ≤ (3884856367 / 50000000000000) := by
  have hs := Certificate.sound boxH23Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH23Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH23Expr = hessian c θ 2 3 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH23Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH23Expr,Fin.ofNat]

private def boxH24Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 2) ⟨(-695398940163 / 500000000000), (1 / 50000)⟩) (.mul (.const (-1)) (.atom 11) ⟨(15847207705777 / 20000000000000), (5627069 / 100000000000)⟩) ⟨(-110201314431403 / 100000000000000), (9410948951 / 100000000000000)⟩)

theorem boxH24 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 2 4-((-110201314431403 / 100000000000000) : ℝ)| ≤ (9410948951 / 100000000000000) := by
  have hs := Certificate.sound boxH24Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH24Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH24Expr = hessian c θ 2 4 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH24Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH24Expr,Fin.ofNat]

private def boxH25Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.mul (.const (-1)) (.atom 8) ⟨(-7838205726517 / 6250000000000), (5259081459 / 100000000000000)⟩) ⟨(-125466145033719 / 100000000000000), (3884856367 / 50000000000000)⟩) ⟨(-125466145033719 / 100000000000000), (3884856367 / 50000000000000)⟩) (.mul (.atom 2) (.mul (.const (-1)) (.atom 11) ⟨(15847207705777 / 20000000000000), (5627069 / 100000000000)⟩) ⟨(110201314431403 / 100000000000000), (9410948951 / 100000000000000)⟩) ⟨(-3816207650579 / 25000000000000), (3436132337 / 20000000000000)⟩) (.mul (.atom 3) (.const 0) ⟨0, 0⟩) ⟨(-3816207650579 / 25000000000000), (3436132337 / 20000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 32) ⟨(-90932257962179 / 50000000000000), (707659173 / 20000000000000)⟩) (.atom 35) ⟨(-403553910571 / 2500000000000), (1460400681 / 25000000000000)⟩) (.atom 38) ⟨(-15264830602657 / 100000000000000), (1243316103 / 20000000000000)⟩) ⟨(15264830602657 / 100000000000000), (1243316103 / 20000000000000)⟩) ⟨(341 / 100000000000000), (116986211 / 500000000000)⟩)

theorem boxH25 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 2 5-((341 / 100000000000000) : ℝ)| ≤ (116986211 / 500000000000) := by
  have hs := Certificate.sound boxH25Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH25Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH25Expr = hessian c θ 2 5 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH25Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH25Expr,Fin.ofNat]

private def boxH30Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.const 0) ⟨0, 0⟩) ⟨0, 0⟩) (.mul (.atom 2) (.atom 5) ⟨(-93614268472677 / 100000000000000), (9008633681 / 100000000000000)⟩) ⟨(-93614268472677 / 100000000000000), (9008633681 / 100000000000000)⟩) (.mul (.atom 3) (.atom 8) ⟨(2368520198991 / 3125000000000), (1421667707 / 25000000000000)⟩) ⟨(-3564324420993 / 20000000000000), (14695304509 / 100000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 14) ⟨(39308433419249 / 25000000000000), (1316023311 / 20000000000000)⟩) (.atom 17) ⟨(77077313295171 / 50000000000000), (7283873167 / 100000000000000)⟩) (.atom 20) ⟨(-2227702763099 / 12500000000000), (9867642073 / 100000000000000)⟩) ⟨(2227702763099 / 12500000000000), (9867642073 / 100000000000000)⟩) ⟨(-173 / 100000000000000), (12281473291 / 50000000000000)⟩)

theorem boxH30 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 3 0-((-173 / 100000000000000) : ℝ)| ≤ (12281473291 / 50000000000000) := by
  have hs := Certificate.sound boxH30Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH30Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH30Expr = hessian c θ 3 0 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH30Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH30Expr,Fin.ofNat]

private def boxH31Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 1) ⟨(-1000437388123 / 1000000000000), (1 / 50000)⟩) (.mul (.const (-1)) (.atom 5) ⟨(67309757799411 / 100000000000000), (5509304009 / 100000000000000)⟩) ⟨(-33669599144017 / 50000000000000), (428626191 / 6250000000000)⟩)

theorem boxH31 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 3 1-((-33669599144017 / 50000000000000) : ℝ)| ≤ (428626191 / 6250000000000) := by
  have hs := Certificate.sound boxH31Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH31Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH31Expr = hessian c θ 3 1 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH31Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH31Expr,Fin.ofNat]

private def boxH32Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 1) ⟨(-1000437388123 / 1000000000000), (1 / 50000)⟩) (.mul (.const (-1)) (.atom 8) ⟨(-7838205726517 / 6250000000000), (5259081459 / 100000000000000)⟩) ⟨(125466145033719 / 100000000000000), (3884856367 / 50000000000000)⟩)

theorem boxH32 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 3 2-((125466145033719 / 100000000000000) : ℝ)| ≤ (3884856367 / 50000000000000) := by
  have hs := Certificate.sound boxH32Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH32Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH32Expr = hessian c θ 3 2 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH32Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH32Expr,Fin.ofNat]

private def boxH33Expr : Certificate := (.mul (.atom 1) (.add (.add (.add (.const 0) (.mul (.atom 2) (.atom 6) ⟨(7394046862031 / 4000000000000), (1443578609 / 6250000000000)⟩) ⟨(7394046862031 / 4000000000000), (1443578609 / 6250000000000)⟩) (.mul (.atom 3) (.atom 9) ⟨(79199834318547 / 100000000000000), (2101191171 / 25000000000000)⟩) ⟨(132025502934661 / 50000000000000), (7875505607 / 25000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 15) ⟨(-122468521585913 / 100000000000000), (5725365797 / 50000000000000)⟩) (.atom 18) ⟨(-21911296451399 / 25000000000000), (9756392791 / 50000000000000)⟩) (.atom 21) ⟨(-19760123653931 / 100000000000000), (12215002537 / 50000000000000)⟩) ⟨(19760123653931 / 100000000000000), (12215002537 / 50000000000000)⟩) ⟨(283811129523253 / 100000000000000), (27966013751 / 50000000000000)⟩) ⟨(141967632570241 / 50000000000000), (30816916369 / 50000000000000)⟩)

theorem boxH33 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 3 3-((141967632570241 / 50000000000000) : ℝ)| ≤ (30816916369 / 50000000000000) := by
  have hs := Certificate.sound boxH33Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH33Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH33Expr = hessian c θ 3 3 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH33Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf; simp
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH33Expr,Fin.ofNat]

private def boxH34Expr : Certificate := (.mul (.mul (.mul (.const (-1)) (.atom 1) ⟨(-1000437388123 / 1000000000000), (1 / 50000)⟩) (.atom 2) ⟨(-27828123976007 / 20000000000000), (2391255269 / 50000000000000)⟩) (.atom 6) ⟨(-92466011628867 / 50000000000000), (6701211397 / 25000000000000)⟩)

theorem boxH34 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 3 4-((-92466011628867 / 50000000000000) : ℝ)| ≤ (6701211397 / 25000000000000) := by
  have hs := Certificate.sound boxH34Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH34Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH34Expr = hessian c θ 3 4 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH34Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH34Expr,Fin.ofNat]

private def boxH35Expr : Certificate := (.mul (.mul (.mul (.const (-1)) (.atom 1) ⟨(-1000437388123 / 1000000000000), (1 / 50000)⟩) (.atom 3) ⟨(-60461698614999 / 100000000000000), (802405019 / 25000000000000)⟩) (.atom 9) ⟨(-39617237692711 / 50000000000000), (9992605611 / 100000000000000)⟩)

theorem boxH35 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 3 5-((-39617237692711 / 50000000000000) : ℝ)| ≤ (9992605611 / 100000000000000) := by
  have hs := Certificate.sound boxH35Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH35Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH35Expr = hessian c θ 3 5 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH35Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH35Expr,Fin.ofNat]

private def boxH40Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 2) ⟨(-695398940163 / 500000000000), (1 / 50000)⟩) (.atom 5) ⟨(93614268472677 / 100000000000000), (9008633681 / 100000000000000)⟩)

theorem boxH40 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 4 0-((93614268472677 / 100000000000000) : ℝ)| ≤ (9008633681 / 100000000000000) := by
  have hs := Certificate.sound boxH40Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH40Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH40Expr = hessian c θ 4 0 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH40Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH40Expr,Fin.ofNat]

private def boxH41Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.mul (.const (-1)) (.atom 5) ⟨(67309757799411 / 100000000000000), (5509304009 / 100000000000000)⟩) ⟨(33669599144017 / 50000000000000), (428626191 / 6250000000000)⟩) ⟨(33669599144017 / 50000000000000), (428626191 / 6250000000000)⟩) (.mul (.atom 2) (.const 0) ⟨0, 0⟩) ⟨(33669599144017 / 50000000000000), (428626191 / 6250000000000)⟩) (.mul (.atom 3) (.atom 11) ⟨(-2992906863697 / 6250000000000), (1246391843 / 25000000000000)⟩) ⟨(9726344234441 / 50000000000000), (2960896607 / 25000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 23) ⟨(1551291503829 / 50000000000000), (17661207 / 2500000000000)⟩) (.atom 26) ⟨(-154213487461073 / 100000000000000), (1457388123 / 20000000000000)⟩) (.atom 29) ⟨(19452688469103 / 100000000000000), (5999437013 / 50000000000000)⟩) ⟨(-19452688469103 / 100000000000000), (5999437013 / 50000000000000)⟩) ⟨(-221 / 100000000000000), (11921230227 / 50000000000000)⟩)

theorem boxH41 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 4 1-((-221 / 100000000000000) : ℝ)| ≤ (11921230227 / 50000000000000) := by
  have hs := Certificate.sound boxH41Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH41Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH41Expr = hessian c θ 4 1 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH41Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH41Expr,Fin.ofNat]

private def boxH42Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 2) ⟨(-695398940163 / 500000000000), (1 / 50000)⟩) (.mul (.const (-1)) (.atom 11) ⟨(15847207705777 / 20000000000000), (5627069 / 100000000000)⟩) ⟨(-110201314431403 / 100000000000000), (9410948951 / 100000000000000)⟩)

theorem boxH42 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 4 2-((-110201314431403 / 100000000000000) : ℝ)| ≤ (9410948951 / 100000000000000) := by
  have hs := Certificate.sound boxH42Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH42Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH42Expr = hessian c θ 4 2 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH42Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH42Expr,Fin.ofNat]

private def boxH43Expr : Certificate := (.mul (.mul (.mul (.const (-1)) (.atom 2) ⟨(-695398940163 / 500000000000), (1 / 50000)⟩) (.atom 1) ⟨(-27828123976007 / 20000000000000), (2391255269 / 50000000000000)⟩) (.atom 6) ⟨(-92466011628867 / 50000000000000), (6701211397 / 25000000000000)⟩)

theorem boxH43 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 4 3-((-92466011628867 / 50000000000000) : ℝ)| ≤ (6701211397 / 25000000000000) := by
  have hs := Certificate.sound boxH43Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH43Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH43Expr = hessian c θ 4 3 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH43Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH43Expr,Fin.ofNat]

private def boxH44Expr : Certificate := (.mul (.atom 2) (.add (.add (.add (.const 0) (.mul (.atom 1) (.atom 6) ⟨(33242073825707 / 25000000000000), (434015841 / 2500000000000)⟩) ⟨(33242073825707 / 25000000000000), (434015841 / 2500000000000)⟩) (.mul (.atom 3) (.atom 12) ⟨(82875151841879 / 100000000000000), (439905469 / 4000000000000)⟩) ⟨(215843447144707 / 100000000000000), (5671654073 / 20000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 24) ⟨(34953747504807 / 100000000000000), (8062530561 / 100000000000000)⟩) (.atom 27) ⟨(-87306004591101 / 100000000000000), (9757869267 / 50000000000000)⟩) (.atom 30) ⟨(-39292687124453 / 25000000000000), (5986193557 / 20000000000000)⟩) ⟨(39292687124453 / 25000000000000), (5986193557 / 20000000000000)⟩) ⟨(373014195642519 / 100000000000000), (1165784763 / 2000000000000)⟩) ⟨(518787352631123 / 100000000000000), (88529998563 / 100000000000000)⟩)

theorem boxH44 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 4 4-((518787352631123 / 100000000000000) : ℝ)| ≤ (88529998563 / 100000000000000) := by
  have hs := Certificate.sound boxH44Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH44Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH44Expr = hessian c θ 4 4 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH44Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf; simp
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH44Expr,Fin.ofNat]

private def boxH45Expr : Certificate := (.mul (.mul (.mul (.const (-1)) (.atom 2) ⟨(-695398940163 / 500000000000), (1 / 50000)⟩) (.atom 3) ⟨(-1050665479831 / 1250000000000), (3990341061 / 100000000000000)⟩) (.atom 12) ⟨(-57631292756691 / 50000000000000), (16953212837 / 100000000000000)⟩)

theorem boxH45 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 4 5-((-57631292756691 / 50000000000000) : ℝ)| ≤ (16953212837 / 100000000000000) := by
  have hs := Certificate.sound boxH45Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH45Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH45Expr = hessian c θ 4 5 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH45Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH45Expr,Fin.ofNat]

private def boxH50Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 3) ⟨(-604352649479 / 1000000000000), (1 / 50000)⟩) (.atom 8) ⟨(-2368520198991 / 3125000000000), (1421667707 / 25000000000000)⟩)

theorem boxH50 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 5 0-((-2368520198991 / 3125000000000) : ℝ)| ≤ (1421667707 / 25000000000000) := by
  have hs := Certificate.sound boxH50Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH50Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH50Expr = hessian c θ 5 0 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH50Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH50Expr,Fin.ofNat]

private def boxH51Expr : Certificate := (.mul (.mul (.const (-1)) (.atom 3) ⟨(-604352649479 / 1000000000000), (1 / 50000)⟩) (.atom 11) ⟨(2992906863697 / 6250000000000), (1246391843 / 25000000000000)⟩)

theorem boxH51 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 5 1-((2992906863697 / 6250000000000) : ℝ)| ≤ (1246391843 / 25000000000000) := by
  have hs := Certificate.sound boxH51Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH51Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH51Expr = hessian c θ 5 1 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH51Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH51Expr,Fin.ofNat]

private def boxH52Expr : Certificate := (.add (.add (.add (.add (.const 0) (.mul (.atom 1) (.mul (.const (-1)) (.atom 8) ⟨(-7838205726517 / 6250000000000), (5259081459 / 100000000000000)⟩) ⟨(-125466145033719 / 100000000000000), (3884856367 / 50000000000000)⟩) ⟨(-125466145033719 / 100000000000000), (3884856367 / 50000000000000)⟩) (.mul (.atom 2) (.mul (.const (-1)) (.atom 11) ⟨(15847207705777 / 20000000000000), (5627069 / 100000000000)⟩) ⟨(110201314431403 / 100000000000000), (9410948951 / 100000000000000)⟩) ⟨(-3816207650579 / 25000000000000), (3436132337 / 20000000000000)⟩) (.mul (.atom 3) (.const 0) ⟨0, 0⟩) ⟨(-3816207650579 / 25000000000000), (3436132337 / 20000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 32) ⟨(-90932257962179 / 50000000000000), (707659173 / 20000000000000)⟩) (.atom 35) ⟨(-403553910571 / 2500000000000), (1460400681 / 25000000000000)⟩) (.atom 38) ⟨(-15264830602657 / 100000000000000), (1243316103 / 20000000000000)⟩) ⟨(15264830602657 / 100000000000000), (1243316103 / 20000000000000)⟩) ⟨(341 / 100000000000000), (116986211 / 500000000000)⟩)

theorem boxH52 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 5 2-((341 / 100000000000000) : ℝ)| ≤ (116986211 / 500000000000) := by
  have hs := Certificate.sound boxH52Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH52Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH52Expr = hessian c θ 5 2 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH52Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH52Expr,Fin.ofNat]

private def boxH53Expr : Certificate := (.mul (.mul (.mul (.const (-1)) (.atom 3) ⟨(-604352649479 / 1000000000000), (1 / 50000)⟩) (.atom 1) ⟨(-60461698614999 / 100000000000000), (802405019 / 25000000000000)⟩) (.atom 9) ⟨(-39617237692711 / 50000000000000), (9992605611 / 100000000000000)⟩)

theorem boxH53 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 5 3-((-39617237692711 / 50000000000000) : ℝ)| ≤ (9992605611 / 100000000000000) := by
  have hs := Certificate.sound boxH53Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH53Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH53Expr = hessian c θ 5 3 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH53Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH53Expr,Fin.ofNat]

private def boxH54Expr : Certificate := (.mul (.mul (.mul (.const (-1)) (.atom 3) ⟨(-604352649479 / 1000000000000), (1 / 50000)⟩) (.atom 2) ⟨(-1050665479831 / 1250000000000), (3990341061 / 100000000000000)⟩) (.atom 12) ⟨(-57631292756691 / 50000000000000), (16953212837 / 100000000000000)⟩)

theorem boxH54 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 5 4-((-57631292756691 / 50000000000000) : ℝ)| ≤ (16953212837 / 100000000000000) := by
  have hs := Certificate.sound boxH54Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH54Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH54Expr = hessian c θ 5 4 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH54Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH54Expr,Fin.ofNat]

private def boxH55Expr : Certificate := (.mul (.atom 3) (.add (.add (.add (.const 0) (.mul (.atom 1) (.atom 9) ⟨(32776589733547 / 25000000000000), (12195254761 / 100000000000000)⟩) ⟨(32776589733547 / 25000000000000), (12195254761 / 100000000000000)⟩) (.mul (.atom 2) (.atom 12) ⟨(95360370813917 / 50000000000000), (1086978209 / 5000000000000)⟩) ⟨(160913550281011 / 50000000000000), (33934818941 / 100000000000000)⟩) (.mul (.const (-1)) (.add (.add (.add (.const 0) (.atom 33) ⟨(1505032399227 / 20000000000000), (753875017 / 10000000000000)⟩) (.atom 36) ⟨(9150665407909 / 10000000000000), (2905599423 / 25000000000000)⟩) (.atom 39) ⟨(13774830713547 / 12500000000000), (19639995393 / 100000000000000)⟩) ⟨(-13774830713547 / 12500000000000), (19639995393 / 100000000000000)⟩) ⟨(105814227426823 / 50000000000000), (26787407167 / 50000000000000)⟩) ⟨(31974554348987 / 25000000000000), (18305860791 / 50000000000000)⟩)

theorem boxH55 {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    |hessian c θ 5 5-((31974554348987 / 25000000000000) : ℝ)| ≤ (18305860791 / 50000000000000) := by
  have hs := Certificate.sound boxH55Expr boxInput (boxValues c θ)
    (box_inputs hc ht)
    (by norm_num [Certificate.check,Certificate.ball,boxInput,boxH55Expr,Fin.ofNat,abs_of_nonneg])
  have heq : Certificate.eval (boxValues c θ) boxH55Expr = hessian c θ 5 5 := by
    have hj10 := J_sub_comm (θ 1) (θ 0)
    have hj20 := J_sub_comm (θ 2) (θ 0)
    have hj21 := J_sub_comm (θ 2) (θ 1)
    have hf10 := J1_sub_comm (θ 1) (θ 0)
    have hf20 := J1_sub_comm (θ 2) (θ 0)
    have hf21 := J1_sub_comm (θ 2) (θ 1)
    have hs10 := J2_sub_comm (θ 1) (θ 0)
    have hs20 := J2_sub_comm (θ 2) (θ 0)
    have hs21 := J2_sub_comm (θ 2) (θ 1)
    norm_num [boxH55Expr,Certificate.eval,boxValues,Fin.ofNat,
      gradient,hessian,mixed,angular,teacherAngle,Fin.sum_univ_three,Fin.ext_iff,
      hj10,hj20,hj21,hf10,hf20,hf21,hs10,hs20,hs21]; ring_nf; simp
  rw [heq] at hs
  convert hs using 1 <;> norm_num [Certificate.ball,boxInput,boxH55Expr,Fin.ofNat]

end PaperLeanFormalization.SeedNumerics


/-! Fresh numerical certificate component: SeedClosure. -/

/-! Generated exact certificate data. Do not edit emitted source.
Producer: the certificate generator of this development, part: closure
Schema SHA256: 52d78277f3f1ad2146ecf733e1e7238c78f6c1192abbdf0157de3ea8fb3d301a
A generator run is not proof: compile this file and audit its declarations. -/

open Real
noncomputable section

namespace PaperLeanFormalization.SeedNumerics

open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def seedGramWitness : Fin 6 → Fin 6 → ℝ := ![
    ![(109001 / 62500), (118937 / 1000000), (176957 / 500000), 0, (268387 / 500000), (-434587 / 1000000)],
    ![0, (434989 / 250000), (16519 / 125000), (-387017 / 1000000), (-9173 / 250000), (76231 / 250000)],
    ![0, 0, (106413 / 62500), (153389 / 200000), (-755979 / 1000000), (16667 / 250000)],
    ![0, 0, 0, (1414697 / 1000000), (-453711 / 500000), (-256403 / 500000)],
    ![0, 0, 0, 0, (1844853 / 1000000), (-717181 / 1000000)],
    ![0, 0, 0, 0, 0, (339667 / 1000000)]]

theorem seed_center_gradient_coordinates (i : Fin 6) :
    |gradient seedMass seedAngle i| ≤ (1/100000000 : ℝ) := by
  fin_cases i
  · have h := centerG0 (c := seedMass) (θ := seedAngle)
      (by intro i; simp) (by intro i; simp)
    have hr := bound_round h (b := 0) (s := (1/100000000 : ℝ)) (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using hr
  · have h := centerG1 (c := seedMass) (θ := seedAngle)
      (by intro i; simp) (by intro i; simp)
    have hr := bound_round h (b := 0) (s := (1/100000000 : ℝ)) (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using hr
  · have h := centerG2 (c := seedMass) (θ := seedAngle)
      (by intro i; simp) (by intro i; simp)
    have hr := bound_round h (b := 0) (s := (1/100000000 : ℝ)) (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using hr
  · have h := centerG3 (c := seedMass) (θ := seedAngle)
      (by intro i; simp) (by intro i; simp)
    have hr := bound_round h (b := 0) (s := (1/100000000 : ℝ)) (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using hr
  · have h := centerG4 (c := seedMass) (θ := seedAngle)
      (by intro i; simp) (by intro i; simp)
    have hr := bound_round h (b := 0) (s := (1/100000000 : ℝ)) (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using hr
  · have h := centerG5 (c := seedMass) (θ := seedAngle)
      (by intro i; simp) (by intro i; simp)
    have hr := bound_round h (b := 0) (s := (1/100000000 : ℝ)) (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using hr

theorem seed_center_gradient_sq :
    (∑ i, (gradient seedMass seedAngle i)^2) ≤ (1/10000000000000000000 : ℝ) := by
  have h0 := centerG0 (c := seedMass) (θ := seedAngle)
    (by intro i; simp) (by intro i; simp)
  have hb0 : |gradient seedMass seedAngle 0| ≤ ((14571 / 100000000000000) : ℝ) := by
    have h := bound_round h0 (b := 0) (s := ((14571 / 100000000000000) : ℝ))
      (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using h
  have hs0 := mul_self_le_mul_self (abs_nonneg _) hb0
  rw [← pow_two,sq_abs] at hs0
  have h1 := centerG1 (c := seedMass) (θ := seedAngle)
    (by intro i; simp) (by intro i; simp)
  have hb1 : |gradient seedMass seedAngle 1| ≤ ((709 / 5000000000000) : ℝ) := by
    have h := bound_round h1 (b := 0) (s := ((709 / 5000000000000) : ℝ))
      (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using h
  have hs1 := mul_self_le_mul_self (abs_nonneg _) hb1
  rw [← pow_two,sq_abs] at hs1
  have h2 := centerG2 (c := seedMass) (θ := seedAngle)
    (by intro i; simp) (by intro i; simp)
  have hb2 : |gradient seedMass seedAngle 2| ≤ ((2997 / 20000000000000) : ℝ) := by
    have h := bound_round h2 (b := 0) (s := ((2997 / 20000000000000) : ℝ))
      (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using h
  have hs2 := mul_self_le_mul_self (abs_nonneg _) hb2
  rw [← pow_two,sq_abs] at hs2
  have h3 := centerG3 (c := seedMass) (θ := seedAngle)
    (by intro i; simp) (by intro i; simp)
  have hb3 : |gradient seedMass seedAngle 3| ≤ ((8537 / 100000000000000) : ℝ) := by
    have h := bound_round h3 (b := 0) (s := ((8537 / 100000000000000) : ℝ))
      (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using h
  have hs3 := mul_self_le_mul_self (abs_nonneg _) hb3
  rw [← pow_two,sq_abs] at hs3
  have h4 := centerG4 (c := seedMass) (θ := seedAngle)
    (by intro i; simp) (by intro i; simp)
  have hb4 : |gradient seedMass seedAngle 4| ≤ ((11601 / 100000000000000) : ℝ) := by
    have h := bound_round h4 (b := 0) (s := ((11601 / 100000000000000) : ℝ))
      (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using h
  have hs4 := mul_self_le_mul_self (abs_nonneg _) hb4
  rw [← pow_two,sq_abs] at hs4
  have h5 := centerG5 (c := seedMass) (θ := seedAngle)
    (by intro i; simp) (by intro i; simp)
  have hb5 : |gradient seedMass seedAngle 5| ≤ ((2629 / 50000000000000) : ℝ) := by
    have h := bound_round h5 (b := 0) (s := ((2629 / 50000000000000) : ℝ))
      (by norm_num [abs_of_nonneg])
    simpa only [sub_zero] using h
  have hs5 := mul_self_le_mul_self (abs_nonneg _) hb5
  rw [← pow_two,sq_abs] at hs5
  calc
    (∑ i, (gradient seedMass seedAngle i)^2) = (gradient seedMass seedAngle 0)^2+((gradient seedMass seedAngle 1)^2+((gradient seedMass seedAngle 2)^2+((gradient seedMass seedAngle 3)^2+((gradient seedMass seedAngle 4)^2+((gradient seedMass seedAngle 5)^2))))) := by
      norm_num [Fin.sum_univ_succ]; rfl
    _ ≤ ((14571 / 100000000000000) : ℝ)*(14571 / 100000000000000)+(((709 / 5000000000000) : ℝ)*(709 / 5000000000000)+(((2997 / 20000000000000) : ℝ)*(2997 / 20000000000000)+(((8537 / 100000000000000) : ℝ)*(8537 / 100000000000000)+(((11601 / 100000000000000) : ℝ)*(11601 / 100000000000000)+(((2629 / 50000000000000) : ℝ)*(2629 / 50000000000000)))))) := add_le_add hs0 (add_le_add hs1 (add_le_add hs2 (add_le_add hs3 (add_le_add hs4 (hs5)))))
    _ ≤ (1/10000000000000000000 : ℝ) := by norm_num

theorem seed_center_gradient_linear_bound (v : Fin 6 → ℝ) :
    (∑ i, gradient seedMass seedAngle i*v i)^2 ≤
      (6/10000000000000000 : ℝ)*(∑ i, v i^2) := by
  have h := linear_form_sq_bound (gradient seedMass seedAngle) v
    (by norm_num : (0 : ℝ) ≤ 1/100000000) seed_center_gradient_coordinates
  norm_num at h ⊢
  exact h

theorem seed_hessian_gram_enclosure {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ)) :
    ∀ i j, |hessian c θ i j-(∑ k, seedGramWitness k i*seedGramWitness k j)-
      (if i = j then (1/10 : ℝ) else 0)| ≤ (1/250 : ℝ) := by
  intro i j
  fin_cases i <;> fin_cases j
  · have h := bound_round (boxH00 hc ht) (b := ((12271843001 / 3906250000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1; congr 1; ring_nf
  · have h := bound_round (boxH01 hc ht) (b := ((12964251937 / 62500000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH02 hc ht) (b := ((19288489957 / 31250000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH03 hc ht) (b := (0 : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH04 hc ht) (b := ((29254451387 / 31250000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH05 hc ht) (b := ((-47370417587 / 62500000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH10 hc ht) (b := ((12964251937 / 62500000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH11 hc ht) (b := ((628318578381 / 200000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1; congr 1; ring_nf
  · have h := bound_round (boxH12 hc ht) (b := ((27203213473 / 100000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH13 hc ht) (b := ((-168348137813 / 250000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH14 hc ht) (b := ((-88157 / 500000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH15 hc ht) (b := ((19154634773 / 40000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH20 hc ht) (b := ((19288489957 / 31250000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH21 hc ht) (b := ((27203213473 / 100000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH22 hc ht) (b := ((785398318041 / 250000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1; congr 1; ring_nf; rfl
  · have h := bound_round (boxH23 hc ht) (b := ((156832702747 / 125000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH24 hc ht) (b := ((-55100649049 / 50000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH25 hc ht) (b := ((-318463 / 500000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH30 hc ht) (b := (0 : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH31 hc ht) (b := ((-168348137813 / 250000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH32 hc ht) (b := ((156832702747 / 125000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH33 hc ht) (b := ((2839354393123 / 1000000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1; congr 1; ring_nf; rfl
  · have h := bound_round (boxH34 hc ht) (b := ((-73972842701 / 40000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH35 hc ht) (b := ((-79234519223 / 100000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH40 hc ht) (b := ((29254451387 / 31250000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH41 hc ht) (b := ((-88157 / 500000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH42 hc ht) (b := ((-55100649049 / 50000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH43 hc ht) (b := ((-73972842701 / 40000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH44 hc ht) (b := ((2593937078037 / 500000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1; congr 1; ring_nf; rfl
  · have h := bound_round (boxH45 hc ht) (b := ((-1152624954979 / 1000000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH50 hc ht) (b := ((-47370417587 / 62500000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH51 hc ht) (b := ((19154634773 / 40000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH52 hc ht) (b := ((-318463 / 500000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH53 hc ht) (b := ((-79234519223 / 100000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH54 hc ht) (b := ((-1152624954979 / 1000000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1
  · have h := bound_round (boxH55 hc ht) (b := ((255796275971 / 200000000000) : ℝ))
      (s := (1/250 : ℝ)) (by norm_num [abs_of_nonneg])
    norm_num [seedGramWitness,Fin.sum_univ_succ,Fin.ext_iff] at h ⊢
    convert h using 1; congr 1; ring_nf; rfl

theorem seed_hessian_floor {c θ : Fin 3 → ℝ}
    (hc : ∀ i, |c i-seedMass i| ≤ ((1 / 50000) : ℝ))
    (ht : ∀ i, |θ i-seedAngle i| ≤ ((1 / 50000) : ℝ))
    (v : Fin 6 → ℝ) :
    (1/16 : ℝ)*(∑ i, v i^2) ≤ ∑ i, ∑ j, hessian c θ i j*v i*v j := by
  have h := hessian_floor_of_gram_enclosure (hessian c θ) seedGramWitness
    (μ := (1/10 : ℝ)) (ε := (1/250 : ℝ)) (by norm_num)
    (seed_hessian_gram_enclosure hc ht) v
  have hq : 0 ≤ ∑ i, v i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  norm_num at h
  nlinarith only [h,hq]

end PaperLeanFormalization.SeedNumerics



open Real
open scoped BigOperators
noncomputable section
namespace PaperLeanFormalization.SeedNumerics

/-- The complete shifted Gram certificate, with Q = CᵀC + (19/250)I. -/
theorem eq_seed_hessian_sos (x : Fin 6 → ℝ) :
    (∑ i, ∑ j, ((∑ l, seedGramWitness l i*seedGramWitness l j) +
      (if i=j then (19/250 : ℝ) else 0) - (if i=j then (1/16 : ℝ) else 0))*x i*x j) =
      (∑ l, (∑ i, seedGramWitness l i*x i)^2) + (27/2000 : ℝ)*(∑ i, x i^2) ∧
    0 ≤ (∑ l, (∑ i, seedGramWitness l i*x i)^2) + (27/2000 : ℝ)*(∑ i, x i^2) := by
  constructor
  · rw [← finite_gram_quadratic_eq_sum_sq]
    have hp (i j : Fin 6) :
        ((∑ l, seedGramWitness l i*seedGramWitness l j) +
          (if i=j then (19/250 : ℝ) else 0) - (if i=j then (1/16 : ℝ) else 0))*x i*x j =
        (∑ l, seedGramWitness l i*seedGramWitness l j)*x i*x j +
          (if i=j then (27/2000 : ℝ)*x i^2 else 0) := by
      split_ifs with h
      · subst j
        ring
      · ring
    simp only [hp, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
  · exact add_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))

end PaperLeanFormalization.SeedNumerics

namespace PaperLeanFormalization.Plain.SeedDirectional
open SeedNumerics

theorem J_eq_local (t : ℝ) : J t = LocalKernelCalculus.plainKernel t := by
  simp only [J, LocalKernelCalculus.plainKernel, KernelCalculus.angularKernel,
    KernelCalculus.centeredKernel, arccos_eq_pi_div_two_sub_arcsin,
    KernelCalculus.sqrt_one_sub_cos_sq]
  ring

theorem J1_eq_local (t : ℝ) : J1 t = -LocalKernelCalculus.plainTorque t := by
  simp only [J1, LocalKernelCalculus.plainTorque, arccos_eq_pi_div_two_sub_arcsin]
  ring

theorem J_derivative (t : ℝ) : HasDerivAt J (J1 t) t := by
  simpa only [funext J_eq_local, J1_eq_local] using LocalKernelCalculus.plainKernel_derivative t

theorem J1_derivative (t : ℝ) : HasDerivAt J1 (J2 t) t := by
  simpa only [funext J1_eq_local, J2, J_eq_local, LocalKernelCalculus.plainCurvature] using
    LocalKernelCalculus.plainKernel_second_derivative t

def modelLoss {n m : ℕ} (β s : Fin m → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, p.1 i * p.1 j * J (p.2 i - p.2 j)) -
    ∑ i, ∑ k, p.1 i * s k * J (p.2 i - β k)

def first {n m : ℕ} (β s : Fin m → ℝ)
    (p h : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j,
      ((h.1 i * p.1 j + p.1 i * h.1 j) * J (p.2 i - p.2 j) +
        p.1 i * p.1 j * J1 (p.2 i - p.2 j) * (h.2 i - h.2 j))) -
    ∑ i, ∑ k, (h.1 i * s k * J (p.2 i - β k) +
      p.1 i * s k * J1 (p.2 i - β k) * h.2 i)

def second {n m : ℕ} (β s : Fin m → ℝ)
    (p h : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j,
      (2 * h.1 i * h.1 j * J (p.2 i - p.2 j) +
        2 * (h.1 i * p.1 j + p.1 i * h.1 j) * J1 (p.2 i - p.2 j) *
          (h.2 i - h.2 j) +
        p.1 i * p.1 j * J2 (p.2 i - p.2 j) * (h.2 i - h.2 j)^2)) -
    ∑ i, ∑ k, (2 * h.1 i * s k * J1 (p.2 i - β k) * h.2 i +
      p.1 i * s k * J2 (p.2 i - β k) * (h.2 i)^2)

theorem affine_derivative (a b : ℝ) :
    HasDerivAt (fun t : ℝ ↦ a + t * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

theorem pair_first (a b u v A B U V : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (a+t*u)*(b+t*v)*J ((A+t*U)-(B+t*V)))
      ((u*b+a*v)*J (A-B)+a*b*J1 (A-B)*(U-V)) 0 := by
  have harg := (affine_derivative A U).sub (affine_derivative B V)
  have hJ := (J_derivative ((A+(0:ℝ)*U)-(B+0*V))).comp (0:ℝ) harg
  convert ((affine_derivative a u).mul (affine_derivative b v)).mul hJ using 1
  simp only [Function.comp_def, zero_mul, add_zero]
  ring

theorem pair_second (a b u v A B U V : ℝ) :
    HasDerivAt (fun t : ℝ ↦
      (u*(b+t*v)+(a+t*u)*v)*J ((A+t*U)-(B+t*V)) +
        (a+t*u)*(b+t*v)*J1 ((A+t*U)-(B+t*V))*(U-V))
      (2*u*v*J (A-B)+2*(u*b+a*v)*J1 (A-B)*(U-V)+
        a*b*J2 (A-B)*(U-V)^2) 0 := by
  have harg := (affine_derivative A U).sub (affine_derivative B V)
  have hJ := (J_derivative ((A+(0:ℝ)*U)-(B+0*V))).comp (0:ℝ) harg
  have hJ1 := (J1_derivative ((A+(0:ℝ)*U)-(B+0*V))).comp (0:ℝ) harg
  have hcoef := ((affine_derivative b v).const_mul u).add
    ((affine_derivative a u).mul_const v)
  have hp := (affine_derivative a u).mul (affine_derivative b v)
  convert (hcoef.mul hJ).add ((hp.mul hJ1).mul_const (U-V)) using 1
  simp only [Function.comp_def, zero_mul, add_zero]
  ring

theorem line_first {n m : ℕ} (β s : Fin m → ℝ)
    (p h : (Fin n → ℝ) × (Fin n → ℝ)) :
    HasDerivAt (fun t : ℝ ↦ modelLoss β s (p+t•h)) (first β s p h) 0 := by
  have hs := (HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) ↦
    HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) ↦
      pair_first (p.1 i) (p.1 j) (h.1 i) (h.1 j) (p.2 i) (p.2 j) (h.2 i) (h.2 j)))).const_mul (1/2 : ℝ)
  have ht := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) ↦
    HasDerivAt.sum (fun k (_ : k ∈ Finset.univ) ↦
      pair_first (p.1 i) (s k) (h.1 i) 0 (p.2 i) (β k) (h.2 i) 0))
  simpa only [modelLoss, first, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, zero_mul, add_zero, sub_zero] using hs.sub ht

theorem line_second {n m : ℕ} (β s : Fin m → ℝ)
    (p h : (Fin n → ℝ) × (Fin n → ℝ)) :
    HasDerivAt (fun t : ℝ ↦ first β s (p+t•h) h) (second β s p h) 0 := by
  have hs := (HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) ↦
    HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) ↦
      pair_second (p.1 i) (p.1 j) (h.1 i) (h.1 j) (p.2 i) (p.2 j) (h.2 i) (h.2 j)))).const_mul (1/2 : ℝ)
  have ht := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) ↦
    HasDerivAt.sum (fun k (_ : k ∈ Finset.univ) ↦
      pair_second (p.1 i) (s k) (h.1 i) 0 (p.2 i) (β k) (h.2 i) 0))
  simpa only [first, second, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, zero_mul, add_zero, sub_zero,
    zero_add, mul_assoc] using hs.sub ht

/-- The interval certificate uses an arccos form of the same literal angular
kernel. This is only a definitional normalization, not an old loss theorem. -/
theorem modelLoss_eq_kernelLoss {n m : ℕ} (β s : Fin m → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    modelLoss β s p = PaperLeanFormalization.signedMassLossPairNoncentered β s p := by
  unfold modelLoss PaperLeanFormalization.signedMassLossPairNoncentered PaperLeanFormalization.signedMassLossNoncentered
    PaperLeanFormalization.kernelMassLoss
  simp only [J_eq_local]
  rfl

theorem actual_line_first {n m : ℕ} (β s : Fin m → ℝ)
    (p h : (Fin n → ℝ) × (Fin n → ℝ)) :
    HasDerivAt (fun t : ℝ ↦ PaperLeanFormalization.signedMassLossPairNoncentered β s (p+t•h))
      (first β s p h) 0 := by
  simpa only [modelLoss_eq_kernelLoss] using line_first β s p h

theorem sum_six_split (f : Fin 6 → ℝ) :
    (∑ i, f i) = (∑ i : Fin 3, f (Fin.castAdd 3 i)) +
      ∑ i : Fin 3, f (Fin.natAdd 3 i) := Fin.sum_univ_add (a := 3) (b := 3) f

set_option maxHeartbeats 2000000 in
theorem first_eq_gradient (p h : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    first teacherAngle (fun _ ↦ 1) p h =
      ∑ i : Fin 6, gradient p.1 p.2 i * Fin.append h.1 h.2 i := by
  have hj10 := J_sub_comm (p.2 1) (p.2 0)
  have hj20 := J_sub_comm (p.2 2) (p.2 0)
  have hj21 := J_sub_comm (p.2 2) (p.2 1)
  have hf10 := J1_sub_comm (p.2 1) (p.2 0)
  have hf20 := J1_sub_comm (p.2 2) (p.2 0)
  have hf21 := J1_sub_comm (p.2 2) (p.2 1)
  simp only [sum_six_split, SeedNumerics.gradient, Fin.append_left, Fin.append_right]
  norm_num [first, Fin.sum_univ_three,
    hj10, hj20, hj21, hf10, hf20, hf21]
  ring

set_option maxHeartbeats 4000000 in
theorem second_eq_hessian (p h : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    second teacherAngle (fun _ ↦ 1) p h =
      ∑ i : Fin 6, ∑ j : Fin 6,
        hessian p.1 p.2 i j * Fin.append h.1 h.2 i * Fin.append h.1 h.2 j := by
  have hj10 := J_sub_comm (p.2 1) (p.2 0)
  have hj20 := J_sub_comm (p.2 2) (p.2 0)
  have hj21 := J_sub_comm (p.2 2) (p.2 1)
  have hf10 := J1_sub_comm (p.2 1) (p.2 0)
  have hf20 := J1_sub_comm (p.2 2) (p.2 0)
  have hf21 := J1_sub_comm (p.2 2) (p.2 1)
  have hs10 := J2_sub_comm (p.2 1) (p.2 0)
  have hs20 := J2_sub_comm (p.2 2) (p.2 0)
  have hs21 := J2_sub_comm (p.2 2) (p.2 1)
  simp only [sum_six_split, hessian, Fin.append_left, Fin.append_right]
  norm_num [second, mixed, angular, Fin.sum_univ_three, Fin.ext_iff,
    hj10, hj20, hj21, hf10, hf20, hf21, hs10, hs20, hs21]
  ring

end PaperLeanFormalization.Plain.SeedDirectional


/-!
The certified base case in the proof of `thm:plain-trap` in the paper.

The numerical centre is not asserted to be a critical point.  A uniform
Hessian lower bound on a ball and a small gradient at its centre produce a
genuine interior critical point.  A separate excess bound proves spuriousness;
the positive residual curvature is the extra hypothesis needed for splitting.
All numerical constants in this file use the internal kernel loss, whose
excess is `2 * π` times the Gaussian half-loss.
-/

noncomputable section

namespace PaperLeanFormalization.Plain

open Real PaperLeanFormalization
open PaperLeanFormalization.Definitions PaperLeanFormalization

/-- The paper's kernel is exactly the noncentered angular kernel after
substitution of the direction correlation. Only finite algebra is involved. -/
theorem plain_kernel_angle (t : ℝ) :
    Kernel .plainRelu (cos t) = phiCosJ t := by
  unfold Kernel phiCosJ reluPhi orthantPhi
  ring

/-- Literal population normalization from the new local Gaussian moment
proof, not the old population-loss equivalence theorem. -/
theorem plain_loss_eq_excess_div {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) :
    PlainLoss c (fun i ↦ Angle (θ i)) s (fun k ↦ Angle (β k)) =
      noncenteredExcessLoss c β s θ / (2 * π) := by
  have h := Preliminaries.loss_eq_kernelEnergy (by norm_num : 2 ≤ 2)
    .plainRelu c (fun i ↦ Angle (θ i)) s (fun k ↦ Angle (β k))
    (fun i ↦ Preliminaries.angle_unit (θ i)) (fun k ↦ Preliminaries.angle_unit (β k))
  change PlainLoss c (fun i ↦ Angle (θ i)) s (fun k ↦ Angle (β k)) = _ at h
  rw [h]
  simp only [Preliminaries.KernelEnergy, Preliminaries.angle_inner, plain_kernel_angle]
  unfold noncenteredExcessLoss kernelExcessLoss kernelTeacherSelfEnergy kernelMassLoss
  ring

/-- The complete finite formula and its positive affine population normalization. -/
theorem eq_plain_kernel_normalization {n m : ℕ}
    (s θ : Fin n → ℝ) (t β : Fin m → ℝ) :
    signedMassLossPairNoncentered β t (s, θ) =
      (1/2 : ℝ) * ∑ i, ∑ j, s i*s j*phiCosJ (θ i-θ j) -
        ∑ i, ∑ k, s i*t k*phiCosJ (θ i-β k) ∧
    signedMassLossPairNoncentered β t (s, θ) =
      (2*π)*PlainLoss s (fun i ↦ Angle (θ i)) t (fun k ↦ Angle (β k)) -
        (1/2 : ℝ)*∑ k, ∑ l, t k*t l*phiCosJ (β k-β l) := by
  constructor
  · rfl
  · rw [plain_loss_eq_excess_div]
    unfold noncenteredExcessLoss kernelExcessLoss kernelTeacherSelfEnergy
      signedMassLossPairNoncentered signedMassLossNoncentered
    have hnz : 2*π ≠ 0 := ne_of_gt (by positivity)
    field_simp [hnz]
    ring

/-- The integrand is a square against a positive density. -/
theorem plain_loss_nonnegative {d n m : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d) :
    0 ≤ PlainLoss c w s v := by
  unfold PlainLoss
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply MeasureTheory.integral_nonneg
  intro x
  exact mul_nonneg (sq_nonneg _) (by unfold stdGaussianDensity; positivity)

/-- The quadratic energy of any signed finite feature difference is
nonnegative. This supplies the square term in the merge comparison. -/
theorem plain_kernel_exact_fit_floor {n m : ℕ}
    (β s : Fin m → ℝ) (c θ : Fin n → ℝ) :
    kernelMassLoss phiCosJ s β s β ≤ kernelMassLoss phiCosJ c β s θ := by
  have hnonneg := plain_loss_nonnegative c (fun i ↦ Angle (θ i))
    s (fun k ↦ Angle (β k))
  rw [plain_loss_eq_excess_div] at hnonneg
  have hp : 0 < 2 * π := mul_pos (by norm_num) Real.pi_pos
  have henergy := mul_nonneg hnonneg hp.le
  rw [div_mul_cancel _ hp.ne'] at henergy
  have hid : noncenteredExcessLoss c β s θ =
      kernelMassLoss phiCosJ c β s θ - kernelMassLoss phiCosJ s β s β := by
    unfold noncenteredExcessLoss kernelExcessLoss kernelTeacherSelfEnergy kernelMassLoss
    ring
  rw [hid] at henergy
  exact sub_nonneg.mp henergy

/-- Positive affine normalization preserves the local comparison. -/
theorem kernel_minimum_to_plain {n m : ℕ} {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hmin : IsLocalMin (signedMassLossPairNoncentered β s) (c, θ)) :
    IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      PlainLoss p.1 (fun i ↦ Angle (p.2 i)) s (fun k ↦ Angle (β k))) (c, θ) := by
  filter_upwards [hmin] with p hp
  simp only [plain_loss_eq_excess_div]
  apply (div_le_div_right (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)).mpr
  change signedMassLossPairNoncentered β s (c, θ) + teacherSelfEnergyJ β s ≤
    signedMassLossPairNoncentered β s p + teacherSelfEnergyJ β s
  exact add_le_add_right hp _

/-- The reverse population normalization is an order comparison, not a
derivative or differentiability assumption. -/
theorem plain_minimum_to_kernel {n m : ℕ} {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hmin : IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      PlainLoss p.1 (fun j => Angle (p.2 j)) s (fun k => Angle (β k))) (c, θ)) :
    IsLocalMin (signedMassLossPairNoncentered β s) (c, θ) := by
  filter_upwards [hmin] with p hp
  simp only [plain_loss_eq_excess_div] at hp
  have h := (div_le_div_right (mul_pos (by norm_num : (0 : ℝ) < 2) pi_pos)).mp hp
  change signedMassLossPairNoncentered β s (c, θ) + teacherSelfEnergyJ β s ≤
    signedMassLossPairNoncentered β s p + teacherSelfEnergyJ β s at h
  exact (add_le_add_iff_right _).mp h

theorem kernel_strict_minimum_to_plain {n m : ℕ} {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hmin : IsStrictLocalMinPoint (signedMassLossPairNoncentered β s) (c, θ)) :
    IsStrictLocalMinPoint (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      PlainLoss p.1 (fun i ↦ Angle (p.2 i)) s (fun k ↦ Angle (β k))) (c, θ) := by
  filter_upwards [hmin] with p hp hne
  simp only [plain_loss_eq_excess_div]
  apply (div_lt_div_right (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)).mpr
  change signedMassLossPairNoncentered β s (c, θ) + teacherSelfEnergyJ β s <
    signedMassLossPairNoncentered β s p + teacherSelfEnergyJ β s
  exact add_lt_add_right (hp hne) _

/-- A nonzero affine scaling has the same zero derivative. The
nondifferentiable branch is included, so this also respects Mathlib's
definition of `fderiv` without adding an implicit differentiability premise. -/
theorem affine_critical_to_original {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℝ} {x : E} {a b : ℝ} (ha : a ≠ 0)
    (heq : ∀ y, f y = a * g y + b) (hcrit : fderiv ℝ f x = 0) :
    fderiv ℝ g x = 0 := by
  by_cases hg : DifferentiableAt ℝ g x
  · have H : HasFDerivAt f (a • fderiv ℝ g x) x := by
      convert (hg.hasFDerivAt.const_smul a).add_const b using 1
      funext y
      exact heq y
    rw [H.fderiv] at hcrit
    exact (smul_eq_zero.mp hcrit).resolve_left ha
  · exact fderiv_zero_of_not_differentiableAt hg

theorem plain_critical_to_kernel {n m : ℕ} {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hcrit : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      PlainLoss p.1 (fun i ↦ Angle (p.2 i)) s (fun k ↦ Angle (β k))) (c, θ) = 0) :
    IsSignedMassCriticalNoncentered β s c θ := by
  apply affine_critical_to_original
    (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      PlainLoss p.1 (fun i ↦ Angle (p.2 i)) s (fun k ↦ Angle (β k)))
    (a := 1 / (2 * π)) (b := teacherSelfEnergyJ β s / (2 * π))
    (by positivity) ?_ hcrit
  intro p
  dsimp only
  rw [plain_loss_eq_excess_div]
  change (signedMassLossPairNoncentered β s p + teacherSelfEnergyJ β s) / (2 * π) =
    1 / (2 * π) * signedMassLossPairNoncentered β s p + teacherSelfEnergyJ β s / (2 * π)
  ring


/-- Euclidean squared increment size, distinct from the box's sup norm. -/
def pairEuclideanSq {n : ℕ} (h : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ i, h.1 i^2) + ∑ i, h.2 i^2

/-- The box uses the product sup norm, while the Hessian certificate uses
the visible sum of coordinate squares. Each coordinate square is one
nonnegative summand, which gives the required norm comparison. -/
theorem pair_size_dominates_norm {n : ℕ}
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ‖p‖ ^ 2 ≤ pairEuclideanSq p := by
  have hpi (v : Fin n → ℝ) : ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
    have hsum : (0 : ℝ) ≤ ∑ i, v i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg (v i)
    have hn : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro i
      exact Real.abs_le_sqrt (Finset.single_le_sum
        (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
    have hs := Real.sq_sqrt hsum
    nlinarith only [hn, hs, norm_nonneg v, Real.sqrt_nonneg (∑ i, v i ^ 2)]
  have hfirst := hpi p.1
  have hsecond := hpi p.2
  have hfirst0 : (0 : ℝ) ≤ ∑ i, p.1 i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (p.1 i)
  have hsecond0 : (0 : ℝ) ≤ ∑ i, p.2 i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (p.2 i)
  rw [Prod.norm_def]
  unfold pairEuclideanSq
  rcases le_total ‖p.1‖ ‖p.2‖ with h | h
  · rw [max_eq_right h]
    linarith only [hsecond, hfirst0]
  · rw [max_eq_left h]
    linarith only [hfirst, hsecond0]

theorem seed_teacher_angles : SeedNumerics.teacherAngle = TrapTeacherAngle := by
  funext i
  fin_cases i <;> simp [SeedNumerics.teacherAngle, TrapTeacherAngle]

theorem seed_center_coordinates :
    (SeedNumerics.seedMass, SeedNumerics.seedAngle) = SeedCertificate.seedCentre := rfl

theorem appended_square_sum (h : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    (∑ i : Fin 6, (Fin.append h.1 h.2 i)^2) = pairEuclideanSq h := by
  rw [SeedDirectional.sum_six_split]
  simp only [Fin.append_left, Fin.append_right, pairEuclideanSq]

theorem finite_cauchy_schwarz {n : ℕ} (g v : Fin n → ℝ) :
    (∑ i, g i * v i)^2 ≤ (∑ i, g i^2) * (∑ i, v i^2) := by
  let G : EuclideanSpace ℝ (Fin n) := g
  let V : EuclideanSpace ℝ (Fin n) := v
  have hi : ⟪G, V⟫_ℝ = ∑ i, g i * v i := by
    rw [PiLp.inner_apply]
    rfl
  have hn (a : EuclideanSpace ℝ (Fin n)) : ‖a‖^2 = ∑ i, a i^2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    change (∑ i, a i * a i) = ∑ i, a i^2
    simp only [pow_two]
  have h := mul_self_le_mul_self (abs_nonneg _) (abs_real_inner_le_norm G V)
  rw [← pow_two, sq_abs, hi, ← pow_two, mul_pow, hn, hn] at h
  exact h


/-- Strict neighborhood inequalities imply local minimality directly. -/
theorem strict_to_local {X : Type*} [TopologicalSpace X] {f : X → ℝ} {x : X}
    (h : ∀ᶠ y in nhds x, y ≠ x → f x < f y) : IsLocalMin f x := by
  filter_upwards [h] with y hy
  rcases eq_or_ne y x with rfl | hne
  · exact le_rfl
  · exact (hy hne).le

/-- The centre's directional gradient is small, but is not assumed zero. -/
theorem certified_center_gradient : ∀ h,
    (SeedDirectional.first TrapTeacherAngle TrapTeacherMass SeedCertificate.seedCentre h)^2 ≤
      (1 / 10000000000000000000 : ℝ) * pairEuclideanSq h := by
  intro h
  have hc := finite_cauchy_schwarz
    (SeedNumerics.gradient SeedNumerics.seedMass SeedNumerics.seedAngle) (Fin.append h.1 h.2)
  have hb := hc.trans (mul_le_mul_of_nonneg_right SeedNumerics.seed_center_gradient_sq
    (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (Fin.append h.1 h.2 i))))
  rw [appended_square_sum] at hb
  have hfirst := SeedDirectional.first_eq_gradient
    (SeedNumerics.seedMass, SeedNumerics.seedAngle) h
  rw [seed_teacher_angles, seed_center_coordinates] at hfirst
  change SeedDirectional.first TrapTeacherAngle TrapTeacherMass SeedCertificate.seedCentre h =
    ∑ i : Fin 6, SeedNumerics.gradient SeedNumerics.seedMass SeedNumerics.seedAngle i *
      Fin.append h.1 h.2 i at hfirst
  rw [← hfirst] at hb
  exact hb


open PaperLeanFormalization.Definitions

/-- The numerical first derivative is the actual Fréchet derivative. -/
theorem seed_first_eq_fderiv (z h : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    fderiv ℝ (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass) z h =
      SeedDirectional.first TrapTeacherAngle TrapTeacherMass z h := by
  have hf : ContDiff ℝ 2 (signedMassLossPairNoncentered (n := 3) TrapTeacherAngle TrapTeacherMass) :=
    ParameterCalculus.loss_contDiff_two TrapTeacherAngle TrapTeacherMass
  exact (BoxDirectional.first_line_derivative hf z h).unique
    (SeedDirectional.actual_line_first TrapTeacherAngle TrapTeacherMass z h)

/-- The certified quadratic form is the diagonal of the actual Hessian. -/
theorem seed_second_eq_fderiv (z h : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
    (fderiv ℝ (fderiv ℝ
      (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass)) z h) h =
        SeedDirectional.second TrapTeacherAngle TrapTeacherMass z h := by
  have hf : ContDiff ℝ 2 (signedMassLossPairNoncentered (n := 3) TrapTeacherAngle TrapTeacherMass) :=
    ParameterCalculus.loss_contDiff_two TrapTeacherAngle TrapTeacherMass
  have H := BoxDirectional.second_line_derivative hf z h
  simp only [seed_first_eq_fderiv] at H
  exact H.unique (SeedDirectional.line_second TrapTeacherAngle TrapTeacherMass z h)

/-- The six standard directions, ordered as three masses then three radian angles. -/
def seedCoordinateVector (i : Fin 6) : (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  (fun j ↦ if Fin.castAdd 3 j=i then 1 else 0,
    fun j ↦ if Fin.natAdd 3 j=i then 1 else 0)

theorem append_seedCoordinateVector (i : Fin 6) :
    Fin.append (seedCoordinateVector i).1 (seedCoordinateVector i).2 =
      fun j ↦ if j=i then 1 else 0 := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [seedCoordinateVector]
  · intro k
    simp [seedCoordinateVector]

theorem seed_hessian_symmetric (s θ : Fin 3 → ℝ) (i j : Fin 6) :
    SeedNumerics.hessian s θ i j = SeedNumerics.hessian s θ j i := by
  refine Fin.addCases (m := 3) (n := 3)
    (motive := fun a ↦ SeedNumerics.hessian s θ a j = SeedNumerics.hessian s θ j a) ?_ ?_ i
  · intro a
    refine Fin.addCases (m := 3) (n := 3)
      (motive := fun b ↦ SeedNumerics.hessian s θ (Fin.castAdd 3 a) b =
        SeedNumerics.hessian s θ b (Fin.castAdd 3 a)) ?_ ?_ j
    · intro b
      simp only [SeedNumerics.hessian, Fin.append_left]
      exact SeedNumerics.J_sub_comm _ _
    · intro b
      simp only [SeedNumerics.hessian, Fin.append_left, Fin.append_right]
  · intro a
    refine Fin.addCases (m := 3) (n := 3)
      (motive := fun b ↦ SeedNumerics.hessian s θ (Fin.natAdd 3 a) b =
        SeedNumerics.hessian s θ b (Fin.natAdd 3 a)) ?_ ?_ j
    · intro b
      simp only [SeedNumerics.hessian, Fin.append_left, Fin.append_right]
    · intro b
      simp only [SeedNumerics.hessian, Fin.append_right]
      by_cases hab : a=b
      · subst b
        rfl
      · simp only [SeedNumerics.angular, hab, Ne.symm hab, if_false]
        rw [SeedNumerics.J2_sub_comm (θ a) (θ b)]
        ring

/-- Symmetry and polarization promote the certified diagonal quadratic form
to the entries of the actual Hessian, not an arbitrary named matrix. -/
theorem seed_hessian_entry (z : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (i j : Fin 6) :
    (fderiv ℝ (fderiv ℝ
      (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass)) z
      (seedCoordinateVector i)) (seedCoordinateVector j) =
        SeedNumerics.hessian z.1 z.2 i j := by
  let H := fderiv ℝ (fderiv ℝ
    (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass)) z
  have hf : ContDiff ℝ 2
      (signedMassLossPairNoncentered (n := 3) TrapTeacherAngle TrapTeacherMass) :=
    ParameterCalculus.loss_contDiff_two TrapTeacherAngle TrapTeacherMass
  have hDf : ContDiff ℝ 1 (fderiv ℝ
      (signedMassLossPairNoncentered (n := 3) TrapTeacherAngle TrapTeacherMass)) :=
    hf.fderiv_right (by norm_num)
  have hsymm : H (seedCoordinateVector i) (seedCoordinateVector j) =
      H (seedCoordinateVector j) (seedCoordinateVector i) :=
    second_derivative_symmetric
      (fun y ↦ (hf.differentiable (by norm_num) y).hasFDerivAt)
      (hDf.differentiable (by norm_num) z).hasFDerivAt _ _
  have hdiag (h : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
      H h h = ∑ a, ∑ b, SeedNumerics.hessian z.1 z.2 a b *
        Fin.append h.1 h.2 a * Fin.append h.1 h.2 b := by
    dsimp only [H]
    rw [seed_second_eq_fderiv]
    simpa only [seed_teacher_angles, TrapTeacherMass] using SeedDirectional.second_eq_hessian z h
  have hi := hdiag (seedCoordinateVector i)
  have hj := hdiag (seedCoordinateVector j)
  have hij := hdiag (seedCoordinateVector i+seedCoordinateVector j)
  have happ : Fin.append (seedCoordinateVector i+seedCoordinateVector j).1
      (seedCoordinateVector i+seedCoordinateVector j).2 =
      fun a ↦ (if a=i then (1 : ℝ) else 0)+(if a=j then 1 else 0) := by
    funext a
    refine Fin.addCases ?_ ?_ a
    · intro a
      simp [seedCoordinateVector]
    · intro a
      simp [seedCoordinateVector]
  rw [happ] at hij
  simp only [map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_add', Pi.add_apply] at hij
  simp only [append_seedCoordinateVector, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hi hj
  simp only [mul_add, add_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hij
  have hnum := seed_hessian_symmetric z.1 z.2 i j
  change H (seedCoordinateVector i) (seedCoordinateVector i) +
    H (seedCoordinateVector j) (seedCoordinateVector i) +
    (H (seedCoordinateVector i) (seedCoordinateVector j) +
      H (seedCoordinateVector j) (seedCoordinateVector j)) = _ at hij
  change H (seedCoordinateVector i) (seedCoordinateVector j) = _
  linarith only [hi, hj, hij, hsymm, hnum]

/-- The interval certificate bounds every actual mass-angle Hessian entry
throughout the same max-norm box, with angles measured in radians. -/
theorem eq_seed_hessian_enclosure
    {z : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hz : z ∈ Metric.closedBall SeedCertificate.seedCentre (1/50000 : ℝ)) :
    ∀ i j : Fin 6,
      |(fderiv ℝ (fderiv ℝ
        (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass)) z
        (seedCoordinateVector i)) (seedCoordinateVector j) -
        (∑ k, SeedNumerics.seedGramWitness k i*SeedNumerics.seedGramWitness k j) -
        (if i=j then (1/10 : ℝ) else 0)| ≤ 1/250 := by
  intro i j
  rw [seed_hessian_entry]
  exact SeedNumerics.seed_hessian_gram_enclosure
    (fun k ↦ (SeedCertificate.coordinate_bounds_of_closedBall hz k).1)
    (fun k ↦ (SeedCertificate.coordinate_bounds_of_closedBall hz k).2) i j

/-- The actual Hessian enclosure and the explicit shifted SOS give the
uniform curvature floor throughout the same certified box. -/
theorem certified_ball_curvature :
    ∀ z ∈ Metric.closedBall SeedCertificate.seedCentre (1 / 50000 : ℝ), ∀ h,
      (1 / 16 : ℝ) * pairEuclideanSq h ≤
        SeedDirectional.second TrapTeacherAngle TrapTeacherMass z h := by
  intro z hz h
  have henc := eq_seed_hessian_enclosure hz
  simp only [seed_hessian_entry] at henc
  have hf := SeedNumerics.gram_lower_bound_of_enclosure
    (SeedNumerics.hessian z.1 z.2) SeedNumerics.seedGramWitness
    (1/10 : ℝ) (1/250 : ℝ) (by norm_num) henc (Fin.append h.1 h.2)
  have hsos := SeedNumerics.eq_seed_hessian_sos (Fin.append h.1 h.2)
  have hnonnegative := hsos.2
  rw [← hsos.1] at hnonnegative
  have hshift :
      (∑ i, ∑ j, ((∑ l, SeedNumerics.seedGramWitness l i*SeedNumerics.seedGramWitness l j) +
        (if i=j then (19/250 : ℝ) else 0) - (if i=j then (1/16 : ℝ) else 0))*
          Fin.append h.1 h.2 i*Fin.append h.1 h.2 j) =
      (∑ i, ∑ j, (∑ l, SeedNumerics.seedGramWitness l i*SeedNumerics.seedGramWitness l j)*
          Fin.append h.1 h.2 i*Fin.append h.1 h.2 j) +
          (27/2000 : ℝ)*(∑ i, Fin.append h.1 h.2 i^2) := by
    rw [hsos.1, SeedNumerics.finite_gram_quadratic_eq_sum_sq]
  rw [hshift] at hnonnegative
  have hfloor : (1/16 : ℝ)*(∑ i, Fin.append h.1 h.2 i^2) ≤
      ∑ i, ∑ j, SeedNumerics.hessian z.1 z.2 i j*Fin.append h.1 h.2 i*Fin.append h.1 h.2 j := by
    norm_num at hf
    linarith only [hf, hnonnegative]
  rw [← SeedDirectional.second_eq_hessian, seed_teacher_angles, appended_square_sum] at hfloor
  exact hfloor

/-- The numerical certificate is only an application of the generic C² box
lemma; the returned minimum is unique on the whole certified box. -/
theorem certified_interior_minimum :
    ∃ z : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      ‖z - SeedCertificate.seedCentre‖ < (1 / 50000 : ℝ) ∧
      (∀ h, SeedDirectional.first TrapTeacherAngle TrapTeacherMass z h = 0) ∧
      IsStrictLocalMinPoint
        (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass) z ∧
      (∀ y ∈ Metric.closedBall SeedCertificate.seedCentre (1 / 50000 : ℝ),
        y ≠ z → signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass z <
          signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass y) := by
  let g : ℝ := Real.sqrt (1 / 10000000000000000000 : ℝ)
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have hgSq : g ^ 2 = (1 / 10000000000000000000 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hf : ContDiff ℝ 2 (signedMassLossPairNoncentered (n := 3) TrapTeacherAngle TrapTeacherMass) :=
    ParameterCalculus.loss_contDiff_two TrapTeacherAngle TrapTeacherMass
  have hcurv (z : (Fin 3 → ℝ) × (Fin 3 → ℝ))
      (hz : z ∈ Metric.closedBall SeedCertificate.seedCentre (1 / 50000 : ℝ))
      (h : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
      (1 / 16 : ℝ) * ((∑ i, h.1 i ^ 2) + ∑ j, h.2 j ^ 2) ≤
        (fderiv ℝ (fderiv ℝ
          (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass)) z h) h := by
    rw [seed_second_eq_fderiv]
    exact certified_ball_curvature z hz h
  have hgrad (h : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
      |fderiv ℝ (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass)
        SeedCertificate.seedCentre h| ≤
        g * Real.sqrt ((∑ i, h.1 i ^ 2) + ∑ j, h.2 j ^ 2) := by
    rw [seed_first_eq_fderiv]
    have H := Real.abs_le_sqrt (certified_center_gradient h)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 10000000000000000000)] at H
    exact H
  obtain ⟨z, hz, hcritical, hstrict, hunique⟩ := box_strict_minimum hf
    (by norm_num : (0 : ℝ) < 1 / 50000) (by norm_num : (0 : ℝ) < 1 / 16)
    hg hcurv hgrad (by nlinarith only [hgSq, hg])
  refine ⟨z, hz, ?_, hstrict, hunique⟩
  intro h
  rw [← seed_first_eq_fderiv, hcritical]
  rfl

/-- The actual same seed obtains spuriousness through the generic positive
affine-loss corollary, not through positivity of a shifted surrogate. -/
theorem certified_seed :
    ∃ z : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      ‖z - SeedCertificate.seedCentre‖ < (1 / 50000 : ℝ) ∧
      (∀ h, SeedDirectional.first TrapTeacherAngle TrapTeacherMass z h = 0) ∧
      IsStrictLocalMinPoint
        (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass) z ∧
      0 < noncenteredExcessLoss z.1 TrapTeacherAngle TrapTeacherMass z.2 ∧
      (∀ i, 0 < z.1 i) ∧
      (1 / 8 : ℝ) < residualCurvatureJ z.1 TrapTeacherAngle TrapTeacherMass z.2 (z.2 2) := by
  obtain ⟨z, hinside, hcritical, hstrict, _hunique⟩ := certified_interior_minimum
  let L : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) → ℝ := fun p =>
    PlainLoss p.1 (fun i => Angle (p.2 i))
      TrapTeacherMass (fun k => Angle (TrapTeacherAngle k))
  have hin (p : (Fin 3 → ℝ) × (Fin 3 → ℝ))
      (hp : p ∈ Metric.closedBall SeedCertificate.seedCentre (1 / 50000 : ℝ)) :
      p ∈ Metric.closedBall SeedCertificate.seedCentre (1 / 1000 : ℝ) :=
    Metric.closedBall_subset_closedBall (by norm_num) hp
  have hpositive (p : (Fin 3 → ℝ) × (Fin 3 → ℝ))
      (hp : p ∈ Metric.closedBall SeedCertificate.seedCentre (1 / 50000 : ℝ)) : 0 < L p := by
    have hteacher : SeedCertificate.teacher = fun k => Angle (TrapTeacherAngle k) := by
      funext k
      fin_cases k <;> simp [SeedCertificate.teacher, SeedCertificate.direction,
        PaperLeanFormalization.Definitions.Angle, TrapTeacherAngle]
    have H := SeedCertificate.seed_ball_positive_gaussian_loss (hin p hp)
    rw [hteacher] at H
    simpa only [L, PlainLoss, TrapTeacherMass, one_mul] using H
  have hmassBox (p : (Fin 3 → ℝ) × (Fin 3 → ℝ))
      (hp : p ∈ Metric.closedBall SeedCertificate.seedCentre (1 / 50000 : ℝ)) :
      ∀ i, 0 < p.1 i :=
    (SeedCertificate.seed_ball_mass_and_angle_separation (hin p hp)).1
  have hnormalized (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
      signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass p =
        (2 * π) * L p + (-teacherSelfEnergyJ TrapTeacherAngle TrapTeacherMass) := by
    simpa only [L, sub_eq_add_neg, teacherSelfEnergyJ, kernelTeacherSelfEnergy] using
      (eq_plain_kernel_normalization p.1 p.2 TrapTeacherMass TrapTeacherAngle).2
  have hexact : ∃ p, L p = 0 := by
    refine ⟨(TrapTeacherMass, TrapTeacherAngle), ?_⟩
    simp [L, PlainLoss]
  have hzbox : z ∈ Metric.closedBall SeedCertificate.seedCentre (1 / 50000 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hinside.le
  obtain ⟨hplainStrict, _hpositive, hmass_of_box, yexact, hyexact, hbetter⟩ :=
    box_minimum_affine_spurious hzbox hstrict (by positivity : 0 < 2 * π)
      hnormalized hpositive hexact
  have hmass := hmass_of_box hmassBox
  have hgauss : 0 < L z := by simpa only [hyexact] using hbetter
  have hexcess : 0 < noncenteredExcessLoss z.1 TrapTeacherAngle TrapTeacherMass z.2 := by
    dsimp only [L] at hgauss
    rw [plain_loss_eq_excess_div] at hgauss
    exact (div_pos_iff.mp hgauss).resolve_right
      (fun h => (not_lt_of_gt (by positivity : (0 : ℝ) < 2 * π)) h.2) |>.1
  have hcrit : IsSignedMassCriticalNoncentered TrapTeacherAngle TrapTeacherMass z.1 z.2 :=
    plain_critical_to_kernel (strict_to_local hplainStrict).fderiv_eq_zero
  have hzero := ((critical_iff_student_double_zeros
    (fun i => ne_of_gt (hmass i))).mp hcrit 2).1
  have hidentity := eq_sine_load_identity z.1 z.2
    TrapTeacherMass TrapTeacherAngle (z.2 2)
  rw [hzero, sub_zero] at hidentity
  refine ⟨z, hinside, hcritical, hstrict, hexcess, hmass, ?_⟩
  rw [hidentity]
  convert SeedCertificate.seed_ball_slot_two_sine_load_positive (hin z hzbox) using 1
  simp [Fin.sum_univ_three, TrapTeacherMass, TrapTeacherAngle]
  ring


end PaperLeanFormalization.Plain



/-!
The width step in `thm:plain-trap`.  Positive residual curvature controls a
nearby split by its mass-weighted merge.  A finite positive partition then
produces any desired width in one step, preserving the network and its loss.
This finite construction is more efficient than nesting a binary split n times.
-/

noncomputable section

namespace PaperLeanFormalization.Plain

open Real Filter Topology PaperLeanFormalization PaperLeanFormalization
open scoped BigOperators

/-- Expanding the two finite squares isolates the residual pairing and
the feature energy of the difference. No kernel sign hypothesis is needed
for the identity itself. -/
theorem loss_difference_expansion {n n' m : ℕ} (K : ℝ → ℝ)
    (c θ : Fin n → ℝ) (c' θ' : Fin n' → ℝ) (β s : Fin m → ℝ) :
    kernelMassLoss K c β s θ - kernelMassLoss K c' β s θ' =
      ((∑ i, c i * kernelResidual K c' β s θ' (θ i)) -
        ∑ j, c' j * kernelResidual K c' β s θ' (θ' j)) +
      (kernelMassLoss K c θ' c' θ - kernelMassLoss K c' θ' c' θ') := by
  unfold kernelMassLoss kernelResidual
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, ← mul_assoc]
  ring


/-- The finite split is merged by adding its masses and taking their
mass-weighted angle. These coordinates and their denominator are explicit. -/
def clusterTotalMass {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) : ℝ :=
  ∑ i : Fin k, p.1 (Fin.castAdd q i)

def clusterFirstMoment {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) : ℝ :=
  ∑ i : Fin k, p.1 (Fin.castAdd q i) * p.2 (Fin.castAdd q i)

def clusterBarycenter {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) : ℝ :=
  clusterFirstMoment p / clusterTotalMass p

/-- Expanding the actual merge angle requires no positive-mass convention;
positivity is used separately for the local Jensen comparison. -/
theorem eq_split_barycenter {k q : ℕ}
    (p : (Fin (k+q) → ℝ) × (Fin (k+q) → ℝ)) :
    clusterBarycenter (k := k) (q := q) p =
      (∑ j : Fin k, p.1 (Fin.castAdd q j) * p.2 (Fin.castAdd q j)) /
        (∑ j : Fin k, p.1 (Fin.castAdd q j)) := by
  rfl

def clusterMergeMass {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) : Fin (1 + q) → ℝ :=
  Fin.append ![clusterTotalMass p] (fun j ↦ p.1 (Fin.natAdd k j))

def clusterMergeAngle {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) : Fin (1 + q) → ℝ :=
  Fin.append ![clusterBarycenter p] (fun j ↦ p.2 (Fin.natAdd k j))

def clusterMerge {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) :
    (Fin (1 + q) → ℝ) × (Fin (1 + q) → ℝ) :=
  (clusterMergeMass p, clusterMergeAngle p)

theorem clusterMergeMass_head {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) :
    clusterMergeMass p (Fin.castAdd q (0 : Fin 1)) = clusterTotalMass p := by
  simp only [clusterMergeMass, Fin.append_left, Matrix.cons_val_zero]

theorem clusterMergeAngle_head {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) :
    clusterMergeAngle p (Fin.castAdd q (0 : Fin 1)) = clusterBarycenter p := by
  simp only [clusterMergeAngle, Fin.append_left, Matrix.cons_val_zero]

theorem clusterMergeMass_tail {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) (j : Fin q) :
    clusterMergeMass p (Fin.natAdd 1 j) = p.1 (Fin.natAdd k j) := by
  simp only [clusterMergeMass, Fin.append_right]

theorem clusterMergeAngle_tail {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) (j : Fin q) :
    clusterMergeAngle p (Fin.natAdd 1 j) = p.2 (Fin.natAdd k j) := by
  simp only [clusterMergeAngle, Fin.append_right]

theorem clusterTotalMass_append {k q : ℕ}
    (w : Fin k → ℝ) (t : ℝ) (b φ : Fin q → ℝ) :
    clusterTotalMass (Fin.append w b, Fin.append (fun _ ↦ t) φ) = ∑ i, w i := by
  simp only [clusterTotalMass, Fin.append_left]

theorem clusterMerge_append {k q : ℕ}
    (w : Fin k → ℝ) (a t : ℝ) (b φ : Fin q → ℝ)
    (hsum : (∑ i, w i) = a) (ha : a ≠ 0) :
    clusterMerge (Fin.append w b, Fin.append (fun _ ↦ t) φ) =
      (Fin.append ![a] b, Fin.append ![t] φ) := by
  unfold clusterMerge clusterMergeMass clusterMergeAngle
  rw [eq_split_barycenter]
  unfold clusterTotalMass
  simp only [Fin.append_left, Fin.append_right, ← Finset.sum_mul, hsum]
  rw [mul_div_cancel_left t ha]

/-- Cancellation of the unchanged tail leaves exactly the child-versus-merge
pairing, for an arbitrary observable `F`. -/
theorem eq_merge_cross_term {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ)) (F : ℝ → ℝ) :
    (∑ i : Fin (k + q), p.1 i * F (p.2 i)) -
      (∑ i : Fin (1 + q), clusterMergeMass p i * F (clusterMergeAngle p i)) =
      (∑ i : Fin k, p.1 (Fin.castAdd q i) * F (p.2 (Fin.castAdd q i))) -
        clusterTotalMass p * F (clusterBarycenter p) := by
  conv_lhs => lhs; rw [Fin.sum_univ_add]
  conv_lhs => rhs; rw [Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [clusterMergeMass_head, clusterMergeAngle_head,
    clusterMergeMass_tail, clusterMergeAngle_tail]
  ring

/-- Splitting a mass at one angle preserves every weighted observable. -/
theorem head_split_weighted_sum {k q : ℕ}
    (w : Fin (k + 1) → ℝ) (a t : ℝ) (b φ : Fin q → ℝ)
    (hsum : (∑ i, w i) = a) (g : ℝ → ℝ) :
    (∑ i, Fin.append w b i * g (Fin.append (fun _ ↦ t) φ i)) =
      ∑ i, Fin.append ![a] b i * g (Fin.append ![t] φ i) := by
  conv_lhs => rw [Fin.sum_univ_add]
  conv_rhs => rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_one, Matrix.cons_val_zero]
  rw [← Finset.sum_mul, hsum]

set_option maxHeartbeats 800000 in
/-- Two uses of the observable identity preserve the student quadratic term;
one use preserves the teacher cross term. This is exact for every kernel. -/
theorem head_split_loss_identity {k q m : ℕ}
    (K : ℝ → ℝ) (w : Fin (k + 1) → ℝ) (a t : ℝ)
    (b φ : Fin q → ℝ) (β s : Fin m → ℝ) (hsum : (∑ i, w i) = a) :
    kernelMassLoss K (Fin.append w b) β s (Fin.append (fun _ ↦ t) φ) =
      kernelMassLoss K (Fin.append ![a] b) β s (Fin.append ![t] φ) := by
  have hobs := head_split_weighted_sum w a t b φ hsum
  let cs := Fin.append w b
  let ts := Fin.append (fun _ : Fin (k + 1) ↦ t) φ
  let cb := Fin.append ![a] b
  let tb := Fin.append ![t] φ
  have hobs' (g : ℝ → ℝ) : (∑ i, cs i * g (ts i)) = ∑ i, cb i * g (tb i) := hobs g
  have hquad : (∑ i, ∑ j, cs i * cs j * K (ts i - ts j)) =
      ∑ i, ∑ j, cb i * cb j * K (tb i - tb j) := by
    calc
      _ = ∑ i, cs i * (∑ j, cs j * K (ts i - ts j)) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ i, cs i * (∑ j, cb j * K (ts i - tb j)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun z ↦ cs i * z) (hobs' (fun x ↦ K (ts i - x)))
      _ = ∑ i, cb i * (∑ j, cb j * K (tb i - tb j)) := hobs' (fun x ↦ ∑ j, cb j * K (x - tb j))
      _ = _ := by simp only [Finset.mul_sum, mul_assoc]
  have hcross : (∑ i, ∑ j, cs i * s j * K (ts i - β j)) =
      ∑ i, ∑ j, cb i * s j * K (tb i - β j) := by
    simpa only [Finset.mul_sum, mul_assoc] using
      hobs' (fun x ↦ ∑ j, s j * K (x - β j))
  exact congrArg₂ (fun x y : ℝ ↦ (1 / 2 : ℝ) * x - y) hquad hcross


/-- Finite relabeling leaves every residual sum unchanged. -/
theorem residual_relabeling {n q m : ℕ}
    (K : ℝ → ℝ) (e : Fin n ≃ Fin q) (c θ : Fin q → ℝ)
    (β s : Fin m → ℝ) (x : ℝ) :
    kernelResidual K (fun i ↦ c (e i)) β s (fun i ↦ θ (e i)) x =
      kernelResidual K c β s θ x := by
  unfold kernelResidual
  rw [Fintype.sum_equiv e (fun i ↦ c (e i) * K (x - θ (e i)))
    (fun i ↦ c i * K (x - θ i)) (fun _ ↦ rfl)]

/-- Jensen's inequality in the unnormalized mass coordinates used here. -/
theorem unnormalized_jensen {ι : Type*} [Fintype ι]
    (w u : ι → ℝ) (A t : ℝ) (D : Set ℝ) (F : ℝ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : 0 < A) (hsum : (∑ i, w i) = A)
    (hmoment : (∑ i, w i * u i) = A * t) (hu : ∀ i, u i ∈ D)
    (hconv : ConvexOn ℝ D F) : A * F t ≤ ∑ i, w i * F (u i) := by
  have hnormalize (g : ι → ℝ) :
      (∑ i, w i / A * g i) = (∑ i, w i * g i) / A := by
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div]
  have hweights : (∑ i, w i / A) = 1 := by
    rw [← Finset.sum_div, hsum, div_self (ne_of_gt hA)]
  have hcenter : (∑ i, w i / A * u i) = t := by
    rw [hnormalize, hmoment]
    exact mul_div_cancel_left t (ne_of_gt hA)
  have hjensen := hconv.map_sum_le
    (fun i _ ↦ div_nonneg (hw i) hA.le) hweights (fun i _ ↦ hu i)
  simp only [smul_eq_mul] at hjensen
  rw [hcenter, hnormalize] at hjensen
  simpa only [mul_comm] using (le_div_iff hA).mp hjensen

/-- The split-loss gap consists of a residual pairing and a nonnegative
quadratic energy. Convexity and the mass-weighted barycenter control the first
term by Jensen's inequality. -/
theorem merge_inequality_from_residual_convexity {k q m : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ))
    (β s : Fin m → ℝ) (D : Set ℝ)
    (hmass : ∀ i : Fin k, 0 ≤ p.1 (Fin.castAdd q i))
    (htotal : 0 < clusterTotalMass p)
    (hangle : ∀ i : Fin k, p.2 (Fin.castAdd q i) ∈ D)
    (hconvex : ConvexOn ℝ D
      (residualPotentialJ (clusterMergeMass p) β s (clusterMergeAngle p))) :
    kernelMassLoss phiCosJ (clusterMergeMass p) β s (clusterMergeAngle p) ≤
      kernelMassLoss phiCosJ p.1 β s p.2 := by
  have hmoment : (∑ i : Fin k, p.1 (Fin.castAdd q i) * p.2 (Fin.castAdd q i)) =
      clusterTotalMass p * clusterBarycenter p := by
    unfold clusterBarycenter clusterFirstMoment
    field_simp [ne_of_gt htotal]
    ring
  have hjensen := unnormalized_jensen
    (fun i : Fin k ↦ p.1 (Fin.castAdd q i))
    (fun i : Fin k ↦ p.2 (Fin.castAdd q i))
    (clusterTotalMass p) (clusterBarycenter p) D
    (residualPotentialJ (clusterMergeMass p) β s (clusterMergeAngle p))
    hmass htotal rfl hmoment hangle hconvex
  have henergy := plain_kernel_exact_fit_floor (clusterMergeAngle p) (clusterMergeMass p) p.1 p.2
  have hexpand := loss_difference_expansion phiCosJ p.1 p.2
    (clusterMergeMass p) (clusterMergeAngle p) β s
  rw [eq_merge_cross_term] at hexpand
  unfold residualPotentialJ at hjensen
  linarith only [hjensen, henergy, hexpand]

/-- A positive continuous function on a product stays positive on one fixed
closed interval in the second variable, uniformly for nearby first variables. -/
theorem positive_on_a_common_interval {X : Type*} [PseudoMetricSpace X]
    {f : X × ℝ → ℝ} {p : X} {t : ℝ}
    (hcont : ContinuousAt f (p, t)) (hpos : 0 < f (p, t)) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ q in nhds p,
      ∀ x ∈ Set.Icc (t - r) (t + r), 0 < f (q, x) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually (Ioi_mem_nhds hpos))
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds p (half_pos hρ)] with q hq
  intro x hx
  apply hball
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · exact (Metric.mem_ball.mp hq).trans (half_lt_self hρ)
  · rw [Real.dist_eq, abs_lt]
    constructor <;> linarith only [hx.1, hx.2, hρ]

/-- The barycentric merge is continuous wherever its total mass is nonzero:
its only denominator is the sum of the child masses. -/
theorem barycentric_merge_continuous {k q : ℕ}
    (p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ))
    (hden : clusterTotalMass p ≠ 0) : ContinuousAt clusterMerge p := by
  have hmass : Continuous (clusterTotalMass (k := k) (q := q)) := by
    unfold clusterTotalMass
    exact continuous_finset_sum _ fun i _ ↦ (continuous_apply _).comp continuous_fst
  have hmoment : Continuous (clusterFirstMoment (k := k) (q := q)) := by
    unfold clusterFirstMoment
    exact continuous_finset_sum _ fun i _ ↦
      ((continuous_apply _).comp continuous_fst).mul ((continuous_apply _).comp continuous_snd)
  have hbary : ContinuousAt (clusterBarycenter (k := k) (q := q)) p :=
    hmoment.continuousAt.div hmass.continuousAt hden
  apply ContinuousAt.prod
  · apply continuousAt_pi.mpr
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · fin_cases j
      simpa only [clusterMergeMass_head] using hmass.continuousAt
    · simpa only [clusterMergeMass_tail] using
        (((continuous_apply (Fin.natAdd k j)).comp continuous_fst).continuousAt :
          ContinuousAt (fun p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ) ↦
            p.1 (Fin.natAdd k j)) p)
  · apply continuousAt_pi.mpr
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · fin_cases j
      simpa only [clusterMergeAngle_head] using hbary
    · simpa only [clusterMergeAngle_tail] using
        (((continuous_apply (Fin.natAdd k j)).comp continuous_snd).continuousAt :
          ContinuousAt (fun p : (Fin (k + q) → ℝ) × (Fin (k + q) → ℝ) ↦
            p.2 (Fin.natAdd k j)) p)

/-- Joint continuity of the curvature follows directly from its finite
kernel formula, in both the configuration and the probe angle. -/
theorem residual_curvature_joint_continuous {n m : ℕ} (β s : Fin m → ℝ) :
    Continuous (fun z : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ ↦
      residualCurvatureJ z.1.1 β s z.1.2 z.2) := by
  exact LocalKernelCalculus.residual_curvature_continuous β s

/-- Finite coordinate continuity and the preceding product lemma produce all
conditions of the split estimate in the same neighborhood. -/
theorem positive_cluster_common_neighborhood {k q m : ℕ}
    (β s : Fin m → ℝ) (w : Fin (k + 1) → ℝ)
    (t : ℝ) (b φ : Fin q → ℝ) (hw : ∀ i, 0 < w i)
    (hcurv : 0 < residualCurvatureJ (Fin.append ![∑ i, w i] b) β s
      (Fin.append ![t] φ) t) :
    ∃ r : ℝ, 0 < r ∧
      ∀ᶠ p in nhds (Fin.append w b, Fin.append (fun _ ↦ t) φ),
        (∀ i : Fin (k + 1), 0 < p.1 (Fin.castAdd q i)) ∧
        0 < clusterTotalMass p ∧
        (∀ i : Fin (k + 1), p.2 (Fin.castAdd q i) ∈ Set.Icc (t - r) (t + r)) ∧
        ∀ x ∈ Set.Icc (t - r) (t + r),
          0 < residualCurvatureJ (clusterMergeMass p) β s (clusterMergeAngle p) x := by
  let P := (Fin ((k + 1) + q) → ℝ) × (Fin ((k + 1) + q) → ℝ)
  let z : P := (Fin.append w b, Fin.append (fun _ ↦ t) φ)
  have htotal : 0 < ∑ i, w i :=
    Finset.sum_pos (fun i _ ↦ hw i) Finset.univ_nonempty
  have hden : clusterTotalMass z ≠ 0 := by
    rw [clusterTotalMass_append]
    exact ne_of_gt htotal
  have hmerge := clusterMerge_append w (∑ i, w i) t b φ rfl (ne_of_gt htotal)
  have hfst : ContinuousAt (fun y : P × ℝ ↦ y.1) (z, t) := continuousAt_fst
  have hmap : ContinuousAt (fun y : P × ℝ ↦ (clusterMerge y.1, y.2)) (z, t) :=
    ((barycentric_merge_continuous z hden).comp_of_eq hfst rfl).prod continuousAt_snd
  have houter : ContinuousAt
      (fun y : ((Fin (1 + q) → ℝ) × (Fin (1 + q) → ℝ)) × ℝ ↦
        residualCurvatureJ y.1.1 β s y.1.2 y.2) (clusterMerge z, t) :=
    (residual_curvature_joint_continuous (n := 1 + q) β s).continuousAt
  have hcontinuous : ContinuousAt (fun y : P × ℝ ↦
      residualCurvatureJ (clusterMergeMass y.1) β s (clusterMergeAngle y.1) y.2) (z, t) := by
    have h := houter.comp_of_eq hmap rfl
    exact h
  have hbase : 0 < residualCurvatureJ (clusterMergeMass z) β s (clusterMergeAngle z) t := by
    change 0 < residualCurvatureJ (clusterMerge z).1 β s (clusterMerge z).2 t
    rw [hmerge]
    exact hcurv
  obtain ⟨r, hr, hcurvature⟩ := positive_on_a_common_interval hcontinuous hbase
  have hcoordinates : ∀ᶠ p : P in nhds z,
      ∀ i : Fin (k + 1), 0 < p.1 (Fin.castAdd q i) ∧
        p.2 (Fin.castAdd q i) ∈ Set.Icc (t - r) (t + r) := by
    rw [eventually_all]
    intro i
    have hc := (((continuous_apply (Fin.castAdd q i)).comp continuous_fst).continuousAt :
      ContinuousAt (fun p : P ↦ p.1 (Fin.castAdd q i)) z)
    have hθ := (((continuous_apply (Fin.castAdd q i)).comp continuous_snd).continuousAt :
      ContinuousAt (fun p : P ↦ p.2 (Fin.castAdd q i)) z)
    have hm : 0 < z.1 (Fin.castAdd q i) := by
      simpa only [z, Fin.append_left] using hw i
    have ha : Set.Icc (t - r) (t + r) ∈ nhds (z.2 (Fin.castAdd q i)) := by
      simp only [z, Fin.append_left]
      exact Icc_mem_nhds (by linarith only [hr]) (by linarith only [hr])
    exact (hc.eventually (Ioi_mem_nhds hm)).and (hθ.eventually ha)
  refine ⟨r, hr, ?_⟩
  filter_upwards [hcoordinates, hcurvature] with p hp hκ
  refine ⟨fun i ↦ (hp i).1, ?_, fun i ↦ (hp i).2, hκ⟩
  exact Finset.sum_pos (fun i _ ↦ (hp i).1) Finset.univ_nonempty

/-- The concrete residual is convex on any interval where its actual second
derivative is nonnegative. The proof uses Mathlib's one-dimensional criterion. -/
theorem residual_convexity_from_curvature {n m : ℕ}
    (c θ : Fin n → ℝ) (β s : Fin m → ℝ) {D : Set ℝ} (hD : Convex ℝ D)
    (hcurv : ∀ x ∈ D, 0 ≤ residualCurvatureJ c β s θ x) :
    ConvexOn ℝ D (residualPotentialJ c β s θ) := by
  have hfirst (x : ℝ) := (LocalKernelCalculus.residual_derivative_chain c β s θ x).1
  have hsecond (x : ℝ) := (LocalKernelCalculus.residual_derivative_chain c β s θ x).2
  have hderiv : deriv (residualPotentialJ c β s θ) =
      fun x ↦ -(massTorqueFieldJ c β s θ x) := funext fun x ↦ (hfirst x).deriv
  have hf : Differentiable ℝ (residualPotentialJ c β s θ) :=
    fun x ↦ (hfirst x).differentiableAt
  have hf' : Differentiable ℝ (deriv (residualPotentialJ c β s θ)) := by
    rw [hderiv]
    exact fun x ↦ (hsecond x).differentiableAt
  apply convexOn_of_deriv2_nonneg' hD hf.differentiableOn hf'.differentiableOn
  intro x hx
  change 0 ≤ deriv (deriv (residualPotentialJ c β s θ)) x
  rw [hderiv]
  change 0 ≤ deriv (fun y ↦ -LocalKernelCalculus.torque c β s θ y) x
  rw [(hsecond x).deriv]
  exact hcurv x hx

/-- The displayed merge inequality is used in an actual neighborhood of the
split point; equality just at the colliding configuration would not suffice. -/
theorem nearby_split_dominates_merge {k q m : ℕ}
    (β s : Fin m → ℝ) (w : Fin (k + 1) → ℝ)
    (t : ℝ) (b φ : Fin q → ℝ) (hw : ∀ i, 0 < w i)
    (hcurv : 0 < residualCurvatureJ (Fin.append ![∑ i, w i] b) β s
      (Fin.append ![t] φ) t) :
    ∀ᶠ p in nhds (Fin.append w b, Fin.append (fun _ ↦ t) φ),
      kernelMassLoss phiCosJ (clusterMergeMass p) β s (clusterMergeAngle p) ≤
        kernelMassLoss phiCosJ p.1 β s p.2 := by
  obtain ⟨r, _hr, hnear⟩ :=
    positive_cluster_common_neighborhood β s w t b φ hw hcurv
  filter_upwards [hnear] with p hp
  apply merge_inequality_from_residual_convexity p β s (Set.Icc (t - r) (t + r))
    (fun i ↦ (hp.1 i).le) hp.2.1 hp.2.2.1
  exact residual_convexity_from_curvature
    (clusterMergeMass p) (clusterMergeAngle p) β s (convex_Icc _ _)
    (fun x hx ↦ (hp.2.2.2 x hx).le)

/-- The actual split-to-merge-to-base comparison, on one common neighborhood. -/
theorem eq_split_local_comparison {k q m : ℕ}
    (β s : Fin m → ℝ) (w : Fin (k+1) → ℝ) (t : ℝ) (b φ : Fin q → ℝ)
    (hw : ∀ i, 0 < w i)
    (hmin : IsLocalMin (fun p : (Fin (1+q) → ℝ) × (Fin (1+q) → ℝ) ↦
      Definitions.PlainLoss p.1 (fun i ↦ Definitions.Angle (p.2 i)) s (fun j ↦ Definitions.Angle (β j)))
      (Fin.append ![∑ i, w i] b, Fin.append ![t] φ))
    (hcurv : 0 < residualCurvatureJ (Fin.append ![∑ i, w i] b) β s
      (Fin.append ![t] φ) t) :
    let split := (Fin.append w b, Fin.append (fun _ ↦ t) φ)
    let base := (Fin.append ![∑ i, w i] b, Fin.append ![t] φ)
    let loss := fun {n : ℕ} (p : (Fin n → ℝ) × (Fin n → ℝ)) ↦
      Definitions.PlainLoss p.1 (fun i ↦ Definitions.Angle (p.2 i)) s (fun j ↦ Definitions.Angle (β j))
    ∀ᶠ p in nhds split,
      loss (clusterMerge (k := k+1) (q := q) p) ≤ loss p ∧
      loss base ≤ loss (clusterMerge (k := k+1) (q := q) p) ∧ loss base = loss split := by
  dsimp only
  let split := (Fin.append w b, Fin.append (fun _ : Fin (k+1) ↦ t) φ)
  let base := (Fin.append ![∑ i, w i] b, Fin.append ![t] φ)
  have htotal : 0 < ∑ i, w i :=
    Finset.sum_pos (fun i _ ↦ hw i) Finset.univ_nonempty
  have hmerge : clusterMerge split = base :=
    clusterMerge_append w (∑ i, w i) t b φ rfl (ne_of_gt htotal)
  have hnonzero : clusterTotalMass split ≠ 0 := by
    dsimp only [split]
    rw [clusterTotalMass_append]
    exact ne_of_gt htotal
  have hcontinuous : Tendsto clusterMerge (nhds split) (nhds base) := by
    rw [← hmerge]
    exact barycentric_merge_continuous split hnonzero
  have hbase := hcontinuous.eventually hmin
  have hsplit := nearby_split_dominates_merge β s w t b φ hw hcurv
  have hequal : signedMassLossPairNoncentered β s split =
      signedMassLossPairNoncentered β s base :=
    head_split_loss_identity phiCosJ w (∑ i, w i) t b φ β s rfl
  have hnorm {n : ℕ} (p : (Fin n → ℝ) × (Fin n → ℝ)) :=
    (eq_plain_kernel_normalization p.1 p.2 s β).2
  have hp : 0 < 2*π := by positivity
  filter_upwards [hbase, hsplit] with p hpbase hpsplit
  refine ⟨?_, hpbase, ?_⟩
  · have h₁ := hnorm (clusterMerge (k := k+1) (q := q) p)
    have h₂ := hnorm p
    change signedMassLossPairNoncentered β s (clusterMerge p) ≤
      signedMassLossPairNoncentered β s p at hpsplit
    nlinarith only [h₁, h₂, hpsplit, hp]
  · have h₁ := hnorm base
    have h₂ := hnorm split
    nlinarith only [h₁, h₂, hequal, hp]

/-- Proof of the stability step: the split loss dominates the merged loss,
which dominates the base minimum; at the base point the two losses agree. -/
theorem positive_curvature_split_is_local_minimum {k q m : ℕ}
    (β s : Fin m → ℝ) (w : Fin (k + 1) → ℝ)
    (t : ℝ) (b φ : Fin q → ℝ)
    (hw : ∀ i, 0 < w i)
    (hmin : IsLocalMin (signedMassLossPairNoncentered β s)
      (Fin.append ![∑ i, w i] b, Fin.append ![t] φ))
    (hcurv : 0 < residualCurvatureJ (Fin.append ![∑ i, w i] b) β s
      (Fin.append ![t] φ) t) :
    IsLocalMin (signedMassLossPairNoncentered β s)
      (Fin.append w b, Fin.append (fun _ ↦ t) φ) := by
  apply plain_minimum_to_kernel
  have hcomparison := eq_split_local_comparison β s w t b φ hw
    (kernel_minimum_to_plain hmin) hcurv
  filter_upwards [hcomparison] with p hp
  rw [← hp.2.2]
  exact hp.2.1.trans hp.1

/-- The explicit equal child masses are positive and sum to the selected mass. -/
theorem equal_child_masses {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∀ _i : Fin (k + 1), 0 < a / (k + 1)) ∧
      (∑ _i : Fin (k + 1), a / (k + 1)) = a := by
  constructor
  · intro _i
    exact div_pos ha (by positivity)
  · rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hden : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hden]
    ring


end PaperLeanFormalization.Plain


/-! A direct constant-loss mass curve for the final paragraph following
`prop:plain-collision-ceiling`.  This argument applies in any dimension and
requires equality of directions, not equality of their projective lines. -/

noncomputable section

namespace PaperLeanFormalization.Plain

open Real Filter Topology MeasureTheory
open PaperLeanFormalization.Definitions PaperLeanFormalization
open scoped BigOperators RealInnerProductSpace

/-- The actual mass curve; directions remain fixed. -/
def collisionMassCurve {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (i j : Fin n) (t : ℝ) : Parameters d n :=
  (c + t • (Pi.single i 1 - Pi.single j 1), w)

/-- Finite-sum mass transfer cancels when the two feature values agree. -/
theorem mass_transfer_weighted_sum {n : ℕ}
    (c f : Fin n → ℝ) {i j : Fin n} (hf : f i = f j) (t : ℝ) :
    (∑ a, (c + t • (Pi.single i 1 - Pi.single j 1) : Fin n → ℝ) a * f a) =
      ∑ a, c a * f a := by
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    add_mul, mul_sub, sub_mul, mul_assoc]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply,
    Finset.mul_sum, hf]

/-- Every real transfer preserves the pointwise response. -/
theorem collision_curve_response {d n : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Vec d) {i j : Fin n}
    (hdir : w i = w j) (t : ℝ) (x : Vec d) :
    (∑ a, (collisionMassCurve c w i j t).1 a * max 0 ⟪w a, x⟫_ℝ) =
      ∑ a, c a * max 0 ⟪w a, x⟫_ℝ := by
  let f : Fin n → ℝ := fun a ↦ max 0 ⟪w a, x⟫_ℝ
  have hfeature : f i = f j := by simp only [f, hdir]
  exact mass_transfer_weighted_sum c f hfeature t

/-- The literal Gaussian integral is constant on the entire curve. -/
theorem collision_curve_loss {d n m : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    {i j : Fin n} (hdir : w i = w j) (t : ℝ) :
    PlainLoss (collisionMassCurve c w i j t).1
      (collisionMassCurve c w i j t).2 s v = PlainLoss c w s v := by
  unfold PlainLoss
  congr 1
  apply integral_congr_ae
  exact Filter.eventually_of_forall fun x ↦ by
    exact congrArg (fun R : ℝ ↦
      (R - ∑ k, s k * max 0 ⟪v k, x⟫_ℝ) ^ 2 * stdGaussianDensity x)
      (collision_curve_response c w hdir t x)

/-- A genuine collision gives an injective continuous curve through the point. -/
theorem collision_curve_geometry {d n : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Vec d) {i j : Fin n} (hij : i ≠ j) :
    Continuous (collisionMassCurve c w i j) ∧
      Function.Injective (collisionMassCurve c w i j) ∧
      collisionMassCurve c w i j 0 = (c, w) ∧
      (∀ t, (collisionMassCurve c w i j t).2 = w) := by
  refine ⟨?_, ?_, ?_, fun _ ↦ rfl⟩
  · unfold collisionMassCurve
    exact (continuous_const.add (continuous_id.smul continuous_const)).prod_mk continuous_const
  · intro t u h
    have hcoordinate := congrArg (fun p : Parameters d n ↦ p.1 i) h
    have hsum : c i + t = c i + u := by
      simpa [collisionMassCurve, Pi.single_apply, hij, hij.symm] using hcoordinate
    exact add_left_cancel hsum
  · simp only [collisionMassCurve, zero_smul, add_zero]

/-- A continuous injective constant-value curve rules out strict minimality
in the exact relative topology of the parameter domain. -/
theorem not_strict_minimum_of_flat_curve {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (S : Set X) (p : X) (g : ℝ → X)
    (hcont : Continuous g) (hinj : Function.Injective g) (hzero : g 0 = p)
    (hmem : ∀ t, g t ∈ S) (hflat : ∀ t, f (g t) = f p) :
    ¬ PaperLeanFormalization.IsStrictLocalMinOn f S p := by
  intro hstrict
  have htendsto : Tendsto g (nhds (0 : ℝ)) (nhdsWithin p S) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hcont.tendsto' 0 p hzero, eventually_of_forall hmem⟩
  have hnear : ∀ᶠ t in nhds (0 : ℝ), g t ≠ p → f p < f (g t) :=
    htendsto.eventually hstrict
  have hpunctured : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ,
      f (g t) = f p ∧ (g t ≠ p → f p < f (g t)) :=
    ((eventually_of_forall hflat).and hnear).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨heq, hlt⟩, ht⟩ := (hpunctured.and self_mem_nhdsWithin).exists
  have hne : g t ≠ p := by
    intro h
    exact ht (hinj (h.trans hzero.symm))
  exact (lt_irrefl (f p)) (heq ▸ hlt hne)

/-- Consequently a colliding direction is flat on the sphere cylinder.
The direction constraint is retained along the entire mass curve. -/
theorem direction_collision_is_flat {d n m : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ a, ‖w a‖ = 1) {i j : Fin n} (hij : i ≠ j) (hdir : w i = w j) :
    ¬ PaperLeanFormalization.IsStrictLocalMinOn
      (fun p : Parameters d n ↦ PlainLoss p.1 p.2 s v)
      {p | ∀ a, ‖p.2 a‖ = 1} (c, w) := by
  obtain ⟨hcont, hinj, hzero, _hangle⟩ := collision_curve_geometry c w hij
  exact not_strict_minimum_of_flat_curve _ _ _ _ hcont hinj hzero
    (fun _ ↦ hw) (collision_curve_loss c w s v hdir)

end PaperLeanFormalization.Plain

noncomputable section
open Real Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace PaperLeanFormalization.Plain
open PaperLeanFormalization.Definitions

/-- Move any selected slot to the head; retain all other slots in their order. -/
def selectedFirstEquiv {n : ℕ} (i : Fin (n + 1)) : Fin (1 + n) ≃ Fin (n + 1) :=
  (finCongr (Nat.add_comm 1 n)).trans
    ((finSuccEquiv n).trans (finSuccEquiv' i).symm)

@[simp] theorem selectedFirstEquiv_head {n : ℕ} (i : Fin (n + 1)) :
    selectedFirstEquiv i (Fin.castAdd n (0 : Fin 1)) = i := by
  change (finSuccEquiv' i).symm ((finSuccEquiv n) 0) = i
  rw [finSuccEquiv_zero, finSuccEquiv'_symm_none]

@[simp] theorem selectedFirstEquiv_tail {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    selectedFirstEquiv i (Fin.natAdd 1 j) = i.succAbove j := by
  have hj : (finCongr (Nat.add_comm 1 n)) (Fin.natAdd 1 j) = j.succ := by
    apply Fin.ext
    simp only [finCongr_apply_coe, Fin.coe_natAdd, Fin.val_succ, Nat.add_comm]
  change (finSuccEquiv' i).symm
    ((finSuccEquiv n) ((finCongr (Nat.add_comm 1 n)) (Fin.natAdd 1 j))) = _
  rw [hj, finSuccEquiv_succ, finSuccEquiv'_symm_some]

theorem selectedFirst_reindex {n : ℕ} {α : Type*} (i : Fin (n + 1))
    (f : Fin (n + 1) → α) :
    (fun j => f (selectedFirstEquiv i j)) =
      Fin.append ![f i] (fun j => f (i.succAbove j)) := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · fin_cases a
    change f (selectedFirstEquiv i (Fin.castAdd n (0 : Fin 1))) = f i
    rw [selectedFirstEquiv_head]
  · simp only [selectedFirstEquiv_tail, Fin.append_right]


/-- The curvature in the local splitting proof is the actual second derivative
of the paper's literal planar residual. -/
theorem planar_plain_residual_second_derivative {n m : ℕ}
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (x : ℝ) :
    deriv (deriv (PlanarResidual .plainRelu c θ s β)) x =
      residualCurvatureJ c β s θ x := by
  have heq : PlanarResidual .plainRelu c θ s β =
      LocalKernelCalculus.residual c β s θ := by
    funext y
    unfold PlanarResidual LocalKernelCalculus.residual
    simp only [plain_kernel_angle]
    rfl
  rw [heq]
  have hfirst : deriv (LocalKernelCalculus.residual c β s θ) =
      fun y => -LocalKernelCalculus.torque c β s θ y :=
    funext fun y => (LocalKernelCalculus.residual_derivative_chain c β s θ y).1.deriv
  rw [hfirst]
  exact (LocalKernelCalculus.residual_derivative_chain c β s θ x).2.deriv

/-- Deleting the selected slot and inserting a partition preserves every
weighted angular observable. No positivity or stationarity is needed here. -/
theorem selected_split_weighted_sum {n k : ℕ}
    (c θ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (a : Fin (k + 1) → ℝ)
    (hsum : (∑ j, a j) = c i) (g : ℝ → ℝ) :
    (∑ j, Fin.append a (fun l => c (i.succAbove l)) j *
      g (Fin.append (fun _ : Fin (k + 1) => θ i) (fun l => θ (i.succAbove l)) j)) =
      ∑ j, c j * g (θ j) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Finset.sum_mul, hsum]
  exact (Fin.sum_univ_succAbove (fun j => c j * g (θ j)) i).symm

theorem selected_split_network {n k : ℕ}
    (c θ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (a : Fin (k + 1) → ℝ)
    (hsum : (∑ j, a j) = c i) (x : Vec 2) :
    Network .plainRelu (Fin.append a (fun l => c (i.succAbove l)))
      (fun j => Angle
        (Fin.append (fun _ : Fin (k + 1) => θ i) (fun l => θ (i.succAbove l)) j)) x =
      Network .plainRelu c (fun j => Angle (θ j)) x := by
  exact selected_split_weighted_sum c θ i a hsum
    (fun t => Feature .plainRelu ⟪Angle t, x⟫_ℝ)

theorem selected_split_loss {n k m : ℕ}
    (c θ : Fin (n + 1) → ℝ) (s β : Fin m → ℝ)
    (i : Fin (n + 1)) (a : Fin (k + 1) → ℝ) (hsum : (∑ j, a j) = c i) :
    PlainLoss (Fin.append a (fun l => c (i.succAbove l)))
      (fun j => Angle
        (Fin.append (fun _ : Fin (k + 1) => θ i) (fun l => θ (i.succAbove l)) j))
      s (fun l => Angle (β l)) =
      PlainLoss c (fun j => Angle (θ j)) s (fun l => Angle (β l)) := by
  unfold PlainLoss
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.eventually_of_forall
  intro x
  have h := selected_split_network c θ i a hsum x
  change (∑ j, Fin.append a (fun l => c (i.succAbove l)) j *
    max 0 ⟪Angle (Fin.append (fun _ : Fin (k + 1) => θ i)
      (fun l => θ (i.succAbove l)) j), x⟫_ℝ) =
      ∑ j, c j * max 0 ⟪Angle (θ j), x⟫_ℝ at h
  exact congrArg (fun R : ℝ =>
    (R - ∑ l, s l * max 0 ⟪Angle (β l), x⟫_ℝ) ^ 2 * stdGaussianDensity x) h

/-- Generic arbitrary-slot splitting of a local minimum. Other student masses
may have either sign; only the selected mass and its children are positive. -/
theorem positive_curvature_selected_split_is_local_minimum {n k m : ℕ}
    (c θ : Fin (n + 1) → ℝ) (s β : Fin m → ℝ)
    (i : Fin (n + 1)) (a : Fin (k + 1) → ℝ)
    (hi : 0 < c i) (ha : ∀ j, 0 < a j) (hsum : (∑ j, a j) = c i)
    (hmin : IsLocalMin (fun p : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      PlainLoss p.1 (fun j => Angle (p.2 j)) s (fun l => Angle (β l))) (c, θ))
    (hcurv : 0 < deriv (deriv (PlanarResidual .plainRelu c θ s β)) (θ i)) :
    IsLocalMin (fun p : (Fin ((k + 1) + n) → ℝ) × (Fin ((k + 1) + n) → ℝ) =>
      PlainLoss p.1 (fun j => Angle (p.2 j)) s (fun l => Angle (β l)))
      (Fin.append a (fun l => c (i.succAbove l)),
        Fin.append (fun _ : Fin (k + 1) => θ i) (fun l => θ (i.succAbove l))) := by
  clear hi; have hkernel := plain_minimum_to_kernel hmin
  have hhead := local_minimum_reindex (kf := phiCosJ) (selectedFirstEquiv i) hkernel
  rw [selectedFirst_reindex i c, selectedFirst_reindex i θ] at hhead
  have hcurvature : residualCurvatureJ
      (Fin.append ![c i] (fun l => c (i.succAbove l))) β s
      (Fin.append ![θ i] (fun l => θ (i.succAbove l))) (θ i) =
      residualCurvatureJ c β s θ (θ i) := by
    rw [← selectedFirst_reindex i c, ← selectedFirst_reindex i θ]
    unfold residualCurvatureJ LocalKernelCalculus.curvature
    congr 1
    exact Equiv.sum_comp (selectedFirstEquiv i)
      (fun j => c j * LocalKernelCalculus.plainCurvature (θ i - θ j))
  have hpositive : 0 < residualCurvatureJ
      (Fin.append ![∑ j, a j] (fun l => c (i.succAbove l))) β s
      (Fin.append ![θ i] (fun l => θ (i.succAbove l))) (θ i) := by
    rw [hsum, hcurvature]
    rwa [planar_plain_residual_second_derivative] at hcurv
  apply kernel_minimum_to_plain
  apply positive_curvature_split_is_local_minimum β s a (θ i)
    (fun l => c (i.succAbove l)) (fun l => θ (i.succAbove l)) ha
  · simpa only [hsum] using hhead
  · exact hpositive

end PaperLeanFormalization.Plain

noncomputable section

open Real Filter Topology MeasureTheory
open PaperLeanFormalization PaperLeanFormalization.Definitions
open scoped BigOperators RealInnerProductSpace

namespace PaperLeanFormalization.Plain

variable {k q m : ℕ}

/-- Transfer mass between the first two children of a split neuron. The
children have one common angle, while the tail is left unchanged. -/
def splitMassTransferCurve (hk : 1 ≤ k) (a : Fin (k + 1) → ℝ)
    (tail : Fin q → ℝ) (t : ℝ) (tailTheta : Fin q → ℝ) :
    ℝ → (Fin (k + 1 + q) → ℝ) × (Fin (k + 1 + q) → ℝ) :=
  fun τ ↦
    (Fin.append a tail + τ •
      (Pi.single (Fin.castAdd q ⟨0, Nat.zero_lt_succ k⟩) 1 -
        Pi.single (Fin.castAdd q ⟨1, by omega (config := {})⟩) 1),
      Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta)

private theorem split_transfer_child_ne (hk : 1 ≤ k) :
    (Fin.castAdd q (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1))) ≠
      Fin.castAdd q (⟨1, by omega (config := {})⟩ : Fin (k + 1)) := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = 1 at hv
  omega (config := {})

private theorem split_transfer_child_direction_eq (hk : 1 ≤ k)
    (t : ℝ) (tailTheta : Fin q → ℝ) :
    Angle (Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta
      (Fin.castAdd q ⟨0, Nat.zero_lt_succ k⟩)) =
    Angle (Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta
      (Fin.castAdd q ⟨1, by omega (config := {})⟩)) := by
  simp only [Fin.append_left]

/-- The split-child mass transfer is an injective continuous curve through
the split parameters; all directions stay fixed for every real transfer. -/
theorem split_mass_transfer_geometry (hk : 1 ≤ k) (a : Fin (k + 1) → ℝ)
    (tail : Fin q → ℝ) (t : ℝ) (tailTheta : Fin q → ℝ) :
    Continuous (splitMassTransferCurve hk a tail t tailTheta) ∧
      Function.Injective (splitMassTransferCurve hk a tail t tailTheta) ∧
      splitMassTransferCurve hk a tail t tailTheta 0 =
        (Fin.append a tail, Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta) ∧
      (∀ τ, (splitMassTransferCurve hk a tail t tailTheta τ).2 =
        Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta) := by
  refine ⟨?_, ?_, ?_, fun _ ↦ rfl⟩
  · unfold splitMassTransferCurve
    exact (continuous_const.add (continuous_id.smul continuous_const)).prod_mk continuous_const
  · intro τ υ h
    have hij := split_transfer_child_ne (q := q) hk
    have hcoordinate := congrArg
      (fun p : (Fin (k + 1 + q) → ℝ) × (Fin (k + 1 + q) → ℝ) ↦
        p.1 (Fin.castAdd q ⟨0, Nat.zero_lt_succ k⟩)) h
    have hsum : a ⟨0, Nat.zero_lt_succ k⟩ + τ =
        a ⟨0, Nat.zero_lt_succ k⟩ + υ := by
      simpa only [splitMassTransferCurve, Pi.add_apply, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
        sub_zero, mul_one, Fin.append_left] using hcoordinate
    exact add_left_cancel hsum
  · simp only [splitMassTransferCurve, zero_smul, add_zero]

/-- This is equality of the actual ReLU networks, pointwise on the whole
ambient plane, not merely equality of a kernel representation. -/
theorem split_mass_transfer_network (hk : 1 ≤ k) (a : Fin (k + 1) → ℝ)
    (tail : Fin q → ℝ) (t : ℝ) (tailTheta : Fin q → ℝ) (τ : ℝ) (x : Vec 2) :
    Network .plainRelu (splitMassTransferCurve hk a tail t tailTheta τ).1
      (fun i ↦ Angle ((splitMassTransferCurve hk a tail t tailTheta τ).2 i)) x =
      Network .plainRelu (Fin.append a tail)
        (fun i ↦ Angle (Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta i)) x := by
  simpa only [Network, Feature, splitMassTransferCurve, collisionMassCurve] using
    collision_curve_response (Fin.append a tail)
      (fun i ↦ Angle (Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta i))
      (split_transfer_child_direction_eq hk t tailTheta) τ x

/-- Consequently the literal Gaussian plain-ReLU loss is constant for all
real transfers, with no integrability, sign, or curvature premise. -/
theorem split_mass_transfer_loss (hk : 1 ≤ k) (a : Fin (k + 1) → ℝ)
    (tail : Fin q → ℝ) (t : ℝ) (tailTheta : Fin q → ℝ)
    (s : Fin m → ℝ) (v : Fin m → Vec 2) (τ : ℝ) :
    PlainLoss (splitMassTransferCurve hk a tail t tailTheta τ).1
      (fun i ↦ Angle ((splitMassTransferCurve hk a tail t tailTheta τ).2 i)) s v =
      PlainLoss (Fin.append a tail)
        (fun i ↦ Angle (Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta i)) s v := by
  simpa only [splitMassTransferCurve, collisionMassCurve] using
    collision_curve_loss (Fin.append a tail)
      (fun i ↦ Angle (Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta i)) s v
      (split_transfer_child_direction_eq hk t tailTheta) τ

/-- A genuine finite split cannot be strict in the same angle-chart
topology as the Gaussian-loss local-minimum statement. Positive curvature
is used by the separate preservation argument, not by this flatness proof. -/
theorem split_children_not_strict (hk : 1 ≤ k) (a : Fin (k + 1) → ℝ)
    (tail : Fin q → ℝ) (t : ℝ) (tailTheta : Fin q → ℝ)
    (s : Fin m → ℝ) (v : Fin m → Vec 2) :
    ¬ IsStrictLocalMinPoint
      (fun p : (Fin (k + 1 + q) → ℝ) × (Fin (k + 1 + q) → ℝ) ↦
        PlainLoss p.1 (fun i ↦ Angle (p.2 i)) s v)
      (Fin.append a tail, Fin.append (fun _ : Fin (k + 1) ↦ t) tailTheta) := by
  obtain ⟨hcont, hinj, hzero, _hfixed⟩ :=
    split_mass_transfer_geometry hk a tail t tailTheta
  have hflat := not_strict_minimum_of_flat_curve
    (fun p : (Fin (k + 1 + q) → ℝ) × (Fin (k + 1 + q) → ℝ) ↦
      PlainLoss p.1 (fun i ↦ Angle (p.2 i)) s v)
    Set.univ _ _ hcont hinj hzero (fun _ ↦ Set.mem_univ _)
    (split_mass_transfer_loss hk a tail t tailTheta s v)
  simpa only [IsStrictLocalMinOn, IsStrictLocalMinPoint, nhdsWithin_univ] using hflat

end PaperLeanFormalization.Plain

noncomputable section
open Real Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace PaperLeanFormalization.Plain
open PaperLeanFormalization.Definitions

/-- Any positive finite partition of one positive-curvature student preserves
the represented network, its Gaussian loss, and local minimality. Two or more
children additionally give a genuine constant-loss mass-transfer curve.
Other student and teacher masses may have either sign. -/
theorem positive_curvature_finite_splitting {n k m : ℕ}
    (c θ : Fin (n + 1) → ℝ) (s β : Fin m → ℝ)
    (i : Fin (n + 1)) (a : Fin (k + 1) → ℝ)
    (hi : 0 < c i) (ha : ∀ j, 0 < a j) (hsum : (∑ j, a j) = c i)
    (hmin : IsLocalMin (fun p : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      PlainLoss p.1 (fun j => Angle (p.2 j)) s (fun l => Angle (β l))) (c, θ))
    (hcurv : 0 < deriv (deriv (PlanarResidual .plainRelu c θ s β)) (θ i)) :
    let c' := Fin.append a (fun l => c (i.succAbove l))
    let θ' := Fin.append (fun _ : Fin (k + 1) => θ i) (fun l => θ (i.succAbove l))
    (∀ x : Vec 2, Network .plainRelu c' (fun j => Angle (θ' j)) x =
      Network .plainRelu c (fun j => Angle (θ j)) x) ∧
    PlainLoss c' (fun j => Angle (θ' j)) s (fun l => Angle (β l)) =
      PlainLoss c (fun j => Angle (θ j)) s (fun l => Angle (β l)) ∧
    IsLocalMin (fun p : (Fin ((k + 1) + n) → ℝ) × (Fin ((k + 1) + n) → ℝ) =>
      PlainLoss p.1 (fun j => Angle (p.2 j)) s (fun l => Angle (β l))) (c', θ') ∧
    (1 ≤ k →
      (∃ γ : ℝ → (Fin ((k + 1) + n) → ℝ) × (Fin ((k + 1) + n) → ℝ),
        Continuous γ ∧ Function.Injective γ ∧ γ 0 = (c', θ') ∧
        (∀ t, (γ t).2 = θ') ∧
        (∀ t x, Network .plainRelu (γ t).1 (fun j => Angle ((γ t).2 j)) x =
          Network .plainRelu c' (fun j => Angle (θ' j)) x) ∧
        (∀ t, PlainLoss (γ t).1 (fun j => Angle ((γ t).2 j)) s
          (fun l => Angle (β l)) =
            PlainLoss c' (fun j => Angle (θ' j)) s (fun l => Angle (β l)))) ∧
      ¬ IsStrictLocalMinPoint
        (fun p : (Fin ((k + 1) + n) → ℝ) × (Fin ((k + 1) + n) → ℝ) =>
          PlainLoss p.1 (fun j => Angle (p.2 j)) s (fun l => Angle (β l))) (c', θ')) := by
  dsimp only
  refine ⟨selected_split_network c θ i a hsum,
    selected_split_loss c θ s β i a hsum,
    positive_curvature_selected_split_is_local_minimum c θ s β i a hi ha hsum hmin hcurv,
    ?_⟩
  intro hk
  have hgeometry := split_mass_transfer_geometry hk a
    (fun l => c (i.succAbove l)) (θ i) (fun l => θ (i.succAbove l))
  constructor
  · refine ⟨splitMassTransferCurve hk a (fun l => c (i.succAbove l))
      (θ i) (fun l => θ (i.succAbove l)), hgeometry.1, hgeometry.2.1,
      hgeometry.2.2.1, hgeometry.2.2.2, ?_, ?_⟩
    · exact split_mass_transfer_network hk a
        (fun l => c (i.succAbove l)) (θ i) (fun l => θ (i.succAbove l))
    · exact split_mass_transfer_loss hk a (fun l => c (i.succAbove l))
        (θ i) (fun l => θ (i.succAbove l)) s (fun l => Angle (β l))
  · exact split_children_not_strict hk a (fun l => c (i.succAbove l))
      (θ i) (fun l => θ (i.succAbove l)) s (fun l => Angle (β l))


end PaperLeanFormalization.Plain

noncomputable section
open Real Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace PaperLeanFormalization.Plain
open PaperLeanFormalization.Definitions

/-- The all-width construction consumes the public arbitrary-slot theorem.
This adapter only reindexes its original head-and-tail coordinates. -/
theorem head_partition_from_public_splitting {k q m : ℕ}
    (β s : Fin m → ℝ) (w : Fin (k + 1) → ℝ)
    (t : ℝ) (b φ : Fin q → ℝ)
    (hw : ∀ i, 0 < w i)
    (hmin : IsLocalMin (signedMassLossPairNoncentered β s)
      (Fin.append ![∑ i, w i] b, Fin.append ![t] φ))
    (hcurv : 0 < residualCurvatureJ (Fin.append ![∑ i, w i] b) β s
      (Fin.append ![t] φ) t) :
    IsLocalMin (signedMassLossPairNoncentered β s)
      (Fin.append w b, Fin.append (fun _ ↦ t) φ) := by
  let e := (selectedFirstEquiv (0 : Fin (q + 1))).symm
  let c : Fin (q + 1) → ℝ := fun i => Fin.append ![∑ j, w j] b (e i)
  let θ : Fin (q + 1) → ℝ := fun i => Fin.append ![t] φ (e i)
  have hezero : e 0 = Fin.castAdd q (0 : Fin 1) := by
    apply (selectedFirstEquiv (0 : Fin (q + 1))).injective
    change selectedFirstEquiv (0 : Fin (q + 1))
      ((selectedFirstEquiv (0 : Fin (q + 1))).symm 0) = _
    rw [Equiv.apply_symm_apply, selectedFirstEquiv_head]
  have hetail (j : Fin q) : e ((0 : Fin (q + 1)).succAbove j) = Fin.natAdd 1 j := by
    apply (selectedFirstEquiv (0 : Fin (q + 1))).injective
    change selectedFirstEquiv (0 : Fin (q + 1))
      ((selectedFirstEquiv (0 : Fin (q + 1))).symm _) = _
    rw [Equiv.apply_symm_apply, selectedFirstEquiv_tail]
  have hc : c 0 = ∑ j, w j := by
    simp only [c, hezero, Fin.append_left, Matrix.cons_val_zero]
  have hθ : θ 0 = t := by
    simp only [θ, hezero, Fin.append_left, Matrix.cons_val_zero]
  have hctail : (fun j => c ((0 : Fin (q + 1)).succAbove j)) = b := by
    funext j
    simp only [c, hetail, Fin.append_right]
  have hθtail : (fun j => θ ((0 : Fin (q + 1)).succAbove j)) = φ := by
    funext j
    simp only [θ, hetail, Fin.append_right]
  have hlocal : IsLocalMin (signedMassLossPairNoncentered β s) (c, θ) :=
    local_minimum_reindex (kf := phiCosJ) e hmin
  have hderiv : 0 < deriv (deriv (PlanarResidual .plainRelu c θ s β)) (θ 0) := by
    rw [planar_plain_residual_second_derivative, hθ]
    have hreindex : residualCurvatureJ c β s θ t =
        residualCurvatureJ (Fin.append ![∑ j, w j] b) β s
          (Fin.append ![t] φ) t := by
      unfold residualCurvatureJ LocalKernelCalculus.curvature
      congr 1
      exact Equiv.sum_comp e (fun j => Fin.append ![∑ l, w l] b j *
        LocalKernelCalculus.plainCurvature (t - Fin.append ![t] φ j))
    rwa [hreindex]
  have hi : 0 < c 0 := by
    rw [hc]
    exact Finset.sum_pos (fun j _ => hw j) Finset.univ_nonempty
  have hpublic := positive_curvature_finite_splitting c θ s β 0 w hi hw hc.symm
    (kernel_minimum_to_plain hlocal) hderiv
  have hsplit := hpublic.2.2.1
  rw [hctail, hθtail, hθ] at hsplit
  exact plain_minimum_to_kernel hsplit


end PaperLeanFormalization.Plain

namespace PaperLeanFormalization.Plain
open Real Set Filter
open scoped BigOperators Topology RealInnerProductSpace
open PaperLeanFormalization.Definitions

/-- Split the first student directly into equally weighted children.  This
constructs each requested width explicitly, with no nested binary induction. -/
theorem all_widths_from_a_head_seed {q m : ℕ}
    (β s : Fin m → ℝ) (a t : ℝ) (b φ : Fin q → ℝ)
    (ha : 0 < a) (hb : ∀ i, 0 < b i)
    (hmin : IsLocalMin (signedMassLossPairNoncentered β s)
      (Fin.append ![a] b, Fin.append ![t] φ))
    (hcurv : 0 < residualCurvatureJ (Fin.append ![a] b) β s
      (Fin.append ![t] φ) t) (n : ℕ) (hn : 1 + q ≤ n) :
    ∃ c θ : Fin n → ℝ,
      (∀ i, 0 < c i) ∧
      IsLocalMin (signedMassLossPairNoncentered β s) (c, θ) ∧
      noncenteredExcessLoss c β s θ =
        noncenteredExcessLoss (Fin.append ![a] b) β s (Fin.append ![t] φ) ∧
      (1 + q < n → ∃ i j : Fin n, i ≠ j ∧ θ i = θ j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  let w : Fin (k + 1) → ℝ := fun _ ↦ a / (k + 1)
  have hw := equal_child_masses ha k
  let cS := Fin.append w b
  let θS := Fin.append (fun _ : Fin (k + 1) ↦ t) φ
  have hminS : IsLocalMin (signedMassLossPairNoncentered β s) (cS, θS) := by
    apply head_partition_from_public_splitting β s w t b φ hw.1
    · simpa only [hw.2] using hmin
    · simpa only [hw.2] using hcurv
  let e : Fin ((1 + q) + k) ≃ Fin ((k + 1) + q) := finCongr (by omega (config := {}))
  let c : Fin ((1 + q) + k) → ℝ := fun i ↦ cS (e i)
  let θ : Fin ((1 + q) + k) → ℝ := fun i ↦ θS (e i)
  have hlocal : IsLocalMin (signedMassLossPairNoncentered β s) (c, θ) :=
    local_minimum_reindex (kf := phiCosJ) e hminS
  have hmass : ∀ i, 0 < c i := by
    intro i
    change 0 < Fin.append w b (e i)
    exact Fin.addCases (fun j ↦ by simpa only [Fin.append_left] using hw.1 j)
      (fun j ↦ by simpa only [Fin.append_right] using hb j) (e i)
  have hkernel : kernelMassLoss phiCosJ c β s θ =
      kernelMassLoss phiCosJ (Fin.append ![a] b) β s (Fin.append ![t] φ) := by
    rw [show kernelMassLoss phiCosJ c β s θ = kernelMassLoss phiCosJ cS β s θS from
      kernel_loss_reindex (kf := phiCosJ) e cS θS β s]
    exact head_split_loss_identity phiCosJ w a t b φ β s hw.2
  refine ⟨c, θ, hmass, hlocal, ?_, ?_⟩
  · exact congrArg (fun L : ℝ ↦ L + teacherSelfEnergyJ β s) hkernel
  · intro hwide
    have hk : 1 < k + 1 := by omega (config := {})
    let i : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
    let j : Fin (k + 1) := ⟨1, hk⟩
    refine ⟨e.symm (Fin.castAdd q i), e.symm (Fin.castAdd q j), ?_, ?_⟩
    · intro h
      have hcast := e.symm.injective h
      have hv := congrArg Fin.val hcast
      change 0 = 1 at hv
      omega (config := {})
    · dsimp only [θ]
      rw [e.apply_symm_apply, e.apply_symm_apply]
      simp only [θS, Fin.append_left]

end PaperLeanFormalization.Plain

namespace PaperLeanFormalization.Plain

open Real PaperLeanFormalization PaperLeanFormalization
open PaperLeanFormalization.Definitions

/-- Reverse the three seed slots so its certified positive-curvature student
is the head of the explicit finite split construction. -/
theorem certified_seed_at_every_width (n : ℕ) (hn : 3 ≤ n) :
    ∃ c θ : Fin n → ℝ,
      (∀ i, 0 < c i) ∧
      IsLocalMin (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass) (c, θ) ∧
      0 < noncenteredExcessLoss c TrapTeacherAngle TrapTeacherMass θ ∧
      (3 < n → ∃ i j : Fin n, i ≠ j ∧ θ i = θ j) := by
  obtain ⟨z, _hinside, _hcritical, hstrict, hexcess, hmass, hcurv⟩ := certified_seed
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
  have hreverse (u : Fin 3 → ℝ) :
      Fin.append ![u 2] ![u 1, u 0] = fun i ↦ u (e i) := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · fin_cases j
      rw [Fin.append_left]
      change u 2 = u (e 0)
      rw [show e 0 = 2 from Equiv.swap_apply_left _ _]
    · fin_cases j
      · rw [Fin.append_right]
        change u 1 = u (e 1)
        rw [show e 1 = 1 from Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      · rw [Fin.append_right]
        change u 0 = u (e 2)
        rw [show e 2 = 0 from Equiv.swap_apply_right _ _]
  have hminR : IsLocalMin (signedMassLossPairNoncentered TrapTeacherAngle TrapTeacherMass)
      (Fin.append ![z.1 2] ![z.1 1, z.1 0],
        Fin.append ![z.2 2] ![z.2 1, z.2 0]) := by
    rw [hreverse, hreverse]
    exact local_minimum_reindex (kf := phiCosJ) e (strict_to_local hstrict)
  have hcurvR : 0 < residualCurvatureJ
      (Fin.append ![z.1 2] ![z.1 1, z.1 0]) TrapTeacherAngle TrapTeacherMass
      (Fin.append ![z.2 2] ![z.2 1, z.2 0]) (z.2 2) := by
    rw [hreverse, hreverse]
    change 0 < kernelResidual phiCosJSecondDeriv
      (fun i ↦ z.1 (e i)) TrapTeacherAngle TrapTeacherMass
      (fun i ↦ z.2 (e i)) (z.2 2)
    rw [residual_relabeling phiCosJSecondDeriv e]
    change (1 / 8 : ℝ) < kernelResidual phiCosJSecondDeriv
      z.1 TrapTeacherAngle TrapTeacherMass z.2 (z.2 2) at hcurv
    linarith only [hcurv]
  have htail : ∀ i : Fin 2, 0 < (![z.1 1, z.1 0] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact hmass 1
    · exact hmass 0
  obtain ⟨c, θ, hc, hlocal, heq, hcollision⟩ :=
    all_widths_from_a_head_seed TrapTeacherAngle TrapTeacherMass (z.1 2) (z.2 2)
      ![z.1 1, z.1 0] ![z.2 1, z.2 0] (hmass 2) htail hminR hcurvR n hn
  have hseedEq : noncenteredExcessLoss
      (Fin.append ![z.1 2] ![z.1 1, z.1 0]) TrapTeacherAngle TrapTeacherMass
      (Fin.append ![z.2 2] ![z.2 1, z.2 0]) =
      noncenteredExcessLoss z.1 TrapTeacherAngle TrapTeacherMass z.2 := by
    rw [hreverse, hreverse]
    exact congrArg (fun L : ℝ ↦ L + teacherSelfEnergyJ TrapTeacherAngle TrapTeacherMass)
      (kernel_loss_reindex (kf := phiCosJ) e z.1 z.2
        TrapTeacherAngle TrapTeacherMass)
  refine ⟨c, θ, hc, hlocal, ?_, hcollision⟩
  rw [heq, hseedEq]
  exact hexcess

/-- Padding the teacher by zero masses gives an exact fit in every wider
parameter space. Thus positive loss really is nonglobal at the same width. -/
theorem padded_teacher_exact_fit {n m : ℕ} (hn : m ≤ n) (s β : Fin m → ℝ) :
    ∃ (c : Fin n → ℝ) (w : Fin n → Vec 2),
      (∀ i, ‖w i‖ = 1) ∧ PlainLoss c w s (fun k ↦ Angle (β k)) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  let θ : Fin (m + k) → ℝ := Fin.append β (fun _ ↦ 0)
  refine ⟨Fin.append s (fun _ : Fin k ↦ 0), fun i ↦ Angle (θ i),
    fun i ↦ Preliminaries.angle_unit (θ i), ?_⟩
  unfold PlainLoss
  have hresponse (x : Vec 2) :
      (∑ i : Fin (m + k), Fin.append s (fun _ : Fin k ↦ 0) i *
        max 0 ⟪Angle (θ i), x⟫_ℝ) =
      ∑ j : Fin m, s j * max 0 ⟪Angle (β j), x⟫_ℝ := by
    rw [Fin.sum_univ_add]
    simp only [θ, Fin.append_left, Fin.append_right, zero_mul,
      Finset.sum_const_zero, add_zero]
  simp only [hresponse, sub_self, zero_pow (by norm_num : 0 < (2 : ℕ)),
    zero_mul, MeasureTheory.integral_zero, mul_zero]

/-- `thm:plain-trap`, local existence at every width, obtained from the new
certificate interpretation and explicit finite split proof above. -/
theorem thm_plain_trap {n : ℕ} (hn : 3 ≤ n) :
    ∃ c : Fin n → ℝ, ∃ w : Fin n → Vec 2,
      (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < c i) ∧
      IsLocalMinOn (fun p : Parameters 2 n ↦
        PlainLoss p.1 p.2 TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (c, w) ∧
      0 < PlainLoss c w TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)) := by
  obtain ⟨c, θ, hc, hlocal, hexcess, _hcollision⟩ := certified_seed_at_every_width n hn
  have hchart := kernel_minimum_to_plain hlocal
  have hsphere := CircleChart.local_minimum_to_sphere
    (fun c w ↦ PlainLoss c w TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k))) hchart
  refine ⟨c, fun i ↦ Angle (θ i), fun i ↦ Preliminaries.angle_unit (θ i), hc, ?_, ?_⟩
  · exact hsphere
  · rw [plain_loss_eq_excess_div]
    exact div_pos hexcess
      (mul_pos (by norm_num) Real.pi_pos)

/-- The positive-loss minimum is genuinely spurious in its own parameter
space: the zero-padded teacher from `padded_teacher_exact_fit` is an explicit
competitor with strictly smaller loss. This is the last step of the sketch,
not a comparison with an unavailable wider network. -/
theorem thm_plain_trap_spurious {n : ℕ} (hn : 3 ≤ n) :
    ∃ c : Fin n → ℝ, ∃ w : Fin n → Vec 2,
      (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < c i) ∧
      IsLocalMinOn (fun p : Parameters 2 n ↦
        PlainLoss p.1 p.2 TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (c, w) ∧
      ∃ c₀ : Fin n → ℝ, ∃ w₀ : Fin n → Vec 2,
        (∀ i, ‖w₀ i‖ = 1) ∧
        PlainLoss c₀ w₀ TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)) <
          PlainLoss c w TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)) := by
  obtain ⟨c, w, hw, hc, hmin, hpos⟩ := thm_plain_trap hn
  obtain ⟨c₀, w₀, hw₀, hzero⟩ := padded_teacher_exact_fit hn
    TrapTeacherMass TrapTeacherAngle
  exact ⟨c, w, hw, hc, hmin, c₀, w₀, hw₀, by rw [hzero]; exact hpos⟩

/-- Width three uses the genuine critical strict seed, in the same unit-circle
topology as the theorem statement. -/
theorem thm_plain_trap_strict :
    ∃ c : Fin 3 → ℝ, ∃ w : Fin 3 → Vec 2,
      (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < c i) ∧
      PaperLeanFormalization.IsStrictLocalMinOn
        (fun p : Parameters 2 3 ↦
          PlainLoss p.1 p.2 TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (c, w) ∧
      0 < PlainLoss c w TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)) := by
  obtain ⟨z, _hinside, _hcritical, hstrict, hexcess, hc, _hcurv⟩ := certified_seed
  have hchart := kernel_strict_minimum_to_plain (c := z.1) (θ := z.2) hstrict
  have hsphere := CircleChart.strict_minimum_to_sphere
    (fun c w ↦ PlainLoss c w TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)))
    (c := z.1) (theta := z.2) (by simpa only [Prod.eta] using hchart)
  refine ⟨z.1, fun i ↦ Angle (z.2 i), fun i ↦ Preliminaries.angle_unit (z.2 i), hc, ?_, ?_⟩
  · exact hsphere
  · rw [plain_loss_eq_excess_div]
    exact div_pos hexcess
      (mul_pos (by norm_num) Real.pi_pos)

/-- Every wider constructed witness has an actual colliding pair, yielding
the constant-loss curve proved locally above and therefore flatness. -/
theorem thm_plain_trap_flat {n : ℕ} (hn : 3 < n) :
    ∃ c : Fin n → ℝ, ∃ w : Fin n → Vec 2,
      (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < c i) ∧
      IsLocalMinOn (fun p : Parameters 2 n ↦
        PlainLoss p.1 p.2 TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (c, w) ∧
      0 < PlainLoss c w TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)) ∧
      ¬ PaperLeanFormalization.IsStrictLocalMinOn
        (fun p : Parameters 2 n ↦
          PlainLoss p.1 p.2 TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (c, w) := by
  obtain ⟨c, θ, hc, hlocal, hexcess, hcollision⟩ := certified_seed_at_every_width n hn.le
  obtain ⟨i, j, hij, hdir⟩ := hcollision hn
  have hchart := kernel_minimum_to_plain hlocal
  have hsphere := CircleChart.local_minimum_to_sphere
    (fun c w ↦ PlainLoss c w TrapTeacherMass (fun k ↦ Angle (TrapTeacherAngle k))) hchart
  refine ⟨c, fun a ↦ Angle (θ a), fun a ↦ Preliminaries.angle_unit (θ a), hc, ?_, ?_, ?_⟩
  · exact hsphere
  · rw [plain_loss_eq_excess_div]
    exact div_pos hexcess
      (mul_pos (by norm_num) Real.pi_pos)
  · exact direction_collision_is_flat c (fun a ↦ Angle (θ a)) TrapTeacherMass
      (fun k ↦ Angle (TrapTeacherAngle k)) (fun a ↦ Preliminaries.angle_unit (θ a)) hij
      (congrArg Angle hdir)

end PaperLeanFormalization.Plain

/-!
The direction census of the paper, including configurations which already
have collisions.  First merge equal oriented directions, preserving the entire
residual and torque fields.  Positivity then lets the distinct-student width
ceiling apply to the merged configuration.  The quotient is modulo `2π`.
-/

open Real
open scoped BigOperators

noncomputable section

namespace PaperLeanFormalization.Plain

open PaperLeanFormalization
open PaperLeanFormalization

variable {n m : ℕ}

local instance : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _

/-- Canonical representative of an oriented direction in `[0, 2π)`. -/
def orientationRepresentative (x : ℝ) : ℝ :=
  x - (⌊x / (2 * π)⌋ : ℝ) * (2 * π)

theorem orientationRepresentative_mem (x : ℝ) :
    0 ≤ orientationRepresentative x ∧ orientationRepresentative x < 2 * π := by
  have hp : 0 < 2 * π := mul_pos (by norm_num) Real.pi_pos
  have hlo := (le_div_iff hp).mp (Int.floor_le (x / (2 * π)))
  have hhi := (div_lt_iff hp).mp (Int.lt_floor_add_one (x / (2 * π)))
  unfold orientationRepresentative
  constructor <;> nlinarith only [hlo, hhi]

/-- Every full-turn periodic observable is unchanged by reducing its right
argument to the canonical orientation. -/
theorem periodic_sub_orientationRepresentative (f : ℝ → ℝ)
    (hf : ∀ x (k : ℤ), f (x + (k : ℝ) * (2 * π)) = f x) (x y : ℝ) :
    f (x - orientationRepresentative y) = f (x - y) := by
  have harg : x - orientationRepresentative y =
      (x - y) + (⌊y / (2 * π)⌋ : ℝ) * (2 * π) := by
    unfold orientationRepresentative
    ring
  rw [harg, hf]

theorem periodic_orientationRepresentative_sub (f : ℝ → ℝ)
    (hf : ∀ x (k : ℤ), f (x + (k : ℝ) * (2 * π)) = f x) (x y : ℝ) :
    f (orientationRepresentative x - y) = f (x - y) := by
  have harg : orientationRepresentative x - y =
      (x - y) + ((-⌊x / (2 * π)⌋ : ℤ) : ℝ) * (2 * π) := by
    unfold orientationRepresentative
    push_cast
    ring
  rw [harg, hf]

theorem couplingHJ_full_turn (x : ℝ) (k : ℤ) :
    couplingHJ (x + (k : ℝ) * (2 * π)) = couplingHJ x := by
  simp only [couplingHJ, couplingH, Real.sin_add_int_mul_two_pi,
    Real.cos_add_int_mul_two_pi]

/-- Number of occupied oriented directions, computed before merging masses. -/
def orientedAggregateWidth (theta : Fin n → ℝ) : ℕ :=
  SortedFibres.count (fun i => orientationRepresentative (theta i))

/-- Increasing enumeration of occupied oriented representatives. -/
def orientedAggregateAngle (theta : Fin n → ℝ) :
    Fin (orientedAggregateWidth theta) → ℝ :=
  SortedFibres.angle (fun i => orientationRepresentative (theta i))

/-- Total student mass on each occupied oriented direction. -/
def orientedAggregateMass (c theta : Fin n → ℝ) :
    Fin (orientedAggregateWidth theta) → ℝ :=
  SortedFibres.mass (fun i => orientationRepresentative (theta i)) c

theorem orientedAggregateMass_pos (c theta : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) : ∀ j, 0 < orientedAggregateMass c theta j :=
  SortedFibres.mass_positive (fun i => orientationRepresentative (theta i)) c hc

theorem exists_raw_on_orientedAggregateAngle (theta : Fin n → ℝ)
    (j : Fin (orientedAggregateWidth theta)) :
    ∃ i, orientationRepresentative (theta i) = orientedAggregateAngle theta j :=
  SortedFibres.angle_has_preimage (fun i => orientationRepresentative (theta i)) j

/-- Fibre aggregation preserves any full-turn periodic kernel sum. -/
theorem periodic_weighted_sum_aggregate (f : ℝ → ℝ)
    (hf : ∀ x (k : ℤ), f (x + (k : ℝ) * (2 * π)) = f x)
    (c theta : Fin n → ℝ) (x : ℝ) :
    (∑ i, c i * f (x - theta i)) =
      ∑ j, orientedAggregateMass c theta j * f (x - orientedAggregateAngle theta j) := by
  calc
    (∑ i, c i * f (x - theta i)) =
        ∑ i, c i * f (x - orientationRepresentative (theta i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [periodic_sub_orientationRepresentative f hf]
    _ = _ := SortedFibres.weighted_observable
      (fun i => orientationRepresentative (theta i)) c (fun y => f (x - y))

theorem residual_preserved_by_oriented_aggregation (c theta : Fin n → ℝ)
    (beta s : Fin m → ℝ) (x : ℝ) :
    residualPotentialJ (orientedAggregateMass c theta) beta s
      (orientedAggregateAngle theta) x = residualPotentialJ c beta s theta x := by
  unfold residualPotentialJ kernelResidual
  rw [periodic_weighted_sum_aggregate phiCosJ plain_kernel_full_turn c theta]

theorem torque_preserved_by_oriented_aggregation (c theta : Fin n → ℝ)
    (beta s : Fin m → ℝ) (x : ℝ) :
    massTorqueFieldJ (orientedAggregateMass c theta) beta s
      (orientedAggregateAngle theta) x = massTorqueFieldJ c beta s theta x := by
  unfold massTorqueFieldJ kernelTorqueField
  rw [periodic_weighted_sum_aggregate couplingHJ couplingHJ_full_turn c theta]

/-- Reducing the probe angle also preserves the full residual. -/
theorem residual_orientationRepresentative (c theta : Fin n → ℝ)
    (beta s : Fin m → ℝ) (x : ℝ) :
    residualPotentialJ c beta s theta (orientationRepresentative x) =
      residualPotentialJ c beta s theta x := by
  simp only [residualPotentialJ, kernelResidual,
    periodic_orientationRepresentative_sub phiCosJ plain_kernel_full_turn]

theorem torque_orientationRepresentative (c theta : Fin n → ℝ)
    (beta s : Fin m → ℝ) (x : ℝ) :
    massTorqueFieldJ c beta s theta (orientationRepresentative x) =
      massTorqueFieldJ c beta s theta x := by
  simp only [massTorqueFieldJ, kernelTorqueField,
    periodic_orientationRepresentative_sub couplingHJ couplingHJ_full_turn]

/-- The merged positive configuration has the same double zeros and remains
critical in all of its mass and angle variables. -/
theorem criticality_preserved_by_oriented_aggregation
    {c theta : Fin n → ℝ} {beta s : Fin m → ℝ}
    (hcrit : IsSignedMassCriticalNoncentered beta s c theta)
    (hc : ∀ i, 0 < c i) :
    IsSignedMassCriticalNoncentered beta s
      (orientedAggregateMass c theta) (orientedAggregateAngle theta) := by
  have hraw := (critical_iff_student_double_zeros (fun i => ne_of_gt (hc i))).mp hcrit
  apply (critical_iff_student_double_zeros
    (fun j => ne_of_gt (orientedAggregateMass_pos c theta hc j))).mpr
  intro j
  obtain ⟨i, hi⟩ := exists_raw_on_orientedAggregateAngle theta j
  rw [residual_preserved_by_oriented_aggregation,
    torque_preserved_by_oriented_aggregation, ← hi,
    residual_orientationRepresentative, torque_orientationRepresentative]
  exact hraw i

/-- Assemble the local analytic census on a sorted full-turn tour.
Width zero is empty; width one uses its mass equation rather than the
automatically vanishing full-circle moment. -/
theorem sorted_positive_critical_width {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hcrit : IsSignedMassCriticalNoncentered β s c θ) (hc : ∀ i, 0 < c i)
    (hθ : StrictMono θ) (hwindow : ∀ i, 0 ≤ θ i ∧ θ i < 2 * π) :
    n ≤ 2 * m := by
  by_cases hn : 2 ≤ n
  · have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
    apply PlainTourCount.direct_sine_moment_tour_count c s β (closeTour θ hn0)
      (closeTour_strictMono θ hn0 hθ hwindow) (closeTour_last θ hn0) hn hc
    intro i a
    simpa only [closeTour_castSucc] using eq_gap_orthogonality hn0 hcrit hc i a
  · have hn1 : n ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)
    rcases Nat.eq_zero_or_pos n with hzero | hpos
    · subst n
      exact Nat.zero_le _
    · have hone : n = 1 := Nat.le_antisymm hn1 hpos
      subst n
      have hm : 0 < m := one_student_requires_teacher hcrit (hc 0)
      exact le_trans (show 1 ≤ m from hm) (by rw [two_mul]; exact Nat.le_add_right m m)

/-- The oriented fibre aggregate is already an increasing enumeration.
The new gap equations and teacher-charge census apply directly, so this step
uses no old width-ceiling or ordering theorem. -/
theorem critical_oriented_aggregate_width
    {c theta : Fin n → ℝ} {beta s : Fin m → ℝ}
    (hcrit : IsSignedMassCriticalNoncentered beta s c theta)
    (hc : ∀ i, 0 < c i) : orientedAggregateWidth theta ≤ 2 * m := by
  apply sorted_positive_critical_width
    (criticality_preserved_by_oriented_aggregation hcrit hc)
    (orientedAggregateMass_pos c theta hc)
  · exact SortedFibres.angle_strictMono _
  · intro j
    obtain ⟨i, hi⟩ := exists_raw_on_orientedAggregateAngle theta j
    rw [← hi]
    exact orientationRepresentative_mem _


theorem angleVec_orientationRepresentative (x : ℝ) :
    Definitions.Angle (orientationRepresentative x) = Definitions.Angle x := by
  have harg : orientationRepresentative x =
      x + ((-⌊x / (2 * π)⌋ : ℤ) : ℝ) * (2 * π) := by
    unfold orientationRepresentative
    push_cast
    ring
  unfold Definitions.Angle
  rw [harg, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- Every positive critical plain-ReLU configuration has at most `2m`
distinct oriented directions, whether or not some student slots coincide.
No sign or separation assumption is needed for the teacher. -/
theorem critical_oriented_direction_count
    {c theta : Fin n → ℝ} {beta s : Fin m → ℝ}
    (hcrit : IsSignedMassCriticalNoncentered beta s c theta)
    (hc : ∀ i, 0 < c i) :
    (Finset.univ.image (fun i => Definitions.Angle (theta i))).card ≤ 2 * m := by
  classical
  have himage : Finset.univ.image (fun i => Definitions.Angle (theta i)) =
      (Finset.univ.image (fun i => orientationRepresentative (theta i))).image Definitions.Angle := by
    rw [Finset.image_image]
    congr 1
    funext i
    exact (angleVec_orientationRepresentative (theta i)).symm
  rw [himage]
  exact Finset.card_image_le.trans (critical_oriented_aggregate_width hcrit hc)

/-- `prop:plain-collision-ceiling` for the inspectable literal loss. -/
theorem prop_plain_collision_ceiling
    {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hc : ∀ i, 0 < c i)
    (hcrit : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      PaperLeanFormalization.Definitions.PlainLoss p.1
        (fun i ↦ PaperLeanFormalization.Definitions.Angle (p.2 i)) s
        (fun k ↦ PaperLeanFormalization.Definitions.Angle (β k))) (c, θ) = 0) :
    (Finset.univ.image (fun i ↦ PaperLeanFormalization.Definitions.Angle (θ i))).card ≤
      2 * m := by
  exact critical_oriented_direction_count (plain_critical_to_kernel hcrit) hc

/-- The difference between an antipodal split and its doubled teacher is the
negative first moment. This identity is pointwise and distribution-free. -/
theorem antipodal_sum_identity {m : ℕ} (z : Fin m → ℝ) :
    (∑ i, max 0 (z i)) + (∑ i, max 0 (-z i)) -
      (∑ i, 2 * max 0 (z i)) = -(∑ i, z i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : max 0 (z i) - max 0 (-z i) = z i := by
    simpa only [max_comm] using max_zero_sub_max_neg_zero_eq_self (z i)
  linarith only [h]

/-- Both coordinate moments vanish, so the ring has zero linear response
in every input direction. The two scalar moments are evaluations of the
same shifted-cosine equation. -/
theorem regular_ring_linear_response_zero (m : ℕ) (hm : 2 ≤ m)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ j : Fin m, ⟪Definitions.Angle (RingTeacherAngle m j), x⟫_ℝ) = 0 := by
  have hcos : (∑ j : Fin m, Real.cos (RingTeacherAngle m j)) = 0 := by
    simpa only [zero_sub, Real.cos_neg] using regular_ring_shifted_cosine_sum m hm 0
  have hsin : (∑ j : Fin m, Real.sin (RingTeacherAngle m j)) = 0 := by
    simpa only [Real.cos_pi_div_two_sub] using regular_ring_shifted_cosine_sum m hm (π / 2)
  simp only [PiLp.inner_apply, Fin.sum_univ_two]
  change (∑ j : Fin m, (Real.cos (RingTeacherAngle m j) * x 0 +
      Real.sin (RingTeacherAngle m j) * x 1)) = 0
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hcos, hsin,
    zero_mul, zero_mul, add_zero]

/-- The equality example follows directly in input space from the scalar
antipodal identity and zero first moment. Oddness is only needed later for
distinctness, not for this pointwise exact fit. -/
theorem regular_ring_response_exact (m : ℕ) (hm : 2 ≤ m)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ i, RingStudentMass m i * max 0 ⟪Definitions.Angle (RingStudentAngle m i), x⟫_ℝ) -
      (∑ k, RingTeacherMass m k * max 0 ⟪Definitions.Angle (RingTeacherAngle m k), x⟫_ℝ) = 0 := by
  unfold RingStudentMass RingTeacherMass RingStudentAngle
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, one_mul]
  have hantipodal (j : Fin m) :
      ⟪Definitions.Angle (RingTeacherAngle m j + π), x⟫_ℝ =
        -⟪Definitions.Angle (RingTeacherAngle m j), x⟫_ℝ := by
    simp [Definitions.Angle, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_add_pi, Real.sin_add_pi]
    ring
  simp_rw [hantipodal]
  have hmoment := regular_ring_linear_response_zero m hm x
  simpa only [hmoment, neg_zero] using
    antipodal_sum_identity (fun j ↦ ⟪Definitions.Angle (RingTeacherAngle m j), x⟫_ℝ)

/-- The literal Gaussian loss is zero because the integrand is pointwise
zero. No prior exact-fit or population-loss normalization theorem is needed. -/
theorem regular_ring_loss_zero (m : ℕ) (hm : 2 ≤ m) :
    PaperLeanFormalization.Definitions.PlainLoss
      (RingStudentMass m) (fun i ↦ Definitions.Angle (RingStudentAngle m i))
      (RingTeacherMass m) (fun k ↦ Definitions.Angle (RingTeacherAngle m k)) = 0 := by
  unfold PaperLeanFormalization.Definitions.PlainLoss
  simp only [regular_ring_response_exact m hm, zero_pow (by decide : 0 < 2),
    zero_mul, MeasureTheory.integral_zero, mul_zero]

/-- Sharpness holds for every odd teacher width at least three. The example
is an exact fit, critical, and has precisely `2m` distinct student directions. -/
theorem prop_plain_collision_ceiling_sharp (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ (c θ : Fin (m + m) → ℝ) (s β : Fin m → ℝ),
      (∀ i, 0 < c i) ∧ (∀ k, 0 < s k) ∧
      (Finset.univ.image (fun i ↦ Definitions.Angle (θ i))).card = 2 * m ∧
      PaperLeanFormalization.Definitions.PlainLoss c (fun i ↦ Definitions.Angle (θ i))
        s (fun k ↦ Definitions.Angle (β k)) = 0 ∧
      fderiv ℝ (fun p : (Fin (m + m) → ℝ) × (Fin (m + m) → ℝ) ↦
        PaperLeanFormalization.Definitions.PlainLoss p.1 (fun i ↦ Definitions.Angle (p.2 i))
          s (fun k ↦ Definitions.Angle (β k))) (c, θ) = 0 := by
  refine ⟨RingStudentMass m, RingStudentAngle m,
    RingTeacherMass m, RingTeacherAngle m,
    (fun _ ↦ by norm_num [RingStudentMass]), (fun _ ↦ by norm_num [RingTeacherMass]), ?_,
    regular_ring_loss_zero m (by omega (config := {})), ?_⟩
  · change (Finset.univ.image (fun i ↦ RingDirection (RingStudentAngle m i))).card = 2 * m
    rw [Finset.card_image_of_injective _
      (regular_odd_ring_student_directions_injective m (by omega (config := {})) hodd),
      Finset.card_fin]
    omega (config := {})
  · have hglobal : IsMinOn
        (fun p : (Fin (m + m) → ℝ) × (Fin (m + m) → ℝ) ↦
          PaperLeanFormalization.Definitions.PlainLoss p.1 (fun i ↦ Definitions.Angle (p.2 i))
            (RingTeacherMass m)
            (fun k ↦ Definitions.Angle (RingTeacherAngle m k)))
        Set.univ (RingStudentMass m,
          RingStudentAngle m) := by
      intro p _
      change PaperLeanFormalization.Definitions.PlainLoss
        (RingStudentMass m) (fun i ↦ Definitions.Angle (RingStudentAngle m i))
        (RingTeacherMass m) (fun k ↦ Definitions.Angle (RingTeacherAngle m k)) ≤
        PaperLeanFormalization.Definitions.PlainLoss p.1 (fun i ↦ Definitions.Angle (p.2 i))
          (RingTeacherMass m) (fun k ↦ Definitions.Angle (RingTeacherAngle m k))
      rw [regular_ring_loss_zero m (by omega (config := {}))]
      unfold PaperLeanFormalization.Definitions.PlainLoss
      apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      apply MeasureTheory.integral_nonneg
      intro x
      exact mul_nonneg (sq_nonneg _) (by unfold stdGaussianDensity; positivity)
    exact (hglobal.isLocalMin Filter.univ_mem).fderiv_eq_zero

end PaperLeanFormalization.Plain

noncomputable section
open Real Filter Set MeasureTheory
open scoped BigOperators Topology

namespace PaperLeanFormalization.Plain.ZeroMassExample

open Definitions Preliminaries

/-- The fixed signed teacher from the zero-mass example, in radians. -/
def teacherAngle : Fin 5 → ℝ := ![π/6, π/3, π/2, 2*π/3, 5*π/6]

def teacherMass : Fin 5 → ℝ := ![1, -2*sqrt 3, 5, -2*sqrt 3, 1]

/-- The actual finite teacher potential, for either activation. -/
def potential {m : ℕ} (q : Model) (t β : Fin m → ℝ) (θ : ℝ) : ℝ :=
  ∑ k, t k * Kernel q (cos (θ - β k))

/-- The paper's literal Gaussian half-loss, with one student. -/
abbrev oneStudentLoss {m : ℕ} (q : Model) (t β : Fin m → ℝ) (s θ : ℝ) : ℝ :=
  Loss q (fun _ : Fin 1 => s) (fun _ => Angle θ) t (fun k => Angle (β k))

/-- `eq:one-student-quadratic`, including the exact Gaussian normalization. -/
theorem eq_one_student_quadratic {m : ℕ} (q : Model) (t β : Fin m → ℝ)
    (s θ : ℝ) :
    oneStudentLoss q t β s θ - oneStudentLoss q t β 0 θ =
      (match q with | .centered => (1/8 : ℝ) | .plainRelu => (1/4 : ℝ)) * s^2 -
        s / (2*π) * potential q t β θ := by
  have h (a : ℝ) := loss_eq_kernelEnergy (by norm_num : 2 ≤ 2) q
    (fun _ : Fin 1 => a) (fun _ => Angle θ) t (fun k => Angle (β k))
    (fun _ => angle_unit θ) (fun k => angle_unit (β k))
  dsimp only [oneStudentLoss]
  rw [h s, h 0]
  simp only [KernelEnergy, Fin.sum_univ_one, angle_inner, sub_self, cos_zero,
    zero_mul, Finset.sum_const_zero, mul_zero, sub_zero, zero_add]
  unfold potential
  simp only [← Finset.mul_sum, mul_assoc]
  cases q <;> norm_num [Kernel, Real.arcsin_one] <;> field_simp [pi_ne_zero] <;> ring

theorem zero_student_angle_irrelevant {m : ℕ} (q : Model) (t β : Fin m → ℝ)
    (θ τ : ℝ) : oneStudentLoss q t β 0 θ = oneStudentLoss q t β 0 τ := by
  cases q <;> simp [oneStudentLoss, Loss, CenteredLoss, PlainLoss]

theorem centered_principal_branch {z : ℝ} (hz : 0 ≤ z) (hzπ : z ≤ π) :
    Kernel .centered (cos z) = (π/2-z)*cos z + sin z := by
  have hs : sqrt (1-cos z^2) = sin z := by
    rw [show 1-cos z^2 = sin z^2 by nlinarith only [sin_sq_add_cos_sq z],
      sqrt_sq (sin_nonneg_of_nonneg_of_le_pi hz hzπ)]
  simp only [Kernel, CircleMoments.arcsin_cos_principal hz hzπ, hs]
  ring

theorem plain_negative_principal_branch {z : ℝ} (hz : -π ≤ z) (hz0 : z ≤ 0) :
    Kernel .plainRelu (cos z) = (π+z)*cos z-sin z := by
  have h := centered_principal_branch (neg_nonneg.mpr hz0) (by linarith : -z ≤ π)
  simp only [cos_neg, sin_neg] at h
  change Kernel .centered (cos z) + (π/2)*cos z = _
  rw [h]
  ring

/-- `eq:teacher-potential-expansion`: the four moments are actual finite sums. -/
theorem eq_teacher_potential_expansion {m : ℕ} (t β : Fin m → ℝ) (θ : ℝ)
    (hβ : ∀ k, -π ≤ θ-β k ∧ θ-β k ≤ 0) :
    let A := ∑ k, t k*cos (β k)
    let B := ∑ k, t k*sin (β k)
    let C := ∑ k, t k*β k*cos (β k)
    let D := ∑ k, t k*β k*sin (β k)
    potential .plainRelu t β θ =
      (π+θ)*(A*cos θ+B*sin θ) - (C*cos θ+D*sin θ) -
        (A*sin θ-B*cos θ) := by
  dsimp only
  unfold potential
  simp_rw [plain_negative_principal_branch (hβ _).1 (hβ _).2]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [cos_sub, sin_sub]
  ring

theorem weighted_trigonometric_values :
    (fun k => teacherMass k*cos (teacherAngle k)) =
      ![sqrt 3/2, -sqrt 3, 0, sqrt 3, -sqrt 3/2] ∧
    (fun k => teacherMass k*sin (teacherAngle k)) =
      ![(1/2 : ℝ), -3, 5, -3, 1/2] := by
  have h23 : 2*π/3 = π-π/3 := by ring
  have h56 : 5*π/6 = π-π/6 := by ring
  have hsq : sqrt 3 * sqrt 3 = 3 := mul_self_sqrt (by norm_num)
  constructor <;> funext k <;> fin_cases k <;>
    norm_num [teacherMass, teacherAngle, h23, h56, cos_pi_sub, sin_pi_sub,
      cos_pi_div_six, cos_pi_div_three, sin_pi_div_six, sin_pi_div_three] <;>
    nlinarith only [hsq]

/-- The displayed C,D cancellations, with their actual teacher sums, also
providing the A,B cancellations used in the potential expansion. -/
theorem teacher_moment_cancellations :
    (∑ k, teacherMass k*cos (teacherAngle k)) = 0 ∧
    (∑ k, teacherMass k*sin (teacherAngle k)) = 0 ∧
    (∑ k, teacherMass k*teacherAngle k*cos (teacherAngle k)) =
      π*sqrt 3*((1/12 : ℝ)-1/3+2/3-5/12) ∧
    π*sqrt 3*((1/12 : ℝ)-1/3+2/3-5/12) = 0 ∧
    (∑ k, teacherMass k*teacherAngle k*sin (teacherAngle k)) =
      π*((1/12 : ℝ)-1+5/2-2+5/12) ∧
    π*((1/12 : ℝ)-1+5/2-2+5/12) = 0 := by
  obtain ⟨hc, hs⟩ := weighted_trigonometric_values
  have hc' (k : Fin 5) := congrFun hc k
  have hs' (k : Fin 5) := congrFun hs k
  have hC (k : Fin 5) : teacherMass k*teacherAngle k*cos (teacherAngle k) =
      teacherAngle k*(teacherMass k*cos (teacherAngle k)) := by ring
  have hD (k : Fin 5) : teacherMass k*teacherAngle k*sin (teacherAngle k) =
      teacherAngle k*(teacherMass k*sin (teacherAngle k)) := by ring
  simp_rw [hC, hD, hc', hs']
  norm_num [Fin.sum_univ_succ, teacherAngle]
  constructor
  · ring
  · constructor <;> ring

theorem potential_plain_centered_difference {m : ℕ} (t β : Fin m → ℝ) (θ : ℝ) :
    potential .plainRelu t β θ - potential .centered t β θ =
      (π/2)*((∑ k, t k*cos (β k))*cos θ + (∑ k, t k*sin (β k))*sin θ) := by
  unfold potential
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Kernel, cos_sub]
  ring

theorem teacher_potential_zero_on_arc (q : Model) {θ : ℝ} (hθ : |θ| < π/6) :
    potential q teacherMass teacherAngle θ = 0 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hθ
  have hβ (k : Fin 5) : -π ≤ θ-teacherAngle k ∧ θ-teacherAngle k ≤ 0 := by
    fin_cases k <;> norm_num [teacherAngle] <;> constructor <;>
      linarith only [hlo, hhi, pi_pos]
  obtain ⟨hA, hB, hC, hC0, hD, hD0⟩ := teacher_moment_cancellations
  have hplain := eq_teacher_potential_expansion teacherMass teacherAngle θ hβ
  dsimp only at hplain
  rw [hA, hB, hC, hC0, hD, hD0] at hplain
  norm_num at hplain
  cases q with
  | plainRelu => exact hplain
  | centered =>
      have h := potential_plain_centered_difference teacherMass teacherAngle θ
      rw [hA, hB, hplain] at h
      linarith only [h]

/-- `eq:one-student-arc`, for the literal loss and the fixed five-unit teacher. -/
theorem eq_one_student_arc (q : Model) (s θ τ : ℝ) (hθ : |θ| < π/6) :
    oneStudentLoss q teacherMass teacherAngle s θ =
      oneStudentLoss q teacherMass teacherAngle 0 τ +
        (match q with | .centered => (1/8 : ℝ) | .plainRelu => (1/4 : ℝ))*s^2 := by
  have h := eq_one_student_quadratic q teacherMass teacherAngle s θ
  rw [teacher_potential_zero_on_arc q hθ, mul_zero,
    zero_student_angle_irrelevant q teacherMass teacherAngle θ τ] at h
  linarith only [h]

/-- A concrete nonzero probe certifies that the zero-mass minimum is nonglobal. -/
theorem teacher_potential_at_pi_div_two (q : Model) :
    potential q teacherMass teacherAngle (π/2) = 2*π/3-sqrt 3 := by
  have hdiff : (fun k => π/2-teacherAngle k) =
      ![π/3, π/6, 0, -π/6, -π/3] := by
    funext k
    fin_cases k <;> norm_num [teacherAngle] <;> ring
  have h3 := centered_principal_branch
    (by positivity : 0 ≤ π/3) (by linarith only [pi_pos] : π/3 ≤ π)
  have h6 := centered_principal_branch
    (by positivity : 0 ≤ π/6) (by linarith only [pi_pos] : π/6 ≤ π)
  have hc : potential .centered teacherMass teacherAngle (π/2) =
      2*Kernel .centered (cos (π/3))-4*sqrt 3*Kernel .centered (cos (π/6))+
        5*Kernel .centered 1 := by
    unfold potential
    simp_rw [congrFun hdiff]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    change 1*Kernel .centered (cos (π/3)) +
      (-2*sqrt 3*Kernel .centered (cos (π/6)) +
      (5*Kernel .centered (cos 0) +
      (-2*sqrt 3*Kernel .centered (cos (-π/6)) +
        (1*Kernel .centered (cos (-π/3)) + 0)))) = _
    simp only [neg_div, cos_neg, cos_zero]
    ring
  have hcval : potential .centered teacherMass teacherAngle (π/2) =
      2*π/3-sqrt 3 := by
    rw [hc, h3, h6]
    have hsq : sqrt 3 * sqrt 3 = 3 := mul_self_sqrt (by norm_num)
    norm_num [cos_pi_div_three, sin_pi_div_three, cos_pi_div_six,
      sin_pi_div_six, Kernel, Real.arcsin_one]
    nlinarith only [congrArg (fun x : ℝ => π*x) hsq]
  cases q with
  | centered => exact hcval
  | plainRelu =>
      have h := potential_plain_centered_difference teacherMass teacherAngle (π/2)
      obtain ⟨hA, hB, _⟩ := teacher_moment_cancellations
      rw [hA, hB, hcval] at h
      linarith only [h]

theorem teacher_potential_at_pi_div_two_pos (q : Model) :
    0 < potential q teacherMass teacherAngle (π/2) := by
  rw [teacher_potential_at_pi_div_two]
  have hs : (sqrt 3)^2 = 3 := sq_sqrt (by norm_num)
  have hs0 := sqrt_nonneg (3 : ℝ)
  have hpi := pi_gt_three
  nlinarith only [hs, hs0, hpi]

theorem one_student_loss_nonneg {m : ℕ} (q : Model) (t β : Fin m → ℝ)
    (s θ : ℝ) : 0 ≤ oneStudentLoss q t β s θ := by
  rw [oneStudentLoss, eq_q_losses]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro x
  apply mul_nonneg (sq_nonneg _)
  unfold stdGaussianDensity
  positivity

/-- The quadratic produces an explicit, feasible one-student competitor. -/
theorem lower_loss_competitor (q : Model) (τ : ℝ) :
    oneStudentLoss q teacherMass teacherAngle
        (potential q teacherMass teacherAngle (π/2)/(2*π)) (π/2) <
      oneStudentLoss q teacherMass teacherAngle 0 τ := by
  let P := potential q teacherMass teacherAngle (π/2)
  let a := P/(2*π)
  have ha : 0 < a := div_pos (teacher_potential_at_pi_div_two_pos q) (by positivity)
  have h := eq_one_student_quadratic q teacherMass teacherAngle a (π/2)
  rw [zero_student_angle_irrelevant q teacherMass teacherAngle (π/2) τ] at h
  have hcross : a/(2*π)*P = a^2 := by
    dsimp [a]
    field_simp [pi_ne_zero]
    ring
  change oneStudentLoss q teacherMass teacherAngle a (π/2) < _
  change _ = _ - a/(2*π)*P at h
  rw [hcross] at h
  cases q with
  | centered =>
      change _ = (1/8 : ℝ)*a^2-a^2 at h
      nlinarith only [h, sq_pos_of_pos ha]
  | plainRelu =>
      change _ = (1/4 : ℝ)*a^2-a^2 at h
      nlinarith only [h, sq_pos_of_pos ha]

theorem zero_mass_angle_local_minimum (q : Model) {τ : ℝ} (hτ : |τ| < π/6) :
    IsLocalMin
      (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        Loss q p.1 (fun i => Angle (p.2 i)) teacherMass
          (fun k => Angle (teacherAngle k)))
      (fun _ => 0, fun _ => τ) := by
  have hc : Continuous
      (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => |p.2 0|) :=
    ((continuous_apply 0).comp continuous_snd).abs
  have hnear : ∀ᶠ p : (Fin 1 → ℝ) × (Fin 1 → ℝ) in
      𝓝 (fun _ => 0, fun _ => τ), |p.2 0| < π/6 :=
    (isOpen_lt hc continuous_const).mem_nhds hτ
  filter_upwards [hnear] with p hp
  have hmass : p.1 = fun _ => p.1 0 := by
    funext i
    exact congrArg p.1 (Subsingleton.elim i 0)
  have hang : (fun i => Angle (p.2 i)) = fun _ => Angle (p.2 0) := by
    funext i
    exact congrArg (fun j => Angle (p.2 j)) (Subsingleton.elim i 0)
  change oneStudentLoss q teacherMass teacherAngle 0 τ ≤ _
  rw [hmass, hang]
  change _ ≤ oneStudentLoss q teacherMass teacherAngle (p.1 0) (p.2 0)
  rw [eq_one_student_arc q (p.1 0) (p.2 0) τ hp]
  exact le_add_of_nonneg_right (mul_nonneg (by cases q <;> norm_num) (sq_nonneg _))

/-- The existing manuscript example is a full signed-parameter local minimum
for both models, with positive Gaussian loss and an explicit lower-loss
one-student competitor. All three displayed identities above enter this proof. -/
theorem zero_mass_spurious_minimum (q : Model) {τ : ℝ} (hτ : |τ| < π/6) :
    IsLocalMinOn
      (fun p : (Fin 1 → ℝ) × (Fin 1 → Vec 2) =>
        Loss q p.1 p.2 teacherMass (fun k => Angle (teacherAngle k)))
      {p | ∀ i, ‖p.2 i‖ = 1}
      (fun _ => 0, fun _ => Angle τ) ∧
    0 < oneStudentLoss q teacherMass teacherAngle 0 τ ∧
    ∃ s θ, oneStudentLoss q teacherMass teacherAngle s θ <
      oneStudentLoss q teacherMass teacherAngle 0 τ := by
  have hm := CircleChart.local_minimum_to_sphere
    (fun s w => Loss q s w teacherMass (fun k => Angle (teacherAngle k)))
    (zero_mass_angle_local_minimum q hτ)
  refine ⟨hm, ?_, ?_⟩
  · exact lt_of_le_of_lt
      (one_student_loss_nonneg q teacherMass teacherAngle _ _) (lower_loss_competitor q τ)
  · exact ⟨_, _, lower_loss_competitor q τ⟩

end PaperLeanFormalization.Plain.ZeroMassExample

end

noncomputable section
open Real Filter Set MeasureTheory
open scoped BigOperators Topology RealInnerProductSpace

/-! ## `lem:nc-dead-counterexamples` (a): the line

On the line the unit sphere is the pair `{e, -e}`, so a student opposed to the
teacher can only change its mass. The opposed student never overlaps the
teacher's active half-line, which makes the loss `(s^2 + 1)/4`: the paper's
computation `E[X]_+^2 = 1/2` is the scalar Gaussian half moment below. -/

namespace PaperLeanFormalization.Plain.LineExample

open Definitions Preliminaries

/-- The unit direction of the line. -/
def e : Vec 1 := EuclideanSpace.single 0 1

theorem e_unit : ‖e‖ = 1 := by
  simp [e, EuclideanSpace.norm_single]

theorem inner_e (x : Vec 1) : ⟪e, x⟫_ℝ = x 0 := by
  simp [e, EuclideanSpace.inner_single_left]

theorem inner_neg_e (x : Vec 1) : ⟪-e, x⟫_ℝ = -(x 0) := by
  rw [inner_neg_left, inner_e]

/-- Every unit vector of the line is `e` or `-e`. -/
theorem unit_eq_or_neg (u : Vec 1) (hu : ‖u‖ = 1) : u = e ∨ u = -e := by
  have habs : ‖u‖ = |u 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
      Real.sqrt_sq_eq_abs]
  rw [habs] at hu
  rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hu with h | h
  · left
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [e, h]
  · right
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [e, h]

/-- The positive half of the scalar Gaussian second moment. -/
theorem half_second_moment :
    (∫ t in Ioi (0:ℝ), t ^ 2 * GaussianScalarDensity t) = 1 / 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := (1/2:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hgamma : Real.Gamma ((2 + 1) / 2) = sqrt π / 2 := by
    have h1 : ((2:ℝ) + 1) / 2 = 1 / 2 + 1 := by norm_num
    rw [h1, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hpow : ((1:ℝ) / 2) ^ (-((2:ℝ) + 1) / 2) = 2 * sqrt 2 := by
    rw [show (-((2:ℝ) + 1) / 2) = -(3 / 2) by norm_num,
      Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv,
      show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hgamma, hpow] at h
  have hfun : (fun t : ℝ => t ^ 2 * GaussianScalarDensity t) =
      fun t => (sqrt (2 * π))⁻¹ * (t ^ (2:ℝ) * exp (-(1/2) * t ^ (2:ℝ))) := by
    funext t
    simp only [GaussianScalarDensity, Real.rpow_two]
    ring_nf
  rw [hfun, integral_mul_left, h]
  have hsq : sqrt (2 * π) = sqrt 2 * sqrt π := Real.sqrt_mul (by norm_num) π
  rw [hsq]
  field_simp
  ring

/-- The scalar Gaussian second moment on the line. -/
theorem second_moment_integrable :
    Integrable (fun t : ℝ => t ^ 2 * GaussianScalarDensity t) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1/2:ℝ)) (by norm_num) (s := 2) (by norm_num)
  have hfun : (fun t : ℝ => t ^ 2 * GaussianScalarDensity t) =
      fun t => (sqrt (2 * π))⁻¹ * (t ^ (2:ℝ) * exp (-(1/2) * t ^ 2)) := by
    funext t
    simp only [GaussianScalarDensity, Real.rpow_two]
    ring_nf
  rw [hfun]
  exact h.const_mul _

theorem gaussian_scalar_density_even (t : ℝ) :
    GaussianScalarDensity (-t) = GaussianScalarDensity t := by
  simp [GaussianScalarDensity]

theorem gaussian_scalar_density_continuous : Continuous GaussianScalarDensity := by
  unfold GaussianScalarDensity
  exact continuous_const.mul (continuous_exp.comp ((continuous_id.pow 2).neg.div_const 2))

theorem gaussian_scalar_density_nonneg (t : ℝ) : 0 ≤ GaussianScalarDensity t := by
  unfold GaussianScalarDensity; positivity

theorem relu_square_integrable :
    Integrable (fun t : ℝ => max 0 t ^ 2 * GaussianScalarDensity t) := by
  refine second_moment_integrable.mono' ?_ (eventually_of_forall fun t => ?_)
  · exact ((continuous_const.max continuous_id).pow 2).aestronglyMeasurable.mul
      gaussian_scalar_density_continuous.aestronglyMeasurable
  · have hd := gaussian_scalar_density_nonneg t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hd)]
    apply mul_le_mul_of_nonneg_right _ hd
    rcases le_or_lt t 0 with ht | ht
    · rw [max_eq_left ht]
      exact (by norm_num : (0:ℝ) ^ 2 ≤ 0 ^ 2).trans (by nlinarith [sq_nonneg t])
    · rw [max_eq_right ht.le]

theorem relu_square_neg_integrable :
    Integrable (fun t : ℝ => max 0 (-t) ^ 2 * GaussianScalarDensity t) := by
  have h := relu_square_integrable.comp_neg
  simpa only [gaussian_scalar_density_even] using h

/-- The positive part of the line carries half of the second moment. -/
theorem relu_square_moment :
    (∫ t : ℝ, max 0 t ^ 2 * GaussianScalarDensity t) = 1 / 2 := by
  rw [← integral_add_compl (measurableSet_Ioi (a := (0:ℝ))) relu_square_integrable]
  have hpos : (∫ t in Ioi (0:ℝ), max 0 t ^ 2 * GaussianScalarDensity t) =
      ∫ t in Ioi (0:ℝ), t ^ 2 * GaussianScalarDensity t := by
    refine set_integral_congr measurableSet_Ioi fun t ht => ?_
    simp only [max_eq_right (le_of_lt (mem_Ioi.mp ht))]
  have hneg : (∫ t in (Ioi (0:ℝ))ᶜ, max 0 t ^ 2 * GaussianScalarDensity t) = 0 := by
    rw [compl_Ioi]
    refine set_integral_eq_zero_of_forall_eq_zero fun t ht => ?_
    simp only [max_eq_left (mem_Iic.mp ht), zero_pow (by decide : 0 < 2), zero_mul]
  rw [hpos, hneg, half_second_moment]
  norm_num

/-- The negative part carries the other half, by the reflection symmetry. -/
theorem relu_square_moment_neg :
    (∫ t : ℝ, max 0 (-t) ^ 2 * GaussianScalarDensity t) = 1 / 2 := by
  have h := integral_neg_eq_self (fun t : ℝ => max 0 t ^ 2 * GaussianScalarDensity t) volume
  simp only [gaussian_scalar_density_even] at h
  rw [h, relu_square_moment]

/-- The plain loss of one student on the line, as a scalar Gaussian integral. -/
theorem loss_opposed (s : ℝ) :
    PlainLoss (fun _ : Fin 1 => s) (fun _ => -e) (fun _ : Fin 1 => (1:ℝ)) (fun _ => e) =
      (1 / 2 : ℝ) * ∫ t : ℝ, (s * max 0 (-t) - max 0 t) ^ 2 * GaussianScalarDensity t := by
  unfold PlainLoss
  congr 1
  have hb := gaussian_integral_in_basis (EuclideanSpace.basisFun (Fin 1) ℝ)
    (fun y : Fin 1 → ℝ => (s * max 0 (-(y 0)) - max 0 (y 0)) ^ 2)
  simp only [EuclideanSpace.basisFun_repr] at hb
  have hleft : (∫ x : Vec 1, ((∑ _i : Fin 1, s * max 0 ⟪-e, x⟫_ℝ) -
      ∑ _k : Fin 1, (1:ℝ) * max 0 ⟪e, x⟫_ℝ) ^ 2 * stdGaussianDensity x) =
      ∫ x : Vec 1, (s * max 0 (-(x 0)) - max 0 (x 0)) ^ 2 *
        ((sqrt (2 * π))⁻¹ ^ 1 * exp (-‖x‖ ^ 2 / 2)) := by
    congr 1
    funext x
    simp only [Fin.sum_univ_one, inner_neg_e, inner_e, one_mul, stdGaussianDensity]
  rw [hleft, hb]
  have hfin := (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
    (fun t : ℝ => (s * max 0 (-t) - max 0 t) ^ 2 * GaussianScalarDensity t)
  rw [← hfin]
  congr 1
  funext y
  simp [Fin.prod_univ_one, MeasurableEquiv.funUnique_apply]

/-- `eq:line-opposed-loss`: the explicit loss of the opposed student. -/
theorem loss_opposed_value (s : ℝ) :
    PlainLoss (fun _ : Fin 1 => s) (fun _ => -e) (fun _ : Fin 1 => (1:ℝ)) (fun _ => e) =
      (s ^ 2 + 1) / 4 := by
  rw [loss_opposed]
  have hpt : ∀ t : ℝ, (s * max 0 (-t) - max 0 t) ^ 2 * GaussianScalarDensity t =
      s ^ 2 * (max 0 (-t) ^ 2 * GaussianScalarDensity t) +
        max 0 t ^ 2 * GaussianScalarDensity t := by
    intro t
    have h0 : max 0 (-t) * max 0 t = 0 := by
      rcases le_or_lt t 0 with ht | ht
      · rw [max_eq_left ht, mul_zero]
      · rw [max_eq_left (neg_nonpos.mpr ht.le), zero_mul]
    have hexp : (s * max 0 (-t) - max 0 t) ^ 2 =
        s ^ 2 * max 0 (-t) ^ 2 + max 0 t ^ 2 - 2 * s * (max 0 (-t) * max 0 t) := by ring
    rw [hexp, h0]
    ring
  simp_rw [hpt]
  rw [integral_add (relu_square_neg_integrable.const_mul _) relu_square_integrable,
    integral_mul_left, relu_square_moment_neg, relu_square_moment]
  ring

/-- The opposed zero-mass student is a local minimum on the unit-direction
parameter space: the two unit directions of the line are isolated, so only
the mass can move, and the loss is even in the mass. -/
theorem opposed_local_minimum :
    IsLocalMinOn
      (fun p : Parameters 1 1 => PlainLoss p.1 p.2 (fun _ : Fin 1 => (1:ℝ)) (fun _ : Fin 1 => e))
      {p | ∀ i, ‖p.2 i‖ = 1} (fun _ => 0, fun _ => -e) := by
  refine eventually_nhdsWithin_iff.mpr ?_
  refine Metric.eventually_nhds_iff.mpr ⟨1, one_pos, fun p hp hunit => ?_⟩
  have hdir : p.2 0 = -e := by
    rcases unit_eq_or_neg (p.2 0) (hunit 0) with h | h
    · exfalso
      have h1 : dist (p.2 0) (-e) ≤ dist p (fun _ => 0, fun _ => -e) :=
        (dist_le_pi_dist p.2 (fun _ => -e) 0).trans
          (by rw [Prod.dist_eq]; exact le_max_right _ _)
      rw [h, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ e, norm_smul, e_unit] at h1
      norm_num at h1
      linarith
    · exact h
  have hp1 : p.1 = fun _ => p.1 0 := by
    funext i
    exact congrArg p.1 (Subsingleton.elim i 0)
  have hp2 : p.2 = fun _ => -e := by
    funext i
    rw [← hdir]
    exact congrArg p.2 (Subsingleton.elim i 0)
  show PlainLoss (fun _ => 0) (fun _ => -e) _ _ ≤ PlainLoss p.1 p.2 _ _
  rw [hp1, hp2, loss_opposed_value, loss_opposed_value]
  nlinarith [sq_nonneg (p.1 0)]

/-- The teacher itself is a student parameter with zero loss. -/
theorem teacher_copy_zero :
    PlainLoss (fun _ : Fin 1 => (1:ℝ)) (fun _ => e) (fun _ : Fin 1 => (1:ℝ)) (fun _ => e) = 0 := by
  unfold PlainLoss
  simp

end PaperLeanFormalization.Plain.LineExample
