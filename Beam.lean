import Preliminaries
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sign
import Mathlib.Data.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.Tactic

/-!
The cyclic beam construction from the paper, with every proof local to
this new tree. The local kernel calculus is imported from Preliminaries; this
file proves the gap Green readings, reciprocal mode, feature reconstruction,
exact feature energy, scalar gap inequality, and actual second variation.
The final ordered theorem receives the residual's geometric endpoint readings;
Planar derives those readings from criticality and strict interlacing.
-/

noncomputable section

open Real MeasureTheory Set
open scoped BigOperators Interval

namespace PaperLeanFormalization.BeamKernel

/-- `eq:rotating-frame-conserved`: actual derivatives of both frame coordinates. -/
theorem eq_rotating_frame_conserved {y y1 : ℝ → ℝ} {y2 x : ℝ}
    (hy : HasDerivAt y (y1 x) x) (hy1 : HasDerivAt y1 y2 x) :
    HasDerivAt (fun t => y t*cos t-y1 t*sin t) (-(y2+y x)*sin x) x ∧
    HasDerivAt (fun t => y t*sin t+y1 t*cos t) ((y2+y x)*cos x) x := by
  constructor
  · convert (hy.mul (hasDerivAt_cos x)).sub (hy1.mul (hasDerivAt_sin x)) using 1
    ring
  · convert (hy.mul (hasDerivAt_sin x)).add (hy1.mul (hasDerivAt_cos x)) using 1
    ring

/-- `eq:rotating-frame-reconstruction`: the inverse rotating frame. -/
theorem eq_rotating_frame_reconstruction (y y1 x : ℝ) :
    (y*cos x-y1*sin x)*cos x+(y*sin x+y1*cos x)*sin x = y := by
  nlinarith only [congrArg (fun z => y*z) (cos_sq_add_sin_sq x)]

theorem eqOn_constant_of_hasDerivAt_zero {s : Set ℝ} (hs : Convex ℝ s)
    {f : ℝ → ℝ} (hf : ∀ x ∈ s, HasDerivAt f 0 x) {x0 : ℝ} (hx0 : x0 ∈ s) :
    ∀ x ∈ s, f x = f x0 := by
  intro x hx
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf z hz).differentiableAt)
    (C := 0) (fun z hz => by rw [(hf z hz).deriv, norm_zero]) hs hx0 hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h

/-- The second-order homogeneous equation is solved by conserved frame coordinates. -/
theorem harmonic_eqOn {s : Set ℝ} (hs : Convex ℝ s) (hsne : s.Nonempty)
    {y y1 y2 : ℝ → ℝ}
    (hy : ∀ x ∈ s, HasDerivAt y (y1 x) x)
    (hy1 : ∀ x ∈ s, HasDerivAt y1 (y2 x) x)
    (heq : ∀ x ∈ s, y2 x+y x=0) :
    ∃ A B : ℝ, ∀ x ∈ s, y x = A*cos x+B*sin x := by
  obtain ⟨x0, hx0⟩ := hsne
  let a : ℝ → ℝ := fun x => y x*cos x-y1 x*sin x
  let b : ℝ → ℝ := fun x => y x*sin x+y1 x*cos x
  have ha : ∀ x ∈ s, HasDerivAt a 0 x := by
    intro x hx
    simpa only [heq x hx, neg_zero, zero_mul] using
      (eq_rotating_frame_conserved (hy x hx) (hy1 x hx)).1
  have hb : ∀ x ∈ s, HasDerivAt b 0 x := by
    intro x hx
    simpa only [heq x hx, zero_mul] using
      (eq_rotating_frame_conserved (hy x hx) (hy1 x hx)).2
  refine ⟨a x0, b x0, ?_⟩
  intro x hx
  calc
    y x = a x*cos x+b x*sin x := (eq_rotating_frame_reconstruction (y x) (y1 x) x).symm
    _ = a x0*cos x+b x0*sin x := by
      rw [eqOn_constant_of_hasDerivAt_zero hs ha hx0 x hx,
        eqOn_constant_of_hasDerivAt_zero hs hb hx0 x hx]

/-- The four-dimensional space, with its complete scalar formula in one definition. -/
def mode (A B C D x : ℝ) : ℝ := (A+C*x)*cos x+(B+D*x)*sin x

theorem mode_hasDerivAt (A B C D x : ℝ) :
    HasDerivAt (mode A B C D) (mode (B+C) (D-A) D (-C) x) x := by
  unfold mode
  convert (((hasDerivAt_id x).const_mul C).const_add A).mul (hasDerivAt_cos x) |>.add
    ((((hasDerivAt_id x).const_mul D).const_add B).mul (hasDerivAt_sin x)) using 1
  simp only [id_eq]
  ring

theorem deriv_mode (A B C D : ℝ) :
    deriv (mode A B C D) = mode (B+C) (D-A) D (-C) :=
  funext fun x => (mode_hasDerivAt A B C D x).deriv

theorem mode_second_add (A B C D x : ℝ) :
    mode ((D-A)+D) ((-C)-(B+C)) (-C) (-D) x + mode A B C D x =
      (2*D)*cos x-(2*C)*sin x := by
  unfold mode
  ring

theorem mode_beam_equation (A B C D x : ℝ) :
    deriv (deriv (deriv (deriv (mode A B C D)))) x +
      2*deriv (deriv (mode A B C D)) x + mode A B C D x = 0 := by
  simp only [deriv_mode, mode]
  ring

/-- The resonant particular solution explicitly specified in the proof sketch. -/
theorem particular_second_add (u v x : ℝ) :
    deriv (deriv (mode 0 0 (-v/2) (u/2))) x + mode 0 0 (-v/2) (u/2) x =
      u*cos x+v*sin x := by
  simp only [deriv_mode, mode]
  ring

/-- `eq:harmonic-difference`: subtracting two actual derivative chains with
the same forcing leaves a homogeneous second-order equation. -/
theorem eq_harmonic_difference {f f1 p p1 : ℝ → ℝ} {f2 p2 g x : ℝ}
    (hf0 : HasDerivAt f (f1 x) x) (hf1 : HasDerivAt f1 f2 x)
    (hp0 : HasDerivAt p (p1 x) x) (hp1 : HasDerivAt p1 p2 x)
    (hf : f2 + f x = g) (hp : p2 + p x = g) :
    HasDerivAt (fun y => f y - p y) (f1 x - p1 x) x ∧
      HasDerivAt (fun y => f1 y - p1 y) (f2 - p2) x ∧
      (f2 - p2) + (f x - p x) = (f2 + f x) - (p2 + p x) ∧
      (f2 + f x) - (p2 + p x) = g - g ∧
      (f2 - p2) + (f x - p x) = 0 := by
  exact ⟨hf0.sub hp0, hf1.sub hp1, by ring, by rw [hf, hp], by linarith only [hf, hp]⟩

/-- On any nonempty interval, four actual derivative witnesses yield the four modes. -/
theorem beam_eqOn_of_chain {s : Set ℝ} (hs : Convex ℝ s) (hsne : s.Nonempty)
    {f f1 f2 f3 f4 : ℝ → ℝ}
    (h0 : ∀ x ∈ s, HasDerivAt f (f1 x) x)
    (h1 : ∀ x ∈ s, HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x ∈ s, HasDerivAt f2 (f3 x) x)
    (h3 : ∀ x ∈ s, HasDerivAt f3 (f4 x) x)
    (heq : ∀ x ∈ s, f4 x+2*f2 x+f x=0) :
    ∃ A B C D : ℝ, ∀ x ∈ s, f x=A*cos x+B*sin x+C*x*cos x+D*x*sin x := by
  obtain ⟨u, v, huv⟩ := harmonic_eqOn hs hsne
    (y := fun x => f2 x+f x) (y1 := fun x => f3 x+f1 x)
    (y2 := fun x => f4 x+f2 x)
    (fun x hx => (h2 x hx).add (h0 x hx))
    (fun x hx => (h3 x hx).add (h1 x hx)) (by
      intro x hx
      dsimp only
      linarith only [heq x hx])
  let p := mode 0 0 (-v/2) (u/2)
  have hp : ∀ x, HasDerivAt p (deriv p x) x := by
    intro x
    rw [show p = mode 0 0 (-v/2) (u/2) from rfl, deriv_mode]
    exact mode_hasDerivAt _ _ _ _ _
  have hp1 : ∀ x, HasDerivAt (deriv p) (deriv (deriv p) x) x := by
    intro x
    rw [show p = mode 0 0 (-v/2) (u/2) from rfl, deriv_mode, deriv_mode]
    exact mode_hasDerivAt _ _ _ _ _
  have hsub (x : ℝ) (hx : x ∈ s) := eq_harmonic_difference
    (h0 x hx) (h1 x hx) (hp x) (hp1 x) (huv x hx) (particular_second_add u v x)
  obtain ⟨A, B, hAB⟩ := harmonic_eqOn hs hsne
    (y := fun x => f x-p x) (y1 := fun x => f1 x-deriv p x)
    (y2 := fun x => f2 x-deriv (deriv p) x)
    (fun x hx => (hsub x hx).1)
    (fun x hx => (hsub x hx).2.1)
    (fun x hx => (hsub x hx).2.2.2.2)
  refine ⟨A, B, -v/2, u/2, ?_⟩
  intro x hx
  have h := hAB x hx
  dsimp [p, mode] at h
  linarith only [h]

/-- `lem:beam-kernel`, with the differential operator stated literally. -/
theorem lem_beam_kernel {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) :
    (∀ x, deriv (deriv (deriv (deriv f))) x+2*deriv (deriv f) x+f x=0) ↔
    ∃ A B C D : ℝ, ∀ x, f x=A*cos x+B*sin x+C*x*cos x+D*x*sin x := by
  have hd (n : ℕ) (hn : n < 4) : Differentiable ℝ (iteratedDeriv n f) :=
    hf.differentiable_iteratedDeriv n (by exact_mod_cast hn)
  have h0 : ∀ x, HasDerivAt f (deriv f x) x := by
    simpa only [iteratedDeriv_zero] using fun x => (hd 0 (by decide) x).hasDerivAt
  have h1 : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using fun x => (hd 1 (by decide) x).hasDerivAt
  have h2 : ∀ x, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using fun x => (hd 2 (by decide) x).hasDerivAt
  have h3 : ∀ x, HasDerivAt (deriv (deriv (deriv f))) (deriv (deriv (deriv (deriv f))) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using fun x => (hd 3 (by decide) x).hasDerivAt
  constructor
  · intro heq
    obtain ⟨A, B, C, D, h⟩ := beam_eqOn_of_chain convex_univ ⟨0, mem_univ _⟩
      (fun x _ => h0 x) (fun x _ => h1 x) (fun x _ => h2 x) (fun x _ => h3 x)
      (fun x _ => heq x)
    exact ⟨A, B, C, D, fun x => h x (mem_univ _)⟩
  · rintro ⟨A, B, C, D, h⟩
    have heq : f = mode A B C D := by
      funext x
      rw [h x]
      unfold mode
      ring
    rw [heq]
    exact mode_beam_equation A B C D

end PaperLeanFormalization.BeamKernel


namespace PaperLeanFormalization.Beam

/-! The local endpoint data. -/

def psi (z : ℝ) : ℝ := sin z - z * cos z
def chi (z : ℝ) : ℝ := z * sin z
def determinant (l : ℝ) : ℝ := l ^ 2 - sin l ^ 2
def curvatureNumerator (l p : ℝ) : ℝ :=
  psi l * chi (l - p) - psi (l - p) * chi l
def jerkNumerator (l p : ℝ) : ℝ :=
  chi l * chi (l - p) - psi (l - p) * (sin l + l * cos l)
def a (l : ℝ) : ℝ := 2 * (l - sin l * cos l) / (l ^ 2 - sin l ^ 2)
def b (l : ℝ) : ℝ := 2 * (sin l - l * cos l) / (l ^ 2 - sin l ^ 2)
def m0 (l p : ℝ) : ℝ := curvatureNumerator l p / determinant l
def ml (l p : ℝ) : ℝ := curvatureNumerator l (l - p) / determinant l
def j0 (l p : ℝ) : ℝ := -jerkNumerator l p / determinant l
def jl (l p : ℝ) : ℝ := jerkNumerator l (l - p) / determinant l

/-- `eq:beam-feature-energy-definition-paper`: the feature itself. -/
def feature {n : ℕ} (dc x theta : Fin n → ℝ) (y : ℝ) : ℝ :=
  ∑ i, (dc i * |cos (y - theta i)| +
    x i * Real.sign (cos (y - theta i)) * sin (y - theta i))

/-- `eq:beam-feature-variation`, with the derivative of `|cos|` written out. -/
theorem eq_beam_feature_variation {n : ℕ} (dc x theta : Fin n → ℝ) (y : ℝ) :
    feature dc x theta y = ∑ i, (dc i * |cos (y - theta i)| +
      x i * Real.sign (cos (y - theta i)) * sin (y - theta i)) := rfl

/-- The entire energy formula is inspectable here. -/
def featureEnergy {n : ℕ} (dc x theta : Fin n → ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..π, (∑ i, (dc i * |cos (y - theta i)| +
    x i * Real.sign (cos (y - theta i)) * sin (y - theta i))) ^ 2

theorem featureEnergy_nonnegative {n : ℕ} (dc x theta : Fin n → ℝ) :
    0 ≤ featureEnergy dc x theta :=
  intervalIntegral.integral_nonneg pi_pos.le (fun _ _ => sq_nonneg _)

/-- `eq:definition_E`: the actual squared-feature integral and its sign. -/
theorem eq_definition_E {n : ℕ} (dc x theta : Fin n → ℝ) :
    featureEnergy dc x theta = (∫ y in (0 : ℝ)..π, feature dc x theta y ^ 2) ∧
      0 ≤ featureEnergy dc x theta :=
  ⟨rfl, featureEnergy_nonnegative dc x theta⟩

/-- `eq:beam-clamped-matrix-paper`: the determinant of the value--slope system. -/
theorem clamped_matrix_determinant (l : ℝ) :
    -(psi l * (sin l + l * cos l) - chi l * chi l) = l ^ 2 - sin l ^ 2 := by
  dsimp [psi, chi]
  nlinarith [sin_sq_add_cos_sq l]

/-- The full-period case is valid for the clamped determinant too. -/
theorem determinant_pos {l : ℝ} (hl : 0 < l) (hlpi : l ≤ π) :
    0 < determinant l := by
  have hs := sin_lt hl
  have hs0 := sin_nonneg_of_nonneg_of_le_pi hl.le hlpi
  dsimp [determinant]
  nlinarith

/-- `eq:beam-numerators-closed-paper`, first closed form. -/
theorem curvature_numerator_closed_form (l p : ℝ) :
    curvatureNumerator l p =
      l * (l - p) * sin p - p * sin l * sin (l - p) := by
  have hs : sin p = sin l * cos (l - p) - cos l * sin (l - p) := by
    rw [← sin_sub]
    congr 1
    ring
  dsimp [curvatureNumerator, psi, chi]
  rw [hs]
  ring

/-- `eq:beam-numerators-closed-paper`, second closed form. -/
theorem jerk_numerator_closed_form (l p : ℝ) :
    jerkNumerator l p = l * (l - p) * cos p + l * sin p -
      p * sin l * cos (l - p) - sin l * sin (l - p) := by
  have hs : sin p = sin l * cos (l - p) - cos l * sin (l - p) := by
    rw [← sin_sub]
    congr 1
    ring
  have hc : cos p = cos l * cos (l - p) + sin l * sin (l - p) := by
    rw [← cos_sub]
    congr 1
    ring
  dsimp [jerkNumerator, psi, chi]
  rw [hs, hc]
  ring

/-- Cauchy's mean-value theorem transports strict decrease of the derivative
ratio to strict decrease of the ratio itself. -/
theorem strictAntiOn_ratio_of_derivative_ratio
    {f g f' g' : ℝ → ℝ} {L : ℝ}
    (hf : ContinuousOn f (Ico 0 L)) (hg : ContinuousOn g (Ico 0 L))
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hdf : ∀ x ∈ Ioo 0 L, HasDerivAt f (f' x) x)
    (hdg : ∀ x ∈ Ioo 0 L, HasDerivAt g (g' x) x)
    (hgpos : ∀ x ∈ Ioo 0 L, 0 < g x)
    (hgp : ∀ x ∈ Ioo 0 L, 0 < g' x)
    (hr : StrictAntiOn (fun x => f' x / g' x) (Ioo 0 L)) :
    StrictAntiOn (fun x => f x / g x) (Ioo 0 L) := by
  have hquot : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun t => f t / g t)
        ((f' x * g x - f x * g' x) / (g x)^2) x := by
    intro x hx
    exact (hdf x hx).div (hdg x hx) (ne_of_gt (hgpos x hx))
  apply (convex_Ioo (0 : ℝ) L).strictAntiOn_of_deriv_neg
  · exact fun x hx => (hquot x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo 0 L := interior_subset hx
    have hsub : Icc 0 x ⊆ Ico 0 L := by
      intro t ht
      exact ⟨ht.1, lt_of_le_of_lt ht.2 hx'.2⟩
    have hsub' : Ioo 0 x ⊆ Ioo 0 L := by
      intro t ht
      exact ⟨ht.1, lt_trans ht.2 hx'.2⟩
    obtain ⟨c, hc, heq⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope f f' hx'.1 (hf.mono hsub)
        (fun t ht => hdf t (hsub' ht)) g g' (hg.mono hsub)
        (fun t ht => hdg t (hsub' ht))
    simp only [hf0, hg0, sub_zero] at heq
    have hstrict := (div_lt_div_iff (hgp x hx') (hgp c (hsub' hc))).mp
      (hr (hsub' hc) hx' hc.2)
    have hmul := mul_lt_mul_of_pos_right hstrict (hgpos x hx')
    have hnum : f' x * g x - f x * g' x < 0 := by
      have hrew : f' c * g' x * g x = f x * g' x * g' c := by
        calc
          f' c * g' x * g x = (g x * f' c) * g' x := by ring
          _ = (f x * g' c) * g' x := by rw [heq]
          _ = f x * g' x * g' c := by ring
      have hfactor : (f' x * g x) * g' c < (f x * g' x) * g' c := by
        calc
          (f' x * g x) * g' c = (f' x * g' c) * g x := by ring
          _ < (f' c * g' x) * g x := hmul
          _ = (f x * g' x) * g' c := hrew
      exact sub_neg.mpr ((mul_lt_mul_right (hgp c (hsub' hc))).mp hfactor)
    rw [(hquot x hx').deriv]
    exact div_neg_of_neg_of_pos hnum (sq_pos_of_pos (hgpos x hx'))

lemma psi_derivative (t : ℝ) : HasDerivAt psi (t * sin t) t := by
  convert (hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (hasDerivAt_cos t)) using 1
  simp only [psi, id_eq]
  ring

lemma psi_pos {t : ℝ} (ht : 0 < t) (htpi : t < π) : 0 < psi t := by
  have hm : StrictMonoOn psi (Icc 0 t) := by
    apply (convex_Icc (0 : ℝ) t).strictMonoOn_of_deriv_pos
    · exact fun x _ => (psi_derivative x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(psi_derivative x).deriv]
      exact mul_pos hx.1 (sin_pos_of_pos_of_lt_pi hx.1 (lt_trans hx.2 htpi))
  have h := hm ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht
  simpa [psi] using h

lemma sinc_strictAnti : StrictAntiOn (fun t : ℝ => sin t / t) (Ioo 0 π) := by
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) π) :
      HasDerivAt (fun t : ℝ => sin t / t) (-psi t / t ^ 2) t := by
    convert (hasDerivAt_sin t).div (hasDerivAt_id t) (ne_of_gt ht.1) using 1
    simp only [psi, id_eq]
    ring
  apply (convex_Ioo (0 : ℝ) π).strictAntiOn_of_deriv_neg
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(hd t ht).deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (psi_pos ht.1 ht.2)) (pow_pos ht.1 2)

lemma determinant_derivative (t : ℝ) :
    HasDerivAt determinant (2 * (t - sin t * cos t)) t := by
  convert (hasDerivAt_pow 2 t).sub ((hasDerivAt_sin t).pow 2) using 1
  ring

lemma area_pos {t : ℝ} (ht : 0 < t) (htpi : t < π) :
    0 < t - sin t * cos t := by
  have hs := sin_pos_of_pos_of_lt_pi ht htpi
  have hb := mul_le_mul_of_nonneg_left (cos_le_one t) hs.le
  linarith [sin_lt ht]

/-- The derivative ratio has a factored sign: only three positive factors. -/
lemma ratio_derivative (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) π) :
    HasDerivAt (fun x => x * sin x / (2 * (x - sin x * cos x)))
      (-2 * psi t * (t + sin t * cos t) / (2 * (t - sin t * cos t)) ^ 2) t := by
  have hn := (hasDerivAt_id t).mul (hasDerivAt_sin t)
  have hd := ((hasDerivAt_id t).sub ((hasDerivAt_sin t).mul (hasDerivAt_cos t))).const_mul 2
  convert hn.div hd (ne_of_gt (mul_pos (by norm_num) (area_pos ht.1 ht.2))) using 1
  congr 1
  dsimp [psi]
  linear_combination 2 * t * sin t * (sin_sq_add_cos_sq t)

lemma derivative_ratio_strictAnti :
    StrictAntiOn (fun x => x * sin x / (2 * (x - sin x * cos x))) (Ioo 0 π) := by
  apply (convex_Ioo (0 : ℝ) π).strictAntiOn_of_deriv_neg
  · exact fun x hx => (ratio_derivative x hx).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(ratio_derivative t ht).deriv]
    have hs := sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hb := mul_le_mul_of_nonneg_left (neg_one_le_cos t) hs.le
    have hp : 0 < t + sin t * cos t := by linarith [sin_lt ht.1]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (psi_pos ht.1 ht.2)) hp)
      (pow_pos (mul_pos (by norm_num) (area_pos ht.1 ht.2)) 2)

/-- All scalar analysis reduces to this single monotone quotient. -/
lemma psi_div_determinant_strictAnti :
    StrictAntiOn (fun x => psi x / determinant x) (Ioo 0 π) := by
  apply strictAntiOn_ratio_of_derivative_ratio
    (f' := fun x => x * sin x) (g' := fun x => 2 * (x - sin x * cos x))
  · exact fun x _ => (psi_derivative x).continuousAt.continuousWithinAt
  · exact fun x _ => (determinant_derivative x).continuousAt.continuousWithinAt
  · simp [psi]
  · simp [determinant]
  · exact fun x _ => psi_derivative x
  · exact fun x _ => determinant_derivative x
  · exact fun x hx => determinant_pos hx.1 hx.2.le
  · exact fun x hx => mul_pos (by norm_num) (area_pos hx.1 hx.2)
  · exact derivative_ratio_strictAnti

/-- Cancellation-free bracket: its two summands are positive. -/
def theta (p q : ℝ) : ℝ :=
  q * sin q * (determinant (p + q) * psi p - determinant p * psi (p + q)) +
    psi (p + q) * (q - sin q) * (q * sin p ^ 2 + p ^ 2 * sin q)

lemma theta_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hl : p + q < π) :
    0 < theta p q := by
  have hppi : p < π := by linarith
  have hqpi : q < π := by linarith
  have hpq : 0 < p + q := add_pos hp hq
  have hratio := psi_div_determinant_strictAnti ⟨hp, hppi⟩ ⟨hpq, hl⟩
    (lt_add_of_pos_right p hq)
  rw [div_lt_div_iff (determinant_pos hpq hl.le) (determinant_pos hp hppi.le)] at hratio
  have hbracket : 0 < determinant (p + q) * psi p - determinant p * psi (p + q) := by
    linarith only [hratio]
  have hsq := sin_pos_of_pos_of_lt_pi hq hqpi
  unfold theta
  exact add_pos (mul_pos (mul_pos hq hsq) hbracket)
    (mul_pos (mul_pos (psi_pos hpq hl) (sub_pos.mpr (sin_lt hq)))
      (add_pos_of_nonneg_of_pos (mul_nonneg hq.le (sq_nonneg _))
        (mul_pos (sq_pos_of_pos hp) hsq)))

def M (p q : ℝ) : ℝ := (p + q) * q * sin p - p * sin (p + q) * sin q
def J (p q : ℝ) : ℝ :=
  (p + q) * q * cos p + (p + q) * sin p -
    p * sin (p + q) * cos q - sin (p + q) * sin q

/-- End-curvature positivity needs only decreasing sinc and `sin q < q`. -/
lemma M_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hl : p + q < π) :
    0 < M p q := by
  have hpq := add_pos hp hq
  have hppi : p < π := by linarith
  have hc := sinc_strictAnti ⟨hp, hppi⟩ ⟨hpq, hl⟩ (lt_add_of_pos_right p hq)
  rw [div_lt_div_iff hpq hp] at hc
  have hfirst := mul_lt_mul_of_pos_right hc hq
  have hsecond := mul_lt_mul_of_pos_left (sin_lt hq)
    (mul_pos hp (sin_pos_of_pos_of_lt_pi hpq hl))
  unfold M
  nlinarith only [hfirst, hsecond]

private lemma complementary_sine (p q : ℝ) :
    sin (p + q) * cos p - cos (p + q) * sin p = sin q := by
  rw [← sin_sub]
  congr 1
  ring

/-- The endpoint response and the bracket factorization use only sine subtraction. -/
lemma bracket_identity (p q : ℝ) :
    (2 * ((p + q) - sin (p + q) * cos (p + q)) * M p q -
      determinant (p + q) * J p q) * M q p +
      2 * psi (p + q) * (M p q) ^ 2 = determinant (p + q) * theta p q := by
  let H := 2 * p * sin q - 2 * q * cos (p + q) * sin p
  have hresponse : determinant (p + q) * H =
      2 * ((p + q) - sin (p + q) * cos (p + q)) * M q p +
        2 * psi (p + q) * M p q := by
    dsimp [H, determinant, M, psi]
    rw [add_comm q p]
    ring
  have hjerk : J p q = (p + q) * q * cos p + q * sin p -
      p * cos (p + q) * sin q - sin (p + q) * sin q := by
    have hs := complementary_sine q p
    rw [add_comm q p] at hs
    unfold J
    linear_combination -p * hs
  have hbracket : H * M p q - M q p * J p q = theta p q := by
    rw [hjerk]
    dsimp [H, M, theta, determinant, psi]
    rw [add_comm q p]
    linear_combination
      (q * ((p + q) * q * sin p - p * sin (p + q) * sin q)) *
        complementary_sine p q
  calc
    _ = (2 * ((p + q) - sin (p + q) * cos (p + q)) * M q p +
        2 * psi (p + q) * M p q) * M p q -
          determinant (p + q) * M q p * J p q := by ring
    _ = determinant (p + q) * (H * M p q - M q p * J p q) := by
      rw [← hresponse]
      ring
    _ = determinant (p + q) * theta p q := by rw [hbracket]

/-- The physical per-gap scalar, with all six endpoint ratios visible here. -/
def C2 (p q : ℝ) : ℝ :=
  let d := determinant (p + q)
  let m0 := M p q / d
  let ml := M q p / d
  let j0 := -J p q / d
  let jl := J q p / d
  let a := 2 * ((p + q) - sin (p + q) * cos (p + q)) / d
  let b := 2 * psi (p + q) / d
  jl * m0 ^ 3 - j0 * ml ^ 3 - a * m0 * ml * (m0 ^ 2 + ml ^ 2) -
    2 * b * m0 ^ 2 * ml ^ 2

/-- The two-bracket identity exposes the sign without expanding the large scalar. -/
lemma C2_eq_negative_brackets (p q : ℝ) (hd : determinant (p + q) ≠ 0) :
    C2 p q * determinant (p + q) ^ 4 =
      -((M p q) ^ 2 * theta q p + (M q p) ^ 2 * theta p q) := by
  have hleft := bracket_identity p q
  have hright := bracket_identity q p
  rw [add_comm q p] at hright
  apply mul_right_cancel₀ hd
  have halgebra : C2 p q * determinant (p + q) ^ 5 =
      -((M p q) ^ 2 *
          ((2 * ((p + q) - sin (p + q) * cos (p + q)) * M q p -
            determinant (p + q) * J q p) * M p q +
              2 * psi (p + q) * (M q p) ^ 2) +
        (M q p) ^ 2 *
          ((2 * ((p + q) - sin (p + q) * cos (p + q)) * M p q -
            determinant (p + q) * J p q) * M q p +
              2 * psi (p + q) * (M p q) ^ 2)) := by
    unfold C2
    field_simp [hd]
    ring
  calc
    _ = C2 p q * determinant (p + q) ^ 5 := by ring
    _ = _ := halgebra
    _ = _ := by rw [hleft, hright]; ring

/-- The open-triangle scalar beam sign, proved locally from elementary calculus. -/
theorem C2_negative {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hl : p + q < π) :
    C2 p q < 0 := by
  have hd := determinant_pos (add_pos hp hq) hl.le
  have hleft := mul_pos (sq_pos_of_pos (M_pos hp hq hl))
    (theta_pos hq hp (by linarith))
  have hright := mul_pos (sq_pos_of_pos (M_pos hq hp (by linarith)))
    (theta_pos hp hq hl)
  have hmul : C2 p q * determinant (p + q) ^ 4 < 0 := by
    rw [C2_eq_negative_brackets p q (ne_of_gt hd)]
    linarith only [hleft, hright]
  exact (mul_lt_mul_right (pow_pos hd 4)).mp (by simpa using hmul)

/-- The local sign's two-arc coordinates and the Green endpoint coordinates
are exactly the same scalar, including every denominator. -/
theorem M_eq_curvatureNumerator (p q : ℝ) :
    M p q = curvatureNumerator (p + q) p := by
  rw [curvature_numerator_closed_form]
  simp only [M, show p + q - p = q by ring]

theorem J_eq_jerkNumerator (p q : ℝ) :
    J p q = jerkNumerator (p + q) p := by
  rw [jerk_numerator_closed_form]
  simp only [J, show p + q - p = q by ring]

theorem m0_pos {l p : ℝ} (hp : 0 < p) (hpl : p < l) (hlpi : l < π) :
    0 < m0 l p := by
  have hm := M_pos hp (sub_pos.mpr hpl) (by linarith : p + (l - p) < π)
  rw [M_eq_curvatureNumerator, show p + (l - p) = l by ring] at hm
  exact div_pos hm (determinant_pos (lt_trans hp hpl) hlpi.le)

theorem ml_pos {l p : ℝ} (hp : 0 < p) (hpl : p < l) (hlpi : l < π) :
    0 < ml l p := m0_pos (sub_pos.mpr hpl) (by linarith) hlpi

theorem a_pos {l : ℝ} (hl : 0 < l) (hlpi : l < π) : 0 < a l :=
  div_pos (mul_pos (by norm_num) (area_pos hl hlpi)) (determinant_pos hl hlpi.le)

theorem b_pos {l : ℝ} (hl : 0 < l) (hlpi : l < π) : 0 < b l :=
  div_pos (mul_pos (by norm_num) (psi_pos hl hlpi)) (determinant_pos hl hlpi.le)

/-- `eq:c2-paper`, with the generic sign result specialized to the actual
left/right Green readings. There is no assumed scalar sign. -/
theorem C2_endpoint_readings_negative {l p : ℝ}
    (hp : 0 < p) (hpl : p < l) (hlpi : l < π) :
    jl l p * m0 l p ^ 3 - j0 l p * ml l p ^ 3 -
      a l * m0 l p * ml l p * (m0 l p ^ 2 + ml l p ^ 2) -
      2 * b l * m0 l p ^ 2 * ml l p ^ 2 < 0 := by
  have h := C2_negative hp (sub_pos.mpr hpl) (by linarith : p + (l - p) < π)
  unfold C2 at h
  rw [M_eq_curvatureNumerator p (l - p), M_eq_curvatureNumerator (l - p) p,
    J_eq_jerkNumerator p (l - p), J_eq_jerkNumerator (l - p) p,
    show p + (l - p) = l by ring, show l - p + p = l by ring] at h
  exact h

def branch (z : ℝ) : ℝ := sin z + (π / 2 - z) * cos z
def branchD1 (z : ℝ) : ℝ := (z - π / 2) * sin z
def branchD2 (z : ℝ) : ℝ := sin z + (z - π / 2) * cos z
def branchD3 (z : ℝ) : ℝ := 2 * cos z - (z - π / 2) * sin z

theorem hasDerivAt_branch (z : ℝ) : HasDerivAt branch (branchD1 z) z := by
  convert (hasDerivAt_sin z).add
    (((hasDerivAt_id z).const_sub (π / 2)).mul (hasDerivAt_cos z)) using 1;
    dsimp [branch, branchD1]; ring

theorem hasDerivAt_branchD1 (z : ℝ) : HasDerivAt branchD1 (branchD2 z) z := by
  convert (((hasDerivAt_id z).sub_const (π / 2)).mul (hasDerivAt_sin z)) using 1;
    dsimp [branchD1, branchD2]; ring

theorem hasDerivAt_branchD2 (z : ℝ) : HasDerivAt branchD2 (branchD3 z) z := by
  convert (hasDerivAt_sin z).add
    (((hasDerivAt_id z).sub_const (π / 2)).mul (hasDerivAt_cos z)) using 1;
    dsimp [branchD2, branchD3]; ring

theorem hasDerivAt_psi (z : ℝ) : HasDerivAt psi (chi z) z := by
  convert (hasDerivAt_sin z).sub ((hasDerivAt_id z).mul (hasDerivAt_cos z)) using 1;
    dsimp [psi, chi]; ring

theorem hasDerivAt_chi (z : ℝ) : HasDerivAt chi (sin z + z * cos z) z := by
  convert (hasDerivAt_id z).mul (hasDerivAt_sin z) using 1;
    dsimp [chi]; ring

/-- The exact Taylor basis of every smooth kernel branch. -/
theorem branch_shift (x z : ℝ) :
    branch (x + z) = branch z * cos x + branchD1 z * sin x +
      cos z * psi x + sin z * chi x := by
  dsimp [branch, branchD1, psi, chi]
  rw [sin_add, cos_add]
  ring

theorem branchD1_shift (x z : ℝ) :
    branchD1 (x + z) = -branch z * sin x + branchD1 z * cos x +
      cos z * chi x + sin z * (sin x + x * cos x) := by
  dsimp [branch, branchD1, psi, chi]
  rw [sin_add]
  ring

/-- Crossing the teacher adds exactly the causal Green forcing term. -/
theorem branch_crossing (z : ℝ) : branch z - branch (z + π) = 2 * psi z := by
  simp only [branch, sin_add_pi, cos_add_pi]
  dsimp [psi]
  ring

theorem branchD1_crossing (z : ℝ) :
    branchD1 z - branchD1 (z + π) = 2 * chi z := by
  simp only [branchD1, sin_add_pi]
  dsimp [chi]
  ring

/-- `eq:kernel-jet`: the right and left kernel jets at a projective cut,
read in the smooth principal branch at zero and at π respectively. -/
theorem eq_kernel_jet :
    (branch 0, branchD1 0, branchD2 0, branchD3 0) = (π / 2, 0, -π / 2, 2) ∧
    (branch π, branchD1 π, branchD2 π, branchD3 π) = (π / 2, 0, -π / 2, -2) := by
  norm_num [branch, branchD1, branchD2, branchD3]; ring_nf; simp

/-- The kernel jet gives the one-sided jump used in the residual equation. -/
theorem branch_jerk_jump : branchD3 0 - branchD3 π = 4 := by
  have hp := congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) eq_kernel_jet.1
  have hm := congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) eq_kernel_jet.2
  dsimp only at hp hm
  linarith only [hp, hm]

def leftBranch (U V x : ℝ) : ℝ := U * psi x + V * chi x
def leftSlope (U V x : ℝ) : ℝ := U * chi x + V * (sin x + x * cos x)
def leftCurvature (U V x : ℝ) : ℝ :=
  U * (sin x + x * cos x) + V * (2 * cos x - x * sin x)
def leftJerk (U V x : ℝ) : ℝ :=
  U * (2 * cos x - x * sin x) + V * (-3 * sin x - x * cos x)

theorem hasDerivAt_leftBranch (U V x : ℝ) :
    HasDerivAt (leftBranch U V) (leftSlope U V x) x := by
  exact ((hasDerivAt_psi x).const_mul U).add ((hasDerivAt_chi x).const_mul V)

theorem hasDerivAt_leftSlope (U V x : ℝ) :
    HasDerivAt (leftSlope U V) (leftCurvature U V x) x := by
  convert ((hasDerivAt_chi x).const_mul U).add
    (((hasDerivAt_sin x).add ((hasDerivAt_id x).mul (hasDerivAt_cos x))).const_mul V)
    using 1; dsimp [leftSlope, leftCurvature]; ring

theorem hasDerivAt_leftCurvature (U V x : ℝ) :
    HasDerivAt (leftCurvature U V) (leftJerk U V x) x := by
  convert (((hasDerivAt_sin x).add ((hasDerivAt_id x).mul (hasDerivAt_cos x))).const_mul U).add
    ((((hasDerivAt_cos x).const_mul 2).sub
      ((hasDerivAt_id x).mul (hasDerivAt_sin x))).const_mul V)
    using 1; dsimp [leftCurvature, leftJerk]; ring

/-- Clamping at the far endpoint solves both unknown coefficients at once. -/
theorem clamped_coefficients {l p sigma U V : ℝ}
    (hdet : determinant l ≠ 0)
    (hvalue : leftBranch U V l = 2 * sigma * psi (l - p))
    (hslope : leftSlope U V l = 2 * sigma * chi (l - p)) :
    U = -2 * sigma * j0 l p ∧ V = -2 * sigma * m0 l p := by
  have hmatrix :
      psi l * (sin l + l * cos l) - chi l * chi l = -determinant l := by
    have h := clamped_matrix_determinant l
    change -(_ : ℝ) = determinant l at h
    linarith only [h]
  dsimp [leftBranch, leftSlope] at hvalue hslope
  constructor
  · dsimp [j0, jerkNumerator]
    field_simp [hdet]
    linear_combination -(sin l + l * cos l) * hvalue + chi l * hslope + U * hmatrix
  · dsimp [m0, curvatureNumerator]
    field_simp [hdet]
    linear_combination chi l * hvalue - psi l * hslope + V * hmatrix

theorem left_endpoint_jets {l p sigma U V : ℝ}
    (hdet : determinant l ≠ 0)
    (hvalue : leftBranch U V l = 2 * sigma * psi (l - p))
    (hslope : leftSlope U V l = 2 * sigma * chi (l - p)) :
    leftCurvature U V 0 = -4 * sigma * m0 l p ∧
      leftJerk U V 0 = -4 * sigma * j0 l p := by
  obtain ⟨hU, hV⟩ := clamped_coefficients hdet hvalue hslope
  simp only [leftCurvature, leftJerk, sin_zero, cos_zero, zero_mul, mul_zero,
    one_mul, mul_one, sub_zero, zero_add, add_zero]
  constructor
  · rw [hV]; ring
  · rw [hU]; ring

set_option maxHeartbeats 600000 in
theorem right_endpoint_jets {l p sigma U V : ℝ}
    (hdet : determinant l ≠ 0)
    (hvalue : leftBranch U V l = 2 * sigma * psi (l - p))
    (hslope : leftSlope U V l = 2 * sigma * chi (l - p)) :
    leftCurvature U V l - 2 * sigma * (sin (l - p) + (l - p) * cos (l - p)) =
        -4 * sigma * ml l p ∧
      leftJerk U V l - 2 * sigma * (2 * cos (l - p) - (l - p) * sin (l - p)) =
        -4 * sigma * jl l p := by
  obtain ⟨hU, hV⟩ := clamped_coefficients hdet hvalue hslope
  have hUd : U * determinant l = 2 * sigma * jerkNumerator l p := by
    rw [hU]
    dsimp [j0]
    field_simp [hdet]
  have hVd : V * determinant l = -2 * sigma * curvatureNumerator l p := by
    rw [hV]
    dsimp [m0]
    field_simp [hdet]
  have hc2 : cos l ^ 2 = 1 - sin l ^ 2 := by
    nlinarith only [sin_sq_add_cos_sq l]
  have hc3 : cos l ^ 3 = cos l * (1 - sin l ^ 2) := by
    rw [pow_succ, hc2]
  constructor
  · apply mul_right_cancel₀ hdet
    calc
      (leftCurvature U V l - 2 * sigma * (sin (l - p) + (l - p) * cos (l - p))) *
          determinant l =
        (U * determinant l) * (sin l + l * cos l) +
        (V * determinant l) * (2 * cos l - l * sin l) -
          2 * sigma * (sin (l - p) + (l - p) * cos (l - p)) * determinant l := by
            unfold leftCurvature
            ring
      _ = (-4 * sigma * ml l p) * determinant l := by
        rw [hUd, hVd]
        unfold ml
        simp only [mul_assoc, div_mul_cancel _ hdet]
        simp only [curvatureNumerator, jerkNumerator,
          show l - (l - p) = p by ring, psi, chi, determinant, sin_sub, cos_sub]
        ring_nf
        simp only [hc2, hc3]
        ring
  · apply mul_right_cancel₀ hdet
    calc
      (leftJerk U V l - 2 * sigma * (2 * cos (l - p) - (l - p) * sin (l - p))) *
          determinant l =
        (U * determinant l) * (2 * cos l - l * sin l) +
        (V * determinant l) * (-3 * sin l - l * cos l) -
          2 * sigma * (2 * cos (l - p) - (l - p) * sin (l - p)) * determinant l := by
            unfold leftJerk
            ring
      _ = (-4 * sigma * jl l p) * determinant l := by
        rw [hUd, hVd]
        unfold jl
        simp only [mul_assoc, div_mul_cancel _ hdet]
        simp only [curvatureNumerator, jerkNumerator,
          show l - (l - p) = p by ring, psi, chi, determinant, sin_sub, cos_sub]
        ring_nf
        simp only [hc2, hc3]
        ring

def smoothSum {ι : Type*} [Fintype ι] (weight offset : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, weight i * branch (x + offset i)
def smoothSumD1 {ι : Type*} [Fintype ι] (weight offset : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, weight i * branchD1 (x + offset i)
def cosineSum {ι : Type*} [Fintype ι] (weight offset : ι → ℝ) : ℝ :=
  ∑ i, weight i * cos (offset i)
def sineSum {ι : Type*} [Fintype ι] (weight offset : ι → ℝ) : ℝ :=
  ∑ i, weight i * sin (offset i)

theorem smoothSum_expansion {ι : Type*} [Fintype ι]
    (weight offset : ι → ℝ) (x : ℝ) :
    smoothSum weight offset x = smoothSum weight offset 0 * cos x +
      smoothSumD1 weight offset 0 * sin x +
      leftBranch (cosineSum weight offset) (sineSum weight offset) x := by
  unfold smoothSum smoothSumD1 leftBranch cosineSum sineSum
  simp only [zero_add, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [branch_shift]
  ring

theorem smoothSumD1_expansion {ι : Type*} [Fintype ι]
    (weight offset : ι → ℝ) (x : ℝ) :
    smoothSumD1 weight offset x = -smoothSum weight offset 0 * sin x +
      smoothSumD1 weight offset 0 * cos x +
      leftSlope (cosineSum weight offset) (sineSum weight offset) x := by
  unfold smoothSum smoothSumD1 leftSlope cosineSum sineSum
  simp only [zero_add, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [branchD1_shift]
  ring

/-- A finite residual in a one-teacher gap: the smooth continuation from the
left, followed by the teacher's explicit third-derivative jump. -/
def gapResidual {ι : Type*} [Fintype ι] (weight offset : ι → ℝ)
    (sigma p x : ℝ) : ℝ :=
  smoothSum weight offset x - if p ≤ x then 2 * sigma * psi (x - p) else 0

def gapSlope {ι : Type*} [Fintype ι] (weight offset : ι → ℝ)
    (sigma p x : ℝ) : ℝ :=
  smoothSumD1 weight offset x - if p ≤ x then 2 * sigma * chi (x - p) else 0

/-- Four criticality equations determine the entire clamped residual. -/
theorem critical_gap_coefficients {ι : Type*} [Fintype ι]
    (weight offset : ι → ℝ) {sigma p l : ℝ}
    (hp : 0 < p) (hpl : p < l) (hdet : determinant l ≠ 0)
    (hzero : gapResidual weight offset sigma p 0 = 0)
    (hslopeZero : gapSlope weight offset sigma p 0 = 0)
    (hend : gapResidual weight offset sigma p l = 0)
    (hslopeEnd : gapSlope weight offset sigma p l = 0) :
    cosineSum weight offset = -2 * sigma * j0 l p ∧
      sineSum weight offset = -2 * sigma * m0 l p := by
  have h0 : smoothSum weight offset 0 = 0 := by
    simpa only [gapResidual, if_neg (not_le.mpr hp), sub_zero] using hzero
  have h1 : smoothSumD1 weight offset 0 = 0 := by
    simpa only [gapSlope, if_neg (not_le.mpr hp), sub_zero] using hslopeZero
  apply clamped_coefficients hdet
  · dsimp [gapResidual] at hend
    rw [if_pos hpl.le, smoothSum_expansion, h0, h1] at hend
    simpa only [zero_mul, zero_add, sub_eq_zero] using hend
  · dsimp [gapSlope] at hslopeEnd
    rw [if_pos hpl.le, smoothSumD1_expansion, h0, h1] at hslopeEnd
    simpa only [neg_zero, zero_mul, zero_add, sub_eq_zero] using hslopeEnd

/-- The clamped profile is derived from the finite residual, not assumed. -/
theorem critical_gap_residual {ι : Type*} [Fintype ι]
    (weight offset : ι → ℝ) {sigma p l : ℝ}
    (hp : 0 < p) (hpl : p < l) (hdet : determinant l ≠ 0)
    (hzero : gapResidual weight offset sigma p 0 = 0)
    (hslopeZero : gapSlope weight offset sigma p 0 = 0)
    (hend : gapResidual weight offset sigma p l = 0)
    (hslopeEnd : gapSlope weight offset sigma p l = 0) (x : ℝ) :
    gapResidual weight offset sigma p x =
      -2 * sigma * (j0 l p * psi x + m0 l p * chi x +
        if p ≤ x then psi (x - p) else 0) := by
  obtain ⟨hU, hV⟩ := critical_gap_coefficients weight offset hp hpl hdet
    hzero hslopeZero hend hslopeEnd
  have h0 : smoothSum weight offset 0 = 0 := by
    simpa only [gapResidual, if_neg (not_le.mpr hp), sub_zero] using hzero
  have h1 : smoothSumD1 weight offset 0 = 0 := by
    simpa only [gapSlope, if_neg (not_le.mpr hp), sub_zero] using hslopeZero
  unfold gapResidual
  rw [smoothSum_expansion, h0, h1, hU, hV]
  unfold leftBranch
  split_ifs <;> ring

theorem smoothSum_hasDerivAt {ι : Type*} [Fintype ι]
    (weight offset : ι → ℝ) (x : ℝ) :
    HasDerivAt (smoothSum weight offset) (smoothSumD1 weight offset x) x := by
  apply HasDerivAt.sum
  intro i _
  convert ((hasDerivAt_branch (x + offset i)).comp x
    ((hasDerivAt_id x).add_const (offset i))).const_mul (weight i) using 1; simp

theorem rightBranch_hasDerivAt (U V sigma p x : ℝ) :
    HasDerivAt (fun y => leftBranch U V y - 2 * sigma * psi (y - p))
      (leftSlope U V x - 2 * sigma * chi (x - p)) x := by
  convert (hasDerivAt_leftBranch U V x).sub
    (((hasDerivAt_psi (x - p)).comp x
      ((hasDerivAt_id x).sub_const p)).const_mul (2 * sigma)) using 1; simp

theorem rightSlope_hasDerivAt (U V sigma p x : ℝ) :
    HasDerivAt (fun y => leftSlope U V y - 2 * sigma * chi (y - p))
      (leftCurvature U V x - 2 * sigma * (sin (x - p) + (x - p) * cos (x - p))) x := by
  convert (hasDerivAt_leftSlope U V x).sub
    (((hasDerivAt_chi (x - p)).comp x
      ((hasDerivAt_id x).sub_const p)).const_mul (2 * sigma)) using 1; simp

theorem rightCurvature_hasDerivAt (U V sigma p x : ℝ) :
    HasDerivAt (fun y => leftCurvature U V y -
      2 * sigma * (sin (y - p) + (y - p) * cos (y - p)))
      (leftJerk U V x - 2 * sigma * (2 * cos (x - p) - (x - p) * sin (x - p))) x := by
  have hf : HasDerivAt (fun z => sin z + z * cos z)
      (2 * cos (x - p) - (x - p) * sin (x - p)) (x - p) := by
    convert (hasDerivAt_sin (x - p)).add
      ((hasDerivAt_id (x - p)).mul (hasDerivAt_cos (x - p))) using 1; dsimp; ring
  convert (hasDerivAt_leftCurvature U V x).sub
    ((hf.comp x ((hasDerivAt_id x).sub_const p)).const_mul (2 * sigma)) using 1; simp

def cutJerkRight (a t : ℝ) : ℝ :=
  branchD3 (if t ≤ a then a - t else a - t + π)
def cutJerkLeft (a t : ℝ) : ℝ :=
  branchD3 (if t < a then a - t else a - t + π)

theorem cut_jerk_jump (a t : ℝ) :
    cutJerkRight a t - cutJerkLeft a t = if t = a then 4 else 0 := by
  rcases lt_trichotomy t a with h | h | h
  · simp [cutJerkRight, cutJerkLeft, h, h.le, ne_of_lt h]
  · subst t
    simpa [cutJerkRight, cutJerkLeft] using branch_jerk_jump
  · simp [cutJerkRight, cutJerkLeft, not_le.mpr h, not_lt.mpr h.le, ne_of_gt h]

/-- No sorted-gap machinery is needed for the mass jump: every non-boundary
atom cancels, and the unique boundary student contributes four times its mass. -/
theorem eq_LFC_jump {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c theta : ι → ℝ) (sigma beta : κ → ℝ)
    (hinj : Function.Injective theta) (i : ι)
    (hsep : ∀ k, beta k ≠ theta i) :
    ((∑ j, c j * cutJerkRight (theta i) (theta j)) -
      ∑ k, sigma k * cutJerkRight (theta i) (beta k)) -
    ((∑ j, c j * cutJerkLeft (theta i) (theta j)) -
      ∑ k, sigma k * cutJerkLeft (theta i) (beta k)) = 4 * c i := by
  classical
  have hstudent : (∑ j, c j * (cutJerkRight (theta i) (theta j) -
      cutJerkLeft (theta i) (theta j))) = 4 * c i := by
    simp only [cut_jerk_jump, hinj.eq_iff, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp [mul_comm]
  have hteacher : (∑ k, sigma k * (cutJerkRight (theta i) (beta k) -
      cutJerkLeft (theta i) (beta k))) = 0 := by
    simp only [cut_jerk_jump, if_neg (hsep _), mul_zero, Finset.sum_const_zero]
  simp only [mul_sub, Finset.sum_sub_distrib] at hstudent hteacher
  linarith only [hstudent, hteacher]

/-- Adjacent clamped jets and the actual residual jump identify the student mass. -/
theorem mass_of_adjacent_gap_jets {c sigmaPrev sigma lPrev pPrev l p right left : ℝ}
    (hleft : left = -4 * sigmaPrev * jl lPrev pPrev)
    (hright : right = -4 * sigma * j0 l p)
    (hjump : right - left = 4 * c) :
    c = sigmaPrev * jl lPrev pPrev - sigma * j0 l p := by
  rw [hleft, hright] at hjump
  linarith only [hjump]

/-- Continuity of the residual second derivative matches the adjacent masses. -/
theorem mass_match_of_adjacent_gap_curvatures
    {sigmaPrev sigma lPrev pPrev l p curvature : ℝ}
    (hleft : curvature = -4 * sigmaPrev * ml lPrev pPrev)
    (hright : curvature = -4 * sigma * m0 l p) :
    sigmaPrev * ml lPrev pPrev = sigma * m0 l p := by
  linarith only [hleft, hright]

/-! Mode choice and gluing. The profile and velocity remain visible here. -/

def d (l : ℝ) : ℝ := 8 * sin l ^ 2 / determinant l
def e (l : ℝ) : ℝ := 8 * l * sin l / determinant l

def profile (l u v z : ℝ) : ℝ :=
  -4 * (a l * u + b l * v) * cos z +
    (8 * (sin l ^ 2 * u + l * sin l * v) / (l ^ 2 - sin l ^ 2)) * sin z

def profileSlope (l u v z : ℝ) : ℝ :=
  4 * (a l * u + b l * v) * sin z +
    (8 * (sin l ^ 2 * u + l * sin l * v) / (l ^ 2 - sin l ^ 2)) * cos z

/-- `eq:beam-branch`: the profile in the paper's literal d/e coordinates. -/
theorem eq_beam_branch (l u v z : ℝ) :
    profile l u v z = -4 * (a l * u + b l * v) * cos z +
      (d l * u + e l * v) * sin z := by
  unfold profile d e determinant
  ring

theorem hasDerivAt_profile_display (l u v z : ℝ) :
    HasDerivAt (profile l u v)
      (4 * (a l * u + b l * v) * sin z + (d l * u + e l * v) * cos z) z := by
  have hf := funext (eq_beam_branch l u v)
  change profile l u v = (fun z => -4 * (a l * u + b l * v) * cos z +
    (d l * u + e l * v) * sin z) at hf
  rw [hf]
  convert ((hasDerivAt_cos z).const_mul (-4 * (a l * u + b l * v))).add
    ((hasDerivAt_sin z).const_mul (d l * u + e l * v)) using 1
  ring

def angleMomentum {n : ℕ} [NeZero n] (a b u : Fin n → ℝ) (i : Fin n) : ℝ :=
  (a i + a (i - 1)) * u i + b i * u (i + 1) + b (i - 1) * u (i - 1)

/-- `eq:beam-curvature-matching-paper` implies `eq:beam-reciprocal-mass-paper`. -/
theorem reciprocal_mass_of_curvature_match {sigma sigmaNext ml m0Next : ℝ}
    (hmatch : -4 * sigma * ml = -4 * sigmaNext * m0Next) :
    1 / (sigmaNext * m0Next) = 1 / (sigma * ml) := by
  congr 1
  linarith

theorem reciprocal_mode_pos {sigma m0 : ℝ} (hsigma : 0 < sigma) (hm0 : 0 < m0) :
    0 < 1 / (sigma * m0) := one_div_pos.mpr (mul_pos hsigma hm0)

theorem hasDerivAt_profile (l u v z : ℝ) :
    HasDerivAt (profile l u v) (profileSlope l u v z) z := by
  unfold profile profileSlope
  convert ((hasDerivAt_cos z).const_mul (-4 * (a l * u + b l * v))).add
    ((hasDerivAt_sin z).const_mul
      (8 * (sin l ^ 2 * u + l * sin l * v) / (l ^ 2 - sin l ^ 2))) using 1; ring

/-- All four readings of `eq:beam-profile-endpoints-paper`, in one place. -/
private theorem profile_endpoints (l u v : ℝ) :
    profile l u v 0 = -4 * (a l * u + b l * v) ∧
    profile l u v l = 4 * (b l * u + a l * v) ∧
    profileSlope l u v 0 = 8 * (sin l ^ 2 * u + l * sin l * v) / determinant l ∧
    profileSlope l u v l = 8 * (l * sin l * u + sin l ^ 2 * v) / determinant l := by
  have ht := sin_sq_add_cos_sq l
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [profile]
  · unfold profile a b
    simp only [div_eq_mul_inv]
    linear_combination 8 * (l * v + sin l * u) * (l ^ 2 - sin l ^ 2)⁻¹ * ht
  · simp [profileSlope, determinant]
  · unfold profileSlope a b determinant
    simp only [div_eq_mul_inv]
    ring

/-- `eq:beam-branch-start`: the value and actual derivative at zero, in
literal d/e coordinates; the explicit slope formula is retained as well. -/
theorem eq_beam_branch_start (l u v : ℝ) :
    profile l u v 0 = -4 * (a l * u + b l * v) ∧
    profileSlope l u v 0 = 8 * (sin l ^ 2 * u + l * sin l * v) / determinant l ∧
    HasDerivAt (profile l u v) (d l * u + e l * v) 0 ∧
    deriv (profile l u v) 0 = d l * u + e l * v := by
  have hd : HasDerivAt (profile l u v) (d l * u + e l * v) 0 := by
    simpa only [sin_zero, cos_zero, mul_zero, mul_one, zero_add] using
      hasDerivAt_profile_display l u v 0
  refine ⟨?_, ?_, hd, hd.deriv⟩
  · simp only [eq_beam_branch, sin_zero, cos_zero, mul_one, mul_zero, add_zero]
  · simp only [profileSlope, sin_zero, cos_zero, mul_zero, mul_one, zero_add, determinant]

/-- `eq:beam-branch-end`: the value and actual derivative at the right
endpoint, together with the explicit slope formula. -/
theorem eq_beam_branch_end (l u v : ℝ) :
    profile l u v l = 4 * (b l * u + a l * v) ∧
    profileSlope l u v l = 8 * (l * sin l * u + sin l ^ 2 * v) / determinant l ∧
    HasDerivAt (profile l u v) (e l * u + d l * v) l ∧
    deriv (profile l u v) l = e l * u + d l * v := by
  have hd : HasDerivAt (profile l u v) (e l * u + d l * v) l := by
    convert hasDerivAt_profile_display l u v l using 1
    unfold a b d e determinant
    ring
  exact ⟨(profile_endpoints l u v).2.1, (profile_endpoints l u v).2.2.2, hd, hd.deriv⟩

/-! Integrating one gap: the Riesz identity gives the energy directly. -/

/-- `eq:beam-sinusoid-gram`: the actual Gram matrix of cosine and sine. -/
theorem eq_beam_sinusoid_gram (l : ℝ) :
    (fun i j : Fin 2 =>
      ∫ z in (0 : ℝ)..l, (![cos z, sin z] i) * (![cos z, sin z] j)) =
      (1 / 2 : ℝ) •
        (!![l + sin l * cos l, sin l ^ 2;
          sin l ^ 2, l - sin l * cos l] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (∫ z in (0 : ℝ)..l, cos z * cos z) = (1 / 2) * (l + sin l * cos l)
    simp only [← pow_two]
    rw [integral_cos_sq, sin_zero, cos_zero]
    ring
  · change (∫ z in (0 : ℝ)..l, cos z * sin z) = (1 / 2) * sin l ^ 2
    simp only [mul_comm (cos _) (sin _)]
    rw [integral_sin_mul_cos₁, sin_zero]
    ring
  · change (∫ z in (0 : ℝ)..l, sin z * cos z) = (1 / 2) * sin l ^ 2
    rw [integral_sin_mul_cos₁, sin_zero]
    ring
  · change (∫ z in (0 : ℝ)..l, sin z * sin z) = (1 / 2) * (l - sin l * cos l)
    simp only [← pow_two]
    rw [integral_sin_sq, sin_zero, cos_zero]
    ring

/-- The sinusoid product integral is the bilinear form of its actual Gram matrix. -/
theorem integral_sinusoid_product (A B C D l : ℝ) :
    (∫ z in (0 : ℝ)..l, (A * cos z + B * sin z) * (C * cos z + D * sin z)) =
      A * C * (l + sin l * cos l) / 2 +
      (A * D + B * C) * sin l ^ 2 / 2 + B * D * (l - sin l * cos l) / 2 := by
  have hcc := (continuous_cos.pow 2).intervalIntegrable (μ := volume) 0 l
  have hsc := (continuous_sin.mul continuous_cos).intervalIntegrable (μ := volume) 0 l
  have hss := (continuous_sin.pow 2).intervalIntegrable (μ := volume) 0 l
  have hgram := eq_beam_sinusoid_gram l
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hgram
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hgram
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hgram
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    ← pow_two] at h00 h10 h11
  calc
    (∫ z in (0 : ℝ)..l, (A * cos z + B * sin z) * (C * cos z + D * sin z)) =
        ∫ z in (0 : ℝ)..l, (A * C) * cos z ^ 2 +
          (A * D + B * C) * (sin z * cos z) + (B * D) * sin z ^ 2 := by
      apply intervalIntegral.integral_congr
      intro z _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((hcc.const_mul _).add (hsc.const_mul _))
          (hss.const_mul _), intervalIntegral.integral_add (hcc.const_mul _) (hsc.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
      rw [h00, h10, h11]
      ring

/-- The matrix-vector part of `eq:beam-riesz-paper`, proved simultaneously
for both coordinates. -/
theorem profile_riesz_coordinates {l : ℝ} (u v : ℝ) (hdet : determinant l ≠ 0) :
    ((l + sin l * cos l) / 2) * (-4 * (a l * u + b l * v)) +
        (sin l ^ 2 / 2) * (8 * (sin l ^ 2 * u + l * sin l * v) / determinant l) =
      4 * (v * cos l - u) ∧
    (sin l ^ 2 / 2) * (-4 * (a l * u + b l * v)) +
        ((l - sin l * cos l) / 2) *
          (8 * (sin l ^ 2 * u + l * sin l * v) / determinant l) = 4 * v * sin l := by
  dsimp [determinant] at hdet
  constructor <;> dsimp [a, b, determinant] <;> field_simp [hdet]
  · have hc : cos l ^ 2 = 1 - sin l ^ 2 := by nlinarith [sin_sq_add_cos_sq l]
    ring_nf
    rw [hc]
    ring
  · ring

/-- `eq:beam-riesz-paper`: the local beam represents the endpoint functional
on the whole two-dimensional sinusoid space. -/
theorem profile_riesz {l : ℝ} (u v C D : ℝ) (hdet : determinant l ≠ 0) :
    (∫ z in (0 : ℝ)..l, profile l u v z * (C * cos z + D * sin z)) =
      4 * (v * (C * cos l + D * sin l) - u * C) := by
  unfold profile
  rw [integral_sinusoid_product]
  obtain ⟨hc, hs⟩ := profile_riesz_coordinates u v hdet
  dsimp [determinant] at hc hs
  linear_combination C * hc + D * hs

/-- Taking the beam itself as test function proves its exact squared energy. -/
theorem eq_beam_branch_energy {l : ℝ} (u v : ℝ) (hdet : determinant l ≠ 0) :
    (∫ z in (0 : ℝ)..l, profile l u v z ^ 2) =
      16 * (a l * (u ^ 2 + v ^ 2) + 2 * b l * u * v) := by
  have h := profile_riesz u v (-4 * (a l * u + b l * v))
    (8 * (sin l ^ 2 * u + l * sin l * v) / determinant l) hdet
  change (∫ z in (0 : ℝ)..l, profile l u v z * profile l u v z) =
    4 * (v * profile l u v l - u * (-4 * (a l * u + b l * v))) at h
  simp only [← pow_two] at h
  rw [(eq_beam_branch_end _ _ _).1] at h
  rw [h]
  ring

/-- The assigned values at feature kinks preserve the exact period. -/
theorem feature_periodic {n : ℕ} (dc x theta : Fin n → ℝ) :
    Function.Periodic (feature dc x theta) π := by
  intro y
  unfold feature
  apply Finset.sum_congr rfl
  intro i _
  rw [show y + π - theta i = (y - theta i) + π by ring,
    cos_add_pi, sin_add_pi, abs_neg, Real.sign_neg]
  ring

/-- Shifting and doubling the feature contributes exactly a factor of four. -/
theorem integral_shifted_feature_sq {n : ℕ} (dc x theta : Fin n → ℝ) (base : ℝ) :
    (∫ y in base..(base + π), (2 * feature dc x theta (y + π / 2)) ^ 2) =
      4 * featureEnergy dc x theta := by
  have hp : Function.Periodic (fun y => feature dc x theta y ^ 2) π :=
    fun y => congrArg (fun z : ℝ => z ^ 2) (feature_periodic dc x theta y)
  calc
    (∫ y in base..(base + π), (2 * feature dc x theta (y + π / 2)) ^ 2) =
        4 * ∫ y in base..(base + π), feature dc x theta (y + π / 2) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      ring
    _ = 4 * ∫ y in (base + π / 2)..(base + π / 2 + π), feature dc x theta y ^ 2 := by
      rw [intervalIntegral.integral_comp_add_right
        (f := fun y => feature dc x theta y ^ 2) (π / 2)]
      congr 2; ring
    _ = 4 * featureEnergy dc x theta := by
      rw [hp.intervalIntegral_add_eq (base + π / 2) 0]
      rw [zero_add]
      rfl

/-- A gapwise sinusoid supplies its own integrability; no separate measurable
feature expansion is needed. Endpoints, a null set, have no effect. -/
theorem intervalIntegral_eq_of_open_gap {f g : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (h : ∀ x ∈ Set.Ioo l r, f x = g x) :
    (∫ x in l..r, f x) = ∫ x in l..r, g x := by
  rw [intervalIntegral.integral_of_le hlr, intervalIntegral.integral_of_le hlr,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact set_integral_congr measurableSet_Ioo h

/-- The integral over one cycle is the sum of the local Riesz energies.
Cuts are an increasing finite prefix of an ordinary sequence, which avoids
sorting machinery and cyclic casts in the integration argument. -/
theorem integral_gap_profile_cycle {n : ℕ} (cut u : ℕ → ℝ) (f : ℝ → ℝ)
    (hcut : ∀ g < n, cut g < cut (g + 1))
    (hdet : ∀ g < n, determinant (cut (g + 1) - cut g) ≠ 0)
    (hrealize : ∀ g < n, ∀ y ∈ Set.Ioo (cut g) (cut (g + 1)),
      f y = profile (cut (g + 1) - cut g) (u g) (u (g + 1)) (y - cut g)) :
    (∫ y in (cut 0)..(cut n), f y ^ 2) =
      16 * ∑ g in Finset.range n,
        (a (cut (g + 1) - cut g) * (u g ^ 2 + u (g + 1) ^ 2) +
          2 * b (cut (g + 1) - cut g) * u g * u (g + 1)) := by
  have hcontinuous : ∀ g, Continuous (fun y =>
      profile (cut (g + 1) - cut g) (u g) (u (g + 1)) (y - cut g) ^ 2) := by
    intro g
    unfold profile
    continuity
  have hint : ∀ g < n, IntervalIntegrable (fun y => f y ^ 2) volume (cut g) (cut (g + 1)) := by
    intro g hg
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (hcut g hg).le]
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (hcut g hg).le).mp
      ((hcontinuous g).intervalIntegrable (μ := volume) (cut g) (cut (g + 1)))
    exact hi.congr_fun (fun y hy => congrArg (fun z : ℝ => z ^ 2)
      (hrealize g hg y hy).symm) measurableSet_Ioo
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have hgn := Finset.mem_range.mp hg
  rw [intervalIntegral_eq_of_open_gap (hcut g hgn).le (fun y hy =>
    congrArg (fun z : ℝ => z ^ 2) (hrealize g hgn y hy)),
    intervalIntegral.integral_comp_sub_right
      (f := fun z => profile (cut (g + 1) - cut g) (u g) (u (g + 1)) z ^ 2) (cut g)]
  rw [sub_self]
  exact eq_beam_branch_energy (u g) (u (g + 1)) (hdet g hgn)

/-- Feature realization and the local Riesz formula imply the whole energy
identity; this is the integral step preceding `eq:beam-pairing-paper`. -/
theorem feature_energy_of_gap_realization {n : ℕ} (dc x theta : Fin n → ℝ)
    (cut u : ℕ → ℝ) (hperiod : cut n = cut 0 + π)
    (hcut : ∀ g < n, cut g < cut (g + 1))
    (hdet : ∀ g < n, determinant (cut (g + 1) - cut g) ≠ 0)
    (hrealize : ∀ g < n, ∀ y ∈ Set.Ioo (cut g) (cut (g + 1)),
      2 * feature dc x theta (y + π / 2) =
        profile (cut (g + 1) - cut g) (u g) (u (g + 1)) (y - cut g)) :
    featureEnergy dc x theta = 4 * ∑ g in Finset.range n,
      (a (cut (g + 1) - cut g) * (u g ^ 2 + u (g + 1) ^ 2) +
        2 * b (cut (g + 1) - cut g) * u g * u (g + 1)) := by
  have h := integral_gap_profile_cycle cut u
    (fun y => 2 * feature dc x theta (y + π / 2)) hcut hdet hrealize
  rw [hperiod, integral_shifted_feature_sq] at h
  linarith

/-- The mode has all angular components in the same sense. -/
theorem angleMomentum_pos {n : ℕ} [NeZero n] (a b u : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hu : ∀ i, 0 < u i) :
    ∀ i, 0 < angleMomentum a b u i := by
  intro i
  exact add_pos (add_pos (mul_pos (add_pos (ha i) (ha (i - 1))) (hu i))
    (mul_pos (hb i) (hu (i + 1)))) (mul_pos (hb (i - 1)) (hu (i - 1)))

def sinePiece (A B t : ℝ) : ℝ := A * cos t + B * sin t
def sinePieceSlope (A B t : ℝ) : ℝ := -A * sin t + B * cos t

/-- The value and slope are rotation coordinates for the two coefficients. -/
theorem sinePiece_coefficients {A B C D t : ℝ}
    (hv : sinePiece A B t = sinePiece C D t)
    (hd : sinePieceSlope A B t = sinePieceSlope C D t) : A = C ∧ B = D := by
  unfold sinePiece at hv
  unfold sinePieceSlope at hd
  have htrig := sin_sq_add_cos_sq t
  constructor
  · linear_combination cos t * hv - sin t * hd - (A - C) * htrig
  · linear_combination sin t * hv + cos t * hd - (B - D) * htrig

/-- Ordered gaps need no cyclic-index infrastructure: equal jumps propagate
the difference coefficients, and the final half-turn kills both coefficients. -/
theorem eq_beam_periodic_antiperiodic {N : ℕ} (θ A B C D : ℕ → ℝ)
    (hvalue : ∀ k < N,
      sinePiece (A (k + 1)) (B (k + 1)) (θ (k + 1)) -
        sinePiece (A k) (B k) (θ (k + 1)) =
      sinePiece (C (k + 1)) (D (k + 1)) (θ (k + 1)) -
        sinePiece (C k) (D k) (θ (k + 1)))
    (hslope : ∀ k < N,
      sinePieceSlope (A (k + 1)) (B (k + 1)) (θ (k + 1)) -
        sinePieceSlope (A k) (B k) (θ (k + 1)) =
      sinePieceSlope (C (k + 1)) (D (k + 1)) (θ (k + 1)) -
        sinePieceSlope (C k) (D k) (θ (k + 1)))
    (hwrapValue : sinePiece (A 0) (B 0) (θ 0) -
        sinePiece (A N) (B N) (θ 0 + π) =
      sinePiece (C 0) (D 0) (θ 0) - sinePiece (C N) (D N) (θ 0 + π))
    (hwrapSlope : sinePieceSlope (A 0) (B 0) (θ 0) -
        sinePieceSlope (A N) (B N) (θ 0 + π) =
      sinePieceSlope (C 0) (D 0) (θ 0) -
        sinePieceSlope (C N) (D N) (θ 0 + π)) :
    ∀ g ≤ N, ∀ t, sinePiece (A g) (B g) t = sinePiece (C g) (D g) t := by
  have step : ∀ k < N, A (k + 1) - C (k + 1) = A k - C k ∧
      B (k + 1) - D (k + 1) = B k - D k := by
    intro k hk
    apply sinePiece_coefficients (t := θ (k + 1))
    · have h := hvalue k hk
      dsimp [sinePiece] at h ⊢
      linarith only [h]
    · have h := hslope k hk
      dsimp [sinePieceSlope] at h ⊢
      linarith only [h]
  have constant : ∀ g ≤ N, A g - C g = A 0 - C 0 ∧ B g - D g = B 0 - D 0 := by
    intro g
    induction g with
    | zero => intro _; exact ⟨rfl, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨hA, hB⟩ := step k (by omega (config := {}))
      obtain ⟨hA0, hB0⟩ := ih (by omega (config := {}))
      exact ⟨hA.trans hA0, hB.trans hB0⟩
  obtain ⟨hA, hB⟩ := constant N le_rfl
  have hv : sinePiece (A 0 - C 0) (B 0 - D 0) (θ 0) = sinePiece 0 0 (θ 0) := by
    dsimp [sinePiece] at hwrapValue ⊢
    rw [cos_add_pi, sin_add_pi] at hwrapValue
    linear_combination (hwrapValue - cos (θ 0) * hA - sin (θ 0) * hB) / 2
  have hd : sinePieceSlope (A 0 - C 0) (B 0 - D 0) (θ 0) =
      sinePieceSlope 0 0 (θ 0) := by
    dsimp [sinePieceSlope] at hwrapSlope ⊢
    rw [cos_add_pi, sin_add_pi] at hwrapSlope
    linear_combination (hwrapSlope + sin (θ 0) * hA - cos (θ 0) * hB) / 2
  obtain ⟨hA0, hB0⟩ := sinePiece_coefficients hv hd
  intro g hg t
  obtain ⟨hAg, hBg⟩ := constant g hg
  have hAc : A g = C g := by linarith only [hAg, hA0]
  have hBc : B g = D g := by linarith only [hBg, hB0]
  rw [hAc, hBc]

def atomBranch (dc x θ t : ℝ) : ℝ := 2 * (dc * sin (t - θ) - x * cos (t - θ))
def atomBranchSlope (dc x θ t : ℝ) : ℝ :=
  2 * (dc * cos (t - θ) + x * sin (t - θ))

def cutBranch (N : ℕ) (dc x θ : ℕ → ℝ) (g : ℕ) (t : ℝ) : ℝ :=
  ∑ i in Finset.range (N + 1), if i ≤ g then atomBranch (dc i) (x i) (θ i) t
    else -atomBranch (dc i) (x i) (θ i) t

def cutBranchSlope (N : ℕ) (dc x θ : ℕ → ℝ) (g : ℕ) (t : ℝ) : ℝ :=
  ∑ i in Finset.range (N + 1), if i ≤ g then atomBranchSlope (dc i) (x i) (θ i) t
    else -atomBranchSlope (dc i) (x i) (θ i) t

theorem hasDerivAt_atomBranch (dc x θ t : ℝ) :
    HasDerivAt (atomBranch dc x θ) (atomBranchSlope dc x θ t) t := by
  have hs := (hasDerivAt_sin (t - θ)).comp t ((hasDerivAt_id t).sub_const θ)
  have hc := (hasDerivAt_cos (t - θ)).comp t ((hasDerivAt_id t).sub_const θ)
  simpa only [atomBranch, atomBranchSlope, Function.comp_apply, mul_one,
    mul_neg, sub_neg_eq_add] using ((hs.const_mul dc).sub (hc.const_mul x)).const_mul 2

theorem hasDerivAt_cutBranch (N : ℕ) (dc x θ : ℕ → ℝ) (g : ℕ) (t : ℝ) :
    HasDerivAt (cutBranch N dc x θ g) (cutBranchSlope N dc x θ g t) t := by
  unfold cutBranch cutBranchSlope
  apply HasDerivAt.sum
  intro i _
  by_cases hi : i ≤ g
  · simp only [hi, if_true]
    exact hasDerivAt_atomBranch (dc i) (x i) (θ i) t
  · simp only [hi, if_false]
    exact (hasDerivAt_atomBranch (dc i) (x i) (θ i) t).neg

theorem deriv_cutBranch (N : ℕ) (dc x θ : ℕ → ℝ) (g : ℕ) (t : ℝ) :
    deriv (cutBranch N dc x θ g) t = cutBranchSlope N dc x θ g t :=
  (hasDerivAt_cutBranch N dc x θ g t).deriv

/-- One cut changes one summand; this supplies both value and slope jumps. -/
theorem signed_sum_cut_jump {N k : ℕ} (hk : k < N) (f : ℕ → ℝ) :
    (∑ i in Finset.range (N + 1), if i ≤ k + 1 then f i else -f i) -
      (∑ i in Finset.range (N + 1), if i ≤ k then f i else -f i) = 2 * f (k + 1) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i in Finset.range (N + 1), if i = k + 1 then 2 * f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ≤ k
      · simp [hi, show i ≤ k + 1 by omega (config := {}), show i ≠ k + 1 by omega (config := {})]
      · by_cases hj : i = k + 1
        · subst i; simp [hi]; ring
        · simp [hi, hj, show ¬ i ≤ k + 1 by omega (config := {})]
    _ = _ := by simp [Finset.mem_range, hk, Nat.not_le.mpr hk]

theorem cutBranch_value_slope_jumps {N k : ℕ} (hk : k < N) (dc x θ : ℕ → ℝ) :
    cutBranch N dc x θ (k + 1) (θ (k + 1)) -
      cutBranch N dc x θ k (θ (k + 1)) = -4 * x (k + 1) ∧
    cutBranchSlope N dc x θ (k + 1) (θ (k + 1)) -
      cutBranchSlope N dc x θ k (θ (k + 1)) = 4 * dc (k + 1) := by
  constructor
  · rw [cutBranch, cutBranch, signed_sum_cut_jump hk]
    simp [atomBranch]
    ring
  · rw [cutBranchSlope, cutBranchSlope, signed_sum_cut_jump hk]
    simp [atomBranchSlope]
    ring

/-- The lifted last cut gives the same two jumps as an ordinary cut. -/
theorem cutBranch_wrap (N : ℕ) (dc x θ : ℕ → ℝ) :
    cutBranch N dc x θ 0 (θ 0) - cutBranch N dc x θ N (θ 0 + π) = -4 * x 0 ∧
    cutBranchSlope N dc x θ 0 (θ 0) -
      cutBranchSlope N dc x θ N (θ 0 + π) = 4 * dc 0 := by
  have wrap : ∀ f : ℕ → ℝ,
      (∑ i in Finset.range (N + 1), if i ≤ 0 then f i else -f i) -
        (∑ i in Finset.range (N + 1), -f i) = 2 * f 0 := by
    intro f
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i in Finset.range (N + 1), if i = 0 then 2 * f i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = 0
        · subst i
          simp only [le_refl, if_true]
          ring
        · simp [hi]
      _ = _ := by simp
  have anti : ∀ i, atomBranch (dc i) (x i) (θ i) (θ 0 + π) =
      -atomBranch (dc i) (x i) (θ i) (θ 0) := by
    intro i
    unfold atomBranch
    rw [show θ 0 + π - θ i = (θ 0 - θ i) + π by ring, sin_add_pi, cos_add_pi]
    ring
  have antiSlope : ∀ i, atomBranchSlope (dc i) (x i) (θ i) (θ 0 + π) =
      -atomBranchSlope (dc i) (x i) (θ i) (θ 0) := by
    intro i
    unfold atomBranchSlope
    rw [show θ 0 + π - θ i = (θ 0 - θ i) + π by ring, sin_add_pi, cos_add_pi]
    ring
  constructor
  · unfold cutBranch
    have hlast : ∀ i ∈ Finset.range (N + 1),
        (if i ≤ N then atomBranch (dc i) (x i) (θ i) (θ 0 + π)
          else -atomBranch (dc i) (x i) (θ i) (θ 0 + π)) =
        -atomBranch (dc i) (x i) (θ i) (θ 0) := by
      intro i hi
      rw [if_pos (by simp only [Finset.mem_range] at hi; omega (config := {})), anti]
    rw [Finset.sum_congr rfl hlast, wrap]
    simp [atomBranch]
    ring
  · unfold cutBranchSlope
    have hlast : ∀ i ∈ Finset.range (N + 1),
        (if i ≤ N then atomBranchSlope (dc i) (x i) (θ i) (θ 0 + π)
          else -atomBranchSlope (dc i) (x i) (θ i) (θ 0 + π)) =
        -atomBranchSlope (dc i) (x i) (θ i) (θ 0) := by
      intro i hi
      rw [if_pos (by simp only [Finset.mem_range] at hi; omega (config := {})), antiSlope]
    rw [Finset.sum_congr rfl hlast, wrap]
    simp [atomBranchSlope]
    ring

/-- `eq:beam-feature-jumps`: actual value and derivative jumps at an ordinary student cut. -/
theorem eq_beam_feature_jumps {N k : ℕ} (hk : k < N) (dc x θ : ℕ → ℝ) :
    cutBranch N dc x θ (k + 1) (θ (k + 1)) -
      cutBranch N dc x θ k (θ (k + 1)) = -4 * x (k + 1) ∧
    deriv (cutBranch N dc x θ (k + 1)) (θ (k + 1)) -
      deriv (cutBranch N dc x θ k) (θ (k + 1)) = 4 * dc (k + 1) := by
  simpa only [deriv_cutBranch] using cutBranch_value_slope_jumps hk dc x θ

/-- `eq:beam-feature-jumps`, cyclic wrap: the same actual derivative statement at the lifted cyclic cut. -/
theorem eq_beam_feature_jumps_wrap (N : ℕ) (dc x θ : ℕ → ℝ) :
    cutBranch N dc x θ 0 (θ 0) - cutBranch N dc x θ N (θ 0 + π) = -4 * x 0 ∧
    deriv (cutBranch N dc x θ 0) (θ 0) -
      deriv (cutBranch N dc x θ N) (θ 0 + π) = 4 * dc 0 := by
  simpa only [deriv_cutBranch] using cutBranch_wrap N dc x θ

def cutCos (N : ℕ) (dc x θ : ℕ → ℝ) (g : ℕ) : ℝ :=
  ∑ i in Finset.range (N + 1), if i ≤ g then 2 * (-dc i * sin (θ i) - x i * cos (θ i))
    else -(2 * (-dc i * sin (θ i) - x i * cos (θ i)))

def cutSin (N : ℕ) (dc x θ : ℕ → ℝ) (g : ℕ) : ℝ :=
  ∑ i in Finset.range (N + 1), if i ≤ g then 2 * (dc i * cos (θ i) - x i * sin (θ i))
    else -(2 * (dc i * cos (θ i) - x i * sin (θ i)))

theorem cutBranch_coefficients (N : ℕ) (dc x θ : ℕ → ℝ) (g : ℕ) (t : ℝ) :
    cutBranch N dc x θ g t = sinePiece (cutCos N dc x θ g) (cutSin N dc x θ g) t ∧
    cutBranchSlope N dc x θ g t =
      sinePieceSlope (cutCos N dc x θ g) (cutSin N dc x θ g) t := by
  constructor
  · unfold cutBranch cutCos cutSin sinePiece
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold atomBranch
    rw [sin_sub, cos_sub]
    split_ifs <;> ring
  · unfold cutBranchSlope cutCos cutSin sinePieceSlope
    rw [neg_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold atomBranchSlope
    rw [sin_sub, cos_sub]
    split_ifs <;> ring

/-- Every finite cyclic family of sinusoidal pieces is reconstructed by the
mass and angular velocities read directly from its endpoint jumps. -/
theorem cutBranch_reconstructs {N : ℕ} (θ A B dc x : ℕ → ℝ)
    (hvalue : ∀ k < N,
      sinePiece (A (k + 1)) (B (k + 1)) (θ (k + 1)) -
        sinePiece (A k) (B k) (θ (k + 1)) = -4 * x (k + 1))
    (hslope : ∀ k < N,
      sinePieceSlope (A (k + 1)) (B (k + 1)) (θ (k + 1)) -
        sinePieceSlope (A k) (B k) (θ (k + 1)) = 4 * dc (k + 1))
    (hwrapValue : sinePiece (A 0) (B 0) (θ 0) -
      sinePiece (A N) (B N) (θ 0 + π) = -4 * x 0)
    (hwrapSlope : sinePieceSlope (A 0) (B 0) (θ 0) -
      sinePieceSlope (A N) (B N) (θ 0 + π) = 4 * dc 0) :
    ∀ g ≤ N, ∀ t, cutBranch N dc x θ g t = sinePiece (A g) (B g) t := by
  have hjumps := fun k (hk : k < N) => eq_beam_feature_jumps hk dc x θ
  have hwrap := eq_beam_feature_jumps_wrap N dc x θ
  simp only [deriv_cutBranch] at hjumps hwrap
  have uniq := eq_beam_periodic_antiperiodic (N := N) θ A B (cutCos N dc x θ) (cutSin N dc x θ)
  have hEq := uniq (fun k hk => by
      rw [← (cutBranch_coefficients N dc x θ (k + 1) (θ (k + 1))).1,
        ← (cutBranch_coefficients N dc x θ k (θ (k + 1))).1, hvalue k hk,
        (hjumps k hk).1])
    (fun k hk => by
      rw [← (cutBranch_coefficients N dc x θ (k + 1) (θ (k + 1))).2,
        ← (cutBranch_coefficients N dc x θ k (θ (k + 1))).2, hslope k hk,
        (hjumps k hk).2])
    (by rw [← (cutBranch_coefficients N dc x θ 0 (θ 0)).1,
        ← (cutBranch_coefficients N dc x θ N (θ 0 + π)).1,
        hwrapValue, hwrap.1])
    (by rw [← (cutBranch_coefficients N dc x θ 0 (θ 0)).2,
        ← (cutBranch_coefficients N dc x θ N (θ 0 + π)).2,
        hwrapSlope, hwrap.2])
  intro g hg t
  rw [(cutBranch_coefficients N dc x θ g t).1]
  exact (hEq g hg t).symm

def rangeFeature (N : ℕ) (dc x θ : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ i in Finset.range (N + 1), (dc i * |cos (y - θ i)| +
    x i * Real.sign (cos (y - θ i)) * sin (y - θ i))

/-- On an open gap, the literal feature is its sine branch. The corner values
are deliberately excluded: the velocity uses `sign 0 = 0` there. -/
theorem eq_beam_gap_sinusoid {N g : ℕ} (dc x θ : ℕ → ℝ) (t : ℝ)
    (hgap : ∀ i ≤ N, if i ≤ g then 0 < t - θ i ∧ t - θ i < π
      else -π < t - θ i ∧ t - θ i < 0) :
    2 * rangeFeature N dc x θ (t + π / 2) = cutBranch N dc x θ g t := by
  unfold rangeFeature cutBranch
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := hgap i (by simp only [Finset.mem_range] at hi; omega (config := {}))
  rw [show t + π / 2 - θ i = (t - θ i) + π / 2 by ring,
    cos_add_pi_div_two, sin_add_pi_div_two, abs_neg, Real.sign_neg]
  by_cases hg : i ≤ g
  · rw [if_pos hg] at h ⊢
    have hs := sin_pos_of_pos_of_lt_pi h.1 h.2
    rw [abs_of_pos hs, Real.sign_of_pos hs]
    unfold atomBranch
    ring
  · rw [if_neg hg] at h ⊢
    have hs := sin_neg_of_neg_of_neg_pi_lt h.2 h.1
    rw [abs_of_neg hs, Real.sign_of_neg hs]
    unfold atomBranch
    ring

/-- Feature reconstruction: endpoint matching, half-period closure, and the
open-gap geometry are sufficient; no realization hypothesis is assumed. -/
theorem feature_reconstruction {N g : ℕ} (θ A B dc x : ℕ → ℝ)
    (hvalue : ∀ k < N,
      sinePiece (A (k + 1)) (B (k + 1)) (θ (k + 1)) -
        sinePiece (A k) (B k) (θ (k + 1)) = -4 * x (k + 1))
    (hslope : ∀ k < N,
      sinePieceSlope (A (k + 1)) (B (k + 1)) (θ (k + 1)) -
        sinePieceSlope (A k) (B k) (θ (k + 1)) = 4 * dc (k + 1))
    (hwrapValue : sinePiece (A 0) (B 0) (θ 0) -
      sinePiece (A N) (B N) (θ 0 + π) = -4 * x 0)
    (hwrapSlope : sinePieceSlope (A 0) (B 0) (θ 0) -
      sinePieceSlope (A N) (B N) (θ 0 + π) = 4 * dc 0)
    (hg : g ≤ N) (t : ℝ)
    (hgap : ∀ i ≤ N, if i ≤ g then 0 < t - θ i ∧ t - θ i < π
      else -π < t - θ i ∧ t - θ i < 0) :
    2 * rangeFeature N dc x θ (t + π / 2) = sinePiece (A g) (B g) t := by
  rw [eq_beam_gap_sinusoid dc x θ t hgap]
  exact cutBranch_reconstructs θ A B dc x hvalue hslope hwrapValue hwrapSlope g hg t

/-- Strictly ordered cuts in a half-period supply the branch signs directly. -/
theorem open_gap_displacements {N g : ℕ} (θ : ℕ → ℝ) (hg : g ≤ N)
    (hmono : ∀ i j, i ≤ j → j ≤ N → θ i ≤ θ j)
    (hspan : θ N < θ 0 + π) (t : ℝ) (hleft : θ g < t)
    (hright : t < if g = N then θ 0 + π else θ (g + 1)) :
    ∀ i ≤ N, if i ≤ g then 0 < t - θ i ∧ t - θ i < π
      else -π < t - θ i ∧ t - θ i < 0 := by
  have hbase : θ 0 < t := lt_of_le_of_lt (hmono 0 g (Nat.zero_le _) hg) hleft
  have htop : t < θ 0 + π := by
    by_cases hlast : g = N
    · simpa [hlast] using hright
    · rw [if_neg hlast] at hright
      exact lt_trans hright (lt_of_le_of_lt (hmono (g + 1) N (by omega (config := {})) le_rfl) hspan)
  intro i hi
  by_cases hig : i ≤ g
  · rw [if_pos hig]
    have hlow := hmono 0 i (Nat.zero_le _) hi
    have hhigh := hmono i g hig hg
    constructor <;> linarith only [hleft, hhigh, hlow, htop]
  · rw [if_neg hig]
    have hlast : g ≠ N := by omega (config := {})
    rw [if_neg hlast] at hright
    have hlow := hmono (g + 1) i (by omega (config := {})) hi
    have hhigh := hmono i N hi le_rfl
    constructor <;> linarith only [hbase, hspan, hlow, hhigh, hright]

/-- The predecessor of a cut, with one explicit wrap at the first student. -/
def previousCut (N k : ℕ) : ℕ := if k = 0 then N else k - 1

/-- Angular momentum in the ordered-cut coordinates used in the integral. -/
def orderedMomentum (N : ℕ) (cut u : ℕ → ℝ) (k : ℕ) : ℝ :=
  let j := previousCut N k
  (a (cut (k + 1) - cut k) + a (cut (j + 1) - cut j)) * u k +
    b (cut (k + 1) - cut k) * u (k + 1) + b (cut (j + 1) - cut j) * u j

/-- The mass velocity is exactly one quarter of the profile's slope jump. -/
def orderedMassVelocity (N : ℕ) (cut u : ℕ → ℝ) (k : ℕ) : ℝ :=
  let j := previousCut N k
  (profileSlope (cut (k + 1) - cut k) (u k) (u (k + 1)) 0 -
    profileSlope (cut (j + 1) - cut j) (u j) (u (j + 1)) (cut (j + 1) - cut j)) / 4

def profileGlobalCos (cut u : ℕ → ℝ) (g : ℕ) : ℝ :=
  let l := cut (g + 1) - cut g;
  -4 * (a l * u g + b l * u (g + 1)) * cos (cut g) -
    (8 * (sin l ^ 2 * u g + l * sin l * u (g + 1)) / (l ^ 2 - sin l ^ 2)) * sin (cut g)

def profileGlobalSin (cut u : ℕ → ℝ) (g : ℕ) : ℝ :=
  let l := cut (g + 1) - cut g;
  -4 * (a l * u g + b l * u (g + 1)) * sin (cut g) +
    (8 * (sin l ^ 2 * u g + l * sin l * u (g + 1)) / (l ^ 2 - sin l ^ 2)) * cos (cut g)

theorem profile_global_coordinates (cut u : ℕ → ℝ) (g : ℕ) (t : ℝ) :
    sinePiece (profileGlobalCos cut u g) (profileGlobalSin cut u g) t =
      profile (cut (g + 1) - cut g) (u g) (u (g + 1)) (t - cut g) ∧
    sinePieceSlope (profileGlobalCos cut u g) (profileGlobalSin cut u g) t =
      profileSlope (cut (g + 1) - cut g) (u g) (u (g + 1)) (t - cut g) := by
  constructor
  · dsimp [sinePiece, profileGlobalCos, profileGlobalSin, profile]
    rw [sin_sub t (cut g), cos_sub t (cut g)]
    ring
  · dsimp [sinePieceSlope, profileGlobalCos, profileGlobalSin, profileSlope]
    rw [sin_sub t (cut g), cos_sub t (cut g)]
    ring

/-- Literal local values and actual derivatives in `eq:beam-branch-jumps`. -/
theorem eq_beam_branch_jumps (N : ℕ) (cut u : ℕ → ℝ) (k : ℕ) :
    profile (cut (k + 2) - cut (k + 1)) (u (k + 1)) (u (k + 2)) 0 -
      profile (cut (k + 1) - cut k) (u k) (u (k + 1)) (cut (k + 1) - cut k) =
      -4 * orderedMomentum N cut u (k + 1) ∧
    deriv (profile (cut (k + 2) - cut (k + 1)) (u (k + 1)) (u (k + 2))) 0 -
      deriv (profile (cut (k + 1) - cut k) (u k) (u (k + 1))) (cut (k + 1) - cut k) =
      4 * orderedMassVelocity N cut u (k + 1) := by
  have hs (l u v : ℝ) : profileSlope l u v 0 = d l * u + e l * v :=
    (hasDerivAt_profile l u v 0).unique (eq_beam_branch_start l u v).2.2.1
  have he (l u v : ℝ) : profileSlope l u v l = e l * u + d l * v :=
    (hasDerivAt_profile l u v l).unique (eq_beam_branch_end l u v).2.2.1
  constructor
  · rw [(eq_beam_branch_start _ _ _).1, (eq_beam_branch_end _ _ _).1]
    simp only [orderedMomentum, previousCut, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, Nat.add_sub_cancel]
    ring
  · rw [(eq_beam_branch_start _ _ _).2.2.2, (eq_beam_branch_end _ _ _).2.2.2]
    simp only [orderedMassVelocity, previousCut, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, Nat.add_sub_cancel, hs, he]
    ring

/-- Reconstruction consumes the actual derivative jump, not an unrelated
display appended to the old slope calculation. -/
theorem beam_branch_jumps_from_derivatives (N : ℕ) (cut u : ℕ → ℝ) (k : ℕ) :
    sinePiece (profileGlobalCos cut u (k + 1)) (profileGlobalSin cut u (k + 1)) (cut (k + 1)) -
      sinePiece (profileGlobalCos cut u k) (profileGlobalSin cut u k) (cut (k + 1)) =
      -4 * orderedMomentum N cut u (k + 1) ∧
    sinePieceSlope (profileGlobalCos cut u (k + 1)) (profileGlobalSin cut u (k + 1)) (cut (k + 1)) -
      sinePieceSlope (profileGlobalCos cut u k) (profileGlobalSin cut u k) (cut (k + 1)) =
      4 * orderedMassVelocity N cut u (k + 1) := by
  have h := eq_beam_branch_jumps N cut u k
  constructor
  · rw [(profile_global_coordinates cut u (k + 1) (cut (k + 1))).1,
      (profile_global_coordinates cut u k (cut (k + 1))).1, sub_self]
    exact h.1
  · rw [(profile_global_coordinates cut u (k + 1) (cut (k + 1))).2,
      (profile_global_coordinates cut u k (cut (k + 1))).2, sub_self]
    simpa only [(hasDerivAt_profile _ _ _ _).deriv] using h.2

/-- `eq:beam-branch-jumps`, including the cyclic last-to-first cut: the
local profile has exactly the prescribed value and actual derivative jumps. -/
theorem eq_beam_branch_jumps_wrap (N : ℕ) (cut u : ℕ → ℝ)
    (hu : u (N + 1) = u 0) :
    profile (cut 1 - cut 0) (u 0) (u 1) 0 -
      profile (cut (N + 1) - cut N) (u N) (u (N + 1)) (cut (N + 1) - cut N) =
      -4 * orderedMomentum N cut u 0 ∧
    deriv (profile (cut 1 - cut 0) (u 0) (u 1)) 0 -
      deriv (profile (cut (N + 1) - cut N) (u N) (u (N + 1))) (cut (N + 1) - cut N) =
      4 * orderedMassVelocity N cut u 0 := by
  constructor
  · rw [(eq_beam_branch_start _ _ _).1, (eq_beam_branch_end _ _ _).1]
    simp only [orderedMomentum, previousCut, if_true, zero_add, hu]
    ring
  · rw [(hasDerivAt_profile _ _ _ _).deriv, (hasDerivAt_profile _ _ _ _).deriv]
    simp only [orderedMassVelocity, previousCut, if_true, zero_add]
    ring

/-- The reconstruction's wrap condition is supplied by actual derivatives. -/
theorem ordered_profile_wrap (N : ℕ) (cut u : ℕ → ℝ)
    (hcut : cut (N + 1) = cut 0 + π) (hu : u (N + 1) = u 0) :
    sinePiece (profileGlobalCos cut u 0) (profileGlobalSin cut u 0) (cut 0) -
      sinePiece (profileGlobalCos cut u N) (profileGlobalSin cut u N) (cut 0 + π) =
      -4 * orderedMomentum N cut u 0 ∧
    sinePieceSlope (profileGlobalCos cut u 0) (profileGlobalSin cut u 0) (cut 0) -
      sinePieceSlope (profileGlobalCos cut u N) (profileGlobalSin cut u N) (cut 0 + π) =
      4 * orderedMassVelocity N cut u 0 := by
  have h := eq_beam_branch_jumps_wrap N cut u hu
  constructor
  · rw [← hcut, (profile_global_coordinates cut u 0 (cut 0)).1,
      (profile_global_coordinates cut u N (cut (N + 1))).1, sub_self]
    exact h.1
  · rw [← hcut, (profile_global_coordinates cut u 0 (cut 0)).2,
      (profile_global_coordinates cut u N (cut (N + 1))).2, sub_self]
    simpa only [(hasDerivAt_profile _ _ _ _).deriv] using h.2

/-- Passing between finite vectors and ordered finite sums changes no feature. -/
theorem rangeFeature_eq_feature (N : ℕ) (dc x θ : ℕ → ℝ) (t : ℝ) :
    rangeFeature N dc x θ t =
      feature (fun i : Fin (N + 1) => dc i) (fun i => x i) (fun i => θ i) t := by
  unfold rangeFeature feature
  exact (Fin.sum_univ_eq_sum_range (fun i => dc i * |cos (t - θ i)| +
    x i * Real.sign (cos (t - θ i)) * sin (t - θ i)) (N + 1)).symm

/-- The full physical feature realizes the local profiles. The velocities
are constructed from the profiles; realization is not an input. -/
theorem ordered_feature_realization (N : ℕ) (cut u : ℕ → ℝ)
    (hperiod : cut (N + 1) = cut 0 + π) (huperiod : u (N + 1) = u 0)
    (hcut : ∀ k < N + 1, cut k < cut (k + 1)) :
    ∀ g < N + 1, ∀ t ∈ Set.Ioo (cut g) (cut (g + 1)),
      2 * feature (fun i : Fin (N + 1) => orderedMassVelocity N cut u i)
        (fun i => orderedMomentum N cut u i) (fun i => cut i) (t + π / 2) =
        profile (cut (g + 1) - cut g) (u g) (u (g + 1)) (t - cut g) := by
  have hmono : ∀ i j, i ≤ j → j ≤ N + 1 → cut i ≤ cut j := by
    intro i j hij hj
    induction j with
    | zero => have hi : i = 0 := Nat.eq_zero_of_le_zero hij; subst i; exact le_rfl
    | succ j ih =>
      by_cases hi : i ≤ j
      · exact le_trans (ih hi (by omega (config := {}))) (hcut j (by omega (config := {}))).le
      · have heq : i = j + 1 := by omega (config := {})
        rw [heq]
  have hspan : cut N < cut 0 + π := by rw [← hperiod]; exact hcut N (by omega (config := {}))
  intro g hg t ht
  have hright : t < if g = N then cut 0 + π else cut (g + 1) := by
    by_cases hlast : g = N
    · subst g; simpa [← hperiod] using ht.2
    · simpa [hlast] using ht.2
  have hgap := open_gap_displacements cut (by omega (config := {}) : g ≤ N)
    (fun i j hij hj => hmono i j hij (by omega (config := {}))) hspan t ht.1 hright
  rw [← rangeFeature_eq_feature]
  rw [feature_reconstruction cut (profileGlobalCos cut u) (profileGlobalSin cut u)
    (orderedMassVelocity N cut u) (orderedMomentum N cut u)
    (fun k _ => (beam_branch_jumps_from_derivatives N cut u k).1)
    (fun k _ => (beam_branch_jumps_from_derivatives N cut u k).2)
    (ordered_profile_wrap N cut u hperiod huperiod).1
    (ordered_profile_wrap N cut u hperiod huperiod).2 (by omega (config := {}) : g ≤ N) t hgap]
  exact (profile_global_coordinates cut u g t).1

/-- The ordered-cut momentum is exactly the cyclic `Fin` momentum. -/
theorem orderedMomentum_eq_angleMomentum (N : ℕ) (cut u : ℕ → ℝ)
    (hu : u (N + 1) = u 0) (i : Fin (N + 1)) :
    orderedMomentum N cut u i =
      angleMomentum (fun j => a (cut (j.val + 1) - cut j.val))
        (fun j => b (cut (j.val + 1) - cut j.val)) (fun j => u j.val) i := by
  have hprev : ((i - 1 : Fin (N + 1)) : ℕ) = previousCut N i := by
    simp [Fin.coe_sub_one, previousCut, Fin.ext_iff]
  have hnext : u ((i + 1 : Fin (N + 1)) : ℕ) = u (i.val + 1) := by
    rw [Fin.val_add_one]
    split_ifs with hlast
    · subst i
      exact hu.symm
    · rfl
  dsimp [orderedMomentum, angleMomentum]
  rw [hprev, hnext]

/-- The same realization in the cyclic momentum coordinates used by the
energy and second-variation identities. -/
theorem ordered_feature_realization_cyclic (N : ℕ) (cut u : ℕ → ℝ)
    (hperiod : cut (N + 1) = cut 0 + π) (huperiod : u (N + 1) = u 0)
    (hcut : ∀ k < N + 1, cut k < cut (k + 1)) :
    ∀ g < N + 1, ∀ t ∈ Set.Ioo (cut g) (cut (g + 1)),
      2 * feature (fun i : Fin (N + 1) => orderedMassVelocity N cut u i)
        (angleMomentum (fun j => a (cut (j.val + 1) - cut j.val))
          (fun j => b (cut (j.val + 1) - cut j.val)) (fun j => u j.val))
        (fun i => cut i) (t + π / 2) =
        profile (cut (g + 1) - cut g) (u g) (u (g + 1)) (t - cut g) := by
  have hm := funext (orderedMomentum_eq_angleMomentum N cut u huperiod)
  change (fun i : Fin (N + 1) => orderedMomentum N cut u i) =
    angleMomentum (fun j => a (cut (j.val + 1) - cut j.val))
      (fun j => b (cut (j.val + 1) - cut j.val)) (fun j => u j.val) at hm
  rw [← hm]
  exact ordered_feature_realization N cut u hperiod huperiod hcut

/-- Ordered students, lifted by one half-period only at the final endpoint. -/
def liftedCut {N : ℕ} (θ : Fin (N + 1) → ℝ) (k : ℕ) : ℝ :=
  if hk : k < N + 1 then θ ⟨k, hk⟩ else θ 0 + π

def liftedMode {N : ℕ} (u : Fin (N + 1) → ℝ) (k : ℕ) : ℝ :=
  if hk : k < N + 1 then u ⟨k, hk⟩ else u 0

@[simp] theorem liftedCut_coe {N : ℕ} (θ : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    liftedCut θ i = θ i := by simp [liftedCut, i.isLt]

@[simp] theorem liftedMode_coe {N : ℕ} (u : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    liftedMode u i = u i := by simp [liftedMode, i.isLt]

theorem liftedCut_period {N : ℕ} (θ : Fin (N + 1) → ℝ) :
    liftedCut θ (N + 1) = liftedCut θ 0 + π := by simp [liftedCut]

theorem liftedMode_period {N : ℕ} (u : Fin (N + 1) → ℝ) :
    liftedMode u (N + 1) = liftedMode u 0 := by simp [liftedMode]

theorem liftedCut_strict {N : ℕ} (θ : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π) :
    ∀ k < N + 1, liftedCut θ k < liftedCut θ (k + 1) := by
  intro k hk
  by_cases hlast : k = N
  · subst k
    simpa [liftedCut] using hspan
  · have hn : k + 1 < N + 1 := by omega (config := {})
    simp only [liftedCut, dif_pos hk, dif_pos hn]
    exact hmono (show (⟨k, hk⟩ : Fin (N + 1)) < ⟨k + 1, hn⟩ from Nat.lt_succ_self k)

/-- Finite-data realization, ready to consume the sorted student directions.
No beam or feature realization assumption remains in the theorem. -/
theorem eq_beam_glued_feature {N : ℕ} (θ u : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π) :
    ∀ g < N + 1, ∀ t ∈ Set.Ioo (liftedCut θ g) (liftedCut θ (g + 1)),
      2 * feature (fun i => orderedMassVelocity N (liftedCut θ) (liftedMode u) i)
        (angleMomentum (fun j => a (liftedCut θ (j.val + 1) - θ j))
          (fun j => b (liftedCut θ (j.val + 1) - θ j)) u) θ (t + π / 2) =
        profile (liftedCut θ (g + 1) - liftedCut θ g)
          (liftedMode u g) (liftedMode u (g + 1)) (t - liftedCut θ g) := by
  have h := ordered_feature_realization_cyclic N (liftedCut θ) (liftedMode u)
    (liftedCut_period θ) (liftedMode_period u) (liftedCut_strict θ hmono hspan)
  simpa only [liftedCut_coe, liftedMode_coe] using h

section FiniteSecondVariation

variable {n m : ℕ}

/-- The finite Gram expression in the paper's normalization.  The teacher-only
constant is retained, although it disappears under differentiation. -/
def finiteKernelLoss (K : ℝ → ℝ) (s beta : Fin m → ℝ)
    (c theta : Fin n → ℝ) : ℝ :=
  (1 / (4 * π)) *
    ((∑ i, ∑ j, c i * c j * K (theta i - theta j)) -
      2 * (∑ i, ∑ k, c i * s k * K (theta i - beta k)) +
      ∑ k, ∑ l, s k * s l * K (beta k - beta l))

/-- The first-order feature Gram form: mass velocities and angular momenta
are separate, so the formula remains meaningful at zero student masses. -/
def featureGram (K K1 K2 : ℝ → ℝ) (dc x theta : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j,
    (dc i * dc j * K (theta i - theta j) +
    (x i * dc j - dc i * x j) * K1 (theta i - theta j) -
    x i * x j * K2 (theta i - theta j))

def finiteResidual (K : ℝ → ℝ) (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  (∑ i, c i * K (x - theta i)) - ∑ k, s k * K (x - beta k)

/-- The elementary second variation before using symmetry or stationarity. -/
def jointSecondVariation (K K1 K2 : ℝ → ℝ) (c dc theta v : Fin n → ℝ)
    (s beta : Fin m → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, (
    2 * dc i * dc j * K (theta i - theta j) +
    2 * (dc i * c j + c i * dc j) * (v i - v j) * K1 (theta i - theta j) +
    c i * c j * (v i - v j) ^ 2 * K2 (theta i - theta j))) -
    ∑ i, ∑ k, (
      2 * dc i * s k * v i * K1 (theta i - beta k) +
      c i * s k * v i ^ 2 * K2 (theta i - beta k))

private theorem sum_transpose (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f j i) = ∑ i, ∑ j, f i j := Finset.sum_comm

private theorem affine_derivative (a b t : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b) b t := by
  simpa only [one_mul] using ((hasDerivAt_id t).mul_const b).const_add a

/-- A reusable calculus calculation, stated on the actual product rather than
on a domain-specific atom. -/
private theorem hasDerivAt_affine_kernel_product
    (K K1 : ℝ → ℝ) (hK : ∀ x, HasDerivAt K (K1 x) x)
    (a da b db z dz t : ℝ) :
    HasDerivAt (fun t => (a + t * da) * (b + t * db) * K (z + t * dz))
      ((da * (b + t * db) + (a + t * da) * db) * K (z + t * dz) +
        (a + t * da) * (b + t * db) * (K1 (z + t * dz) * dz)) t :=
  ((affine_derivative a da t).mul (affine_derivative b db t)).mul
    ((hK (z + t * dz)).comp t (affine_derivative z dz t))

private theorem hasDerivAt_affine_kernel_product_slope
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x) (hK1 : ∀ x, HasDerivAt K1 (K2 x) x)
    (a da b db z dz t : ℝ) :
    HasDerivAt
      (fun t => (da * (b + t * db) + (a + t * da) * db) * K (z + t * dz) +
        (a + t * da) * (b + t * db) * (K1 (z + t * dz) * dz))
      (2 * da * db * K (z + t * dz) +
        2 * (da * (b + t * db) + (a + t * da) * db) * dz * K1 (z + t * dz) +
        (a + t * da) * (b + t * db) * dz ^ 2 * K2 (z + t * dz)) t := by
  have hfactor := ((affine_derivative b db t).const_mul da).add
    ((affine_derivative a da t).mul_const db)
  have hk := (hK (z + t * dz)).comp t (affine_derivative z dz t)
  have hk1 := ((hK1 (z + t * dz)).comp t (affine_derivative z dz t)).mul_const dz
  convert (hfactor.mul hk).add
    (((affine_derivative a da t).mul (affine_derivative b db t)).mul hk1) using 1
  simp only [Function.comp_apply]
  ring

/-- The derivative along an affine parameter curve, with all terms visible. -/
def finiteKernelSlope (K K1 : ℝ → ℝ) (c dc theta v : Fin n → ℝ)
    (s beta : Fin m → ℝ) (t : ℝ) : ℝ :=
  (1 / (4 * π)) *
    ((∑ i, ∑ j,
      ((dc i * (c j + t * dc j) + (c i + t * dc i) * dc j) *
          K ((theta i - theta j) + t * (v i - v j)) +
        (c i + t * dc i) * (c j + t * dc j) *
          (K1 ((theta i - theta j) + t * (v i - v j)) * (v i - v j)))) -
      2 * (∑ i, ∑ k,
        (dc i * s k * K ((theta i - beta k) + t * v i) +
          (c i + t * dc i) * s k * (K1 ((theta i - beta k) + t * v i) * v i))))

theorem hasDerivAt_finiteKernelLoss_line
    (K K1 : ℝ → ℝ) (hK : ∀ x, HasDerivAt K (K1 x) x)
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun t => finiteKernelLoss K s beta
      (fun i => c i + t * dc i) (fun i => theta i + t * v i))
      (finiteKernelSlope K K1 c dc theta v s beta t) t := by
  have hss := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun j _ =>
      hasDerivAt_affine_kernel_product K K1 hK (c i) (dc i) (c j) (dc j)
        (theta i - theta j) (v i - v j) t))
  have hst := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin m))) (fun k _ =>
      hasDerivAt_affine_kernel_product K K1 hK (c i) (dc i) (s k) 0
        (theta i - beta k) (v i) t))
  have h := ((hss.sub (hst.const_mul 2)).add_const
    (∑ k, ∑ l, s k * s l * K (beta k - beta l))).const_mul (1 / (4 * π))
  convert h using 1
  · funext x
    simp only [finiteKernelLoss, mul_zero, add_zero]
    congr 2
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 2
      ring
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      ring
  · simp only [finiteKernelSlope, mul_zero, zero_mul, add_zero]

/-- The actual second derivative of the normalized finite kernel loss.
No distinctness or positivity assumption is needed for this calculus step. -/
theorem hasDerivAt_deriv_finiteKernelLoss_line
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x) (hK1 : ∀ x, HasDerivAt K1 (K2 x) x)
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ) :
    HasDerivAt (deriv (fun t => finiteKernelLoss K s beta
      (fun i => c i + t * dc i) (fun i => theta i + t * v i)))
      ((1 / (2 * π)) * jointSecondVariation K K1 K2 c dc theta v s beta) 0 := by
  have hd : deriv (fun t => finiteKernelLoss K s beta
      (fun i => c i + t * dc i) (fun i => theta i + t * v i)) =
      finiteKernelSlope K K1 c dc theta v s beta :=
    funext (fun t => (hasDerivAt_finiteKernelLoss_line K K1 hK c dc theta v s beta t).deriv)
  rw [hd]
  have hss := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun j _ =>
      hasDerivAt_affine_kernel_product_slope K K1 K2 hK hK1 (c i) (dc i) (c j) (dc j)
        (theta i - theta j) (v i - v j) 0))
  have hst := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin m))) (fun k _ =>
      hasDerivAt_affine_kernel_product_slope K K1 K2 hK hK1 (c i) (dc i) (s k) 0
        (theta i - beta k) (v i) 0))
  convert (hss.sub (hst.const_mul 2)).const_mul (1 / (4 * π)) using 1
  · funext t
    simp only [finiteKernelSlope, mul_zero, add_zero, zero_mul]
  · simp only [jointSecondVariation, mul_zero, add_zero, zero_mul, zero_add]
    simp only [mul_assoc]
    ring

/-- Symmetry exposes precisely the two residual terms, without a Hessian
matrix, a selected-slot construction, or any assumption on the mass signs. -/
theorem jointSecondVariation_eq_featureGram_add_residual
    (K K1 K2 : ℝ → ℝ)
    (hK1 : ∀ x, K1 (-x) = -K1 x) (hK2 : ∀ x, K2 (-x) = K2 x)
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ) :
    jointSecondVariation K K1 K2 c dc theta v s beta =
      featureGram K K1 K2 dc (fun i => c i * v i) theta +
      ∑ i, (2 * dc i * v i * finiteResidual K1 c theta s beta (theta i) +
        c i * v i ^ 2 * finiteResidual K2 c theta s beta (theta i)) := by
  have hcross : (∑ i, ∑ j, c i * dc j * v j * K1 (theta i - theta j)) =
      -(∑ i, ∑ j, dc i * c j * v i * K1 (theta i - theta j)) := by
    rw [← sum_transpose (fun i j => c i * dc j * v j * K1 (theta i - theta j))]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [show theta j - theta i = -(theta i - theta j) by ring, hK1]
    ring
  have hdiag : (∑ i, ∑ j, c i * c j * v j ^ 2 * K2 (theta i - theta j)) =
      ∑ i, ∑ j, c i * c j * v i ^ 2 * K2 (theta i - theta j) := by
    rw [← sum_transpose (fun i j => c i * c j * v j ^ 2 * K2 (theta i - theta j))]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show theta j - theta i = -(theta i - theta j) by ring, hK2]
    ring
  have hSS : (1 / 2 : ℝ) * (∑ i, ∑ j,
      (2 * dc i * dc j * K (theta i - theta j) +
      2 * (dc i * c j + c i * dc j) * (v i - v j) * K1 (theta i - theta j) +
      c i * c j * (v i - v j) ^ 2 * K2 (theta i - theta j))) =
      featureGram K K1 K2 dc (fun i => c i * v i) theta +
      ∑ i, (2 * dc i * v i * (∑ j, c j * K1 (theta i - theta j)) +
        c i * v i ^ 2 * (∑ j, c j * K2 (theta i - theta j))) := by
    calc
      _ = featureGram K K1 K2 dc (fun i => c i * v i) theta +
        (∑ i, (2 * dc i * v i * (∑ j, c j * K1 (theta i - theta j)) +
          c i * v i ^ 2 * (∑ j, c j * K2 (theta i - theta j)))) -
        (∑ i, ∑ j, dc i * c j * v i * K1 (theta i - theta j)) -
        (∑ i, ∑ j, c i * dc j * v j * K1 (theta i - theta j)) +
        (1 / 2 : ℝ) * ((∑ i, ∑ j, c i * c j * v j ^ 2 * K2 (theta i - theta j)) -
          ∑ i, ∑ j, c i * c j * v i ^ 2 * K2 (theta i - theta j)) := by
        unfold featureGram
        simp only [mul_sub, Finset.mul_sum]
        simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hcross, hdiag]; ring
  unfold jointSecondVariation
  rw [hSS]
  unfold finiteResidual
  simp only [mul_sub, Finset.mul_sum]
  rw [add_sub_assoc]
  congr 1
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hst1 : (∑ k, 2 * dc i * s k * v i * K1 (theta i - beta k)) =
      ∑ k, 2 * dc i * v i * (s k * K1 (theta i - beta k)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hst2 : (∑ k, c i * s k * v i ^ 2 * K2 (theta i - beta k)) =
      ∑ k, c i * v i ^ 2 * (s k * K2 (theta i - beta k)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hst1, hst2]
  ring

/-- At the stationary double zeros, only residual curvature survives.  The
zero value itself is not needed in this identity, only the zero slope. -/
theorem jointSecondVariation_at_stationary_directions
    (K K1 K2 : ℝ → ℝ)
    (hK1 : ∀ x, K1 (-x) = -K1 x) (hK2 : ∀ x, K2 (-x) = K2 x)
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hstationary : ∀ i, finiteResidual K1 c theta s beta (theta i) = 0) :
    jointSecondVariation K K1 K2 c dc theta v s beta =
      featureGram K K1 K2 dc (fun i => c i * v i) theta +
      ∑ i, c i * v i ^ 2 * finiteResidual K2 c theta s beta (theta i) := by
  rw [jointSecondVariation_eq_featureGram_add_residual K K1 K2 hK1 hK2]
  simp only [hstationary, mul_zero, zero_add]

theorem hasDerivAt_finiteResidual
    (K K1 : ℝ → ℝ) (hK : ∀ x, HasDerivAt K (K1 x) x)
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    HasDerivAt (finiteResidual K c theta s beta)
      (finiteResidual K1 c theta s beta x) x := by
  unfold finiteResidual
  have hs := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ =>
    ((hK (x - theta i)).comp x ((hasDerivAt_id x).sub_const (theta i))).const_mul (c i))
  have ht := HasDerivAt.sum (u := (Finset.univ : Finset (Fin m))) (fun k _ =>
    ((hK (x - beta k)).comp x ((hasDerivAt_id x).sub_const (beta k))).const_mul (s k))
  simpa only [Function.comp_apply, mul_one] using hs.sub ht

theorem finiteResidual_second_derivative
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x) (hK1 : ∀ x, HasDerivAt K1 (K2 x) x)
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    deriv (deriv (finiteResidual K c theta s beta)) x =
      finiteResidual K2 c theta s beta x := by
  have hd : deriv (finiteResidual K c theta s beta) = finiteResidual K1 c theta s beta :=
    funext (fun x => (hasDerivAt_finiteResidual K K1 hK c theta s beta x).deriv)
  rw [hd, (hasDerivAt_finiteResidual K1 K2 hK1 c theta s beta x).deriv]

/-- The angular block used by the opposed-rotation argument. -/
theorem angularSecondVariation_eq_residual_curvature
    (K K1 K2 : ℝ → ℝ)
    (hodd : ∀ x, K1 (-x) = -K1 x) (heven : ∀ x, K2 (-x) = K2 x)
    (c theta v : Fin n → ℝ) (s beta : Fin m → ℝ) :
    jointSecondVariation K K1 K2 c (fun _ => 0) theta v s beta =
      (∑ i, c i * v i ^ 2 * finiteResidual K2 c theta s beta (theta i)) -
        ∑ i, ∑ j, c i * c j * v i * v j * K2 (theta i - theta j) := by
  rw [jointSecondVariation_eq_featureGram_add_residual K K1 K2 hodd heven]
  simp only [featureGram, mul_zero, zero_mul, sub_zero, zero_sub, zero_add,
    Finset.sum_neg_distrib]
  have heq : (∑ i, ∑ j, c i * v i * (c j * v j) * K2 (theta i - theta j)) =
      ∑ i, ∑ j, c i * c j * v i * v j * K2 (theta i - theta j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  ring

theorem hasDerivAt_deriv_angular_finiteKernelLoss
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x) (hK1 : ∀ x, HasDerivAt K1 (K2 x) x)
    (hodd : ∀ x, K1 (-x) = -K1 x) (heven : ∀ x, K2 (-x) = K2 x)
    (c theta v : Fin n → ℝ) (s beta : Fin m → ℝ) :
    HasDerivAt (deriv (fun t => finiteKernelLoss K s beta c (fun i => theta i + t * v i)))
      ((1 / (2 * π)) * ((∑ i, c i * v i ^ 2 * finiteResidual K2 c theta s beta (theta i)) -
        ∑ i, ∑ j, c i * c j * v i * v j * K2 (theta i - theta j))) 0 := by
  have h := hasDerivAt_deriv_finiteKernelLoss_line K K1 K2 hK hK1 c (fun _ => 0)
    theta v s beta
  simpa only [angularSecondVariation_eq_residual_curvature K K1 K2 hodd heven,
    mul_zero, add_zero] using h

/-- The curvature ratio form used in the beam proof.  No division hypothesis
is needed: a zero mass gives zero on both sides. -/
theorem jointSecondVariation_eq_featureGram_sub_curvature_ratio
    (K K1 K2 : ℝ → ℝ)
    (hodd : ∀ x, K1 (-x) = -K1 x) (heven : ∀ x, K2 (-x) = K2 x)
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hstationary : ∀ i, finiteResidual K1 c theta s beta (theta i) = 0) :
    jointSecondVariation K K1 K2 c dc theta v s beta =
      featureGram K K1 K2 dc (fun i => c i * v i) theta -
      ∑ i, (-(finiteResidual K2 c theta s beta (theta i)) / c i) * (c i * v i) ^ 2 := by
  rw [jointSecondVariation_at_stationary_directions K K1 K2 hodd heven c dc theta v s beta
    hstationary, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : c i = 0
  · simp [hc]
  · field_simp
    ring

/-- Finite integration is independent of the trigonometric calculation.
The four pair moments are precisely the data needed to identify the physical
feature square with its Gram form. -/
theorem integrated_feature_square_eq_featureGram
    (K K1 K2 : ℝ → ℝ) (dc x theta : Fin n → ℝ)
    (A B : Fin n → ℝ → ℝ)
    (hAA : ∀ i j, IntervalIntegrable (fun y => A i y * A j y) volume 0 π)
    (hAB : ∀ i j, IntervalIntegrable (fun y => A i y * B j y) volume 0 π)
    (hBA : ∀ i j, IntervalIntegrable (fun y => B i y * A j y) volume 0 π)
    (hBB : ∀ i j, IntervalIntegrable (fun y => B i y * B j y) volume 0 π)
    (mAA : ∀ i j, (∫ y in (0 : ℝ)..π, A i y * A j y) = K (theta i - theta j))
    (mAB : ∀ i j, (∫ y in (0 : ℝ)..π, A i y * B j y) = -K1 (theta i - theta j))
    (mBA : ∀ i j, (∫ y in (0 : ℝ)..π, B i y * A j y) = K1 (theta i - theta j))
    (mBB : ∀ i j, (∫ y in (0 : ℝ)..π, B i y * B j y) = -K2 (theta i - theta j)) :
    (∫ y in (0 : ℝ)..π, (∑ i, (dc i * A i y + x i * B i y)) ^ 2) =
      featureGram K K1 K2 dc x theta := by
  let g : Fin n → ℝ → ℝ := fun i y => dc i * A i y + x i * B i y
  have hproduct (i j : Fin n) :
      (fun y => g i y * g j y) =
        (fun y => dc i * dc j * (A i y * A j y) +
          dc i * x j * (A i y * B j y) +
          x i * dc j * (B i y * A j y) + x i * x j * (B i y * B j y)) := by
    funext y
    dsimp [g]
    ring
  have hpair (i j : Fin n) : IntervalIntegrable (fun y => g i y * g j y) volume 0 π := by
    rw [hproduct]
    exact ((((hAA i j).const_mul (dc i * dc j)).add
      ((hAB i j).const_mul (dc i * x j))).add
      ((hBA i j).const_mul (x i * dc j))).add ((hBB i j).const_mul (x i * x j))
  have pair_integral (i j : Fin n) : (∫ y in (0 : ℝ)..π, g i y * g j y) =
      dc i * dc j * K (theta i - theta j) +
        (x i * dc j - dc i * x j) * K1 (theta i - theta j) -
        x i * x j * K2 (theta i - theta j) := by
    rw [hproduct]
    rw [intervalIntegral.integral_add
      ((((hAA i j).const_mul (dc i * dc j)).add
        ((hAB i j).const_mul (dc i * x j))).add
        ((hBA i j).const_mul (x i * dc j))) ((hBB i j).const_mul (x i * x j))]
    rw [intervalIntegral.integral_add
      (((hAA i j).const_mul (dc i * dc j)).add
        ((hAB i j).const_mul (dc i * x j))) ((hBA i j).const_mul (x i * dc j))]
    rw [intervalIntegral.integral_add
      ((hAA i j).const_mul (dc i * dc j)) ((hAB i j).const_mul (dc i * x j))]
    simp only [intervalIntegral.integral_const_mul, mAA, mAB, mBA, mBB]
    ring
  have hexpand (y : ℝ) : (∑ i, g i y) ^ 2 = ∑ i, ∑ j, g i y * g j y := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  change (∫ y in (0 : ℝ)..π, (∑ i, g i y) ^ 2) = _
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finset_sum]
  · unfold featureGram
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finset_sum (fun j _ => hpair i j)]
    apply Finset.sum_congr rfl
    intro j _
    exact pair_integral i j
  · intro i _
    simpa only [Finset.sum_fn] using
      IntervalIntegrable.sum Finset.univ (fun j _ => hpair i j)

end FiniteSecondVariation

/-- `eq:beam-gram`: the two derivative-feature inner products. The assigned
values at the finitely many kinks do not affect either integral. -/
theorem eq_beam_gram (alpha beta : ℝ) :
    (∫ y in (0 : ℝ)..π, |cos (y - alpha)| *
      (-(Real.sign (cos (y - beta)) * sin (y - beta)))) = CircleMoments.K1 (alpha - beta) ∧
    (∫ y in (0 : ℝ)..π,
      (-(Real.sign (cos (y - alpha)) * sin (y - alpha))) *
      (-(Real.sign (cos (y - beta)) * sin (y - beta)))) = -CircleMoments.K2 (alpha - beta) := by
  constructor
  · simp only [mul_neg, intervalIntegral.integral_neg]
    rw [CircleMoments.pair_AB, neg_neg]
  · simp only [neg_mul_neg]
    exact CircleMoments.pair_BB alpha beta

/-- The physical feature energy is exactly the finite kernel Gram form.
Every pair integral is evaluated locally by splitting at a single feature
kink; no differentiation under the integral is required. -/
theorem eq_E_first_sum {n : ℕ} (dc x theta : Fin n → ℝ) :
    featureGram CircleMoments.K CircleMoments.K1 CircleMoments.K2 dc x theta =
      featureEnergy dc x theta := by
  have h := integrated_feature_square_eq_featureGram
    CircleMoments.K CircleMoments.K1 CircleMoments.K2 dc x theta
    (fun i y => |cos (y - theta i)|)
    (fun i y => Real.sign (cos (y - theta i)) * sin (y - theta i))
    (fun i j => CircleMoments.pair_AA_integrable (theta i) (theta j) 0 π)
    (fun i j => CircleMoments.pair_AB_integrable (theta i) (theta j) 0 π)
    (fun i j => CircleMoments.pair_BA_integrable (theta i) (theta j) 0 π)
    (fun i j => CircleMoments.pair_BB_integrable (theta i) (theta j) 0 π)
    (fun i j => CircleMoments.pair_AA (theta i) (theta j))
    (fun i j => by
      have h := (eq_beam_gram (theta i) (theta j)).1
      simp only [mul_neg, intervalIntegral.integral_neg] at h
      linarith only [h])
    (fun i j => CircleMoments.pair_BA (theta i) (theta j))
    (fun i j => by simpa only [neg_mul_neg] using (eq_beam_gram (theta i) (theta j)).2)
  rw [(eq_definition_E dc x theta).1]
  simpa only [eq_beam_feature_variation, mul_assoc] using h.symm

section Hessian
variable {n m : ℕ}

/-- Oddness of the derivative already forces the kernel to be even. -/
theorem kernel_even_of_odd_derivative (K K1 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x)
    (hodd : ∀ x, K1 (-x) = -K1 x) : ∀ x, K (-x) = K x := by
  have hd (x : ℝ) : HasDerivAt (fun y => K (-y) - K y) 0 x := by
    convert ((hK (-x)).comp x (hasDerivAt_neg x)).sub (hK x) using 1
    simp only [hodd]
    ring
  intro x
  have hc := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) x 0
  simpa only [neg_zero, sub_self, sub_eq_zero] using hc

def massPartial (K : ℝ → ℝ) (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i : Fin n) : ℝ :=
  deriv (fun t => finiteKernelLoss K s β (Function.update c i t) θ) (c i)

def anglePartial (K : ℝ → ℝ) (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i : Fin n) : ℝ :=
  deriv (fun t => finiteKernelLoss K s β c (Function.update θ i t)) (θ i)

/-- The first mass partial, differentiated directly from the finite loss. -/
theorem massPartial_eq_residual (K : ℝ → ℝ) (hK : ∀ z, K (-z) = K z)
    (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i : Fin n) :
    massPartial K s β c θ i = (1 / (2 * π)) * finiteResidual K c θ s β (θ i) := by
  have hsym : ∀ j k, K (θ j - θ k) = K (θ k - θ j) := by
    intro j k
    rw [show θ j - θ k = -(θ k - θ j) by ring, hK]
  have hss := Preliminaries.hasDerivAt_symmetric_quadratic_update c
    (fun j k => K (θ j - θ k)) hsym i
  have hst := Preliminaries.hasDerivAt_linear_mass_update c
    (fun j => ∑ k, s k * K (θ j - β k)) i
  have h := ((hss.sub (hst.const_mul 2)).add_const
    (∑ k, ∑ l, s k * s l * K (β k - β l))).const_mul (1 / (4 * π))
  have hd : HasDerivAt (fun t => finiteKernelLoss K s β (Function.update c i t) θ)
      ((1 / (2 * π)) * finiteResidual K c θ s β (θ i)) (c i) := by
    convert h using 1
    · funext t
      simp only [finiteKernelLoss, Finset.mul_sum, ← mul_assoc]
    · unfold finiteResidual
      ring
  exact hd.deriv

/-- The first angular partial, including the self-pair cancellation. -/
theorem anglePartial_eq_residual (K K1 : ℝ → ℝ)
    (hK : ∀ z, HasDerivAt K (K1 z) z) (hodd : ∀ z, K1 (-z) = -K1 z)
    (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i : Fin n) :
    anglePartial K s β c θ i = (1 / (2 * π)) * c i * finiteResidual K1 c θ s β (θ i) := by
  have hss := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      ((hK (Function.update θ i (θ i) j - Function.update θ i (θ i) k)).comp (θ i)
        ((Preliminaries.hasDerivAt_mass_update θ i j).sub
          (Preliminaries.hasDerivAt_mass_update θ i k))).const_mul (c j * c k)))
  have hst := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      ((hK (Function.update θ i (θ i) j - β k)).comp (θ i)
        ((Preliminaries.hasDerivAt_mass_update θ i j).sub_const (β k))).const_mul (c j * s k)))
  simp only [Function.update_eq_self] at hss hst
  have hssValue : (∑ j, ∑ k, c j * c k *
      (K1 (θ j - θ k) * ((if j = i then 1 else 0) - (if k = i then 1 else 0)))) =
      2 * c i * ∑ k, c k * K1 (θ i - θ k) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp_rw [show ∀ j, θ j - θ i = -(θ i - θ j) by intro j; ring, hodd]
    simp only [mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hstValue : (∑ j, ∑ k, c j * s k *
      (K1 (θ j - β k) * (if j = i then 1 else 0))) =
      c i * ∑ k, s k * K1 (θ i - β k) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
  have h := ((hss.sub (hst.const_mul 2)).add_const
    (∑ k, ∑ l, s k * s l * K (β k - β l))).const_mul (1 / (4 * π))
  have hd : HasDerivAt (fun t => finiteKernelLoss K s β c (Function.update θ i t))
      ((1 / (2 * π)) * c i * finiteResidual K1 c θ s β (θ i)) (θ i) := by
    convert h using 1
    rw [hssValue, hstValue]
    unfold finiteResidual
    ring
  exact hd.deriv

theorem hasDerivAt_residual_mass_update (K : ℝ → ℝ)
    (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) :
    HasDerivAt (fun t => finiteResidual K (Function.update c j t) θ s β (θ i))
      (K (θ i - θ j)) (c j) := by
  exact (Preliminaries.hasDerivAt_linear_mass_update c (fun k => K (θ i - θ k)) j).sub_const _

/-- Updating one angle changes its own argument and one residual atom. -/
theorem hasDerivAt_residual_angle_update (K K1 : ℝ → ℝ)
    (hK : ∀ z, HasDerivAt K (K1 z) z)
    (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) :
    HasDerivAt (fun t => finiteResidual K c (Function.update θ j t) s β
      (Function.update θ j t i))
      ((if i = j then finiteResidual K1 c θ s β (θ i) else 0) -
        c j * K1 (θ i - θ j)) (θ j) := by
  have hss := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    ((hK (Function.update θ j (θ j) i - Function.update θ j (θ j) k)).comp (θ j)
      ((Preliminaries.hasDerivAt_mass_update θ j i).sub
        (Preliminaries.hasDerivAt_mass_update θ j k))).const_mul (c k))
  have hst := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    ((hK (Function.update θ j (θ j) i - β k)).comp (θ j)
      ((Preliminaries.hasDerivAt_mass_update θ j i).sub_const (β k))).const_mul (s k))
  simp only [Function.update_eq_self] at hss hst
  convert hss.sub hst using 1
  by_cases hij : i = j
  · subst i
    simp only [if_true, finiteResidual, mul_sub, Finset.sum_sub_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, sub_self]
    ring
  · simp only [hij, if_false, zero_sub, mul_neg, mul_ite, mul_one, mul_zero,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero, sub_zero]

/-- These are actual second coordinate derivatives of the finite loss,
scaled by the paper's factor 2π, not stipulated matrix entries. -/
def hessianCC (K : ℝ → ℝ) (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * π * deriv (fun t => massPartial K s β (Function.update c j t) θ i) (c j)

def hessianCA (K : ℝ → ℝ) (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * π * deriv (fun t => massPartial K s β c (Function.update θ j t) i) (θ j)

def hessianAA (K : ℝ → ℝ) (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * π * deriv (fun t => anglePartial K s β c (Function.update θ j t) i) (θ j)

private theorem hessian_all_entries (K K1 K2 : ℝ → ℝ)
    (hK : ∀ z, HasDerivAt K (K1 z) z) (hK1 : ∀ z, HasDerivAt K1 (K2 z) z)
    (heven : ∀ z, K (-z) = K z) (hodd : ∀ z, K1 (-z) = -K1 z)
    (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) :
    hessianCC K s β c θ i j = K (θ i - θ j) ∧
    hessianCA K s β c θ i j =
      (if i = j then finiteResidual K1 c θ s β (θ i) else 0) - c j * K1 (θ i - θ j) ∧
    hessianAA K s β c θ i j = c i *
      ((if i = j then finiteResidual K2 c θ s β (θ i) else 0) - c j * K2 (θ i - θ j)) := by
  have hmass := (hasDerivAt_residual_mass_update K s β c θ i j).const_mul (1 / (2 * π))
  have hmixed := (hasDerivAt_residual_angle_update K K1 hK s β c θ i j).const_mul (1 / (2 * π))
  have hangle := (hasDerivAt_residual_angle_update K1 K2 hK1 s β c θ i j).const_mul
    ((1 / (2 * π)) * c i)
  refine ⟨?_, ?_, ?_⟩
  · unfold hessianCC
    simp_rw [massPartial_eq_residual K heven]
    rw [hmass.deriv]
    field_simp [pi_ne_zero]
    ring
  · unfold hessianCA
    simp_rw [massPartial_eq_residual K heven]
    rw [hmixed.deriv]
    field_simp [pi_ne_zero]
    ring
  · unfold hessianAA
    simp_rw [anglePartial_eq_residual K K1 hK hodd]
    rw [hangle.deriv]
    field_simp [pi_ne_zero]
    ring

/-- `eq:beam-hessian-offdiagonal`: actual second partials of the finite loss. -/
theorem eq_beam_hessian_offdiagonal (K K1 K2 : ℝ → ℝ)
    (hK : ∀ z, HasDerivAt K (K1 z) z) (hK1 : ∀ z, HasDerivAt K1 (K2 z) z)
    (hodd : ∀ z, K1 (-z) = -K1 z)
    (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    hessianCC K s β c θ i j = K (θ i - θ j) ∧
    hessianCA K s β c θ i j = -c j * K1 (θ i - θ j) ∧
    hessianAA K s β c θ i j = -c i * c j * K2 (θ i - θ j) := by
  have h := hessian_all_entries K K1 K2 hK hK1 (kernel_even_of_odd_derivative K K1 hK hodd) hodd s β c θ i j
  simpa only [hij, if_false, zero_sub, neg_mul, mul_neg, mul_assoc] using h

/-- `eq:beam-hessian-diagonal`: the self-pair contributes no angle motion. -/
theorem eq_beam_hessian_diagonal (K K1 K2 : ℝ → ℝ)
    (hK : ∀ z, HasDerivAt K (K1 z) z) (hK1 : ∀ z, HasDerivAt K1 (K2 z) z)
    (hodd : ∀ z, K1 (-z) = -K1 z)
    (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i : Fin n) :
    hessianCC K s β c θ i i = K 0 ∧
    hessianCA K s β c θ i i = finiteResidual K1 c θ s β (θ i) ∧
    hessianAA K s β c θ i i = c i * (finiteResidual K2 c θ s β (θ i) - c i * K2 0) := by
  have hzero : K1 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linarith only [h]
  simpa only [if_true, sub_self, hzero, mul_zero, sub_zero] using
    hessian_all_entries K K1 K2 hK hK1 (kernel_even_of_odd_derivative K K1 hK hodd) hodd s β c θ i i

/- The fourth block is written as an actual derivative as well, so the
contraction below does not silently assume symmetry of mixed partials. -/
def hessianAC (K : ℝ → ℝ) (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) : ℝ :=
  2 * π * deriv (fun t => anglePartial K s β (Function.update c j t) θ i) (c j)

theorem hessianAC_eq_transpose (K K1 K2 : ℝ → ℝ)
    (hK : ∀ z, HasDerivAt K (K1 z) z) (hK1 : ∀ z, HasDerivAt K1 (K2 z) z)
    (hodd : ∀ z, K1 (-z) = -K1 z)
    (s β : Fin m → ℝ) (c θ : Fin n → ℝ) (i j : Fin n) :
    hessianAC K s β c θ i j = hessianCA K s β c θ j i := by
  have hu := Preliminaries.hasDerivAt_mass_update c j i
  have hr := hasDerivAt_residual_mass_update K1 s β c θ i j
  have hh := (hu.mul hr).const_mul (1 / (2 * π))
  simp only [Function.update_eq_self] at hh
  unfold hessianAC
  simp_rw [anglePartial_eq_residual K K1 hK hodd, mul_assoc]
  rw [hh.deriv, (hessian_all_entries K K1 K2 hK hK1 (kernel_even_of_odd_derivative K K1 hK hodd) hodd s β c θ j i).2.1]
  rw [show θ j - θ i = -(θ i - θ j) by ring, hodd]
  by_cases hij : i = j
  · subst j
    simp only [if_true]
    field_simp [pi_ne_zero]
    ring
  · simp only [hij, Ne.symm hij, if_false, zero_mul, zero_add, zero_sub]
    field_simp [pi_ne_zero]
    ring

/-- Contracting the actual four coordinate-derivative blocks, using precisely
the diagonal and off-diagonal equations, recovers the feature Gram form and
the two residual corrections. No stationarity or nonzero masses are assumed. -/
theorem hessian_entries_contraction (K K1 K2 : ℝ → ℝ)
    (hK : ∀ z, HasDerivAt K (K1 z) z) (hK1 : ∀ z, HasDerivAt K1 (K2 z) z)
    (hodd : ∀ z, K1 (-z) = -K1 z)
    (s β : Fin m → ℝ) (c dc θ v : Fin n → ℝ) :
    (∑ i, ∑ j, (dc i * dc j * hessianCC K s β c θ i j +
      dc i * v j * hessianCA K s β c θ i j +
      v i * dc j * hessianAC K s β c θ i j +
      v i * v j * hessianAA K s β c θ i j)) =
      featureGram K K1 K2 dc (fun i => c i * v i) θ +
      ∑ i, (2 * dc i * v i * finiteResidual K1 c θ s β (θ i) +
        c i * v i ^ 2 * finiteResidual K2 c θ s β (θ i)) := by
  have hzero : K1 0 = 0 := by
    have h := hodd 0
    simp only [neg_zero] at h
    linarith only [h]
  have hentry (i j : Fin n) :
      dc i * dc j * hessianCC K s β c θ i j +
        dc i * v j * hessianCA K s β c θ i j +
        v i * dc j * hessianAC K s β c θ i j +
        v i * v j * hessianAA K s β c θ i j =
      (dc i * dc j * K (θ i - θ j) +
        (c i * v i * dc j - dc i * (c j * v j)) * K1 (θ i - θ j) -
        c i * v i * (c j * v j) * K2 (θ i - θ j)) +
      (if i = j then 2 * dc i * v i * finiteResidual K1 c θ s β (θ i) +
        c i * v i ^ 2 * finiteResidual K2 c θ s β (θ i) else 0) := by
    rw [hessianAC_eq_transpose K K1 K2 hK hK1 hodd]
    by_cases hij : i = j
    · subst j
      obtain ⟨hcc, hca, haa⟩ := eq_beam_hessian_diagonal K K1 K2 hK hK1 hodd s β c θ i
      rw [hcc, hca, haa]
      simp only [if_true, sub_self, hzero, mul_zero, add_zero]
      ring
    · obtain ⟨hcc, hca, haa⟩ := eq_beam_hessian_offdiagonal K K1 K2 hK hK1 hodd s β c θ i j hij
      have ht := (eq_beam_hessian_offdiagonal K K1 K2 hK hK1 hodd s β c θ j i (Ne.symm hij)).2.1
      rw [hcc, hca, haa, ht, show θ j - θ i = -(θ i - θ j) by ring, hodd]
      simp only [hij, if_false]
      ring
  simp_rw [hentry]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    featureGram, Finset.sum_ite_eq]

/-- The Hessian contraction is the genuine second derivative along the affine
parameter curve. This identifies the coordinate calculation with the existing
direct finite-sum calculus, not merely with a stipulated quadratic form. -/
theorem finiteKernelLoss_second_derivative_eq_hessian_contraction
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ t, HasDerivAt K (K1 t) t) (hK1 : ∀ t, HasDerivAt K1 (K2 t) t)
    (hodd : ∀ t, K1 (-t) = -K1 t) (heven : ∀ t, K2 (-t) = K2 t)
    (c dc θ v : Fin n → ℝ) (s β : Fin m → ℝ) :
    2 * π * deriv (deriv (fun t : ℝ => finiteKernelLoss K s β
      (fun i => c i + t * dc i) (fun i => θ i + t * v i))) 0 =
    ∑ i, ∑ j, (dc i * dc j * hessianCC K s β c θ i j +
      dc i * v j * hessianCA K s β c θ i j +
      v i * dc j * hessianAC K s β c θ i j +
      v i * v j * hessianAA K s β c θ i j) := by
  rw [(hasDerivAt_deriv_finiteKernelLoss_line K K1 K2 hK hK1 c dc θ v s β).deriv]
  have hden : 2 * π ≠ 0 := ne_of_gt (mul_pos (by norm_num) pi_pos)
  rw [← mul_assoc, mul_one_div_cancel hden, one_mul,
    jointSecondVariation_eq_featureGram_add_residual K K1 K2 hodd heven]
  exact (hessian_entries_contraction K K1 K2 hK hK1 hodd s β c dc θ v).symm


end Hessian

section SecondVariationStep

variable {n m : ℕ}

/-- `eq:beam-second-variation-raw`: contract the actual diagonal and
 off-diagonal mixed partials. The two residual corrections are genuine
 first and second derivatives of the finite residual. -/
theorem eq_beam_second_variation_raw
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ t, HasDerivAt K (K1 t) t) (hK1 : ∀ t, HasDerivAt K1 (K2 t) t)
    (hodd : ∀ t, K1 (-t) = -K1 t) (heven : ∀ t, K2 (-t) = K2 t)
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hgram : ∀ dc x : Fin n → ℝ,
      featureGram K K1 K2 dc x theta = featureEnergy dc x theta) :
    2 * π * deriv (deriv (fun t : ℝ => finiteKernelLoss K s beta
      (fun i => c i + t * dc i) (fun i => theta i + t * v i))) 0 =
      featureEnergy dc (fun i => c i * v i) theta +
      2 * (∑ i, dc i * v i * deriv (finiteResidual K c theta s beta) (theta i)) +
      ∑ i, c i * v i ^ 2 * deriv (deriv (finiteResidual K c theta s beta)) (theta i) := by
  rw [finiteKernelLoss_second_derivative_eq_hessian_contraction K K1 K2 hK hK1 hodd heven,
    hessian_entries_contraction K K1 K2 hK hK1 hodd, hgram]
  have hfirst (x : ℝ) : deriv (finiteResidual K c theta s beta) x =
      finiteResidual K1 c theta s beta x :=
    (hasDerivAt_finiteResidual K K1 hK c theta s beta x).deriv
  simp only [hfirst, finiteResidual_second_derivative K K1 K2 hK hK1,
    Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `eq:beam-second-variation`.  Criticality removes the first residual
derivative; writing the curvature as a ratio gives the signed-energy form.
The equality also covers zero masses by direct cancellation on both sides. -/
theorem eq_beam_second_variation
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ t, HasDerivAt K (K1 t) t) (hK1 : ∀ t, HasDerivAt K1 (K2 t) t)
    (hodd : ∀ t, K1 (-t) = -K1 t) (heven : ∀ t, K2 (-t) = K2 t)
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hgram : ∀ dc x : Fin n → ℝ,
      featureGram K K1 K2 dc x theta = featureEnergy dc x theta)
    (hstationary : ∀ i, finiteResidual K1 c theta s beta (theta i) = 0) :
    2 * π * deriv (deriv (fun t : ℝ => finiteKernelLoss K s beta
      (fun i => c i + t * dc i) (fun i => theta i + t * v i))) 0 =
      featureEnergy dc (fun i => c i * v i) theta -
      ∑ i, (-(deriv (deriv (finiteResidual K c theta s beta)) (theta i)) / c i) *
        (c i * v i) ^ 2 := by
  rw [eq_beam_second_variation_raw K K1 K2 hK hK1 hodd heven c dc theta v s beta hgram]
  have hfirst (i : Fin n) : deriv (finiteResidual K c theta s beta) (theta i) = 0 := by
    rw [(hasDerivAt_finiteResidual K K1 hK c theta s beta (theta i)).deriv, hstationary]
  simp only [hfirst, mul_zero, Finset.sum_const_zero, add_zero,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : c i = 0
  · simp [hc]
  · field_simp
    ring

/-- `stp:beam-second-variation`: the actual signed-energy identity consumed
by the beam descent step, with the weighted velocity and curvature readings
made explicit. Its proof goes through both labeled equations above. -/
theorem stp_beam_second_variation
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ t, HasDerivAt K (K1 t) t) (hK1 : ∀ t, HasDerivAt K1 (K2 t) t)
    (hodd : ∀ t, K1 (-t) = -K1 t) (heven : ∀ t, K2 (-t) = K2 t)
    (c dc theta v x rho : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hgram : ∀ dc x : Fin n → ℝ,
      featureGram K K1 K2 dc x theta = featureEnergy dc x theta)
    (hstationary : ∀ i, finiteResidual K1 c theta s beta (theta i) = 0)
    (hweighted : ∀ i, c i * v i = x i)
    (hrho : ∀ i, rho i = -(finiteResidual K2 c theta s beta (theta i)) / c i) :
    2 * π * deriv (deriv (fun t : ℝ => finiteKernelLoss K s beta
      (fun i => c i + t * dc i) (fun i => theta i + t * v i))) 0 =
      featureEnergy dc x theta - ∑ i, rho i * x i ^ 2 := by
  rw [eq_beam_second_variation K K1 K2 hK hK1 hodd heven c dc theta v s beta hgram hstationary]
  simp only [hweighted, finiteResidual_second_derivative K K1 K2 hK hK1, hrho]

end SecondVariationStep

/-! The gap sign and the curvature-ratio split. -/

/-- `eq:gap-q-negative-paper`, exact common-denominator identity. -/
theorem gap_quadratic_quotient {sigma m0 ml j0 jl a b : ℝ}
    (hsigma : sigma ≠ 0) (hm0 : m0 ≠ 0) (hml : ml ≠ 0) :
    (-j0 / m0 - a) * (1 / (sigma * m0)) ^ 2 -
      2 * b * (1 / (sigma * m0)) * (1 / (sigma * ml)) +
      (jl / ml - a) * (1 / (sigma * ml)) ^ 2 =
    (jl * m0 ^ 3 - j0 * ml ^ 3 - a * m0 * ml * (m0 ^ 2 + ml ^ 2) -
      2 * b * m0 ^ 2 * ml ^ 2) / (sigma ^ 2 * m0 ^ 3 * ml ^ 3) := by
  field_simp
  ring

theorem gap_q_negative {sigma m0 ml j0 jl a b : ℝ}
    (hsigma : 0 < sigma) (hm0 : 0 < m0) (hml : 0 < ml)
    (hC2 : jl * m0 ^ 3 - j0 * ml ^ 3 - a * m0 * ml * (m0 ^ 2 + ml ^ 2) -
      2 * b * m0 ^ 2 * ml ^ 2 < 0) :
    (-j0 / m0 - a) * (1 / (sigma * m0)) ^ 2 -
      2 * b * (1 / (sigma * m0)) * (1 / (sigma * ml)) +
      (jl / ml - a) * (1 / (sigma * ml)) ^ 2 < 0 := by
  rw [gap_quadratic_quotient (ne_of_gt hsigma) (ne_of_gt hm0) (ne_of_gt hml)]
  exact div_neg_of_neg_of_pos hC2 (mul_pos (mul_pos (pow_pos hsigma _) (pow_pos hm0 _))
    (pow_pos hml _))

/-- `eq:beam-gap-inequality`, with the reciprocal mode and all four actual
Green endpoint readings supplied locally. No scalar sign is assumed. -/
theorem eq_beam_gap_inequality {sigma l p : ℝ}
    (hsigma : 0 < sigma) (hp : 0 < p) (hpl : p < l) (hlpi : l < π) :
    (1 / (sigma * ml l p)) ^ 2 * (jl l p / ml l p) -
      (1 / (sigma * m0 l p)) ^ 2 * (j0 l p / m0 l p) <
    a l * ((1 / (sigma * m0 l p)) ^ 2 + (1 / (sigma * ml l p)) ^ 2) +
      2 * b l * (1 / (sigma * m0 l p)) * (1 / (sigma * ml l p)) := by
  have h := gap_q_negative hsigma (m0_pos hp hpl hlpi) (ml_pos hp hpl hlpi)
    (C2_endpoint_readings_negative hp hpl hlpi)
  simp only [neg_div] at h
  nlinarith only [h]

/-- `eq:beam-curvature-ratio`: the reciprocal mode and curvature weight,
read from the two actual adjacent residual curvatures. -/
theorem eq_beam_curvature_ratio
    {r rNext sigma sigmaNext m0 ml m0Next c : ℝ}
    (hsigma : sigma ≠ 0) (hm0 : m0 ≠ 0)
    (hcurvature : r = -4 * sigma * m0)
    (hcurvatureNext : rNext = -4 * sigmaNext * m0Next)
    (hmatch : sigma * ml = sigmaNext * m0Next) :
    -4 / r = 1 / (sigma * m0) ∧
    -4 / rNext = 1 / (sigma * ml) ∧
    4 / (-r / c) = c * (-4 / r) := by
  subst r rNext
  constructor
  · field_simp
    ring
  constructor
  · rw [show -4 * sigmaNext * m0Next = -4 * (sigma * ml) by
      rw [hmatch]; ring]
    ring
  · rw [div_div_eq_mul_div]
    field_simp
    ring

/-- `eq:beam-split`: both equalities, including the intermediate student
mass times the reciprocal mode, follow from the adjacent actual readings. -/
theorem eq_beam_split
    {sigmaPrev sigma mlPrev m0 jlPrev j0 c rho : ℝ}
    (hsigma : sigma ≠ 0) (hml : mlPrev ≠ 0) (hm0 : m0 ≠ 0)
    (hmatch : sigmaPrev * mlPrev = sigma * m0)
    (hjump : c = sigmaPrev * jlPrev - sigma * j0)
    (hrho : rho = 4 * sigma * m0 / c) :
    4 / rho = c * (1 / (sigma * m0)) ∧
    c * (1 / (sigma * m0)) = jlPrev / mlPrev - j0 / m0 := by
  have hratio := eq_beam_curvature_ratio (c := c) hsigma hm0
    (r := -4 * sigma * m0) (rNext := -4 * sigma * m0)
    (sigmaNext := sigma) (m0Next := m0) (ml := m0) rfl rfl rfl
  have hweight : 4 / rho = c * (1 / (sigma * m0)) := by
    rw [hrho, show 4 * sigma * m0 / c = -(-4 * sigma * m0) / c by ring]
    exact hratio.2.2.trans (congrArg (fun z : ℝ => c * z) hratio.1)
  refine ⟨hweight, ?_⟩
  rw [hjump]
  field_simp
  linear_combination jlPrev * m0 * hmatch

/-! Cyclic summation and the exact completed-square descent identity. -/

theorem sum_cyclic_shift {n : ℕ} [NeZero n] (f : Fin n → ℝ) :
    (∑ i, f (i + 1)) = ∑ i, f i := by
  apply Fintype.sum_equiv (Equiv.addRight (1 : Fin n))
  intro i
  rfl

/-- `eq:beam-gap-sum`: cyclically split the curvature penalty into its two
endpoint jerk-to-curvature readings. -/
theorem eq_beam_gap_sum {n : ℕ} [NeZero n] (rho u J0 Jl : Fin n → ℝ)
    (hsplit : ∀ i, 4 / rho (i + 1) = Jl i - J0 (i + 1)) :
    (∑ i, 4 / rho i * u i ^ 2) =
      ∑ i, (u (i + 1) ^ 2 * Jl i - u i ^ 2 * J0 i) := by
  rw [← sum_cyclic_shift (fun i => 4 / rho i * u i ^ 2)]
  simp only [hsplit, sub_mul, Finset.sum_sub_distrib]
  rw [sum_cyclic_shift (fun i => J0 i * u i ^ 2)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- `eq:beam-pairing-paper`: expansion of the actual momentum, with a single
cyclic reindexing for both contributions from the previous gap. -/
theorem cyclic_pairing {n : ℕ} [NeZero n] (a b u : Fin n → ℝ) :
    (∑ i, u i * angleMomentum a b u i) =
      ∑ i, (a i * (u i ^ 2 + u (i + 1) ^ 2) + 2 * b i * u i * u (i + 1)) := by
  have hshift := sum_cyclic_shift (fun i =>
    a (i - 1) * u i ^ 2 + b (i - 1) * u (i - 1) * u i)
  simp only [add_sub_cancel] at hshift
  calc
    (∑ i, u i * angleMomentum a b u i) =
        (∑ i, (a i * u i ^ 2 + b i * u i * u (i + 1))) +
          ∑ i, (a (i - 1) * u i ^ 2 + b (i - 1) * u (i - 1) * u i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold angleMomentum
      ring
    _ = _ := by
      rw [← hshift, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem liftedMode_next {N : ℕ} (u : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    liftedMode u (i.val + 1) = u (i + 1) := by
  by_cases hlast : i = Fin.last N
  · subst i
    simp [liftedMode]
  · have hn : i.val + 1 < N + 1 := by
      have hval : i.val ≠ N := by intro h; apply hlast; exact Fin.ext h
      exact Nat.succ_lt_succ (lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hval)
    rw [liftedMode, dif_pos hn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_add_one, if_neg hlast]

/-- Every lifted gap has a positive clamped determinant, including a full
half-period when the finite configuration consists of a single student. -/
theorem liftedCut_determinant {N : ℕ} (θ : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π) :
    ∀ g < N + 1, determinant (liftedCut θ (g + 1) - liftedCut θ g) ≠ 0 := by
  intro g hg
  have hpos := liftedCut_strict θ hmono hspan g hg
  have hlow : θ 0 ≤ liftedCut θ g := by
    rw [liftedCut, dif_pos hg]
    exact hmono.monotone (show (0 : Fin (N + 1)) ≤ ⟨g, hg⟩ from Nat.zero_le g)
  have htop : liftedCut θ (g + 1) ≤ θ 0 + π := by
    by_cases hn : g + 1 < N + 1
    · rw [liftedCut, dif_pos hn]
      exact (hmono.monotone (Fin.le_last ⟨g + 1, hn⟩)).trans hspan.le
    · simp only [liftedCut, dif_neg hn, le_refl]
  exact ne_of_gt (determinant_pos (by linarith only [hpos])
    (by linarith only [hlow, htop]))

/-- The actual length of the cyclic gap starting at student `i`. -/
def cyclicGapLength {N : ℕ} (theta : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ :=
  liftedCut theta (i.val + 1) - theta i

/-- The actual gap sinusoid for arbitrary velocities. The sign depends only
on the order of the student cuts, not on any chosen descent mode. -/
def gapSinusoid {N : ℕ} (dc x θ : Fin (N + 1) → ℝ)
    (g : Fin (N + 1)) (z : ℝ) : ℝ :=
  2 * ∑ i, (if i ≤ g then (1 : ℝ) else -1) *
    (dc i * sin (z + θ g - θ i) - x i * cos (z + θ g - θ i))

theorem continuous_gapSinusoid {N : ℕ} (dc x θ : Fin (N + 1) → ℝ)
    (g : Fin (N + 1)) : Continuous (gapSinusoid dc x θ g) := by
  unfold gapSinusoid
  have h (i : Fin (N + 1)) : Continuous (fun z : ℝ => z + θ g - θ i) :=
    (continuous_id.add continuous_const).sub continuous_const
  exact continuous_const.mul (continuous_finset_sum _ (fun i _ =>
    continuous_const.mul ((continuous_const.mul (continuous_sin.comp (h i))).sub
      (continuous_const.mul (continuous_cos.comp (h i))))))

theorem gapSinusoid_eq_cutBranch {N : ℕ} (dc x θ : Fin (N + 1) → ℝ)
    (g : Fin (N + 1)) (z : ℝ) :
    gapSinusoid dc x θ g z =
      cutBranch N (liftedMode dc) (liftedMode x) (liftedCut θ) g.val (z + θ g) := by
  unfold gapSinusoid cutBranch
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [liftedMode_coe, liftedCut_coe, atomBranch]
  change 2 * ((if i ≤ g then (1 : ℝ) else -1) * _) =
    if i ≤ g then 2 * _ else -(2 * _)
  split_ifs <;> ring

/-- The branch equality is asserted only on the open gap. At knots the
literal feature uses sign(0)=0, which need not equal either branch trace. -/
theorem gapSinusoid_eq_feature_on_gap {N : ℕ} (dc x θ : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π)
    (g : Fin (N + 1)) (t : ℝ)
    (ht : t ∈ Ioo (θ g) (liftedCut θ (g.val + 1))) :
    2 * feature dc x θ (t + π / 2) = gapSinusoid dc x θ g (t - θ g) := by
  have hmonoNat : ∀ i j, i ≤ j → j ≤ N → liftedCut θ i ≤ liftedCut θ j := by
    intro i j hij hj
    have hi : i < N + 1 := by omega (config := {})
    have hj' : j < N + 1 := by omega (config := {})
    rw [liftedCut, dif_pos hi, liftedCut, dif_pos hj']
    exact hmono.monotone hij
  have hspanNat : liftedCut θ N < liftedCut θ 0 + π := by
    simpa [liftedCut] using hspan
  have hright : t < if g.val = N then liftedCut θ 0 + π else liftedCut θ (g.val + 1) := by
    by_cases hg : g.val = N
    · rw [if_pos hg]
      simpa [hg, liftedCut] using ht.2
    · simpa [hg] using ht.2
  have hsign := open_gap_displacements (liftedCut θ) (Nat.le_of_lt_succ g.isLt)
    hmonoNat hspanNat t (by simpa using ht.1) hright
  have h := eq_beam_gap_sinusoid (liftedMode dc) (liftedMode x) (liftedCut θ) t hsign
  rw [rangeFeature_eq_feature] at h
  simp only [liftedMode_coe, liftedCut_coe] at h
  rw [gapSinusoid_eq_cutBranch, sub_add_cancel]
  exact h

/-- Partition an arbitrary represented function into its continuous open-gap
pieces. A finite set of endpoint values has no effect on the integrals. -/
theorem integral_cycle_of_gap_pieces {n : ℕ} (cut : ℕ → ℝ) (f : ℝ → ℝ)
    (P : ℕ → ℝ → ℝ) (hcut : ∀ g < n, cut g < cut (g + 1))
    (hP : ∀ g, Continuous (P g))
    (hpieces : ∀ g < n, ∀ y ∈ Ioo (cut g) (cut (g + 1)), f y = P g (y - cut g)) :
    (∫ y in (cut 0)..(cut n), f y ^ 2) =
      ∑ g in Finset.range n, ∫ z in (0 : ℝ)..(cut (g + 1) - cut g), P g z ^ 2 := by
  have hint : ∀ g < n, IntervalIntegrable (fun y => f y ^ 2) volume (cut g) (cut (g + 1)) := by
    intro g hg
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (hcut g hg).le]
    have hcont : Continuous (fun y => P g (y - cut g) ^ 2) :=
      ((hP g).comp (continuous_id.sub continuous_const)).pow 2
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (hcut g hg).le).mp
      (hcont.intervalIntegrable (μ := volume) (cut g) (cut (g + 1)))
    exact hi.congr_fun (fun y hy => congrArg (fun z : ℝ => z ^ 2)
      (hpieces g hg y hy).symm) measurableSet_Ioo
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  apply Finset.sum_congr rfl
  intro g hg
  have hgn := Finset.mem_range.mp hg
  rw [intervalIntegral_eq_of_open_gap (hcut g hgn).le (fun y hy =>
    congrArg (fun z : ℝ => z ^ 2) (hpieces g hgn y hy)),
    intervalIntegral.integral_comp_sub_right (f := fun z => P g z ^ 2) (cut g), sub_self]

/-- `eq:beam-energy-gapwise`, for arbitrary mass and mass-weighted angular
velocities. Both equalities in the displayed chain are retained. No critical
point, curvature reading, or prescribed beam profile is assumed. -/
theorem eq_beam_energy_gapwise {N : ℕ} (dc x θ : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π) :
    featureEnergy dc x θ = (∫ γ in (0 : ℝ)..π, feature dc x θ (γ + π / 2) ^ 2) ∧
    (∫ γ in (0 : ℝ)..π, feature dc x θ (γ + π / 2) ^ 2) =
      (1 / 4 : ℝ) * ∑ g, ∫ z in (0 : ℝ)..(cyclicGapLength θ g), gapSinusoid dc x θ g z ^ 2 := by
  let idx : ℕ → Fin (N + 1) := fun g => ⟨g % (N + 1), Nat.mod_lt g (Nat.succ_pos N)⟩
  have hidx (g : ℕ) (hg : g < N + 1) : idx g = ⟨g, hg⟩ := Fin.ext (Nat.mod_eq_of_lt hg)
  have hparts := integral_cycle_of_gap_pieces (liftedCut θ)
    (fun y => 2 * feature dc x θ (y + π / 2))
    (fun g => gapSinusoid dc x θ (idx g)) (liftedCut_strict θ hmono hspan)
    (fun g => continuous_gapSinusoid dc x θ (idx g)) (by
      intro g hg y hy
      change 2 * feature dc x θ (y + π / 2) =
        gapSinusoid dc x θ (idx g) (y - liftedCut θ g)
      rw [hidx g hg]
      have hgcut : liftedCut θ g = θ ⟨g, hg⟩ := by rw [liftedCut, dif_pos hg]
      rw [hgcut] at hy ⊢
      exact gapSinusoid_eq_feature_on_gap dc x θ hmono hspan ⟨g, hg⟩ y hy)
  rw [liftedCut_period, integral_shifted_feature_sq, ← Fin.sum_univ_eq_sum_range] at hparts
  have hsum : (∑ i : Fin (N + 1),
      ∫ z in (0 : ℝ)..(liftedCut θ (i.val + 1) - liftedCut θ i.val),
        gapSinusoid dc x θ (idx i.val) z ^ 2) =
      ∑ i, ∫ z in (0 : ℝ)..(cyclicGapLength θ i), gapSinusoid dc x θ i z ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hidx i.val i.isLt]
    simp only [liftedCut_coe, cyclicGapLength]
  rw [hsum] at hparts
  have hshift := integral_shifted_feature_sq dc x θ 0
  rw [zero_add] at hshift
  have hscale : (∫ γ in (0 : ℝ)..π, (2 * feature dc x θ (γ + π / 2)) ^ 2) =
      4 * ∫ γ in (0 : ℝ)..π, feature dc x θ (γ + π / 2) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro γ _
    ring
  rw [hscale] at hshift
  constructor <;> linarith only [hshift, hparts]

/-- The previously checked prescribed-profile energy is now a corollary of
the arbitrary-velocity gapwise formula, so the general equation is an actual
dependency of the specialized beam calculation. -/
theorem feature_energy_of_ordered_gap_realization {N : ℕ}
    (dc x θ u : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π)
    (hrealize : ∀ g, ∀ z ∈ Ioo (0 : ℝ) (cyclicGapLength θ g),
      2 * feature dc x θ (θ g + z + π / 2) =
        profile (cyclicGapLength θ g) (u g) (u (g + 1)) z) :
    featureEnergy dc x θ = 4 * ∑ g,
      (a (cyclicGapLength θ g) * (u g ^ 2 + u (g + 1) ^ 2) +
        2 * b (cyclicGapLength θ g) * u g * u (g + 1)) := by
  obtain ⟨hshift, hgapwise⟩ := eq_beam_energy_gapwise dc x θ hmono hspan
  rw [hshift, hgapwise, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have hpos : 0 < cyclicGapLength θ g := by
    have h := liftedCut_strict θ hmono hspan g.val g.isLt
    simpa only [cyclicGapLength, liftedCut_coe, sub_pos] using h
  have hp : ∀ z ∈ Ioo (0 : ℝ) (cyclicGapLength θ g),
      gapSinusoid dc x θ g z = profile (cyclicGapLength θ g) (u g) (u (g + 1)) z := by
    intro z hz
    have hy : θ g + z ∈ Ioo (θ g) (liftedCut θ (g.val + 1)) := by
      dsimp [cyclicGapLength] at hz
      constructor <;> linarith only [hz.1, hz.2]
    have hs := gapSinusoid_eq_feature_on_gap dc x θ hmono hspan g (θ g + z) hy
    rw [show θ g + z - θ g = z by ring] at hs
    exact hs.symm.trans (hrealize g z hz)
  rw [intervalIntegral_eq_of_open_gap hpos.le (fun z hz => congrArg (fun r : ℝ => r ^ 2) (hp z hz))]
  have hd := liftedCut_determinant θ hmono hspan g.val g.isLt
  simp only [liftedCut_coe] at hd
  change determinant (cyclicGapLength θ g) ≠ 0 at hd
  dsimp only
  rw [eq_beam_branch_energy (u g) (u (g + 1)) hd]
  ring

/-- Choose the right-hand trace on each half-open gap, then extend by π.
This function is not asserted equal to the sign-zero feature at the knots. -/
def gluedProfile {N : ℕ} (θ u : Fin (N + 1) → ℝ) (γ : ℝ) : ℝ :=
  let t := toIcoMod pi_pos (θ 0) γ
  ∑ g, if θ g ≤ t ∧ t < liftedCut θ (g.val + 1) then
    profile (cyclicGapLength θ g) (u g) (u (g + 1)) (t - θ g) else 0

/-- `eq:beam-glued-profile`: literal half-open branch readings and the
periodicity of their common extension. -/
theorem eq_beam_glued_profile {N : ℕ} (θ u : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π) :
    Function.Periodic (gluedProfile θ u) π ∧
    ∀ g, ∀ γ ∈ Ico (θ g) (liftedCut θ (g.val + 1)),
      gluedProfile θ u γ = profile (cyclicGapLength θ g) (u g) (u (g + 1)) (γ - θ g) := by
  constructor
  · intro γ
    simp only [gluedProfile, toIcoMod_add_right]
  · intro g γ hγ
    have hend (j k : Fin (N + 1)) (hjk : j < k) : liftedCut θ (j.val + 1) ≤ θ k := by
      have hn : j.val + 1 < N + 1 := lt_of_le_of_lt (Nat.succ_le_of_lt hjk) k.isLt
      rw [liftedCut, dif_pos hn]
      exact hmono.monotone (show (⟨j.val + 1, hn⟩ : Fin (N + 1)) ≤ k from Nat.succ_le_of_lt hjk)
    have hbase : θ 0 ≤ γ := le_trans (hmono.monotone (Fin.zero_le g)) hγ.1
    have htop : liftedCut θ (g.val + 1) ≤ θ 0 + π := by
      by_cases hn : g.val + 1 < N + 1
      · rw [liftedCut, dif_pos hn]
        exact (hmono.monotone (Fin.le_last ⟨g.val + 1, hn⟩)).trans hspan.le
      · simp only [liftedCut, dif_neg hn, le_refl]
    have hwrap : toIcoMod pi_pos (θ 0) γ = γ :=
      (toIcoMod_eq_self pi_pos).mpr ⟨hbase, lt_of_lt_of_le hγ.2 htop⟩
    simp only [gluedProfile, hwrap]
    change θ g ≤ γ ∧ γ < liftedCut θ (g.val + 1) at hγ
    rw [Finset.sum_eq_single g]
    · rw [if_pos hγ]
    · intro j _ hjg
      rw [if_neg]
      intro hj
      rcases lt_or_gt_of_ne hjg with hlt | hgt
      · exact (not_lt_of_ge (le_trans (hend j g hlt) hγ.1)) hj.2
      · exact (not_lt_of_ge (le_trans (hend g j hgt) hj.1)) hγ.2
    · intro hg
      exact False.elim (hg (Finset.mem_univ g))

/-- `eq:beam-energy-proof`: all three links of the displayed energy chain.
The glued profile is constructed above and explicitly integrated here. -/
theorem eq_beam_energy_proof {N : ℕ} (θ u : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π) :
    let dc := fun i : Fin (N + 1) => orderedMassVelocity N (liftedCut θ) (liftedMode u) i
    let x := angleMomentum (fun i => a (cyclicGapLength θ i))
      (fun i => b (cyclicGapLength θ i)) u
    let I := ∑ g, ∫ z in (0 : ℝ)..(cyclicGapLength θ g),
      profile (cyclicGapLength θ g) (u g) (u (g + 1)) z ^ 2
    let Q := ∑ g, (a (cyclicGapLength θ g) * (u g ^ 2 + u (g + 1) ^ 2) +
      2 * b (cyclicGapLength θ g) * u g * u (g + 1))
    featureEnergy dc x θ = (1 / 4 : ℝ) * I ∧
      (1 / 4 : ℝ) * I = 4 * Q ∧ 4 * Q = 4 * ∑ g, u g * x g := by
  dsimp only
  let dc := fun i : Fin (N + 1) => orderedMassVelocity N (liftedCut θ) (liftedMode u) i
  let x := angleMomentum (fun i => a (cyclicGapLength θ i))
    (fun i => b (cyclicGapLength θ i)) u
  let P := fun g : ℕ => profile (liftedCut θ (g + 1) - liftedCut θ g)
    (liftedMode u g) (liftedMode u (g + 1))
  have hP (g : ℕ) : Continuous (P g) := by
    apply Differentiable.continuous (𝕜 := ℝ)
    intro z
    exact (hasDerivAt_profile_display _ _ _ z).differentiableAt
  have hglue := eq_beam_glued_profile θ u hmono hspan
  have hB := integral_cycle_of_gap_pieces (liftedCut θ) (gluedProfile θ u) P
    (liftedCut_strict θ hmono hspan) hP (by
      intro g hg γ hγ
      have hcg : liftedCut θ g = θ ⟨g, hg⟩ := by rw [liftedCut, dif_pos hg]
      have hug : liftedMode u g = u ⟨g, hg⟩ := by rw [liftedMode, dif_pos hg]
      have hun := liftedMode_next u (⟨g, hg⟩ : Fin (N + 1))
      have h := hglue.2 ⟨g, hg⟩ γ ⟨by simpa only [hcg] using hγ.1.le, hγ.2⟩
      simpa only [P, cyclicGapLength, hcg, hug, hun] using h)
  rw [← Fin.sum_univ_eq_sum_range] at hB
  have hBfinite : (∫ γ in (liftedCut θ 0)..(liftedCut θ (N + 1)), gluedProfile θ u γ ^ 2) =
      ∑ g, ∫ z in (0 : ℝ)..(cyclicGapLength θ g),
        profile (cyclicGapLength θ g) (u g) (u (g + 1)) z ^ 2 := by
    simpa only [P, cyclicGapLength, liftedCut_coe, liftedMode_coe, liftedMode_next] using hB
  obtain ⟨hshift, hgapwise⟩ := eq_beam_energy_gapwise dc x θ hmono hspan
  let idx : ℕ → Fin (N + 1) := fun g => ⟨g % (N + 1), Nat.mod_lt g (Nat.succ_pos N)⟩
  have hidx (g : ℕ) (hg : g < N + 1) : idx g = ⟨g, hg⟩ := Fin.ext (Nat.mod_eq_of_lt hg)
  have hidxFin (g : Fin (N + 1)) : idx g.val = g := Fin.ext (Nat.mod_eq_of_lt g.isLt)
  have hBSin := integral_cycle_of_gap_pieces (liftedCut θ) (gluedProfile θ u)
    (fun g => gapSinusoid dc x θ (idx g)) (liftedCut_strict θ hmono hspan)
    (fun g => continuous_gapSinusoid dc x θ (idx g)) (by
      intro g hg γ hγ
      have hcg : liftedCut θ g = θ ⟨g, hg⟩ := by rw [liftedCut, dif_pos hg]
      have hγFin : γ ∈ Ioo (θ ⟨g, hg⟩) (liftedCut θ (g + 1)) := by
        simpa only [hcg] using hγ
      have hb := hglue.2 ⟨g, hg⟩ γ ⟨hγFin.1.le, hγFin.2⟩
      have hs := gapSinusoid_eq_feature_on_gap dc x θ hmono hspan ⟨g, hg⟩ γ hγFin
      have hp := eq_beam_glued_feature θ u hmono hspan g hg γ hγ
      have hug : liftedMode u g = u ⟨g, hg⟩ := by rw [liftedMode, dif_pos hg]
      have hun := liftedMode_next u (⟨g, hg⟩ : Fin (N + 1))
      have hp' : 2 * feature dc x θ (γ + π / 2) =
          profile (cyclicGapLength θ ⟨g, hg⟩) (u ⟨g, hg⟩) (u (⟨g, hg⟩ + 1))
            (γ - θ ⟨g, hg⟩) := by
        simpa only [dc, x, cyclicGapLength, hcg, hug, hun] using hp
      change gluedProfile θ u γ = gapSinusoid dc x θ (idx g) (γ - liftedCut θ g)
      rw [hidx g hg, hcg]
      exact hb.trans (hp'.symm.trans hs))
  rw [← Fin.sum_univ_eq_sum_range] at hBSin
  have hBSinFinite : (∫ γ in (liftedCut θ 0)..(liftedCut θ (N + 1)), gluedProfile θ u γ ^ 2) =
      ∑ g, ∫ z in (0 : ℝ)..(cyclicGapLength θ g), gapSinusoid dc x θ g z ^ 2 := by
    simpa only [cyclicGapLength, liftedCut_coe, hidxFin] using hBSin
  have hEB : featureEnergy dc x θ = (1 / 4 : ℝ) *
      ∫ γ in (liftedCut θ 0)..(liftedCut θ (N + 1)), gluedProfile θ u γ ^ 2 :=
    hshift.trans (hgapwise.trans (congrArg (fun v : ℝ => (1 / 4 : ℝ) * v) hBSinFinite.symm))
  refine ⟨hEB.trans (congrArg (fun z : ℝ => (1 / 4 : ℝ) * z) hBfinite), ?_, ?_⟩
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    have hd := liftedCut_determinant θ hmono hspan g.val g.isLt
    simp only [liftedCut_coe] at hd
    change determinant (cyclicGapLength θ g) ≠ 0 at hd
    rw [eq_beam_branch_energy (u g) (u (g + 1)) hd]
    ring
  · rw [cyclic_pairing]

/-- The complete energy identity for the constructed physical feature.
The right-hand side is the actual cyclic momentum pairing; no feature-energy
or realization identity is assumed. -/
theorem eq_beam_energy {N : ℕ} (θ u : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π) :
    featureEnergy (fun i => orderedMassVelocity N (liftedCut θ) (liftedMode u) i)
      (angleMomentum (fun j => a (liftedCut θ (j.val + 1) - θ j))
        (fun j => b (liftedCut θ (j.val + 1) - θ j)) u) θ =
      4 * ∑ i, u i * angleMomentum (fun j => a (liftedCut θ (j.val + 1) - θ j))
        (fun j => b (liftedCut θ (j.val + 1) - θ j)) u i := by
  have h := eq_beam_energy_proof θ u hmono hspan
  exact h.1.trans (h.2.1.trans h.2.2)

/-- `eq:beam-constants`: the four literal coefficients and the positive
reciprocal curvature mode, with all claimed strict signs. -/
theorem eq_beam_constants {l r : ℝ} (hl : 0 < l) (hlpi : l < π) (hr : r < 0) :
    a l = 2 * (l - sin l * cos l) / determinant l ∧
    b l = 2 * psi l / determinant l ∧
    d l = 8 * sin l ^ 2 / determinant l ∧
    e l = 8 * l * sin l / determinant l ∧
    0 < -4 / r ∧ 0 < a l ∧ 0 < b l ∧ 0 < d l ∧ 0 < e l := by
  have hdet := determinant_pos hl hlpi.le
  have hsin := sin_pos_of_pos_of_lt_pi hl hlpi
  refine ⟨rfl, rfl, rfl, rfl, div_pos_of_neg_of_neg (by norm_num) hr,
    a_pos hl hlpi, b_pos hl hlpi, ?_, ?_⟩
  · exact div_pos (mul_pos (by norm_num) (pow_pos hsin 2)) hdet
  · exact div_pos (mul_pos (mul_pos (by norm_num) hl) hsin) hdet

/-- `eq:beam-direction-angle`: angular velocity really realizes the chosen
momentum and has the same strictly positive orientation at every student. -/
theorem eq_beam_direction_angle {n : ℕ} [NeZero n] (a b u c : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hu : ∀ i, 0 < u i)
    (hc : ∀ i, 0 < c i) :
    ∀ i, (angleMomentum a b u i / c i) * c i = angleMomentum a b u i ∧
      0 < angleMomentum a b u i / c i := by
  intro i
  exact ⟨div_mul_cancel _ (ne_of_gt (hc i)),
    div_pos (angleMomentum_pos a b u ha hb hu i) (hc i)⟩

/-- `eq:beam-direction`: the slope-jump mass velocity is exactly the paper's
explicit cyclic expression in the constants d and e. -/
theorem eq_beam_direction {N : ℕ} (θ u : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    let l := fun j : Fin (N + 1) => liftedCut θ (j.val + 1) - θ j
    orderedMassVelocity N (liftedCut θ) (liftedMode u) i =
      (1 / 4 : ℝ) * ((d (l i) - d (l (i - 1))) * u i +
        e (l i) * u (i + 1) - e (l (i - 1)) * u (i - 1)) := by
  dsimp only
  have hprev : previousCut N i = ((i - 1 : Fin (N + 1)) : ℕ) := by
    simp [Fin.coe_sub_one, previousCut, Fin.ext_iff]
  simp only [orderedMassVelocity, hprev, liftedCut_coe, liftedMode_coe,
    liftedMode_next, sub_add_cancel]
  rw [(eq_beam_branch_start _ _ _).2.1,
    (eq_beam_branch_end _ _ _).2.1]
  unfold d e
  ring

/-- `stp:beam-mode`: construct the physical velocity, identify both its
components with the displayed formulas, prove positive angular motion,
and compute its actual feature energy. -/
theorem stp_beam_mode {N : ℕ} (θ c u : Fin (N + 1) → ℝ)
    (hmono : StrictMono θ) (hspan : θ (Fin.last N) < θ 0 + π)
    (hlpi : ∀ i : Fin (N + 1), liftedCut θ (i.val + 1) - θ i < π)
    (hc : ∀ i, 0 < c i) (hu : ∀ i, 0 < u i) :
    let l := fun j : Fin (N + 1) => liftedCut θ (j.val + 1) - θ j
    let x := angleMomentum (fun i => a (l i)) (fun i => b (l i)) u
    ∃ dc dθ : Fin (N + 1) → ℝ,
      (∀ i, dc i = (1 / 4 : ℝ) * ((d (l i) - d (l (i - 1))) * u i +
        e (l i) * u (i + 1) - e (l (i - 1)) * u (i - 1))) ∧
      (∀ i, dθ i = x i / c i ∧ c i * dθ i = x i ∧ 0 < dθ i) ∧
      featureEnergy dc (fun i => c i * dθ i) θ = 4 * ∑ i, u i * x i := by
  dsimp only
  let l := fun j : Fin (N + 1) => liftedCut θ (j.val + 1) - θ j
  let x := angleMomentum (fun i => a (l i)) (fun i => b (l i)) u
  let dc := fun i : Fin (N + 1) => orderedMassVelocity N (liftedCut θ) (liftedMode u) i
  let dθ := fun i => x i / c i
  have hconstants : ∀ i, 0 < a (l i) ∧ 0 < b (l i) := by
    intro i
    have hgap := liftedCut_strict θ hmono hspan i.val i.isLt
    rw [liftedCut_coe] at hgap
    have hli : 0 < l i := sub_pos.mpr hgap
    have h := eq_beam_constants hli (hlpi i)
      (div_neg_of_neg_of_pos (by norm_num : (-4 : ℝ) < 0) (hu i))
    exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
  have hangles := eq_beam_direction_angle (fun i => a (l i)) (fun i => b (l i)) u c
    (fun i => (hconstants i).1) (fun i => (hconstants i).2) hu hc
  have hmomentum : (fun i => c i * dθ i) = x := by
    funext i
    exact (mul_comm _ _).trans (hangles i).1
  refine ⟨dc, dθ, (fun i => eq_beam_direction θ u i), ?_, ?_⟩
  · intro i
    exact ⟨rfl, congrFun hmomentum i, (hangles i).2⟩
  · rw [hmomentum]
    exact eq_beam_energy θ u hmono hspan

/-- Subtracting the momentum pairing from the exact gap sum gives the sum
of local gap quadratics. -/
theorem sum_gap_q {n : ℕ} [NeZero n] (a b left right rho u : Fin n → ℝ)
    (hsplit : ∀ i, 4 / rho (i + 1) =
      (a i + right i) + (a (i + 1) + left (i + 1))) :
    (∑ i, (left i * u i ^ 2 - 2 * b i * u i * u (i + 1) +
      right i * u (i + 1) ^ 2)) =
      4 * (∑ i, u i ^ 2 / rho i) - ∑ i, u i * angleMomentum a b u i := by
  have hsum := eq_beam_gap_sum rho u (fun i => -(a i + left i))
    (fun i => a i + right i) (by intro i; rw [hsplit]; ring)
  have hpen : 4 * (∑ i, u i ^ 2 / rho i) = ∑ i, 4 / rho i * u i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hpen, hsum, cyclic_pairing, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `eq:beam-target`: summing strict local gap inequalities makes the
curvature penalty strictly smaller than the momentum pairing. -/
theorem eq_beam_target {n : ℕ} [NeZero n] (a b left right rho u : Fin n → ℝ)
    (hsplit : ∀ i, 4 / rho (i + 1) =
      (a i + right i) + (a (i + 1) + left (i + 1)))
    (hgap : ∀ i, left i * u i ^ 2 - 2 * b i * u i * u (i + 1) +
      right i * u (i + 1) ^ 2 < 0) :
    (∑ i, 4 / rho i * u i ^ 2) < ∑ i, u i * angleMomentum a b u i := by
  have hsum : (∑ i, (left i * u i ^ 2 - 2 * b i * u i * u (i + 1) +
      right i * u (i + 1) ^ 2)) < 0 :=
    Finset.sum_neg (fun i _ => hgap i) Finset.univ_nonempty
  rw [sum_gap_q a b left right rho u hsplit] at hsum
  have hpen : (∑ i, 4 / rho i * u i ^ 2) = 4 * ∑ i, u i ^ 2 / rho i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hpen]
  linarith only [hsum]

/-- The literal algebraic square completion underlying the descent display. -/
theorem completed_square_identity {n : ℕ} (rho u x : Fin n → ℝ)
    (hrho : ∀ i, 0 < rho i) :
    4 * (∑ i, u i * x i) - ∑ i, rho i * x i ^ 2 =
      4 * ((∑ i, 4 / rho i * u i ^ 2) - ∑ i, u i * x i) -
        ∑ i, (rho i * x i - 4 * u i) ^ 2 / rho i := by
  have hpoint : ∀ i, (rho i * x i - 4 * u i) ^ 2 / rho i =
      rho i * x i ^ 2 - 8 * (u i * x i) + 4 * (4 / rho i * u i ^ 2) := by
    intro i
    field_simp [ne_of_gt (hrho i)]
    ring
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- `eq:beam-descent-identity`: both equalities of the manuscript's actual
normalized second-variation chain, before substituting the gap sum. -/
theorem eq_beam_descent_identity {n : ℕ} (rho u x : Fin n → ℝ)
    (hrho : ∀ i, 0 < rho i) (E D2 : ℝ)
    (henergy : E = 4 * ∑ i, u i * x i)
    (hsecond : 2 * π * D2 = E - ∑ i, rho i * x i ^ 2) :
    2 * π * D2 = 4 * (∑ i, u i * x i) - ∑ i, rho i * x i ^ 2 ∧
    4 * (∑ i, u i * x i) - ∑ i, rho i * x i ^ 2 =
      4 * ((∑ i, 4 / rho i * u i ^ 2) - ∑ i, u i * x i) -
        ∑ i, (rho i * x i - 4 * u i) ^ 2 / rho i := by
  exact ⟨hsecond.trans (by rw [henergy]), completed_square_identity rho u x hrho⟩

/-- The completed-square identity after substituting the sum of local gap
quadratics. The preceding labeled identity retains the unsubstituted form. -/
theorem beam_descent_identity_gap_quadratics {n : ℕ} [NeZero n] (a b left right rho u : Fin n → ℝ)
    (hrho : ∀ i, 0 < rho i)
    (hsplit : ∀ i, 4 / rho (i + 1) =
      (a i + right i) + (a (i + 1) + left (i + 1))) :
    4 * (∑ i, u i * angleMomentum a b u i) -
      ∑ i, rho i * angleMomentum a b u i ^ 2 =
    4 * (∑ i, (left i * u i ^ 2 - 2 * b i * u i * u (i + 1) +
      right i * u (i + 1) ^ 2)) -
      ∑ i, (rho i * angleMomentum a b u i - 4 * u i) ^ 2 / rho i := by
  rw [sum_gap_q a b left right rho u hsplit]
  have hpoint : ∀ i, (rho i * angleMomentum a b u i - 4 * u i) ^ 2 / rho i =
      rho i * angleMomentum a b u i ^ 2 - 8 * (u i * angleMomentum a b u i) +
        16 * (u i ^ 2 / rho i) := by
    intro i
    field_simp [ne_of_gt (hrho i)]
    ring
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Strict per-gap negativity implies strict energy descent, without any
equality-case or nonzero-velocity subcase. -/
theorem beam_energy_negative {n : ℕ} [NeZero n] (a b left right rho u : Fin n → ℝ)
    (hrho : ∀ i, 0 < rho i)
    (hsplit : ∀ i, 4 / rho (i + 1) =
      (a i + right i) + (a (i + 1) + left (i + 1)))
    (hgap : ∀ i, left i * u i ^ 2 - 2 * b i * u i * u (i + 1) +
      right i * u (i + 1) ^ 2 < 0) :
    4 * (∑ i, u i * angleMomentum a b u i) -
      ∑ i, rho i * angleMomentum a b u i ^ 2 < 0 := by
  rw [beam_descent_identity_gap_quadratics a b left right rho u hrho hsplit]
  have hsum : (∑ i, (left i * u i ^ 2 - 2 * b i * u i * u (i + 1) +
      right i * u (i + 1) ^ 2)) < 0 := Finset.sum_neg (fun i _ => hgap i) Finset.univ_nonempty
  have hsquare : 0 ≤ ∑ i, (rho i * angleMomentum a b u i - 4 * u i) ^ 2 / rho i :=
    Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hrho i).le)
  linarith

/-- The strict second-variation inference, consuming the exact
target and both equalities of the normalized descent display. -/
theorem beam_second_variation_negative {n : ℕ} [NeZero n]
    (a b left right rho u : Fin n → ℝ)
    (hrho : ∀ i, 0 < rho i)
    (hsplit : ∀ i, 4 / rho (i + 1) =
      (a i + right i) + (a (i + 1) + left (i + 1)))
    (hgap : ∀ i, left i * u i ^ 2 - 2 * b i * u i * u (i + 1) +
      right i * u (i + 1) ^ 2 < 0)
    (E D2 : ℝ) (henergy : E = 4 * ∑ i, u i * angleMomentum a b u i)
    (hsecond : 2 * π * D2 = E - ∑ i, rho i * angleMomentum a b u i ^ 2) :
    D2 < 0 := by
  have htarget := eq_beam_target a b left right rho u hsplit hgap
  obtain ⟨hfirst, hsquares⟩ := eq_beam_descent_identity rho u
    (angleMomentum a b u) hrho E D2 henergy hsecond
  have hnonneg : 0 ≤ ∑ i, (rho i * angleMomentum a b u i - 4 * u i) ^ 2 / rho i :=
    Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hrho i).le)
  have hnegative : 2 * π * D2 < 0 := by
    rw [hfirst, hsquares]
    linarith only [htarget, hnonneg]
  exact neg_of_mul_neg_right hnegative (mul_pos (by norm_num) pi_pos).le

/-- Step 3 specialized to actual gap lengths and teacher offsets. The exact
displayed gap inequality is the input to the completed-square descent proof. -/
theorem stp_beam_gap_inequality {n : ℕ} [NeZero n]
    (l p sigma c : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpl : ∀ i, p i < l i) (hlpi : ∀ i, l i < π)
    (hc : ∀ i, 0 < c i) (hsigma : ∀ i, 0 < sigma i)
    (hmatch : ∀ i, sigma i * ml (l i) (p i) =
      sigma (i + 1) * m0 (l (i + 1)) (p (i + 1)))
    (hjump : ∀ i, c (i + 1) = sigma i * jl (l i) (p i) -
      sigma (i + 1) * j0 (l (i + 1)) (p (i + 1)))
    (E D2 : ℝ)
    (henergy : E = 4 * ∑ i, (1 / (sigma i * m0 (l i) (p i))) *
      angleMomentum (fun j => a (l j)) (fun j => b (l j))
        (fun j => 1 / (sigma j * m0 (l j) (p j))) i)
    (hsecond : 2 * π * D2 = E - ∑ i,
      (4 * sigma i * m0 (l i) (p i) / c i) *
      angleMomentum (fun j => a (l j)) (fun j => b (l j))
        (fun j => 1 / (sigma j * m0 (l j) (p j))) i ^ 2) :
    D2 < 0 := by
  let u := fun i => 1 / (sigma i * m0 (l i) (p i))
  let rho := fun i => 4 * sigma i * m0 (l i) (p i) / c i
  let left := fun i => -j0 (l i) (p i) / m0 (l i) (p i) - a (l i)
  let right := fun i => jl (l i) (p i) / ml (l i) (p i) - a (l i)
  have hm0 (i : Fin n) := m0_pos (hp i) (hpl i) (hlpi i)
  have hml (i : Fin n) := ml_pos (hp i) (hpl i) (hlpi i)
  have hrho : ∀ i, 0 < rho i := by
    intro i
    exact div_pos (mul_pos (mul_pos (by norm_num) (hsigma i)) (hm0 i)) (hc i)
  have hsplit : ∀ i, 4 / rho (i + 1) =
      (a (l i) + right i) + (a (l (i + 1)) + left (i + 1)) := by
    intro i
    have h := eq_beam_split (ne_of_gt (hsigma (i + 1)))
      (ne_of_gt (hml i)) (ne_of_gt (hm0 (i + 1))) (hmatch i) (hjump i)
      (show rho (i + 1) = _ from rfl)
    rw [h.1.trans h.2]
    dsimp only [left, right]
    ring
  have hgap : ∀ i, left i * u i ^ 2 - 2 * b (l i) * u i * u (i + 1) +
      right i * u (i + 1) ^ 2 < 0 := by
    intro i
    dsimp only [left, right, u]
    rw [← hmatch i]
    have h := eq_beam_gap_inequality (hsigma i) (hp i) (hpl i) (hlpi i)
    simp only [neg_div]
    nlinarith only [h]
  exact beam_second_variation_negative (fun i => a (l i)) (fun i => b (l i))
    left right rho u hrho hsplit hgap E D2 henergy hsecond

/-- The local scalar and finite calculus proofs construct an actual negative
second derivative. Only the geometric readings and physical feature-energy
identity enter from the preceding analytic steps. -/
theorem beam_negative_second_derivative {n m : ℕ} [NeZero n]
    (K K1 K2 : ℝ → ℝ)
    (hK : ∀ t, HasDerivAt K (K1 t) t) (hK1 : ∀ t, HasDerivAt K1 (K2 t) t)
    (hodd : ∀ t, K1 (-t) = -K1 t) (heven : ∀ t, K2 (-t) = K2 t)
    (c dc theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (l p sigma : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpl : ∀ i, p i < l i) (hlpi : ∀ i, l i < π)
    (hc : ∀ i, 0 < c i) (hsigma : ∀ i, 0 < sigma i)
    (hstationary : ∀ i, finiteResidual K1 c theta s beta (theta i) = 0)
    (hcurvature : ∀ i, finiteResidual K2 c theta s beta (theta i) =
      -4 * sigma i * m0 (l i) (p i))
    (hmatch : ∀ i, sigma i * ml (l i) (p i) =
      sigma (i + 1) * m0 (l (i + 1)) (p (i + 1)))
    (hjump : ∀ i, c (i + 1) = sigma i * jl (l i) (p i) -
      sigma (i + 1) * j0 (l (i + 1)) (p (i + 1)))
    (hgram : ∀ dc x : Fin n → ℝ,
      featureGram K K1 K2 dc x theta = featureEnergy dc x theta)
    (henergy : featureEnergy dc
      (angleMomentum (fun i => a (l i)) (fun i => b (l i))
        (fun i => 1 / (sigma i * m0 (l i) (p i)))) theta =
      4 * ∑ i, (1 / (sigma i * m0 (l i) (p i))) *
        angleMomentum (fun i => a (l i)) (fun i => b (l i))
          (fun i => 1 / (sigma i * m0 (l i) (p i))) i) :
    ∃ dtheta : Fin n → ℝ,
      deriv (deriv (fun t : ℝ => finiteKernelLoss K s beta
        (fun i => c i + t * dc i) (fun i => theta i + t * dtheta i))) 0 < 0 := by
  let x := angleMomentum (fun i => a (l i)) (fun i => b (l i))
    (fun i => 1 / (sigma i * m0 (l i) (p i)))
  let dtheta := fun i => x i / c i
  refine ⟨dtheta, ?_⟩
  have hweighted : (fun i => c i * dtheta i) = x := by
    funext i
    dsimp [dtheta]
    exact mul_div_cancel' (x i) (ne_of_gt (hc i))
  have hsecond : 2 * π * deriv (deriv (fun t : ℝ => finiteKernelLoss K s beta
        (fun i => c i + t * dc i) (fun i => theta i + t * dtheta i))) 0 =
      featureEnergy dc x theta - ∑ i, (4 * sigma i * m0 (l i) (p i) / c i) * x i ^ 2 := by
    apply stp_beam_second_variation K K1 K2 hK hK1 hodd heven
      c dc theta dtheta x (fun i => 4 * sigma i * m0 (l i) (p i) / c i)
      s beta hgram hstationary (fun i => congrFun hweighted i)
    intro i
    rw [hcurvature]
    ring
  exact stp_beam_gap_inequality l p sigma c hp hpl hlpi hc hsigma hmatch hjump
    (featureEnergy dc x theta) _ henergy hsecond


theorem cyclicGapLength_lt_pi {N : ℕ} (hN : 0 < N) (theta : Fin (N + 1) → ℝ)
    (hmono : StrictMono theta) (hspan : theta (Fin.last N) < theta 0 + π)
    (i : Fin (N + 1)) : cyclicGapLength theta i < π := by
  by_cases hlast : i = Fin.last N
  · subst i
    have hlt := hmono (show (0 : Fin (N + 1)) < Fin.last N from hN)
    simp only [cyclicGapLength, Fin.val_last, liftedCut, lt_self_iff_false, dite_false]
    linarith only [hlt]
  · have hi : i.val ≠ N := by
      intro hi
      exact hlast (Fin.ext hi)
    have hn : i.val + 1 < N + 1 :=
      Nat.succ_lt_succ (lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hi)
    rw [cyclicGapLength, liftedCut, dif_pos hn]
    have hlow := hmono.monotone (show (0 : Fin (N + 1)) ≤ i from Nat.zero_le _)
    have hhigh := hmono.monotone (Fin.le_last (⟨i.val + 1, hn⟩ : Fin (N + 1)))
    linarith only [hlow, hhigh, hspan]

/-- The ordered beam construction with every mode, feature, integral, and
scalar sign supplied locally. The two calculus facts are instantiated by the
local kernel calculus in the final planar proposition; the geometric inputs
are the actual residual endpoint and jerk readings. -/
theorem ordered_beam_descent_of_kernel_calculus {N m : ℕ}
    (hK : ∀ t, HasDerivAt CircleMoments.K (CircleMoments.K1 t) t)
    (hK1 : ∀ t, HasDerivAt CircleMoments.K1 (CircleMoments.K2 t) t)
    (hN : 0 < N) (c theta p sigma : Fin (N + 1) → ℝ) (s beta : Fin m → ℝ)
    (hmono : StrictMono theta) (hspan : theta (Fin.last N) < theta 0 + π)
    (hc : ∀ i, 0 < c i) (hsigma : ∀ i, 0 < sigma i)
    (hp : ∀ i, 0 < p i) (hpl : ∀ i, p i < cyclicGapLength theta i)
    (hstationary : ∀ i, finiteResidual CircleMoments.K1 c theta s beta (theta i) = 0)
    (hcurvature : ∀ i, finiteResidual CircleMoments.K2 c theta s beta (theta i) =
      -4 * sigma i * m0 (cyclicGapLength theta i) (p i))
    (hmatch : ∀ i, sigma i * ml (cyclicGapLength theta i) (p i) =
      sigma (i + 1) * m0 (cyclicGapLength theta (i + 1)) (p (i + 1)))
    (hjump : ∀ i, c (i + 1) = sigma i * jl (cyclicGapLength theta i) (p i) -
      sigma (i + 1) * j0 (cyclicGapLength theta (i + 1)) (p (i + 1))) :
    ∃ dc dtheta : Fin (N + 1) → ℝ,
      deriv (deriv (fun t : ℝ => finiteKernelLoss CircleMoments.K s beta
        (fun i => c i + t * dc i) (fun i => theta i + t * dtheta i))) 0 < 0 := by
  let u := fun i => 1 / (sigma i * m0 (cyclicGapLength theta i) (p i))
  have hlpi := cyclicGapLength_lt_pi hN theta hmono hspan
  have hmode : ∀ i, u i =
      -4 / finiteResidual CircleMoments.K2 c theta s beta (theta i) := by
    intro i
    exact (eq_beam_curvature_ratio (c := c i) (ne_of_gt (hsigma i))
      (ne_of_gt (m0_pos (hp i) (hpl i) (hlpi i)))
      (hcurvature i) (hcurvature (i + 1)) (hmatch i)).1.symm
  have hu : ∀ i, 0 < u i := by
    intro i
    rw [hmode]
    have hr : finiteResidual CircleMoments.K2 c theta s beta (theta i) < 0 := by
      rw [hcurvature]
      nlinarith only [mul_pos (hsigma i) (m0_pos (hp i) (hpl i) (hlpi i))]
    exact div_pos_of_neg_of_neg (by norm_num) hr
  obtain ⟨dcMode, dthetaMode, hmass, hangle, henergy⟩ :=
    stp_beam_mode theta c u hmono hspan hlpi hc hu
  let dc := fun i : Fin (N + 1) => (1 / 4 : ℝ) *
    ((d (cyclicGapLength theta i) - d (cyclicGapLength theta (i - 1))) * u i +
      e (cyclicGapLength theta i) * u (i + 1) -
      e (cyclicGapLength theta (i - 1)) * u (i - 1))
  have hdc : dcMode = dc := funext hmass
  have hweighted : (fun i => c i * dthetaMode i) =
      angleMomentum (fun i => a (cyclicGapLength theta i))
        (fun i => b (cyclicGapLength theta i)) u :=
    funext fun i => (hangle i).2.1
  rw [hdc, hweighted] at henergy
  have hodd : ∀ t, CircleMoments.K1 (-t) = -CircleMoments.K1 t := by
    intro t
    simp [CircleMoments.K1]
  have heven : ∀ t, CircleMoments.K2 (-t) = CircleMoments.K2 t := by
    intro t
    simp [CircleMoments.K2, CircleMoments.K]
  obtain ⟨dtheta, hnegative⟩ := beam_negative_second_derivative
    CircleMoments.K CircleMoments.K1 CircleMoments.K2 hK hK1 hodd heven
    c dc theta s beta (cyclicGapLength theta) p sigma hp hpl
    hlpi hc hsigma hstationary hcurvature
    hmatch hjump (fun dc x => eq_E_first_sum dc x theta) henergy
  exact ⟨dc, dtheta, hnegative⟩

end PaperLeanFormalization.Beam
