import Beam
import Preliminaries
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv


noncomputable section
open Real
open scoped BigOperators Interval


namespace PaperLeanFormalization.GreenWronskian

open MeasureTheory Set

abbrev Jet := Fin 5 → ℝ → ℝ

/-- The boundary form for the self-adjoint operator `(D²+1)²`. -/
def concomitant (f h : Jet) (x : ℝ) : ℝ :=
  h 0 x * f 3 x - h 1 x * f 2 x + h 2 x * f 1 x - h 3 x * f 0 x +
    2 * (h 0 x * f 1 x - h 1 x * f 0 x)

/-- `eq:concomitant-jump`: matching through order two leaves precisely the
two third-derivative jump terms, also when both sources share one knot. -/
theorem eq_concomitant_jump (fL fR hL hR : Jet) (c : ℝ)
    (hf : ∀ i : Fin 3, fR (i.castLE (by decide)) c = fL (i.castLE (by decide)) c)
    (hh : ∀ i : Fin 3, hR (i.castLE (by decide)) c = hL (i.castLE (by decide)) c) :
    concomitant fR hR c - concomitant fL hL c =
      hL 0 c * (fR 3 c - fL 3 c) - fL 0 c * (hR 3 c - hL 3 c) := by
  have hf0 : fR 0 c = fL 0 c := hf 0
  have hf1 : fR 1 c = fL 1 c := hf 1
  have hf2 : fR 2 c = fL 2 c := hf 2
  have hh0 : hR 0 c = hL 0 c := hh 0
  have hh1 : hR 1 c = hL 1 c := hh 1
  have hh2 : hR 2 c = hL 2 c := hh 2
  dsimp only [concomitant]
  rw [hf0, hf1, hf2, hh0, hh1, hh2]
  ring

/-- `eq:wronski_beauty`, for arbitrary fourth-order differentiable jets. -/
theorem eq_wronski_beauty (f h : Jet) (x : ℝ)
    (hf : ∀ i : Fin 4, HasDerivAt (f i.castSucc) (f i.succ x) x)
    (hh : ∀ i : Fin 4, HasDerivAt (h i.castSucc) (h i.succ x) x) :
    HasDerivAt (concomitant f h)
      (h 0 x * (f 4 x + 2 * f 2 x + f 0 x) -
        f 0 x * (h 4 x + 2 * h 2 x + h 0 x)) x := by
  have hf0 : HasDerivAt (f 0) (f 1 x) x := hf 0
  have hf1 : HasDerivAt (f 1) (f 2 x) x := hf 1
  have hf2 : HasDerivAt (f 2) (f 3 x) x := hf 2
  have hf3 : HasDerivAt (f 3) (f 4 x) x := hf 3
  have hh0 : HasDerivAt (h 0) (h 1 x) x := hh 0
  have hh1 : HasDerivAt (h 1) (h 2 x) x := hh 1
  have hh2 : HasDerivAt (h 2) (h 3 x) x := hh 2
  have hh3 : HasDerivAt (h 3) (h 4 x) x := hh 3
  convert (((hh0.mul hf3).sub (hh1.mul hf2)).add
    (hh2.mul hf1)).sub (hh3.mul hf0) |>.add
      (((hh0.mul hf1).sub (hh1.mul hf0)).const_mul 2) using 1
  dsimp [concomitant]
  ring

/-- A smooth branch of a homogeneous beam solution. The full derivative
chain and differential equation are explicit fields, not total derivatives. -/
structure Branch where
  jet : Jet
  derivative : ∀ (i : Fin 4) (x : ℝ),
    HasDerivAt (jet i.castSucc) (jet i.succ x) x
  equation : ∀ x, jet 4 x + 2 * jet 2 x + jet 0 x = 0

/-- Double-zero endpoint conditions remove the entire boundary pairing. -/
theorem concomitant_clamped (f h : Jet) (x : ℝ)
    (hf : f 0 x = 0 ∧ f 1 x = 0) (hh : h 0 x = 0 ∧ h 1 x = 0) :
    concomitant f h x = 0 := by
  simp only [concomitant, hf.1, hf.2, hh.1, hh.2,
    zero_mul, mul_zero, sub_self, add_zero]

/-- A genuinely smooth fourth-order jet, with no homogeneous equation
assumption. It permits both regular forcing and singular test sources. -/
structure SmoothJet where
  jet : Jet
  derivative : ∀ (i : Fin 4) (x : ℝ),
    HasDerivAt (jet i.castSucc) (jet i.succ x) x
  continuous : ∀ i, Continuous (jet i)

def SmoothJet.operator (f : SmoothJet) (x : ℝ) : ℝ :=
  f.jet 4 x + 2 * f.jet 2 x + f.jet 0 x

theorem SmoothJet.continuous_operator (f : SmoothJet) : Continuous f.operator :=
  ((f.continuous 4).add (continuous_const.mul (f.continuous 2))).add (f.continuous 0)

/-- Integrated adjoint identity on one smooth interval. -/
theorem weak_interval_identity (f h : SmoothJet) (a b : ℝ) :
    (∫ x in a..b, h.jet 0 x * f.operator x - f.jet 0 x * h.operator x) =
      concomitant f.jet h.jet b - concomitant f.jet h.jet a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => eq_wronski_beauty f.jet h.jet x
      (fun i => f.derivative i x) (fun i => h.derivative i x))
    ((((h.continuous 0).mul f.continuous_operator).sub
      ((f.continuous 0).mul h.continuous_operator)).intervalIntegrable _ _)

/-- The weak beam equation for a C² piecewise-C⁴ solution and a C²
piecewise-C⁴ test. Both Dirac contributions and both boundary terms are
retained. Oriented integrals make a separate source-order case unnecessary. -/
theorem eq_LFC_piecewise_test (fL fR hL hR : SmoothJet) (a b p q A B : ℝ)
    (hfjoin : ∀ i : Fin 3, fR.jet (i.castLE (by decide)) p =
      fL.jet (i.castLE (by decide)) p)
    (hfjump : fR.jet 3 p = fL.jet 3 p + A)
    (hhjoin : ∀ i : Fin 3, hR.jet (i.castLE (by decide)) q =
      hL.jet (i.castLE (by decide)) q)
    (hhjump : hR.jet 3 q = hL.jet 3 q + B) :
    (∫ x in a..p, hL.jet 0 x * fL.operator x - fL.jet 0 x * hL.operator x) +
      (∫ x in p..q, hL.jet 0 x * fR.operator x - fR.jet 0 x * hL.operator x) +
      (∫ x in q..b, hR.jet 0 x * fR.operator x - fR.jet 0 x * hR.operator x) =
      concomitant fR.jet hR.jet b - concomitant fL.jet hL.jet a -
        A * hL.jet 0 p + B * fR.jet 0 q := by
  have hF : concomitant fR.jet hL.jet p - concomitant fL.jet hL.jet p =
      A * hL.jet 0 p := by
    rw [eq_concomitant_jump fL.jet fR.jet hL.jet hL.jet p hfjoin (fun _ => rfl), hfjump]
    ring
  have hH : concomitant fR.jet hR.jet q - concomitant fR.jet hL.jet q =
      -B * fR.jet 0 q := by
    rw [eq_concomitant_jump fR.jet fR.jet hL.jet hR.jet q (fun _ => rfl) hhjoin, hhjump]
    ring
  rw [weak_interval_identity, weak_interval_identity, weak_interval_identity]
  linarith only [hF, hH]

/-- A homogeneous branch has a continuous fourth derivative because its
equation explicitly expresses that derivative through its lower jets. -/
def Branch.toSmoothJet (f : Branch) : SmoothJet where
  jet := f.jet
  derivative := f.derivative
  continuous := by
    have h0 : Continuous (f.jet 0) := continuous_iff_continuousAt.mpr fun x =>
      (show HasDerivAt (f.jet 0) (f.jet 1 x) x from f.derivative 0 x).continuousAt
    have h1 : Continuous (f.jet 1) := continuous_iff_continuousAt.mpr fun x =>
      (show HasDerivAt (f.jet 1) (f.jet 2 x) x from f.derivative 1 x).continuousAt
    have h2 : Continuous (f.jet 2) := continuous_iff_continuousAt.mpr fun x =>
      (show HasDerivAt (f.jet 2) (f.jet 3 x) x from f.derivative 2 x).continuousAt
    have h3 : Continuous (f.jet 3) := continuous_iff_continuousAt.mpr fun x =>
      (show HasDerivAt (f.jet 3) (f.jet 4 x) x from f.derivative 3 x).continuousAt
    have h4 : Continuous (f.jet 4) := by
      have heq : f.jet 4 = fun x => -(2 * f.jet 2 x + f.jet 0 x) := by
        funext x
        linarith only [f.equation x]
      rw [heq]
      exact ((continuous_const.mul h2).add h0).neg
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

/-- Green reciprocity is a direct instance of
the weak equation with both source strengths one and all boundary terms zero.
This is consumed by the actual clamped Green construction. -/
theorem branch_reciprocity (fL fR hL hR : Branch) (a b p q : ℝ)
    (hfleft : fL.jet 0 a = 0 ∧ fL.jet 1 a = 0)
    (hfright : fR.jet 0 b = 0 ∧ fR.jet 1 b = 0)
    (hhleft : hL.jet 0 a = 0 ∧ hL.jet 1 a = 0)
    (hhright : hR.jet 0 b = 0 ∧ hR.jet 1 b = 0)
    (hfjoin : ∀ i : Fin 3, fR.jet (i.castLE (by decide)) p = fL.jet (i.castLE (by decide)) p)
    (hfjump : fR.jet 3 p = fL.jet 3 p + 1)
    (hhjoin : ∀ i : Fin 3, hR.jet (i.castLE (by decide)) q = hL.jet (i.castLE (by decide)) q)
    (hhjump : hR.jet 3 q = hL.jet 3 q + 1) :
    fR.jet 0 q = hL.jet 0 p := by
  have H := eq_LFC_piecewise_test fL.toSmoothJet fR.toSmoothJet
    hL.toSmoothJet hR.toSmoothJet a b p q 1 1 hfjoin hfjump hhjoin hhjump
  have ho (f : Branch) (x : ℝ) : f.toSmoothJet.operator x = 0 := f.equation x
  simp_rw [ho] at H
  simp only [mul_zero, sub_self, intervalIntegral.integral_zero, zero_add,
    one_mul] at H
  change (0 : ℝ) = concomitant fR.jet hR.jet b - concomitant fL.jet hL.jet a -
    hL.jet 0 p + fR.jet 0 q at H
  rw [concomitant_clamped fR.jet hR.jet b hfright hhright,
    concomitant_clamped fL.jet hL.jet a hfleft hhleft] at H
  linarith only [H]


end PaperLeanFormalization.GreenWronskian

namespace PaperLeanFormalization.WeakBeamEquation

open Real MeasureTheory Set
open GreenWronskian
open scoped BigOperators Interval

/-- A periodic C4 test, recording actual derivative witnesses rather than
assuming any identity about the total derivative of a nonsmooth function. -/
structure Test extends SmoothJet where
  periodic : ∀ i, Function.Periodic (jet i) π

def Test.operator (h : Test) (x : ℝ) : ℝ :=
  h.jet 4 x + 2 * h.jet 2 x + h.jet 0 x

theorem Test.continuous_operator (h : Test) : Continuous h.operator :=
  ((h.continuous 4).add (continuous_const.mul (h.continuous 2))).add (h.continuous 0)

def Test.translate (h : Test) (a : ℝ) : Test where
  jet i x := h.jet i (x + a)
  derivative i x := by
    simpa only [mul_one] using (h.derivative i (x + a)).comp x
      ((hasDerivAt_id x).add_const a)
  continuous i := (h.continuous i).comp (continuous_id.add continuous_const)
  periodic i x := by
    simpa only [add_right_comm x π a] using h.periodic i (x + a)

theorem periodic_derivative {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hp : Function.Periodic f π) : Function.Periodic (deriv f) π := by
  intro x
  have H := (hf (x + π)).hasDerivAt.comp x ((hasDerivAt_id x).add_const π)
  change HasDerivAt (fun y => f (y + π)) (deriv f (x + π) * 1) x at H
  have heq : (fun y => f (y + π)) = f := funext hp
  rw [heq, mul_one] at H
  exact H.deriv.symm

theorem periodic_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f)
    (hp : Function.Periodic f π) :
    ∀ k : ℕ, k ≤ 4 → Function.Periodic (iteratedDeriv k f) π
  | 0, _ => by simpa only [iteratedDeriv_zero] using hp
  | k + 1, hk => by
      rw [iteratedDeriv_succ]
      apply periodic_derivative
      · apply hf.differentiable_iteratedDeriv k
        exact_mod_cast (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      · exact periodic_iteratedDeriv hf hp k (Nat.le_of_succ_le hk)

/-- Every ordinary periodic C4 function supplies the derivative chain above;
there is no extra jet assumption in the public smooth-test equation. -/
def Test.ofSmooth (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (hp : Function.Periodic f π) : Test where
  jet i := iteratedDeriv i.val f
  derivative i x := by
    change HasDerivAt (iteratedDeriv i.val f) (iteratedDeriv (i.val + 1) f x) x
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv i.val (by exact_mod_cast i.isLt) x).hasDerivAt
  continuous i := hf.continuous_iteratedDeriv i.val
    (by exact_mod_cast Nat.le_of_lt_succ i.isLt)
  periodic i := periodic_iteratedDeriv hf hp i.val (Nat.le_of_lt_succ i.isLt)

/-- The single smooth branch needed for a period. No sorting of atoms and
no interval-by-interval residual construction enters the weak equation. -/
def principalJet (i : Fin 5) (x : ℝ) : ℝ :=
  match i.val with
  | 0 => sin x + (π / 2 - x) * cos x
  | 1 => (x - π / 2) * sin x
  | 2 => sin x + (x - π / 2) * cos x
  | 3 => 2 * cos x - (x - π / 2) * sin x
  | _ => -3 * sin x - (x - π / 2) * cos x

@[simp] theorem principal_zero (x : ℝ) :
    principalJet 0 x = sin x + (π / 2 - x) * cos x := rfl
@[simp] theorem principal_one (x : ℝ) :
    principalJet 1 x = (x - π / 2) * sin x := rfl
@[simp] theorem principal_two (x : ℝ) :
    principalJet 2 x = sin x + (x - π / 2) * cos x := rfl
@[simp] theorem principal_three (x : ℝ) :
    principalJet 3 x = 2 * cos x - (x - π / 2) * sin x := rfl
@[simp] theorem principal_four (x : ℝ) :
    principalJet 4 x = -3 * sin x - (x - π / 2) * cos x := rfl

theorem principal_derivative (i : Fin 4) (x : ℝ) :
    HasDerivAt (principalJet i.castSucc) (principalJet i.succ x) x := by
  fin_cases i
  · change HasDerivAt (fun y => sin y + (π / 2 - y) * cos y)
      ((x - π / 2) * sin x) x
    convert (hasDerivAt_sin x).add
      (((hasDerivAt_id x).const_sub (π / 2)).mul (hasDerivAt_cos x)) using 1
    dsimp only [id]
    ring
  · change HasDerivAt (fun y => (y - π / 2) * sin y)
      (sin x + (x - π / 2) * cos x) x
    simpa only [one_mul] using
      (((hasDerivAt_id x).sub_const (π / 2)).mul (hasDerivAt_sin x))
  · change HasDerivAt (fun y => sin y + (y - π / 2) * cos y)
      (2 * cos x - (x - π / 2) * sin x) x
    convert (hasDerivAt_sin x).add
      (((hasDerivAt_id x).sub_const (π / 2)).mul (hasDerivAt_cos x)) using 1
    dsimp only [id]
    ring
  · change HasDerivAt (fun y => 2 * cos y - (y - π / 2) * sin y)
      (-3 * sin x - (x - π / 2) * cos x) x
    convert ((hasDerivAt_cos x).const_mul 2).sub
      (((hasDerivAt_id x).sub_const (π / 2)).mul (hasDerivAt_sin x)) using 1
    dsimp only [id]
    ring

theorem principal_equation (x : ℝ) :
    principalJet 4 x + 2 * principalJet 2 x + principalJet 0 x = 0 := by
  simp only [principal_zero, principal_two, principal_four]
  ring

def principalBranch : Branch :=
  ⟨principalJet, principal_derivative, principal_equation⟩

theorem principal_eq_kernel {x : ℝ} (hx : 0 ≤ x) (hxpi : x ≤ π) :
    principalJet 0 x = CircleMoments.K x := by
  simp only [principal_zero, CircleMoments.K, CircleMoments.arcsin_cos_principal hx hxpi,
    abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hx hxpi)]
  ring

/-- The boundary pairing is exactly the negative source strength. The
continuous jets cancel by periodicity; the one-sided third jets are ±2. -/
theorem principal_boundary (h : Test) :
    concomitant principalJet h.jet π - concomitant principalJet h.jet 0 =
      -4 * h.jet 0 0 := by
  have hp (i : Fin 5) : h.jet i π = h.jet i 0 := by
    simpa using h.periodic i 0
  have hz := Beam.eq_kernel_jet.1
  have hπ := Beam.eq_kernel_jet.2
  change (principalJet 0 0, principalJet 1 0, principalJet 2 0, principalJet 3 0) =
    (π / 2, 0, -π / 2, 2) at hz
  change (principalJet 0 π, principalJet 1 π, principalJet 2 π, principalJet 3 π) =
    (π / 2, 0, -π / 2, -2) at hπ
  simp only [Prod.mk.injEq] at hz hπ
  simp only [concomitant, hp, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2,
    hπ.1, hπ.2.1, hπ.2.2.1, hπ.2.2.2]
  ring

/-- The circle Dirac identity for one kernel, derived by the adjoint FTC. -/
theorem kernel_weak_zero (h : Test) :
    (∫ x in (0 : ℝ)..π, CircleMoments.K x * h.operator x) = 4 * h.jet 0 0 := by
  have H := weak_interval_identity principalBranch.toSmoothJet h.toSmoothJet 0 π
  have ho (x : ℝ) : principalBranch.toSmoothJet.operator x = 0 := principal_equation x
  simp_rw [ho] at H
  change (∫ x in (0 : ℝ)..π, h.jet 0 x * 0 - principalJet 0 x * h.operator x) =
    concomitant principalJet h.jet π - concomitant principalJet h.jet 0 at H
  simp only [mul_zero, zero_sub] at H
  rw [principal_boundary, intervalIntegral.integral_neg] at H
  have heq : (∫ x in (0 : ℝ)..π, principalJet 0 x * h.operator x) =
      ∫ x in (0 : ℝ)..π, CircleMoments.K x * h.operator x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le pi_pos.le] at hx
    change principalJet 0 x * h.operator x = CircleMoments.K x * h.operator x
    rw [principal_eq_kernel hx.1 hx.2]
  rw [heq] at H
  linarith only [H]

theorem kernel_weak (h : Test) (a : ℝ) :
    (∫ x in (0 : ℝ)..π, CircleMoments.K (x - a) * h.operator x) = 4 * h.jet 0 a := by
  have hp : Function.Periodic (fun x => CircleMoments.K (x - a) * h.operator x) π := by
    intro x
    dsimp only [Test.operator]
    rw [show x + π - a = (x - a) + π by ring, CircleMoments.K_periodic (x - a),
      h.periodic 4 x, h.periodic 2 x, h.periodic 0 x]
  calc
    _ = ∫ x in a..a + π, CircleMoments.K (x - a) * h.operator x := by
      simpa using hp.intervalIntegral_add_eq 0 a
    _ = ∫ x in (0 : ℝ)..π, CircleMoments.K x * (h.translate a).operator x := by
      simpa only [zero_add, add_sub_cancel, add_comm π a,
        Test.operator, Test.translate] using
        (intervalIntegral.integral_comp_add_right
          (fun x => CircleMoments.K (x - a) * h.operator x) a (a := 0) (b := π)).symm
    _ = _ := by simpa only [Test.translate, zero_add] using kernel_weak_zero (h.translate a)

theorem continuous_kernel : Continuous CircleMoments.K :=
  (continuous_cos.mul (continuous_arcsin.comp continuous_cos)).add continuous_sin.abs

/-- `eq:LFC`, as equality against all periodic C4 tests. The right-hand side
is the finite signed Dirac action, including coincident student/teacher atoms. -/
theorem eq_LFC {n m : ℕ} (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (h : Test) :
    (∫ x in (0 : ℝ)..π,
      ((∑ i, c i * CircleMoments.K (x - θ i)) - ∑ k, s k * CircleMoments.K (x - β k)) * h.operator x) =
      4 * ((∑ i, c i * h.jet 0 (θ i)) - ∑ k, s k * h.jet 0 (β k)) := by
  have hi (a b : ℝ) : IntervalIntegrable
      (fun x => a * CircleMoments.K (x - b) * h.operator x) volume 0 π :=
    ((continuous_const.mul (continuous_kernel.comp (continuous_id.sub continuous_const))).mul
      h.continuous_operator).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun x => ∑ i, c i * CircleMoments.K (x - θ i) * h.operator x)
      volume 0 π := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hi (c i) (θ i)) using 1
    ext x
    simp only [Finset.sum_apply]
  have hs : IntervalIntegrable (fun x => ∑ k, s k * CircleMoments.K (x - β k) * h.operator x)
      volume 0 π := by
    convert IntervalIntegrable.sum Finset.univ (fun k _ => hi (s k) (β k)) using 1
    ext x
    simp only [Finset.sum_apply]
  simp_rw [sub_mul, Finset.sum_mul]
  rw [intervalIntegral.integral_sub hc hs,
    intervalIntegral.integral_finset_sum (fun i _ => hi (c i) (θ i)),
    intervalIntegral.integral_finset_sum (fun k _ => hi (s k) (β k))]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, kernel_weak]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Literal distributional equation against any periodic C4 test function.
It characterizes the finite signed circle-Dirac action, including collisions. -/
theorem eq_LFC_smooth {n m : ℕ} (c θ : Fin n → ℝ) (s β : Fin m → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ) (hp : Function.Periodic ψ π) :
    (∫ x in (0 : ℝ)..π,
      ((∑ i, c i * CircleMoments.K (x - θ i)) - ∑ k, s k * CircleMoments.K (x - β k)) *
        (iteratedDeriv 4 ψ x + 2 * iteratedDeriv 2 ψ x + ψ x)) =
      4 * ((∑ i, c i * ψ (θ i)) - ∑ k, s k * ψ (β k)) := by
  have H := eq_LFC c θ s β (Test.ofSmooth ψ hψ hp)
  change (∫ x in (0 : ℝ)..π,
    ((∑ i, c i * CircleMoments.K (x - θ i)) - ∑ k, s k * CircleMoments.K (x - β k)) *
      (iteratedDeriv 4 ψ x + 2 * iteratedDeriv 2 ψ x + iteratedDeriv 0 ψ x)) =
    4 * ((∑ i, c i * iteratedDeriv 0 ψ (θ i)) -
      ∑ k, s k * iteratedDeriv 0 ψ (β k)) at H
  simpa only [iteratedDeriv_zero] using H

end PaperLeanFormalization.WeakBeamEquation




namespace PaperLeanFormalization.BeamGapKernel

def kernel (x : ℝ) : ℝ := cos x * arcsin (cos x) + sqrt (1 - cos x ^ 2)
def branch (x : ℝ) : ℝ := sin x + (π / 2 - x) * cos x
def psi (x : ℝ) : ℝ := sin x - x * cos x
def chi (x : ℝ) : ℝ := x * sin x
def branchD1 (x : ℝ) : ℝ := (x - π / 2) * sin x

theorem kernel_eq_branch {x : ℝ} (h0 : 0 ≤ x) (hpi : x ≤ π) :
    kernel x = branch x := by
  have hsq : sqrt (1 - cos x ^ 2) = sin x := by
    rw [show 1 - cos x ^ 2 = sin x ^ 2 by nlinarith only [sin_sq_add_cos_sq x],
      sqrt_sq (sin_nonneg_of_nonneg_of_le_pi h0 hpi)]
  unfold kernel branch
  rw [arcsin_eq_pi_div_two_sub_arccos, arccos_cos h0 hpi, hsq]
  ring

theorem kernel_add_pi (x : ℝ) : kernel (x + π) = kernel x := by
  simp only [kernel, cos_add_pi, arcsin_neg, neg_mul_neg, neg_sq]

theorem kernel_even (x : ℝ) : kernel (-x) = kernel x := by
  simp only [kernel, cos_neg]

theorem branch_crossing (x : ℝ) : branch x - branch (x + π) = 2 * psi x := by
  change Beam.branch x - Beam.branch (x + π) = 2 * Beam.psi x
  have hzero := Beam.branch_shift x 0
  have hpi := Beam.branch_shift x π
  have hz := Beam.eq_kernel_jet.1
  have hπ := Beam.eq_kernel_jet.2
  simp only [Prod.mk.injEq] at hz hπ
  simp only [add_zero, hz.1, hz.2.1, cos_zero, sin_zero, one_mul, zero_mul, zero_add,
    add_zero] at hzero
  simp only [hπ.1, hπ.2.1, cos_pi, sin_pi, neg_one_mul, zero_mul, add_zero] at hpi
  linarith only [hzero, hpi]

theorem branch_shift (x z : ℝ) :
    branch (x + z) = branch z * cos x + branchD1 z * sin x +
      cos z * psi x + sin z * chi x := by
  dsimp [branch, branchD1, psi, chi]
  rw [sin_add, cos_add]
  ring

/-- At the left endpoint, atoms at zero use the right branch; all other atoms
are continued smoothly from their left branch. -/
def offset (t : ℝ) : ℝ := if t = 0 then 0 else π - t

theorem kernel_gap_branch {x t : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ π)
    (ht0 : 0 ≤ t) (htpi : t ≤ π) :
    kernel (x - t) = branch (x + offset t) +
      if 0 < t ∧ t ≤ x then 2 * psi (x - t) else 0 := by
  by_cases ht : t = 0
  · subst t
    simp only [offset, if_pos rfl, if_true, sub_zero, add_zero, lt_irrefl, false_and, if_false]
    exact kernel_eq_branch hx0 hxpi
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  simp only [offset, if_neg ht, htpos, true_and]
  by_cases htx : t ≤ x
  · rw [if_pos htx, kernel_eq_branch (sub_nonneg.mpr htx) (by linarith)]
    have h := branch_crossing (x - t)
    rw [show x - t + π = x + (π - t) by ring] at h
    linarith only [h]
  · rw [if_neg htx]
    have heq : x - t + π = x + (π - t) := by ring
    rw [← kernel_add_pi (x - t), kernel_eq_branch (by linarith) (by linarith), heq]
    ring

/-- A positive-length gap with no student in its interior has no student
forcing; an atom exactly at the right endpoint contributes `psi 0 = 0`. -/
theorem student_gap_branch {l x t : ℝ} (hx0 : 0 ≤ x) (hxl : x ≤ l)
    (hlpi : l ≤ π) (ht : t = 0 ∨ l ≤ t) (ht0 : 0 ≤ t) (htpi : t ≤ π) :
    kernel (x - t) = branch (x + offset t) := by
  rw [kernel_gap_branch hx0 (hxl.trans hlpi) ht0 htpi]
  by_cases hcross : 0 < t ∧ t ≤ x
  · rw [if_pos hcross]
    have htx : x = t := by rcases ht with h | h <;> linarith
    rw [htx, sub_self]
    simp [psi]
  · rw [if_neg hcross, add_zero]

def residual {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * kernel (x - theta i) - ∑ k, s k * kernel (x - beta k)

def smoothResidual {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * branch (x + offset (theta i)) -
    ∑ k, s k * branch (x + offset (beta k))

/-- The actual finite kernel residual, on any clean local gap, is its smooth
left continuation minus the teacher forcing. This is the missing analytic
bridge before the clamped two by two solve. -/
theorem residual_gap_causal {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {l x : ℝ} (hx0 : 0 ≤ x) (hxl : x ≤ l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π) :
    residual c theta s beta x = smoothResidual c theta s beta x -
      2 * ∑ k, s k * (if 0 < beta k ∧ beta k ≤ x then psi (x - beta k) else 0) := by
  unfold residual smoothResidual
  have hstudent : (∑ i, c i * kernel (x - theta i)) =
      ∑ i, c i * branch (x + offset (theta i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [student_gap_branch hx0 hxl hlpi (hgap i) (htheta i).1 (htheta i).2]
  rw [hstudent]
  have hteacher : (∑ k, s k * kernel (x - beta k)) =
      (∑ k, s k * branch (x + offset (beta k))) +
        2 * ∑ k, s k * (if 0 < beta k ∧ beta k ≤ x then psi (x - beta k) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [kernel_gap_branch hx0 (hxl.trans hlpi) (hbeta k).1 (hbeta k).2]
    split_ifs <;> ring
  rw [hteacher]
  ring

def torque (x : ℝ) : ℝ := -sin x * arcsin (cos x)

theorem torque_eq_branch {x : ℝ} (h0 : 0 ≤ x) (hpi : x ≤ π) :
    torque x = branchD1 x := by
  unfold torque branchD1
  rw [arcsin_eq_pi_div_two_sub_arccos, arccos_cos h0 hpi]
  ring

theorem torque_add_pi (x : ℝ) : torque (x + π) = torque x := by
  simp only [torque, sin_add_pi, cos_add_pi, arcsin_neg, neg_neg, mul_neg]
  ring

theorem branchD1_crossing (x : ℝ) : branchD1 x - branchD1 (x + π) = 2 * chi x := by
  simp only [branchD1, chi, sin_add_pi]
  ring

theorem branchD1_shift (x z : ℝ) :
    branchD1 (x + z) = -branch z * sin x + branchD1 z * cos x +
      cos z * chi x + sin z * (sin x + x * cos x) := by
  dsimp [branch, branchD1, psi, chi]
  rw [sin_add]
  ring

theorem torque_gap_branch {x t : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ π)
    (ht0 : 0 ≤ t) (htpi : t ≤ π) :
    torque (x - t) = branchD1 (x + offset t) +
      if 0 < t ∧ t ≤ x then 2 * chi (x - t) else 0 := by
  by_cases ht : t = 0
  · subst t
    simp only [offset, if_pos rfl, if_true, sub_zero, add_zero, lt_irrefl, false_and, if_false]
    exact torque_eq_branch hx0 hxpi
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  simp only [offset, if_neg ht, htpos, true_and]
  by_cases htx : t ≤ x
  · rw [if_pos htx, torque_eq_branch (sub_nonneg.mpr htx) (by linarith)]
    have h := branchD1_crossing (x - t)
    rw [show x - t + π = x + (π - t) by ring] at h
    linarith only [h]
  · rw [if_neg htx]
    have heq : x - t + π = x + (π - t) := by ring
    rw [← torque_add_pi (x - t), torque_eq_branch (by linarith) (by linarith), heq]
    ring

theorem student_gap_torque {l x t : ℝ} (hx0 : 0 ≤ x) (hxl : x ≤ l)
    (hlpi : l ≤ π) (ht : t = 0 ∨ l ≤ t) (ht0 : 0 ≤ t) (htpi : t ≤ π) :
    torque (x - t) = branchD1 (x + offset t) := by
  rw [torque_gap_branch hx0 (hxl.trans hlpi) ht0 htpi]
  by_cases hcross : 0 < t ∧ t ≤ x
  · rw [if_pos hcross]
    have htx : x = t := by rcases ht with h | h <;> linarith
    rw [htx, sub_self]
    simp [chi]
  · rw [if_neg hcross, add_zero]

def residualTorque {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * torque (x - theta i) - ∑ k, s k * torque (x - beta k)

def smoothSlope {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * branchD1 (x + offset (theta i)) -
    ∑ k, s k * branchD1 (x + offset (beta k))

theorem residual_torque_gap_causal {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {l x : ℝ} (hx0 : 0 ≤ x) (hxl : x ≤ l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π) :
    residualTorque c theta s beta x = smoothSlope c theta s beta x -
      2 * ∑ k, s k * (if 0 < beta k ∧ beta k ≤ x then chi (x - beta k) else 0) := by
  unfold residualTorque smoothSlope
  have hstudent : (∑ i, c i * torque (x - theta i)) =
      ∑ i, c i * branchD1 (x + offset (theta i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [student_gap_torque hx0 hxl hlpi (hgap i) (htheta i).1 (htheta i).2]
  rw [hstudent]
  have hteacher : (∑ k, s k * torque (x - beta k)) =
      (∑ k, s k * branchD1 (x + offset (beta k))) +
        2 * ∑ k, s k * (if 0 < beta k ∧ beta k ≤ x then chi (x - beta k) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [torque_gap_branch hx0 (hxl.trans hlpi) (hbeta k).1 (hbeta k).2]
    split_ifs <;> ring
  rw [hteacher]
  ring

def gapU {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) : ℝ :=
  (∑ i, c i * cos (offset (theta i))) - ∑ k, s k * cos (offset (beta k))
def gapV {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) : ℝ :=
  (∑ i, c i * sin (offset (theta i))) - ∑ k, s k * sin (offset (beta k))

theorem smoothResidual_expansion {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (x : ℝ) :
    smoothResidual c theta s beta x =
      smoothResidual c theta s beta 0 * cos x + smoothSlope c theta s beta 0 * sin x +
        gapU c theta s beta * psi x + gapV c theta s beta * chi x := by
  unfold smoothResidual smoothSlope gapU gapV
  simp only [zero_add, branch_shift, mul_add, Finset.sum_add_distrib,
    sub_mul, Finset.sum_mul, mul_assoc]
  ring

theorem smoothSlope_expansion {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (x : ℝ) :
    smoothSlope c theta s beta x =
      -smoothResidual c theta s beta 0 * sin x + smoothSlope c theta s beta 0 * cos x +
        gapU c theta s beta * chi x + gapV c theta s beta * (sin x + x * cos x) := by
  unfold smoothResidual smoothSlope gapU gapV
  simp only [zero_add, branchD1_shift, mul_add, Finset.sum_add_distrib,
    sub_mul, Finset.sum_mul, mul_assoc, mul_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Truncate any causal source to the open gap. The endpoint source vanishes,
so no generic-position assumption is smuggled into the finite sum. -/
theorem causal_sum_eq_gap_sum {m : ℕ} (s beta : Fin m → ℝ) (f : ℝ → ℝ)
    (hf : f 0 = 0) {l x : ℝ} (hxl : x ≤ l) :
    (∑ k, s k * (if 0 < beta k ∧ beta k ≤ x then f (x - beta k) else 0)) =
      ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
        s k * (if beta k ≤ x then f (x - beta k) else 0) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hpos : 0 < beta k
  · by_cases hinside : beta k < l
    · simp only [hpos, hinside, true_and, if_true]
    · by_cases hbefore : beta k ≤ x
      · have hxeq : x = beta k := by linarith
        simp [hpos, hinside, hbefore, hxeq, hf]
      · simp [hpos, hinside, hbefore]
  · simp [hpos]

/-- Actual double zeros of the finite residual supply exactly the clamped
equations used in the Green sign and beam endpoint calculations. -/
theorem critical_gap_clamps {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {l : ℝ} (hl0 : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π)
    (hzero : residual c theta s beta 0 = 0)
    (hslopeZero : residualTorque c theta s beta 0 = 0)
    (hend : residual c theta s beta l = 0)
    (hslopeEnd : residualTorque c theta s beta l = 0) :
    (gapU c theta s beta * psi l + gapV c theta s beta * chi l =
      2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
        s k * psi (l - beta k)) ∧
    (gapU c theta s beta * chi l + gapV c theta s beta * (sin l + l * cos l) =
      2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
        s k * chi (l - beta k)) ∧
    ∀ x, 0 ≤ x → x ≤ l →
      residual c theta s beta x = gapU c theta s beta * psi x + gapV c theta s beta * chi x -
        2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          s k * (if beta k ≤ x then psi (x - beta k) else 0) := by
  classical
  have hbefore : ∀ k, ¬(0 < beta k ∧ beta k ≤ 0) := fun k h => (not_lt_of_ge h.2) h.1
  have hval0 := residual_gap_causal c theta s beta (show 0 ≤ (0 : ℝ) by rfl)
    hl0.le hlpi htheta hgap hbeta
  simp only [if_neg (hbefore _), mul_zero, Finset.sum_const_zero, sub_zero] at hval0
  have hsmooth0 : smoothResidual c theta s beta 0 = 0 := hval0.symm.trans hzero
  have htor0 := residual_torque_gap_causal c theta s beta (show 0 ≤ (0 : ℝ) by rfl)
    hl0.le hlpi htheta hgap hbeta
  simp only [if_neg (hbefore _), mul_zero, Finset.sum_const_zero, sub_zero] at htor0
  have hsmooth1 : smoothSlope c theta s beta 0 = 0 := htor0.symm.trans hslopeZero
  have hvalue : ∀ x, 0 ≤ x → x ≤ l →
      residual c theta s beta x = gapU c theta s beta * psi x + gapV c theta s beta * chi x -
        2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          s k * (if beta k ≤ x then psi (x - beta k) else 0) := by
    intro x hx0 hxl
    rw [residual_gap_causal c theta s beta hx0 hxl hlpi htheta hgap hbeta,
      smoothResidual_expansion, hsmooth0, hsmooth1,
      causal_sum_eq_gap_sum s beta psi (by simp [psi]) hxl]
    ring
  have hslope := residual_torque_gap_causal c theta s beta hl0.le le_rfl hlpi htheta hgap hbeta
  rw [smoothSlope_expansion, hsmooth0, hsmooth1,
    causal_sum_eq_gap_sum s beta chi (by simp [chi]) le_rfl] at hslope
  have hsum (f : ℝ → ℝ) :
      (∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
        s k * (if beta k ≤ l then f (l - beta k) else 0)) =
      ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l), s k * f (l - beta k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [if_pos ((Finset.mem_filter.mp hk).2.2.le)]
  refine ⟨?_, ?_, hvalue⟩
  · have hv := hvalue l hl0.le le_rfl
    rw [hsum, hend] at hv
    linarith only [hv]
  · rw [hsum, hslopeEnd] at hslope
    linarith only [hslope]

def branchD2 (x : ℝ) : ℝ := sin x + (x - π / 2) * cos x
def branchD3 (x : ℝ) : ℝ := 2 * cos x - (x - π / 2) * sin x
def psiD2 (x : ℝ) : ℝ := sin x + x * cos x
def psiD3 (x : ℝ) : ℝ := 2 * cos x - x * sin x
def chiD3 (x : ℝ) : ℝ := -3 * sin x - x * cos x

theorem branchD2_shift (x z : ℝ) :
    branchD2 (x + z) = -branch z * cos x - branchD1 z * sin x +
      cos z * psiD2 x + sin z * psiD3 x := by
  simp only [branchD2, branch, branchD1, psiD2, psiD3, sin_add, cos_add]
  ring

theorem branchD3_shift (x z : ℝ) :
    branchD3 (x + z) = branch z * sin x - branchD1 z * cos x +
      cos z * psiD3 x + sin z * chiD3 x := by
  simp only [branchD3, branch, branchD1, psiD3, chiD3, sin_add, cos_add]
  ring

theorem branchD2_crossing (x : ℝ) :
    branchD2 x - branchD2 (x + π) = 2 * psiD2 x := by
  simp only [branchD2, psiD2, sin_add_pi, cos_add_pi]
  ring

theorem branchD3_crossing (x : ℝ) :
    branchD3 x - branchD3 (x + π) = 2 * psiD3 x := by
  simp only [branchD3, psiD3, sin_add_pi, cos_add_pi]
  ring

def curvature (x : ℝ) : ℝ := 2 * |sin x| - kernel x

theorem curvature_eq_branch {x : ℝ} (h0 : 0 ≤ x) (hpi : x ≤ π) :
    curvature x = branchD2 x := by
  unfold curvature
  rw [kernel_eq_branch h0 hpi, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h0 hpi)]
  unfold branch branchD2
  ring

theorem curvature_add_pi (x : ℝ) : curvature (x + π) = curvature x := by
  simp only [curvature, sin_add_pi, abs_neg, kernel_add_pi]

theorem curvature_gap_branch {x t : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ π)
    (ht0 : 0 ≤ t) (htpi : t ≤ π) :
    curvature (x - t) = branchD2 (x + offset t) +
      if 0 < t ∧ t ≤ x then 2 * psiD2 (x - t) else 0 := by
  by_cases ht : t = 0
  · subst t
    simp only [offset, if_pos rfl, if_true, sub_zero, add_zero, lt_irrefl, false_and, if_false]
    exact curvature_eq_branch hx0 hxpi
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
  simp only [offset, if_neg ht, htpos, true_and]
  by_cases htx : t ≤ x
  · rw [if_pos htx, curvature_eq_branch (sub_nonneg.mpr htx) (by linarith)]
    have h := branchD2_crossing (x - t)
    rw [show x - t + π = x + (π - t) by ring] at h
    linarith only [h]
  · rw [if_neg htx]
    have heq : x - t + π = x + (π - t) := by ring
    rw [← curvature_add_pi (x - t), curvature_eq_branch (by linarith) (by linarith), heq]
    ring

def cutJerkRight (a t : ℝ) : ℝ := branchD3 (if t ≤ a then a - t else a - t + π)
def cutJerkLeft (a t : ℝ) : ℝ := branchD3 (if t < a then a - t else a - t + π)

theorem right_jerk_at_zero {t : ℝ} (ht0 : 0 ≤ t) :
    cutJerkRight 0 t = branchD3 (offset t) := by
  by_cases ht : t = 0
  · subst t; simp [cutJerkRight, offset]
  · have hp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    simp only [cutJerkRight, offset, if_neg (not_le.mpr hp), if_neg ht]
    congr 1
    ring

theorem left_jerk_at_endpoint {l t : ℝ} (hl : 0 < l) (ht0 : 0 ≤ t) :
    cutJerkLeft l t = branchD3 (l + offset t) +
      if 0 < t ∧ t < l then 2 * psiD3 (l - t) else 0 := by
  by_cases ht : t = 0
  · subst t
    simp [cutJerkLeft, offset, hl]
  · have hp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    simp only [cutJerkLeft, offset, if_neg ht, hp, true_and]
    by_cases htl : t < l
    · rw [if_pos htl, if_pos htl]
      have h := branchD3_crossing (l - t)
      rw [show l - t + π = l + (π - t) by ring] at h
      linarith only [h]
    · rw [if_neg htl, if_neg htl, add_zero]
      congr 1
      ring

def smoothCurvature {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * branchD2 (x + offset (theta i)) -
    ∑ k, s k * branchD2 (x + offset (beta k))
def smoothJerk {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * branchD3 (x + offset (theta i)) -
    ∑ k, s k * branchD3 (x + offset (beta k))

theorem smoothCurvature_expansion {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (x : ℝ) :
    smoothCurvature c theta s beta x =
      -smoothResidual c theta s beta 0 * cos x - smoothSlope c theta s beta 0 * sin x +
        gapU c theta s beta * psiD2 x + gapV c theta s beta * psiD3 x := by
  unfold smoothCurvature smoothResidual smoothSlope gapU gapV
  simp only [zero_add, branchD2_shift, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sub_mul, Finset.sum_mul, mul_assoc, mul_neg, neg_mul,
    Finset.sum_neg_distrib]
  ring

theorem smoothJerk_expansion {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (x : ℝ) :
    smoothJerk c theta s beta x =
      smoothResidual c theta s beta 0 * sin x - smoothSlope c theta s beta 0 * cos x +
        gapU c theta s beta * psiD3 x + gapV c theta s beta * chiD3 x := by
  unfold smoothJerk smoothResidual smoothSlope gapU gapV
  simp only [zero_add, branchD3_shift, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sub_mul, Finset.sum_mul, mul_assoc]
  ring

theorem actual_right_jerk_zero {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (htheta : ∀ i, 0 ≤ theta i) (hbeta : ∀ k, 0 ≤ beta k) :
    (∑ i, c i * cutJerkRight 0 (theta i)) - (∑ k, s k * cutJerkRight 0 (beta k)) =
      smoothJerk c theta s beta 0 := by
  simp only [right_jerk_at_zero (htheta _), right_jerk_at_zero (hbeta _),
    smoothJerk, zero_add]

theorem actual_left_jerk_endpoint {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {l : ℝ} (hl : 0 < l) (htheta : ∀ i, 0 ≤ theta i)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i) (hbeta : ∀ k, 0 ≤ beta k) :
    (∑ i, c i * cutJerkLeft l (theta i)) - (∑ k, s k * cutJerkLeft l (beta k)) =
      smoothJerk c theta s beta l -
        2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          s k * psiD3 (l - beta k) := by
  classical
  have hstudent : ∀ i, cutJerkLeft l (theta i) = branchD3 (l + offset (theta i)) := by
    intro i
    rw [left_jerk_at_endpoint hl (htheta i)]
    have hn : ¬(0 < theta i ∧ theta i < l) := by
      rcases hgap i with h | h <;> rintro ⟨ha, hb⟩ <;> linarith
    rw [if_neg hn, add_zero]
  have hteacher : (∑ k, s k * cutJerkLeft l (beta k)) =
      (∑ k, s k * branchD3 (l + offset (beta k))) +
        2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          s k * psiD3 (l - beta k) := by
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [left_jerk_at_endpoint hl (hbeta k)]
    split_ifs <;> ring
  simp only [hstudent, hteacher, smoothJerk]
  ring

theorem actual_curvature_gap {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {l x : ℝ} (hx0 : 0 ≤ x) (hxl : x ≤ l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π) :
    ((∑ i, c i * curvature (x - theta i)) - ∑ k, s k * curvature (x - beta k)) =
      smoothCurvature c theta s beta x -
        2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          s k * (if beta k ≤ x then psiD2 (x - beta k) else 0) := by
  classical
  have hstudent : ∀ i, curvature (x - theta i) = branchD2 (x + offset (theta i)) := by
    intro i
    rw [curvature_gap_branch hx0 (hxl.trans hlpi) (htheta i).1 (htheta i).2]
    by_cases hcross : 0 < theta i ∧ theta i ≤ x
    · rw [if_pos hcross]
      have hxeq : x = theta i := by rcases hgap i with h | h <;> linarith
      rw [hxeq, sub_self]
      simp [psiD2]
    · rw [if_neg hcross, add_zero]
  have hteacher : (∑ k, s k * curvature (x - beta k)) =
      (∑ k, s k * branchD2 (x + offset (beta k))) +
        2 * ∑ k, s k * (if 0 < beta k ∧ beta k ≤ x then psiD2 (x - beta k) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [curvature_gap_branch hx0 (hxl.trans hlpi) (hbeta k).1 (hbeta k).2]
    split_ifs <;> ring
  rw [hteacher, causal_sum_eq_gap_sum s beta psiD2 (by simp [psiD2]) hxl]
  simp only [hstudent, smoothCurvature]
  ring

/-- The actual initial curvature and right-hand jerk are the two solved
coefficients. These are literal finite kernel sums, not an assumed Green model. -/
theorem critical_gap_initial_jets {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {l : ℝ} (hl0 : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π)
    (hzero : residual c theta s beta 0 = 0)
    (hslopeZero : residualTorque c theta s beta 0 = 0) :
    ((∑ i, c i * curvature (-theta i)) - ∑ k, s k * curvature (-beta k)) =
        2 * gapV c theta s beta ∧
      ((∑ i, c i * cutJerkRight 0 (theta i)) - ∑ k, s k * cutJerkRight 0 (beta k)) =
        2 * gapU c theta s beta := by
  classical
  have hbefore : ∀ k, ¬(0 < beta k ∧ beta k ≤ 0) := fun k h => (not_lt_of_ge h.2) h.1
  have hval0 := residual_gap_causal c theta s beta (show 0 ≤ (0 : ℝ) by rfl)
    hl0.le hlpi htheta hgap hbeta
  simp only [if_neg (hbefore _), mul_zero, Finset.sum_const_zero, sub_zero] at hval0
  have hsmooth0 : smoothResidual c theta s beta 0 = 0 := hval0.symm.trans hzero
  have htor0 := residual_torque_gap_causal c theta s beta (show 0 ≤ (0 : ℝ) by rfl)
    hl0.le hlpi htheta hgap hbeta
  simp only [if_neg (hbefore _), mul_zero, Finset.sum_const_zero, sub_zero] at htor0
  have hsmooth1 : smoothSlope c theta s beta 0 = 0 := htor0.symm.trans hslopeZero
  constructor
  · have hcurv := actual_curvature_gap c theta s beta (show 0 ≤ (0 : ℝ) by rfl)
      hl0.le hlpi htheta hgap hbeta
    have hsum : (∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
        s k * (if beta k ≤ 0 then psiD2 (0 - beta k) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (not_le.mpr (Finset.mem_filter.mp hk).2.1), mul_zero]
    rw [hsum, smoothCurvature_expansion, hsmooth0, hsmooth1] at hcurv
    simpa [psiD2, psiD3, mul_comm] using hcurv
  · rw [actual_right_jerk_zero c theta s beta (fun i => (htheta i).1) (fun k => (hbeta k).1),
      smoothJerk_expansion, hsmooth0, hsmooth1]
    simp [psiD3, chiD3, mul_comm]

/-- The last-to-first student jump is the same jump as at every other cut. -/
theorem cut_jerk_wrap_jump {a t : ℝ} (ht0 : a ≤ t) (htpi : t < a + π) :
    cutJerkRight a t - cutJerkLeft (a + π) t = if t = a then 4 else 0 := by
  by_cases ht : t = a
  · subst t
    have hpi : a < a + π := by linarith only [pi_pos]
    simp only [cutJerkRight, cutJerkLeft, if_pos le_rfl, if_pos hpi, if_pos rfl, sub_self]
    rw [show a + π - a = π by ring]
    norm_num [branchD3]
  · have hp : a < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    simp only [cutJerkRight, cutJerkLeft, if_neg (not_le.mpr hp), if_pos htpi, if_neg ht]
    rw [show a + π - t = a - t + π by ring, sub_self]

theorem residual_jerk_wrap_jump {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c theta : ι → ℝ) (s beta : κ → ℝ) (hinj : Function.Injective theta)
    (i : ι) (htheta : ∀ j, theta i ≤ theta j ∧ theta j < theta i + π)
    (hbeta : ∀ k, theta i ≤ beta k ∧ beta k < theta i + π)
    (hsep : ∀ k, beta k ≠ theta i) :
    ((∑ j, c j * cutJerkRight (theta i) (theta j)) -
      ∑ k, s k * cutJerkRight (theta i) (beta k)) -
    ((∑ j, c j * cutJerkLeft (theta i + π) (theta j)) -
      ∑ k, s k * cutJerkLeft (theta i + π) (beta k)) = 4 * c i := by
  classical
  have hs : (∑ j, c j * (cutJerkRight (theta i) (theta j) -
      cutJerkLeft (theta i + π) (theta j))) = 4 * c i := by
    simp only [cut_jerk_wrap_jump (htheta _).1 (htheta _).2, hinj.eq_iff, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp [mul_comm]
  have ht : (∑ k, s k * (cutJerkRight (theta i) (beta k) -
      cutJerkLeft (theta i + π) (beta k))) = 0 := by
    simp only [cut_jerk_wrap_jump (hbeta _).1 (hbeta _).2, if_neg (hsep _),
      mul_zero, Finset.sum_const_zero]
  simp only [mul_sub, Finset.sum_sub_distrib] at hs ht
  linarith only [hs, ht]

end PaperLeanFormalization.BeamGapKernel


/-! Direct positivity of the clamped `(D²+1)²` Green function.
The proof uses just one decreasing ratio and one diagonal identity. -/

noncomputable section
open Real Set
open scoped BigOperators

namespace PaperLeanFormalization.Planar.Gaps

def psi (x : ℝ) : ℝ := sin x - x * cos x
def chi (x : ℝ) : ℝ := x * sin x
def det (x : ℝ) : ℝ := x ^ 2 - sin x ^ 2
def area (x : ℝ) : ℝ := x - sin x * cos x
def moment (l p : ℝ) : ℝ := psi l * chi (l - p) - psi (l - p) * chi l
def jerk (l p : ℝ) : ℝ :=
  chi l * chi (l - p) - psi (l - p) * (sin l + l * cos l)
def numerator (l p x : ℝ) : ℝ := moment l p * chi x - jerk l p * psi x
def green (l p x : ℝ) : ℝ :=
  if x ≤ p then numerator l p x / (2 * det l)
  else numerator l x p / (2 * det l)

/-- `eq:green-M0`, the source-to-left curvature numerator. -/
theorem eq_green_M0 (l p : ℝ) :
    moment l p = psi l * chi (l - p) - psi (l - p) * chi l := rfl

/-- `eq:green-A`, the source-to-left jerk numerator. -/
theorem eq_green_A (l p : ℝ) :
    jerk l p = chi l * chi (l - p) - psi (l - p) * (sin l + l * cos l) := rfl

/-- `eq:green-determinant`, the nonvanishing clamped matrix determinant. -/
theorem eq_green_determinant (l : ℝ) :
    psi l * (sin l + l * cos l) - chi l ^ 2 = -det l := by
  dsimp [psi, chi, det]
  nlinarith only [sin_sq_add_cos_sq l]

theorem psi_derivative (x : ℝ) : HasDerivAt psi (chi x) x := by
  convert (hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (hasDerivAt_cos x)) using 1;
    dsimp [psi, chi]; ring

theorem chi_derivative (x : ℝ) :
    HasDerivAt chi (sin x + x * cos x) x := by
  convert (hasDerivAt_id x).mul (hasDerivAt_sin x) using 1;
    dsimp [chi]; ring

theorem psi_positive {x : ℝ} (hx : 0 < x) (hxpi : x ≤ π) : 0 < psi x := by
  have hm : StrictMonoOn psi (Icc 0 x) := by
    apply (convex_Icc (0 : ℝ) x).strictMonoOn_of_deriv_pos
    · exact fun t _ => (psi_derivative t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(psi_derivative t).deriv]
      exact mul_pos ht.1 (sin_pos_of_pos_of_lt_pi ht.1 (lt_of_lt_of_le ht.2 hxpi))
  have h := hm ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx
  simpa [psi] using h

theorem det_positive {x : ℝ} (hx : 0 < x) (hxpi : x ≤ π) : 0 < det x := by
  have hs := sin_lt hx
  have hs0 := sin_nonneg_of_nonneg_of_le_pi hx.le hxpi
  dsimp [det]
  nlinarith

theorem area_positive {x : ℝ} (hx : 0 < x) (hxpi : x ≤ π) : 0 < area x := by
  have hs0 := sin_nonneg_of_nonneg_of_le_pi hx.le hxpi
  have hb := mul_le_mul_of_nonneg_left (cos_le_one x) hs0
  dsimp [area]
  linarith [sin_lt hx]

/-- `eq:green-ratio-derivative`: the quotient-rule expression and its
strictly negative determinant form, including the endpoint `x = π`. -/
theorem eq_green_ratio_derivative {x : ℝ} (hx : 0 < x) (hxpi : x ≤ π) :
    HasDerivAt (fun y => chi y / psi y) (-det x / psi x ^ 2) x ∧
      deriv (fun y => chi y / psi y) x =
        (deriv chi x * psi x - chi x ^ 2) / psi x ^ 2 ∧
      (deriv chi x * psi x - chi x ^ 2) / psi x ^ 2 = -det x / psi x ^ 2 ∧
      -det x / psi x ^ 2 < 0 := by
  have hnum : deriv chi x * psi x - chi x ^ 2 = -det x := by
    rw [(chi_derivative x).deriv]
    nlinarith only [eq_green_determinant x]
  have hd : HasDerivAt (fun y => chi y / psi y) (-det x / psi x ^ 2) x := by
    convert (chi_derivative x).div (psi_derivative x)
      (ne_of_gt (psi_positive hx hxpi)) using 1
    congr 1
    dsimp [chi, psi, det]
    nlinarith [sin_sq_add_cos_sq x]
  exact ⟨hd, by rw [hd.deriv, hnum], by rw [hnum],
    div_neg_of_neg_of_pos (neg_neg_of_pos (det_positive hx hxpi))
      (pow_pos (psi_positive hx hxpi) 2)⟩

/-- The only monotonicity argument needed for both the interior and endpoint signs. -/
theorem ratio_strictAnti : StrictAntiOn (fun x => chi x / psi x) (Ioc 0 π) := by
  apply (convex_Ioc (0 : ℝ) π).strictAntiOn_of_deriv_neg
  · exact fun x hx => (eq_green_ratio_derivative hx.1 hx.2).1.continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have hd := eq_green_ratio_derivative hx.1 hx.2.le
    rw [hd.1.deriv]
    exact hd.2.2.2

/-- The source-to-left-end curvature coefficient is strictly positive. -/
theorem moment_positive {l p : ℝ} (hp : 0 < p) (hpl : p < l) (hlpi : l ≤ π) :
    0 < moment l p := by
  have hr : 0 < l - p := sub_pos.mpr hpl
  have hl : 0 < l := lt_trans hp hpl
  have hrpi : l - p ≤ π := by linarith
  have hh := ratio_strictAnti ⟨hr, hrpi⟩ ⟨hl, hlpi⟩ (by linarith : l - p < l)
  have h := (div_lt_div_iff (psi_positive hl hlpi) (psi_positive hr hrpi)).mp hh
  dsimp [moment]
  nlinarith only [h]

/-- At the diagonal the Green numerator is a sum of two positive products. -/
theorem diagonal_identity (p r : ℝ) :
    numerator (p + r) p p = det p * area r + det r * area p := by
  dsimp [numerator, moment, jerk, chi, psi, det, area]
  rw [show p + r - p = r by ring, sin_add, cos_add]
  linear_combination
    (p * (cos r ^ 2 * p * r + cos r ^ 2 * r ^ 2 - cos r * p * sin r +
      p * r * sin r ^ 2 + r ^ 2 * sin r ^ 2 - sin r ^ 2)) * sin_sq_add_cos_sq p +
    (r * (-cos p * r * sin p + p ^ 2 + p * r - sin p ^ 2)) * sin_sq_add_cos_sq r

theorem diagonal_positive {l p : ℝ} (hp : 0 < p) (hpl : p < l) (hlpi : l ≤ π) :
    0 < numerator l p p := by
  have hr : 0 < l - p := sub_pos.mpr hpl
  have hppi : p ≤ π := le_trans hpl.le hlpi
  have hrpi : l - p ≤ π := by linarith
  rw [show l = p + (l - p) by ring, diagonal_identity]
  convert add_pos (mul_pos (det_positive hp hppi) (area_positive hr hrpi))
    (mul_pos (det_positive hr hrpi) (area_positive hp hppi)) using 1

/-- `eq:green-numerator-ratio`: decreasing `chi/psi` carries strict
diagonal positivity to every earlier point of the left branch. -/
theorem eq_green_numerator_ratio {l p x : ℝ} (hx : 0 < x) (hxp : x ≤ p)
    (hpl : p < l) (hlpi : l ≤ π) :
    numerator l p x / psi x = moment l p * (chi x / psi x) - jerk l p ∧
      moment l p * (chi p / psi p) - jerk l p ≤
        moment l p * (chi x / psi x) - jerk l p ∧
      moment l p * (chi p / psi p) - jerk l p = numerator l p p / psi p ∧
      0 < numerator l p p / psi p := by
  have hp : 0 < p := lt_of_lt_of_le hx hxp
  have hppi : p ≤ π := le_trans hpl.le hlpi
  have hxpi : x ≤ π := le_trans hxp hppi
  have hratio := ratio_strictAnti.antitoneOn ⟨hx, hxpi⟩ ⟨hp, hppi⟩ hxp
  have heq (z : ℝ) (hz : psi z ≠ 0) :
      numerator l p z / psi z = moment l p * (chi z / psi z) - jerk l p := by
    dsimp only [numerator]
    field_simp
    ring
  exact ⟨heq x (psi_positive hx hxpi).ne',
    sub_le_sub_right (mul_le_mul_of_nonneg_left hratio (moment_positive hp hpl hlpi).le) _,
    (heq p (psi_positive hp hppi).ne').symm,
    div_pos (diagonal_positive hp hpl hlpi) (psi_positive hp hppi)⟩

/-- Divide by the positive `psi`: decreasing `chi/psi` transfers the diagonal
sign to every earlier point, without estimating the jerk coefficient. -/
theorem numerator_positive {l p x : ℝ} (hx : 0 < x) (hxp : x ≤ p)
    (hpl : p < l) (hlpi : l ≤ π) : 0 < numerator l p x := by
  have h := eq_green_numerator_ratio hx hxp hpl hlpi
  have hpos : 0 < numerator l p x / psi x := by
    rw [h.1]
    exact lt_of_lt_of_le (by rw [h.2.2.1]; exact h.2.2.2) h.2.1
  have hpsi := psi_positive hx (le_trans hxp (le_trans hpl.le hlpi))
  simpa only [div_mul_cancel _ hpsi.ne'] using mul_pos hpos hpsi

theorem green_positive {l p x : ℝ} (hx : 0 < x) (hxl : x < l)
    (hp : 0 < p) (hpl : p < l) (hlpi : l ≤ π) : 0 < green l p x := by
  have hden : 0 < 2 * det l := mul_pos (by norm_num) (det_positive (lt_trans hp hpl) hlpi)
  unfold green
  split_ifs with hxp
  · exact div_pos (numerator_positive hx hxp hpl hlpi) hden
  · exact div_pos (numerator_positive hp (le_of_not_ge hxp) hxl hlpi) hden

/-- Any nonzero nonnegative collection of negative sources makes the clamped
residual strictly negative throughout the gap, including a full-period gap. -/
theorem negative_green_sum {ι : Type*} (T : Finset ι) (p s : ι → ℝ) {l x : ℝ}
    (hx : 0 < x) (hxl : x < l) (hlpi : l ≤ π)
    (hp : ∀ i ∈ T, 0 < p i ∧ p i < l) (hs : ∀ i ∈ T, 0 ≤ s i)
    (hsource : ∃ i ∈ T, 0 < s i) :
    -4 * ∑ i in T, s i * green l (p i) x < 0 := by
  have hsum : 0 < ∑ i in T, s i * green l (p i) x := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hs i hi) (green_positive hx hxl (hp i hi).1 (hp i hi).2 hlpi).le
    · obtain ⟨i, hi, his⟩ := hsource
      exact ⟨i, hi, mul_pos his (green_positive hx hxl (hp i hi).1 (hp i hi).2 hlpi)⟩
  linarith

/-- The two global homogeneous continuations of the unit-jump Green profile. -/
def greenU (l p : ℝ) : ℝ := -jerk l p / (2 * det l)
def greenV (l p : ℝ) : ℝ := moment l p / (2 * det l)
def greenLeft (l p : ℝ) : ℝ → ℝ := Beam.leftBranch (greenU l p) (greenV l p)
def greenLeft1 (l p : ℝ) : ℝ → ℝ := Beam.leftSlope (greenU l p) (greenV l p)
def greenLeft2 (l p : ℝ) : ℝ → ℝ := Beam.leftCurvature (greenU l p) (greenV l p)
def greenLeft3 (l p : ℝ) : ℝ → ℝ := Beam.leftJerk (greenU l p) (greenV l p)
def greenLeft4 (l p x : ℝ) : ℝ := -2 * greenLeft2 l p x - greenLeft l p x

def greenRight (l p x : ℝ) : ℝ := greenLeft l p x + (1 / 2 : ℝ) * psi (x - p)
def greenRight1 (l p x : ℝ) : ℝ := greenLeft1 l p x + (1 / 2 : ℝ) * chi (x - p)
def greenRight2 (l p x : ℝ) : ℝ :=
  greenLeft2 l p x + (1 / 2 : ℝ) * (sin (x - p) + (x - p) * cos (x - p))
def greenRight3 (l p x : ℝ) : ℝ :=
  greenLeft3 l p x + (1 / 2 : ℝ) * (2 * cos (x - p) - (x - p) * sin (x - p))
def greenRight4 (l p x : ℝ) : ℝ := -2 * greenRight2 l p x - greenRight l p x

theorem greenLeft_derivative (l p x : ℝ) :
    HasDerivAt (greenLeft l p) (greenLeft1 l p x) x :=
  Beam.hasDerivAt_leftBranch _ _ _

theorem greenLeft1_derivative (l p x : ℝ) :
    HasDerivAt (greenLeft1 l p) (greenLeft2 l p x) x :=
  Beam.hasDerivAt_leftSlope _ _ _

theorem greenLeft2_derivative (l p x : ℝ) :
    HasDerivAt (greenLeft2 l p) (greenLeft3 l p x) x :=
  Beam.hasDerivAt_leftCurvature _ _ _

theorem greenLeft3_derivative (l p x : ℝ) :
    HasDerivAt (greenLeft3 l p) (greenLeft4 l p x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * cos x - x * sin x)
      (-3 * sin x - x * cos x) x := by
    convert ((hasDerivAt_cos x).const_mul 2).sub
      ((hasDerivAt_id x).mul (hasDerivAt_sin x)) using 1; dsimp; ring
  have h2 : HasDerivAt (fun x : ℝ => -3 * sin x - x * cos x)
      (-4 * cos x + x * sin x) x := by
    convert ((hasDerivAt_sin x).const_mul (-3)).sub
      ((hasDerivAt_id x).mul (hasDerivAt_cos x)) using 1; dsimp; ring
  convert (h1.const_mul (greenU l p)).add (h2.const_mul (greenV l p)) using 1
  simp only [greenLeft4, greenLeft2, greenLeft, Beam.leftCurvature, Beam.leftBranch,
    Beam.psi, Beam.chi]
  ring

theorem greenRight_derivative (l p x : ℝ) :
    HasDerivAt (greenRight l p) (greenRight1 l p x) x := by
  convert (greenLeft_derivative l p x).add
    (((psi_derivative (x - p)).comp x ((hasDerivAt_id x).sub_const p)).const_mul (1 / 2 : ℝ))
    using 1; simp [greenRight, greenRight1]

theorem greenRight1_derivative (l p x : ℝ) :
    HasDerivAt (greenRight1 l p) (greenRight2 l p x) x := by
  convert (greenLeft1_derivative l p x).add
    (((chi_derivative (x - p)).comp x ((hasDerivAt_id x).sub_const p)).const_mul (1 / 2 : ℝ))
    using 1; simp [greenRight1, greenRight2]

theorem greenRight2_derivative (l p x : ℝ) :
    HasDerivAt (greenRight2 l p) (greenRight3 l p x) x := by
  have h : HasDerivAt (fun x : ℝ => sin x + x * cos x)
      (2 * cos (x - p) - (x - p) * sin (x - p)) (x - p) := by
    convert (hasDerivAt_sin (x - p)).add
      ((hasDerivAt_id (x - p)).mul (hasDerivAt_cos (x - p))) using 1; dsimp; ring
  convert (greenLeft2_derivative l p x).add
    ((h.comp x ((hasDerivAt_id x).sub_const p)).const_mul (1 / 2 : ℝ))
    using 1; simp [greenRight2, greenRight3]

theorem greenRight3_derivative (l p x : ℝ) :
    HasDerivAt (greenRight3 l p) (greenRight4 l p x) x := by
  have h : HasDerivAt (fun x : ℝ => 2 * cos x - x * sin x)
      (-3 * sin (x - p) - (x - p) * cos (x - p)) (x - p) := by
    convert ((hasDerivAt_cos (x - p)).const_mul 2).sub
      ((hasDerivAt_id (x - p)).mul (hasDerivAt_sin (x - p))) using 1; dsimp; ring
  convert (greenLeft3_derivative l p x).add
    ((h.comp x ((hasDerivAt_id x).sub_const p)).const_mul (1 / 2 : ℝ)) using 1
  simp only [greenRight4, greenRight2, greenRight, greenLeft4, psi]
  ring

theorem greenLeft_clamped (l p : ℝ) : greenLeft l p 0 = 0 ∧ greenLeft1 l p 0 = 0 := by
  simp [greenLeft, greenLeft1, Beam.leftBranch, Beam.leftSlope, Beam.psi, Beam.chi]

/-- `eq:green-linear-system`: the two coefficients solve the value and
slope clamp equations for the right homogeneous continuation. -/
theorem eq_green_linear_system {l : ℝ} (hdet : det l ≠ 0) (p : ℝ) :
    greenU l p * psi l + greenV l p * chi l = -psi (l - p) / 2 ∧
    greenU l p * chi l + greenV l p * (sin l + l * cos l) = -chi (l - p) / 2 := by
  have hm : psi l * (sin l + l * cos l) - chi l * chi l = -det l := by
    simpa only [pow_two] using eq_green_determinant l
  constructor
  · have hn : -jerk l p * psi l + moment l p * chi l = -det l * psi (l - p) := by
      rw [eq_green_A, eq_green_M0]
      linear_combination psi (l - p) * hm
    calc
      greenU l p * psi l + greenV l p * chi l =
          (-jerk l p * psi l + moment l p * chi l) / (2 * det l) := by
        unfold greenU greenV
        ring
      _ = -psi (l - p) / 2 := by
        rw [hn]
        field_simp [hdet]
        ring
  · have hn : -jerk l p * chi l + moment l p * (sin l + l * cos l) =
        -det l * chi (l - p) := by
      rw [eq_green_A, eq_green_M0]
      linear_combination chi (l - p) * hm
    calc
      greenU l p * chi l + greenV l p * (sin l + l * cos l) =
          (-jerk l p * chi l + moment l p * (sin l + l * cos l)) / (2 * det l) := by
        unfold greenU greenV
        ring
      _ = -chi (l - p) / 2 := by
        rw [hn]
        field_simp [hdet]
        ring

/-- The endpoint clamps are the immediate consequences of the displayed
coefficient system, rather than a second copy of its determinant algebra. -/
theorem greenRight_clamped {l : ℝ} (hdet : det l ≠ 0) (p : ℝ) :
    greenRight l p l = 0 ∧ greenRight1 l p l = 0 := by
  obtain ⟨hvalue, hslope⟩ := eq_green_linear_system hdet p
  constructor
  · change greenU l p * psi l + greenV l p * chi l + (1 / 2 : ℝ) * psi (l - p) = 0
    rw [hvalue]
    ring
  · change greenU l p * chi l + greenV l p * (sin l + l * cos l) +
        (1 / 2 : ℝ) * chi (l - p) = 0
    rw [hslope]
    ring

/-- Value, slope, and curvature glue, while the third derivative has unit jump. -/
theorem green_source_jet (l p : ℝ) :
    greenRight l p p = greenLeft l p p ∧
    greenRight1 l p p = greenLeft1 l p p ∧
    greenRight2 l p p = greenLeft2 l p p ∧
    greenRight3 l p p = greenLeft3 l p p + 1 := by
  simp [greenRight, greenRight1, greenRight2, greenRight3, psi, chi]

theorem greenLeft_eq_numerator (l p x : ℝ) :
    greenLeft l p x = numerator l p x / (2 * det l) := by
  change (-jerk l p / (2 * det l)) * psi x +
    (moment l p / (2 * det l)) * chi x = _
  unfold numerator
  ring

def greenLeftBranch (l p : ℝ) : GreenWronskian.Branch where
  jet := ![greenLeft l p, greenLeft1 l p, greenLeft2 l p, greenLeft3 l p, greenLeft4 l p]
  derivative := by
    intro i x
    fin_cases i
    · exact greenLeft_derivative l p x
    · exact greenLeft1_derivative l p x
    · exact greenLeft2_derivative l p x
    · exact greenLeft3_derivative l p x
  equation := by
    intro x
    change greenLeft4 l p x + 2 * greenLeft2 l p x + greenLeft l p x = 0
    unfold greenLeft4
    ring

def greenRightBranch (l p : ℝ) : GreenWronskian.Branch where
  jet := ![greenRight l p, greenRight1 l p, greenRight2 l p, greenRight3 l p, greenRight4 l p]
  derivative := by
    intro i x
    fin_cases i
    · exact greenRight_derivative l p x
    · exact greenRight1_derivative l p x
    · exact greenRight2_derivative l p x
    · exact greenRight3_derivative l p x
  equation := by
    intro x
    change greenRight4 l p x + 2 * greenRight2 l p x + greenRight l p x = 0
    unfold greenRight4
    ring

theorem green_branch_join (l p : ℝ) (i : Fin 3) :
    (greenRightBranch l p).jet (i.castLE (by decide)) p =
      (greenLeftBranch l p).jet (i.castLE (by decide)) p := by
  fin_cases i
  · exact (green_source_jet l p).1
  · exact (green_source_jet l p).2.1
  · exact (green_source_jet l p).2.2.1

/-- The concrete clamped Green reciprocity is proved through conservation of
the manuscript's adjoint boundary form and its two unit-source jumps. -/
theorem green_branch_reciprocity {l : ℝ} (hdet : det l ≠ 0) (p x : ℝ) :
    greenRight l p x = greenLeft l x p := by
  exact GreenWronskian.branch_reciprocity
    (greenLeftBranch l p) (greenRightBranch l p) (greenLeftBranch l x) (greenRightBranch l x)
    0 l p x (greenLeft_clamped l p) (greenRight_clamped hdet p)
    (greenLeft_clamped l x) (greenRight_clamped hdet x)
    (green_branch_join l p) (green_source_jet l p).2.2.2
    (green_branch_join l x) (green_source_jet l x).2.2.2

/-- The scalar identity used by the causal Green representation is now an
application of the adjoint argument, rather than a separate trig expansion. -/
theorem numerator_reciprocity_of_adjoint {l : ℝ} (hdet : det l ≠ 0) (p x : ℝ) :
    numerator l p x + det l * psi (x - p) = numerator l x p := by
  have h := green_branch_reciprocity hdet p x
  rw [greenRight, greenLeft_eq_numerator, greenLeft_eq_numerator] at h
  have hn := congrArg (fun z : ℝ => z * (2 * det l)) h
  simp only [add_mul, div_mul_cancel _ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hdet)] at hn
  linarith only [hn]


theorem green_causal_identity {l : ℝ} (hdet : det l ≠ 0) (p x : ℝ) :
    2 * det l * green l p x =
      numerator l p x + if p ≤ x then det l * psi (x - p) else 0 := by
  unfold green
  by_cases hxp : x ≤ p
  · rw [if_pos hxp]
    by_cases hpx : p ≤ x
    · have heq : x = p := le_antisymm hxp hpx
      rw [if_pos hpx, heq]
      simp only [sub_self, psi, sin_zero, cos_zero, zero_mul, sub_zero, mul_zero, add_zero]
      field_simp
      ring
    · rw [if_neg hpx]
      field_simp
      ring
  · rw [if_neg hxp, if_pos (le_of_not_ge hxp), numerator_reciprocity_of_adjoint hdet]
    field_simp
    ring

/-- `eq:green-ansatz`: the actual solved homogeneous coefficients and
the half-psi source branch give the clamped Green function. -/
theorem eq_green_ansatz {l : ℝ} (hdet : det l ≠ 0) (p x : ℝ) :
    let d1 : ℝ := 0
    let d2 := greenU l p
    let d3 := -d2
    let d4 := greenV l p
    let g0 := fun z => d1 * cos z + d2 * sin z + d3 * z * cos z + d4 * z * sin z
    green l p x = g0 x + (1 / 2 : ℝ) * (if p < x then psi (x - p) else 0) ∧
      g0 x = greenLeft l p x := by
  dsimp only
  have hleft : (0 : ℝ) * cos x + greenU l p * sin x +
      -greenU l p * x * cos x + greenV l p * x * sin x = greenLeft l p x := by
    dsimp [greenLeft, Beam.leftBranch, Beam.psi, Beam.chi, psi, chi]
    ring
  refine ⟨?_, hleft⟩
  rw [hleft, greenLeft_eq_numerator]
  have h := green_causal_identity hdet p x
  by_cases hpx : p < x
  · rw [if_pos hpx, if_pos hpx.le] at *
    field_simp [hdet]
    nlinarith only [h]
  · rw [if_neg hpx]
    by_cases heq : p = x
    · subst x
      simp [psi] at h ⊢
      field_simp [hdet]
      nlinarith only [h]
    · rw [if_neg (by intro hle; exact heq (le_antisymm hle (le_of_not_gt hpx)))] at h
      field_simp [hdet]
      nlinarith only [h]

/-- `eq:green-function`: the explicit causal clamped Green profile. -/
theorem eq_green_function {l : ℝ} (hdet : det l ≠ 0) (p x : ℝ) :
    green l p x = numerator l p x / (2 * det l) +
      (1 / 2 : ℝ) * (if p ≤ x then psi (x - p) else 0) := by
  have h := eq_green_ansatz hdet p x
  rw [h.1, h.2, greenLeft_eq_numerator]
  congr 2
  by_cases hpx : p < x
  · simp only [if_pos hpx, if_pos hpx.le]
  · by_cases heq : p = x
    · subst x
      simp [psi]
    · have hnp : ¬ p ≤ x := fun hle => heq (le_antisymm hle (not_lt.mp hpx))
      simp only [if_neg hpx, if_neg hnp]

def response {ι : Type*} (T : Finset ι) (p s : ι → ℝ) (U V x : ℝ) : ℝ :=
  U * psi x + V * chi x - 2 * ∑ i in T, s i * (if p i ≤ x then psi (x - p i) else 0)

/-- A two-by-two endpoint solve for any finite number of sources. No ODE
existence/uniqueness theorem and no regularity package enters this calculation. -/
theorem clamped_coefficients {ι : Type*} (T : Finset ι) (p s : ι → ℝ) (l U V : ℝ)
    (hvalue : U * psi l + V * chi l = 2 * ∑ i in T, s i * psi (l - p i))
    (hslope : U * chi l + V * (sin l + l * cos l) =
      2 * ∑ i in T, s i * chi (l - p i)) :
    det l * U = 2 * ∑ i in T, s i * jerk l (p i) ∧
      det l * V = -2 * ∑ i in T, s i * moment l (p i) := by
  have hmatrix : psi l * (sin l + l * cos l) - chi l * chi l = -det l := by
    simpa only [pow_two] using eq_green_determinant l
  have hJ : (∑ i in T, s i * jerk l (p i)) =
      chi l * (∑ i in T, s i * chi (l - p i)) -
        (sin l + l * cos l) * (∑ i in T, s i * psi (l - p i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [eq_green_A]
    ring
  have hM : (∑ i in T, s i * moment l (p i)) =
      psi l * (∑ i in T, s i * chi (l - p i)) -
        chi l * (∑ i in T, s i * psi (l - p i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [eq_green_M0]
    ring
  rw [hJ, hM]
  constructor
  · linear_combination chi l * hslope - (sin l + l * cos l) * hvalue + U * hmatrix
  · linear_combination chi l * hvalue - psi l * hslope + V * hmatrix

/-- Every explicitly forced branch with four clamped endpoint conditions is
the negative Green superposition. The left conditions have already removed
the cosine and sine homogeneous coefficients from `response`. -/
theorem eq_green_pairing {ι : Type*} (T : Finset ι) (p s : ι → ℝ)
    (l U V : ℝ) (hdet : det l ≠ 0)
    (hvalue : U * psi l + V * chi l = 2 * ∑ i in T, s i * psi (l - p i))
    (hslope : U * chi l + V * (sin l + l * cos l) =
      2 * ∑ i in T, s i * chi (l - p i)) (x : ℝ) :
    0 = -4 * ∑ i in T, s i * green l (p i) x - response T p s U V x := by
  have h : response T p s U V x = -4 * ∑ i in T, s i * green l (p i) x := by
    obtain ⟨hU, hV⟩ := clamped_coefficients T p s l U V hvalue hslope
    have hscale : det l * (∑ i in T, s i * (if p i ≤ x then psi (x - p i) else 0)) =
        ∑ i in T, s i * (if p i ≤ x then det l * psi (x - p i) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    apply mul_left_cancel₀ hdet
    calc
      det l * response T p s U V x =
          (det l * U) * psi x + (det l * V) * chi x -
            2 * ∑ i in T, s i * (if p i ≤ x then det l * psi (x - p i) else 0) := by
        unfold response
        linear_combination -2 * hscale
      _ = -2 * ∑ i in T, s i *
          (numerator l (p i) x + if p i ≤ x then det l * psi (x - p i) else 0) := by
        rw [hU, hV]
        simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [numerator]
        ring
      _ = det l * (-4 * ∑ i in T, s i * green l (p i) x) := by
        have hid (p : ℝ) :
            numerator l p x + (if p ≤ x then det l * psi (x - p) else 0) =
              2 * det l * green l p x := by
          rw [eq_green_function hdet]
          split_ifs <;> field_simp [hdet] <;> ring
        simp only [hid]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

  linarith only [h]

theorem stp_green_representation {ι : Type*} (T : Finset ι) (p s : ι → ℝ)
    (l U V : ℝ) (hdet : det l ≠ 0)
    (hvalue : U * psi l + V * chi l = 2 * ∑ i in T, s i * psi (l - p i))
    (hslope : U * chi l + V * (sin l + l * cos l) =
      2 * ∑ i in T, s i * chi (l - p i)) (x : ℝ) :
    response T p s U V x = -4 * ∑ i in T, s i * green l (p i) x := by
  have h := eq_green_pairing T p s l U V hdet hvalue hslope x
  linarith only [h]


end PaperLeanFormalization.Planar.Gaps



open Real
open scoped BigOperators

noncomputable section

namespace PaperLeanFormalization.Planar

/-- Finite kernel loss is genuinely differentiable in the full mass-angle
product space, not merely along a chosen collection of curves. -/
theorem differentiable_finite_kernel_loss {n m : ℕ} (K : ℝ → ℝ)
    (hK : Differentiable ℝ K) (s beta : Fin m → ℝ) :
    Differentiable ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (1 / (4 * π)) *
        ((∑ i, ∑ j, p.1 i * p.1 j * K (p.2 i - p.2 j)) -
          2 * (∑ i, ∑ k, p.1 i * s k * K (p.2 i - beta k)) +
          ∑ k, ∑ l, s k * s l * K (beta k - beta l))) := by
  have hc (i : Fin n) : Differentiable ℝ
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i) :=
    ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).differentiable).comp differentiable_fst
  have ht (i : Fin n) : Differentiable ℝ
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) :=
    ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).differentiable).comp differentiable_snd
  have hstudent : Differentiable ℝ
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ∑ i, ∑ j, p.1 i * p.1 j * K (p.2 i - p.2 j)) := by
    apply Differentiable.sum
    intro i _
    apply Differentiable.sum
    intro j _
    exact ((hc i).mul (hc j)).mul (hK.comp ((ht i).sub (ht j)))
  have hteacher : Differentiable ℝ
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ∑ i, ∑ k, p.1 i * s k * K (p.2 i - beta k)) := by
    apply Differentiable.sum
    intro i _
    apply Differentiable.sum
    intro k _
    exact ((hc i).mul_const (s k)).mul (hK.comp ((ht i).sub_const (beta k)))
  exact ((hstudent.sub (hteacher.const_mul 2)).add_const _).const_mul _

end PaperLeanFormalization.Planar

namespace PaperLeanFormalization.Planar.Gaps

/-- The source contribution at the right endpoint is the reflected moment.
This identity requires no restriction on the source or gap length. -/
theorem right_curvature_identity (l p : ℝ) :
    jerk l p * (sin l + l * cos l) - moment l p * (2 * cos l - l * sin l) -
      det l * (sin (l - p) + (l - p) * cos (l - p)) =
      -2 * moment l (l - p) := by
  dsimp [jerk, moment, psi, chi, det]
  rw [show l - (l - p) = p by ring]
  simp only [sin_sub, cos_sub]
  linear_combination
    (cos l * cos p * l ^ 3 - cos l * cos p * l ^ 2 * p - cos l * l ^ 2 * sin p +
      2 * cos l * l * p * sin p + cos p * l ^ 2 * sin l -
      2 * cos p * l * p * sin l + l ^ 3 * sin l * sin p -
      l ^ 2 * p * sin l * sin p + 2 * l * sin l * sin p -
      2 * p * sin l * sin p) * sin_sq_add_cos_sq l

/-- The left endpoint curvature formula, including an empty source set. -/
theorem clamped_left_curvature_formula {ι : Type*} (T : Finset ι) (p s : ι → ℝ)
    (l U V : ℝ) (hdet : det l ≠ 0)
    (hvalue : U * psi l + V * chi l = 2 * ∑ i in T, s i * psi (l - p i))
    (hslope : U * chi l + V * (sin l + l * cos l) =
      2 * ∑ i in T, s i * chi (l - p i)) :
    2 * V = -(∑ i in T, 4 * s i * moment l (p i) / det l) := by
  have hV := (clamped_coefficients T p s l U V hvalue hslope).2
  have hsum : (∑ i in T, 4 * s i * moment l (p i)) =
      4 * ∑ i in T, s i * moment l (p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← Finset.sum_div, ← neg_div, hsum]
  apply (eq_div_iff hdet).mpr
  nlinarith only [hV]

/-- The right endpoint curvature formula uses the same clamped equations
and the reflected moment. It remains valid for the full-period gap. -/
theorem clamped_right_curvature_formula {ι : Type*} (T : Finset ι) (p s : ι → ℝ)
    (l U V : ℝ) (hdet : det l ≠ 0)
    (hvalue : U * psi l + V * chi l = 2 * ∑ i in T, s i * psi (l - p i))
    (hslope : U * chi l + V * (sin l + l * cos l) =
      2 * ∑ i in T, s i * chi (l - p i)) :
    U * (sin l + l * cos l) + V * (2 * cos l - l * sin l) -
      2 * ∑ i in T, s i * (sin (l - p i) + (l - p i) * cos (l - p i)) =
      -(∑ i in T, 4 * s i * moment l (l - p i) / det l) := by
  obtain ⟨hU, hV⟩ := clamped_coefficients T p s l U V hvalue hslope
  have hsum : (∑ i in T, 4 * s i * moment l (l - p i)) =
      4 * ∑ i in T, s i * moment l (l - p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hid :
      (∑ i in T, s i * jerk l (p i)) * (sin l + l * cos l) -
        (∑ i in T, s i * moment l (p i)) * (2 * cos l - l * sin l) -
        det l * (∑ i in T, s i * (sin (l - p i) + (l - p i) * cos (l - p i))) =
      -2 * ∑ i in T, s i * moment l (l - p i) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    linear_combination s i * right_curvature_identity l (p i)
  rw [← Finset.sum_div, ← neg_div, hsum]
  apply (eq_div_iff hdet).mpr
  linear_combination (sin l + l * cos l) * hU + (2 * cos l - l * sin l) * hV + 2 * hid

end PaperLeanFormalization.Planar.Gaps




/-!
Fresh finite part of the line-count argument.  The analytic input is stated
literally as the two endpoint-curvature sums, rather than as an interlacing
certificate.  Ordinary neighboring gaps already suffice for propagation.
-/

open Real
open scoped BigOperators

noncomputable section

namespace PaperLeanFormalization.Planar.Gaps

/-- The centered kernel is strictly positive at every angle. -/
theorem centered_kernel_pos (x : ℝ) :
    0 < cos x * arcsin (cos x) + sqrt (1 - cos x ^ 2) := by
  rcases lt_trichotomy (cos x) 0 with hn | hz | hp
  · exact add_pos_of_pos_of_nonneg
      (mul_pos_of_neg_of_neg hn (Real.arcsin_lt_zero.mpr hn)) (sqrt_nonneg _)
  · simp [hz]
  · exact add_pos_of_pos_of_nonneg
      (mul_pos hp (Real.arcsin_pos.mpr hp)) (sqrt_nonneg _)

/-- A residual zero with a positive source needs a negative source. -/
theorem negative_weight_exists_of_zero_sum
    {ι : Type*} [Fintype ι] (weight value : ι → ℝ)
    (hvalue : ∀ i, 0 < value i)
    (hzero : ∑ i, weight i * value i = 0)
    (hpositive : ∃ i, 0 < weight i) :
    ∃ i, weight i < 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨i, hi⟩ := hpositive
  have hsum : 0 < ∑ j, weight j * value j :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hnone j) (hvalue j).le)
      ⟨i, Finset.mem_univ _, mul_pos hi (hvalue i)⟩
  linarith

/-- A negative positive-weighted sum detects whether a gap is occupied. -/
theorem negative_gap_sum_iff {r s : ℕ} (gap : Fin s → Fin r)
    (load : Fin r → Fin s → ℝ)
    (hload : ∀ i j, gap j = i → 0 < load i j) (i : Fin r) :
    -(∑ j in Finset.univ.filter (fun j => gap j = i), load i j) < 0 ↔
      ∃ j, gap j = i := by
  classical
  constructor
  · intro h
    by_contra hn
    have hempty : Finset.univ.filter (fun j => gap j = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro j hj
      exact hn ⟨j, (Finset.mem_filter.mp hj).2⟩
    simp [hempty] at h
  · rintro ⟨j, hj⟩
    have hs : 0 < ∑ k in Finset.univ.filter (fun k => gap k = i), load i k :=
      Finset.sum_pos'
        (fun k hk => (hload i k (Finset.mem_filter.mp hk).2).le)
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hload i j hj⟩
    exact neg_neg_of_pos hs

/-- Along the ordered list of gaps, adjacent occupancy equivalences propagate
from any one occupied gap.  No cyclic third-derivative argument is needed. -/
theorem all_gaps_occupied_of_adjacent {r : ℕ} (occupied : Fin (r + 1) → Prop)
    (hadj : ∀ i : Fin r, occupied i.castSucc ↔ occupied i.succ)
    (hsome : ∃ i, occupied i) : ∀ i, occupied i := by
  have hzero : ∀ i, occupied i ↔ occupied 0 := by
    intro i
    induction i using Fin.induction with
    | zero => exact Iff.rfl
    | succ i hi => exact (hadj i).symm.trans hi
  obtain ⟨j, hj⟩ := hsome
  intro i
  exact (hzero i).mpr ((hzero j).mp hj)

/-- The complete finite line-count step from the clamped endpoint formulas.
`gap j` names the unique positive-support gap containing negative line `j`.
The two load arrays are its positive left/right adjoint weights, including
the negative-line mass and the positive jump normalization.
-/
theorem line_count_of_endpoint_curvature_formulas
    {r s : ℕ} (gap : Fin s → Fin (r + 1))
    (left right : Fin (r + 1) → ℝ)
    (loadLeft loadRight : Fin (r + 1) → Fin s → ℝ)
    (hloadLeft : ∀ i j, gap j = i → 0 < loadLeft i j)
    (hloadRight : ∀ i j, gap j = i → 0 < loadRight i j)
    (hleft : ∀ i, left i =
      -(∑ j in Finset.univ.filter (fun j => gap j = i), loadLeft i j))
    (hright : ∀ i, right i =
      -(∑ j in Finset.univ.filter (fun j => gap j = i), loadRight i j))
    (hcontinuous : ∀ i : Fin r, right i.castSucc = left i.succ)
    (hs : 0 < s) :
    Function.Surjective gap ∧ r + 1 ≤ s := by
  classical
  have hleftOcc (i : Fin (r + 1)) : left i < 0 ↔ ∃ j, gap j = i := by
    rw [hleft i]
    exact negative_gap_sum_iff gap loadLeft hloadLeft i
  have hrightOcc (i : Fin (r + 1)) : right i < 0 ↔ ∃ j, gap j = i := by
    rw [hright i]
    exact negative_gap_sum_iff gap loadRight hloadRight i
  have hsurj : Function.Surjective gap := by
    apply all_gaps_occupied_of_adjacent (fun i => ∃ j, gap j = i)
    · intro i
      rw [← hrightOcc i.castSucc, ← hleftOcc i.succ, hcontinuous i]
    · exact ⟨gap ⟨0, hs⟩, ⟨0, hs⟩, rfl⟩
  exact ⟨hsurj, by simpa using Fintype.card_le_of_surjective gap hsurj⟩

/-- Equality in the count means exactly one negative line in every gap. -/
theorem one_negative_per_gap_of_equal_count {r : ℕ}
    (gap : Fin r → Fin r) (hgap : Function.Surjective gap) :
    ∀ i, ∃! j, gap j = i := by
  have hinj : Function.Injective gap :=
    ((Fintype.bijective_iff_surjective_and_card gap).mpr ⟨hgap, rfl⟩).1
  intro i
  obtain ⟨j, hj⟩ := hgap i
  exact ⟨j, hj, fun k hk => hinj (hk.trans hj.symm)⟩

/-- The last gap ends at the first angle plus one projective period. -/
def rightEndpoint {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (i : Fin (r + 1)) : ℝ :=
  if h : i.val + 1 < r + 1 then angle ⟨i.val + 1, h⟩ else angle 0 + π

/-- A base-period angle is lifted into the period beginning at `first`. -/
def liftAngle (first x : ℝ) : ℝ := if x < first then x + π else x

/-- Earlier open gaps end before later open gaps begin. -/
theorem rightEndpoint_le_later {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (hangle : StrictMono angle) {i j : Fin (r + 1)} (hij : i < j) :
    rightEndpoint angle i ≤ angle j := by
  have hnext : i.val + 1 < r + 1 := lt_of_le_of_lt hij j.isLt
  rw [rightEndpoint, dif_pos hnext]
  exact hangle.monotone (show (⟨i.val + 1, hnext⟩ : Fin (r + 1)) ≤ j from hij)

/-- A point off the nodes lies in exactly one gap of an increasing list.
Choosing the greatest node below the point proves existence directly. -/
theorem unique_gap_of_ordered_angles {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (hangle : StrictMono angle) {y : ℝ}
    (hfirst : angle 0 < y) (hlast : y < angle 0 + π)
    (hoff : ∀ i, angle i ≠ y) :
    ∃! i, angle i < y ∧ y < rightEndpoint angle i := by
  classical
  let below := Finset.univ.filter (fun i => angle i < y)
  have hbelow : below.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩⟩
  let g := below.max' hbelow
  have hg : angle g < y := (Finset.mem_filter.mp (Finset.max'_mem below hbelow)).2
  have hright : y < rightEndpoint angle g := by
    unfold rightEndpoint
    split
    · rename_i hn
      let next : Fin (r + 1) := ⟨g.val + 1, hn⟩
      have hnlt : ¬ angle next < y := by
        intro hh
        have hle : next ≤ g :=
          Finset.le_max' below next (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
        have hval : g.val + 1 ≤ g.val := hle
        omega (config := {})
      exact lt_of_le_of_ne (le_of_not_gt hnlt) (hoff next).symm
    · exact hlast
  refine ⟨g, ⟨hg, hright⟩, ?_⟩
  intro j hj
  rcases lt_trichotomy j g with hjg | heq | hgj
  · have hle := rightEndpoint_le_later angle hangle hjg
    linarith [hj.2]
  · exact heq
  · have hle := rightEndpoint_le_later angle hangle hgj
    linarith [hj.1]

/-- Canonical sorting and one explicit lift give the circle-gap assignment.
This includes the singleton positive support and its full-period gap. -/
theorem unique_gap_of_finite_circle {r : ℕ} (positive : Finset ℝ)
    (hcard : positive.card = r + 1)
    (hrange : ∀ x ∈ positive, 0 ≤ x ∧ x < π)
    {x : ℝ} (hx : 0 ≤ x ∧ x < π) (hoff : x ∉ positive) :
    ∃! i, positive.orderEmbOfFin hcard i <
        liftAngle (positive.orderEmbOfFin hcard 0) x ∧
      liftAngle (positive.orderEmbOfFin hcard 0) x <
        rightEndpoint (positive.orderEmbOfFin hcard) i := by
  let angle := positive.orderEmbOfFin hcard
  have harange (i : Fin (r + 1)) : 0 ≤ angle i ∧ angle i < π :=
    hrange _ (Finset.orderEmbOfFin_mem positive hcard i)
  have hne (i : Fin (r + 1)) : angle i ≠ x := by
    intro h
    exact hoff (h ▸ Finset.orderEmbOfFin_mem positive hcard i)
  apply unique_gap_of_ordered_angles angle angle.strictMono
  · unfold liftAngle
    split
    · linarith [(harange 0).2, hx.1]
    · rename_i hn
      exact lt_of_le_of_ne (le_of_not_gt hn) (hne 0)
  · unfold liftAngle
    split
    · rename_i hn
      linarith
    · linarith [(harange 0).1, hx.2]
  · intro i
    unfold liftAngle
    split
    · linarith [(harange i).2, hx.1]
    · exact hne i

/-- Consecutive finite gaps share their endpoint before the final wrap. -/
theorem rightEndpoint_castSucc {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (i : Fin r) : rightEndpoint angle i.castSucc = angle i.succ := by
  have hi : i.castSucc.val + 1 < r + 1 := Nat.succ_lt_succ i.isLt
  simp only [rightEndpoint, dif_pos hi]
  rfl

/-- Every gap length belongs to the closed half-period range needed by the
clamped Green function, including the singleton-support case. -/
theorem gap_length_range {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (hangle : StrictMono angle) (hrange : ∀ i, 0 ≤ angle i ∧ angle i < π)
    (i : Fin (r + 1)) :
    0 < rightEndpoint angle i - angle i ∧ rightEndpoint angle i - angle i ≤ π := by
  unfold rightEndpoint
  split
  · rename_i hn
    have hlt : angle i < angle ⟨i.val + 1, hn⟩ :=
      hangle (show i < (⟨i.val + 1, hn⟩ : Fin (r + 1)) from Nat.lt_succ_self _)
    constructor
    · linarith
    · linarith [(hrange i).1, (hrange ⟨i.val + 1, hn⟩).2]
  · have hfirst : angle 0 ≤ angle i := hangle.monotone (Fin.zero_le i)
    constructor
    · linarith [(hrange 0).1, (hrange i).2]
    · linarith

/-- Enumerating both signed line sets canonically produces the single gap
assignment used by the endpoint-curvature sums.  The equivalence records
the exact strict-gap relation, not merely a chosen membership witness. -/
theorem finite_circle_gap_assignment {r : ℕ} (positive negative : Finset ℝ)
    (hcard : positive.card = r + 1)
    (hpositive : ∀ x ∈ positive, 0 ≤ x ∧ x < π)
    (hnegative : ∀ x ∈ negative, 0 ≤ x ∧ x < π)
    (hdisjoint : Disjoint positive negative) :
    ∃ gap : Fin negative.card → Fin (r + 1), ∀ j i,
      gap j = i ↔
        positive.orderEmbOfFin hcard i <
          liftAngle (positive.orderEmbOfFin hcard 0) (negative.orderEmbOfFin rfl j) ∧
        liftAngle (positive.orderEmbOfFin hcard 0) (negative.orderEmbOfFin rfl j) <
          rightEndpoint (positive.orderEmbOfFin hcard) i := by
  classical
  have hunique (j : Fin negative.card) := unique_gap_of_finite_circle positive hcard
    hpositive (hnegative _ (Finset.orderEmbOfFin_mem negative rfl j))
    (show negative.orderEmbOfFin rfl j ∉ positive from fun hj =>
      Finset.disjoint_left.mp hdisjoint hj (Finset.orderEmbOfFin_mem negative rfl j))
  choose gap hgap huniq using hunique
  refine ⟨gap, ?_⟩
  intro j i
  constructor
  · intro h
    rw [← h]
    exact hgap j
  · intro h
    exact (huniq j i h).symm

end PaperLeanFormalization.Planar.Gaps

namespace PaperLeanFormalization.Planar.Gaps


def relativeAngle (a x : ℝ) : ℝ := if x < a then x + π - a else x - a

theorem relativeAngle_range {a x : ℝ}
    (ha : 0 ≤ a ∧ a < π) (hx : 0 ≤ x ∧ x < π) :
    0 ≤ relativeAngle a x ∧ relativeAngle a x < π := by
  unfold relativeAngle
  split
  · constructor <;> linarith [ha.2, hx.1]
  · constructor <;> linarith [ha.1, hx.2]

@[simp] theorem relativeAngle_self (a : ℝ) : relativeAngle a a = 0 := by
  simp [relativeAngle]

/-- Any projectively periodic scalar quantity transports to local coordinates
by a single period shift. This applies to the kernel and its torque. -/
theorem periodic_sub_relative (f : ℝ → ℝ)
    (hperiod : ∀ z, f (z + π) = f z) (a x t : ℝ) :
    f (x - relativeAngle a t) = f (a + x - t) := by
  unfold relativeAngle
  split
  · have h := hperiod (x - (t + π - a))
    rw [show x - (t + π - a) + π = a + x - t by ring] at h
    exact h.symm
  · congr 1
    ring

/-- The same transport for the full literal finite residual, including all
sources outside the selected gap. -/
theorem periodic_residual_rotate {n m : ℕ} (f : ℝ → ℝ)
    (hperiod : ∀ z, f (z + π) = f z)
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (a x : ℝ) :
    (∑ i, c i * f (x - relativeAngle a (theta i))) -
        ∑ k, s k * f (x - relativeAngle a (beta k)) =
      (∑ i, c i * f (a + x - theta i)) -
        ∑ k, s k * f (a + x - beta k) := by
  simp_rw [periodic_sub_relative f hperiod]

/-- Every sorted positive node is either the left endpoint itself or lies
outside the open local gap. This is precisely the causal-branch hypothesis. -/
theorem positive_nodes_outside_local_gap {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (hangle : StrictMono angle) (hrange : ∀ i, 0 ≤ angle i ∧ angle i < π)
    (g j : Fin (r + 1)) :
    relativeAngle (angle g) (angle j) = 0 ∨
      rightEndpoint angle g - angle g ≤ relativeAngle (angle g) (angle j) := by
  by_cases hjg : angle j < angle g
  · right
    rw [relativeAngle, if_pos hjg]
    unfold rightEndpoint
    split
    · rename_i hn
      linarith [(hrange j).1, (hrange ⟨g.val + 1, hn⟩).2]
    · have hfirst : angle 0 ≤ angle j := hangle.monotone (Fin.zero_le j)
      linarith
  · rw [relativeAngle, if_neg hjg]
    by_cases heq : angle j = angle g
    · left
      rw [heq, sub_self]
    · right
      have hagj : angle g < angle j := lt_of_le_of_ne (le_of_not_gt hjg) (Ne.symm heq)
      have hgj : g < j := hangle.lt_iff_lt.mp hagj
      have hn : g.val + 1 < r + 1 := lt_of_le_of_lt hgj j.isLt
      have hnext : angle ⟨g.val + 1, hn⟩ ≤ angle j :=
        hangle.monotone (show (⟨g.val + 1, hn⟩ : Fin (r + 1)) ≤ j from hgj)
      rw [rightEndpoint, dif_pos hn]
      linarith

/-- The fixed-first lift used for counting and the moving-left-endpoint
coordinates used for analysis define exactly the same open gap. -/
theorem relativeAngle_mem_iff_liftAngle_mem {first a b x : ℝ}
    (hfirst : first ≤ a) (hlast : b ≤ first + π) :
    (0 < relativeAngle a x ∧ relativeAngle a x < b - a) ↔
      (a < liftAngle first x ∧ liftAngle first x < b) := by
  unfold relativeAngle liftAngle
  split_ifs <;> constructor <;> rintro ⟨hL, hR⟩ <;> constructor <;> linarith

theorem rightEndpoint_le_first_add_pi {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (hrange : ∀ i, 0 ≤ angle i ∧ angle i < π) (g : Fin (r + 1)) :
    rightEndpoint angle g ≤ angle 0 + π := by
  unfold rightEndpoint
  split
  · rename_i hn
    linarith [(hrange 0).1, (hrange ⟨g.val + 1, hn⟩).2]
  · exact le_rfl

/-- In particular, a negative line is a local source precisely in its unique
assigned gap; no endpoint or wrap source is lost in the coordinate change. -/
theorem local_gap_mem_iff {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (hangle : StrictMono angle) (hrange : ∀ i, 0 ≤ angle i ∧ angle i < π)
    (g : Fin (r + 1)) (x : ℝ) :
    (0 < relativeAngle (angle g) x ∧
      relativeAngle (angle g) x < rightEndpoint angle g - angle g) ↔
      (angle g < liftAngle (angle 0) x ∧
        liftAngle (angle 0) x < rightEndpoint angle g) :=
  relativeAngle_mem_iff_liftAngle_mem (hangle.monotone (Fin.zero_le g))
    (rightEndpoint_le_first_add_pi angle hrange g)

/-- Inside the chosen gap, the local displacement is literally the global
lift minus the left endpoint. Thus the two adjoint weight formulas agree. -/
theorem relativeAngle_eq_lift_sub_of_inside {first a b x : ℝ}
    (hfirst : first ≤ a) (hlast : b ≤ first + π)
    (hinside : 0 < relativeAngle a x ∧ relativeAngle a x < b - a) :
    relativeAngle a x = liftAngle first x - a := by
  by_cases hxfirst : x < first
  · have hxa : x < a := lt_of_lt_of_le hxfirst hfirst
    simp [relativeAngle, liftAngle, hxfirst, hxa]
  · by_cases hxa : x < a
    · rw [relativeAngle, if_pos hxa] at hinside
      have hfx : first ≤ x := le_of_not_gt hxfirst
      linarith [hinside.2]
    · simp [relativeAngle, liftAngle, hxfirst, hxa]

/-- Returning from a local representative changes a periodic evaluation by
at most one full projective period. -/
theorem periodic_add_relative (f : ℝ → ℝ)
    (hperiod : ∀ z, f (z + π) = f z) (a x : ℝ) :
    f (a + relativeAngle a x) = f x := by
  unfold relativeAngle
  split
  · rw [show a + (x + π - a) = x + π by ring, hperiod]
  · congr 1
    ring

/-- A periodic function vanishing at the sorted nodes also vanishes at the
lifted right endpoint. This handles full-period singleton gaps as well. -/
theorem periodic_rightEndpoint_zero {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (f : ℝ → ℝ) (hperiod : ∀ z, f (z + π) = f z)
    (hzero : ∀ i, f (angle i) = 0) (g : Fin (r + 1)) :
    f (rightEndpoint angle g) = 0 := by
  unfold rightEndpoint
  split
  · exact hzero _
  · rw [hperiod, hzero]


end PaperLeanFormalization.Planar.Gaps


/-!
The planar coordinates used in Section 4 of the paper.
Angles in this file are representatives of lines in `[0, π)`, not oriented
angles modulo `2π`. Every definition is explicit at its point of use.
-/

open Real
open scoped BigOperators

noncomputable section

namespace PaperLeanFormalization.Planar

variable {n m : ℕ}

/-- The angular centered kernel, with no chain of model definitions. -/
def kernel (x : ℝ) : ℝ :=
  Real.cos x * Real.arcsin (Real.cos x) + Real.sqrt (1 - Real.cos x ^ 2)

/-- Equation `eq:residual-potential-paper`, centered case. -/
def residual (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * kernel (x - theta i) - ∑ k, s k * kernel (x - beta k)

/-- Equation `eq:LFC`, as the literal finite circle-Dirac action against
every periodic C4 test function. Coincident atoms need no separation hypothesis. -/
theorem eq_LFC {n m : ℕ} (c θ : Fin n → ℝ) (s β : Fin m → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 4 ψ) (hp : Function.Periodic ψ π) :
    (∫ x in (0 : ℝ)..π, residual c θ s β x *
      (iteratedDeriv 4 ψ x + 2 * iteratedDeriv 2 ψ x + ψ x)) =
      4 * ((∑ i, c i * ψ (θ i)) - ∑ k, s k * ψ (β k)) := by
  simpa only [residual, kernel, ← CircleMoments.K_eq_sqrt] using
    WeakBeamEquation.eq_LFC_smooth c θ s β ψ hψ hp

/-- Equation `eq:net-weight-main`: all coincident masses are summed here. -/
def netWeight (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  (∑ i in Finset.univ.filter (fun i => theta i = x), c i) -
    ∑ k in Finset.univ.filter (fun k => beta k = x), s k

def positiveLines (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) : Finset ℝ :=
  (Finset.univ.image theta ∪ Finset.univ.image beta).filter
    (fun x => 0 < netWeight c theta s beta x)

def negativeLines (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) : Finset ℝ :=
  (Finset.univ.image theta ∪ Finset.univ.image beta).filter
    (fun x => netWeight c theta s beta x < 0)

/-- Equation `eq:net-weight-main` as a named proposition, including both signs. -/
theorem eq_net_weight_main (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    netWeight c theta s beta x =
      (∑ i in Finset.univ.filter (fun i => theta i = x), c i) -
        (∑ k in Finset.univ.filter (fun k => beta k = x), s k) ∧
    positiveLines c theta s beta =
      (Finset.univ.image theta ∪ Finset.univ.image beta).filter
        (fun t => 0 < netWeight c theta s beta t) ∧
    negativeLines c theta s beta =
      (Finset.univ.image theta ∪ Finset.univ.image beta).filter
        (fun t => netWeight c theta s beta t < 0) := by
  exact ⟨rfl, rfl, rfl⟩

/-- The branch expressions read by the cuts are genuine smooth third
derivatives, not independent formal jet variables. -/
theorem third_derivative_principal_branch (x : ℝ) :
    deriv (deriv (deriv Beam.branch)) x = Beam.branchD3 x := by
  have h0 : deriv Beam.branch = WeakBeamEquation.principalJet 1 := by
    funext y
    exact (WeakBeamEquation.principal_derivative 0 y).deriv
  have h1 : deriv (WeakBeamEquation.principalJet 1) = WeakBeamEquation.principalJet 2 := by
    funext y
    exact (WeakBeamEquation.principal_derivative 1 y).deriv
  have h2 : deriv (WeakBeamEquation.principalJet 2) = WeakBeamEquation.principalJet 3 := by
    funext y
    exact (WeakBeamEquation.principal_derivative 2 y).deriv
  rw [h0, h1, h2]
  rfl

/-- `eq:LFC-jump`, including arbitrary coincident student and teacher atoms.
For canonical cut/source angles in `[0, π)`, the two displayed branch
arguments give the right and left analytic continuations. The third
derivatives below are actual derivatives of those smooth branches, not the
total third derivative of the nonsmooth residual at a knot. The algebraic
identity also holds outside the canonical range. -/
theorem eq_LFC_jump {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (alpha : ℝ) :
    ((∑ i, c i * deriv (deriv (deriv Beam.branch)) (if theta i ≤ alpha then alpha - theta i else alpha - theta i + π)) -
      ∑ k, s k * deriv (deriv (deriv Beam.branch)) (if beta k ≤ alpha then alpha - beta k else alpha - beta k + π)) -
    ((∑ i, c i * deriv (deriv (deriv Beam.branch)) (if theta i < alpha then alpha - theta i else alpha - theta i + π)) -
      ∑ k, s k * deriv (deriv (deriv Beam.branch)) (if beta k < alpha then alpha - beta k else alpha - beta k + π)) =
        4 * netWeight c theta s beta alpha := by
  classical
  simp_rw [third_derivative_principal_branch]
  change ((∑ i, c i * Beam.cutJerkRight alpha (theta i)) -
    ∑ k, s k * Beam.cutJerkRight alpha (beta k)) -
    ((∑ i, c i * Beam.cutJerkLeft alpha (theta i)) -
    ∑ k, s k * Beam.cutJerkLeft alpha (beta k)) = 4 * netWeight c theta s beta alpha
  have hsum {N : ℕ} (w angle : Fin N → ℝ) :
      (∑ i, w i * (Beam.cutJerkRight alpha (angle i) -
        Beam.cutJerkLeft alpha (angle i))) =
      4 * ∑ i in Finset.univ.filter (fun i => angle i = alpha), w i := by
    simp only [Beam.cut_jerk_jump, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hstudent := hsum c theta
  have hteacher := hsum s beta
  rw [(eq_net_weight_main c theta s beta alpha).1]
  simp only [mul_sub, Finset.sum_sub_distrib] at hstudent hteacher
  linarith only [hstudent, hteacher]



/-- The centered instance of equation `eq:residual-potential-paper`. -/
theorem eq_residual_potential_paper_centered
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    residual c theta s beta x =
      (∑ i, c i * kernel (x - theta i)) - ∑ k, s k * kernel (x - beta k) :=
  Preliminaries.eq_residual_potential_paper .centered c theta s beta x

theorem residual_eq_shared {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    residual c theta s beta =
      Definitions.PlanarResidual .centered c theta s beta := rfl

theorem netWeight_eq_shared {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    netWeight c theta s beta = Definitions.NetWeight c theta s beta := rfl

theorem positiveLines_eq_shared {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    positiveLines c theta s beta = Definitions.PositiveLines c theta s beta := rfl

theorem negativeLines_eq_shared {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    negativeLines c theta s beta = Definitions.NegativeLines c theta s beta := rfl

/-- The positive and negative line sets cannot contain a common line. -/
theorem positive_negative_disjoint (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    Disjoint (positiveLines c theta s beta) (negativeLines c theta s beta) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hp hn
  have hp' := (Finset.mem_filter.mp hp).2
  have hn' := (Finset.mem_filter.mp hn).2
  exact (not_lt_of_ge (le_of_lt hp')) hn'

/-- Positivity on the teacher side puts every net positive line at a student. -/
theorem positiveLines_subset_students (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hs : ∀ k, 0 ≤ s k) :
    positiveLines c theta s beta ⊆ Finset.univ.image theta := by
  classical
  intro x hx
  by_contra hnot
  have hstudent : (∑ i in Finset.univ.filter (fun i => theta i = x), c i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact False.elim (hnot (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩))
  have hteacher : 0 ≤ ∑ k in Finset.univ.filter (fun k => beta k = x), s k :=
    Finset.sum_nonneg (fun k _ => hs k)
  have hnet := (Finset.mem_filter.mp hx).2
  unfold netWeight at hnet
  rw [hstudent] at hnet
  linarith

/-- Every net negative line is a teacher line, even with zero student masses. -/
theorem negativeLines_subset_teachers (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    negativeLines c theta s beta ⊆ Finset.univ.image beta := by
  classical
  intro x hx
  by_contra hnot
  have hteacher : (∑ k in Finset.univ.filter (fun k => beta k = x), s k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact False.elim (hnot (Finset.mem_image.mpr
      ⟨k, Finset.mem_univ k, (Finset.mem_filter.mp hk).2⟩))
  have hstudent : 0 ≤ ∑ i in Finset.univ.filter (fun i => theta i = x), c i :=
    Finset.sum_nonneg (fun i _ => hc i)
  have hnet := (Finset.mem_filter.mp hx).2
  unfold netWeight at hnet
  rw [hteacher] at hnet
  linarith

/-- The last two inequalities of the line-count chain in the sketch. -/
theorem negative_line_count (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    (negativeLines c theta s beta).card ≤ (Finset.univ.image beta).card ∧
      (Finset.univ.image beta).card ≤ m := by
  classical
  refine ⟨Finset.card_le_of_subset (negativeLines_subset_teachers c theta s beta hc), ?_⟩
  calc
    (Finset.univ.image beta).card ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_image_le
    _ = m := by simp only [Finset.card_univ, Fintype.card_fin]

/-- A finite weighted sum may be grouped by angle in one step. -/
theorem sum_grouped_by_angle (c theta : Fin n → ℝ) (S : Finset ℝ)
    (hS : ∀ i, theta i ∈ S) (f : ℝ → ℝ) :
    (∑ i, c i * f (theta i)) =
      ∑ x in S, (∑ i in Finset.univ.filter (fun i => theta i = x), c i) * f x := by
  classical
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), theta i ∈ S :=
    fun i _ => hS i
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun i => c i * f (theta i))]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- The net-weight representation used in the `S₊ = ∅` proof sketch. -/
theorem residual_eq_sum_netWeight (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (x : ℝ) :
    residual c theta s beta x =
      ∑ t in Finset.univ.image theta ∪ Finset.univ.image beta,
        netWeight c theta s beta t * kernel (x - t) := by
  classical
  rw [eq_residual_potential_paper_centered]
  rw [sum_grouped_by_angle c theta (Finset.univ.image theta ∪ Finset.univ.image beta)
    (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem theta (Finset.mem_univ i)))
    (fun t => kernel (x - t)),
    sum_grouped_by_angle s beta (Finset.univ.image theta ∪ Finset.univ.image beta)
    (fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem beta (Finset.mem_univ k)))
    (fun t => kernel (x - t)), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [(eq_net_weight_main c theta s beta t).1]
  ring

/-- A positive line at a residual zero forces at least one negative line.
This is the initial occupied gap for the endpoint-curvature propagation proof.
-/
theorem negative_lines_nonempty_of_positive_residual_zero
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (x : ℝ) (hx : x ∈ positiveLines c theta s beta)
    (hzero : residual c theta s beta x = 0) :
    (negativeLines c theta s beta).Nonempty := by
  classical
  by_contra hnone
  have hnonneg : ∀ t ∈ Finset.univ.image theta ∪ Finset.univ.image beta,
      0 ≤ netWeight c theta s beta t := by
    intro t ht
    by_contra hnegative
    exact hnone ⟨t, Finset.mem_filter.mpr ⟨ht, lt_of_not_ge hnegative⟩⟩
  have hpositive : 0 < ∑ t in Finset.univ.image theta ∪ Finset.univ.image beta,
      netWeight c theta s beta t * kernel (x - t) := by
    apply Finset.sum_pos'
    · intro t ht
      exact mul_nonneg (hnonneg t ht) (le_of_lt (Gaps.centered_kernel_pos (x - t)))
    · exact ⟨x, (Finset.mem_filter.mp hx).1, mul_pos (Finset.mem_filter.mp hx).2
        (Gaps.centered_kernel_pos (x - x))⟩
  rw [← residual_eq_sum_netWeight, hzero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- Equality throughout the sketch's finite cardinality chain forces both the
teacher lines and student lines to survive, and hence to be disjoint. -/
theorem equality_in_line_count_chain
    (P N A B : Finset ℝ) (hPN : Disjoint P N)
    (hPA : P = A) (hNB : N ⊆ B)
    (hA : A.card = n) (hPNcard : P.card ≤ N.card)
    (hB : B.card ≤ m) (hmn : m ≤ n) :
    n = m ∧ N = B ∧ Disjoint A B := by
  have hNBcard : N.card ≤ B.card := Finset.card_le_of_subset hNB
  have hP : P.card = n := (congrArg Finset.card hPA).trans hA
  have hnm : n = m := by omega (config := {})
  have hcard : B.card ≤ N.card := by omega (config := {})
  have hEq : N = B := Finset.eq_of_subset_of_card_le hNB hcard
  refine ⟨hnm, hEq, ?_⟩
  rw [← hPA, ← hEq]
  exact hPN

end PaperLeanFormalization.Planar



open Real
open scoped BigOperators

noncomputable section

namespace PaperLeanFormalization.Planar

variable {n m : ℕ}

/-- The centered angular loss with its additive teacher constant removed.
The paper's normalized loss equals this divided by `2π`, plus a constant.
Both perturbation variables and the complete finite formula are visible here.
-/
def variableLoss (s beta : Fin m → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, p.1 i * p.1 j * kernel (p.2 i - p.2 j) -
    ∑ i, ∑ k, p.1 i * s k * kernel (p.2 i - beta k)

theorem kernel_neg (x : ℝ) : kernel (-x) = kernel x := by
  unfold kernel
  rw [Real.cos_neg]

theorem kernel_sub_swap (x y : ℝ) : kernel (x - y) = kernel (y - x) := by
  rw [show x - y = -(y - x) by ring, kernel_neg]

/-- Symmetry of the mixed finite kernel pairing. -/
theorem mixed_kernel_pairing_swap (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    (∑ i, ∑ k, c i * s k * kernel (theta i - beta k)) =
      ∑ k, ∑ i, s k * c i * kernel (beta k - theta i) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [kernel_sub_swap]
  ring

/-- The residual pairing expresses the complete excess loss, including the
teacher self-interaction constant missing from `variableLoss` itself. -/
theorem variableLoss_sub_exact_fit (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    variableLoss s beta (c, theta) - variableLoss s beta (s, beta) =
      (1 / 2 : ℝ) * ((∑ i, c i * residual c theta s beta (theta i)) -
        ∑ k, s k * residual c theta s beta (beta k)) := by
  have hstudent : (∑ i, c i * residual c theta s beta (theta i)) =
      (∑ i, ∑ j, c i * c j * kernel (theta i - theta j)) -
        ∑ i, ∑ k, c i * s k * kernel (theta i - beta k) := by
    unfold residual
    simp_rw [mul_sub, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_sub_distrib]
  have hteacher : (∑ k, s k * residual c theta s beta (beta k)) =
      (∑ i, ∑ k, c i * s k * kernel (theta i - beta k)) -
        ∑ k, ∑ l, s k * s l * kernel (beta k - beta l) := by
    unfold residual
    simp_rw [mul_sub, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_sub_distrib, ← mixed_kernel_pairing_swap]
  rw [hstudent, hteacher]
  unfold variableLoss
  dsimp only
  ring

/-- A zero residual field has exactly the teacher's loss value. -/
theorem variableLoss_eq_exact_fit_of_residual_zero
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hzero : ∀ x, residual c theta s beta x = 0) :
    variableLoss s beta (c, theta) = variableLoss s beta (s, beta) := by
  apply sub_eq_zero.mp
  rw [variableLoss_sub_exact_fit]
  have hs : (∑ i, c i * residual c theta s beta (theta i)) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [hzero, mul_zero])
  have ht : (∑ k, s k * residual c theta s beta (beta k)) = 0 :=
    Finset.sum_eq_zero (fun k _ => by rw [hzero, mul_zero])
  rw [hs, ht, sub_self, mul_zero]

def kernelD1 (x : ℝ) : ℝ := -sin x * arcsin (cos x)

theorem hasDerivAt_kernel (x : ℝ) : HasDerivAt kernel (kernelD1 x) x :=
  KernelCalculus.hasDerivAt_angularKernel x

theorem kernelD1_neg (x : ℝ) : kernelD1 (-x) = -kernelD1 x := by
  simp [kernelD1]

theorem hasDerivAt_residual (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    HasDerivAt (residual c theta s beta)
      ((∑ i, c i * kernelD1 (x - theta i)) - ∑ k, s k * kernelD1 (x - beta k)) x := by
  apply HasDerivAt.sub
  · apply HasDerivAt.sum
    intro i _
    simpa using ((hasDerivAt_kernel (x - theta i)).comp x
      ((hasDerivAt_id x).sub_const (theta i))).const_mul (c i)
  · apply HasDerivAt.sum
    intro k _
    simpa using ((hasDerivAt_kernel (x - beta k)).comp x
      ((hasDerivAt_id x).sub_const (beta k))).const_mul (s k)

theorem residual_second_derivative (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    deriv (deriv (residual c theta s beta)) x =
      2 * ((∑ i, c i * |sin (x - theta i)|) -
        ∑ k, s k * |sin (x - beta k)|) - residual c theta s beta x := by
  have hd : deriv (residual c theta s beta) =
      fun x => (∑ i, c i * kernelD1 (x - theta i)) -
        ∑ k, s k * kernelD1 (x - beta k) :=
    funext (fun x => (hasDerivAt_residual c theta s beta x).deriv)
  have hK1 (t : ℝ) : HasDerivAt kernelD1 (2 * |sin t| - kernel t) t :=
    KernelCalculus.hasDerivAt_angularKernel_first t
  have hss := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ =>
    ((hK1 (x - theta i)).comp x ((hasDerivAt_id x).sub_const (theta i))).const_mul (c i))
  have hst := HasDerivAt.sum (u := (Finset.univ : Finset (Fin m))) (fun k _ =>
    ((hK1 (x - beta k)).comp x ((hasDerivAt_id x).sub_const (beta k))).const_mul (s k))
  have hdd := (hss.sub hst).deriv
  dsimp only [Function.comp_apply, id_eq] at hdd
  rw [hd, hdd]
  simp only [mul_one, residual]
  simp_rw [mul_sub, Finset.sum_sub_distrib, mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]
  ring

theorem differentiable_variableLoss (s beta : Fin m → ℝ) :
    Differentiable ℝ (variableLoss (n := n) s beta) := by
  have hc (i : Fin n) : Differentiable ℝ
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i) :=
    ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).differentiable).comp differentiable_fst
  have ht (i : Fin n) : Differentiable ℝ
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) :=
    ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).differentiable).comp differentiable_snd
  have hK : Differentiable ℝ kernel := fun x => (hasDerivAt_kernel x).differentiableAt
  have hstudent : Differentiable ℝ
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ∑ i, ∑ j, p.1 i * p.1 j * kernel (p.2 i - p.2 j)) := by
    apply Differentiable.sum
    intro i _
    apply Differentiable.sum
    intro j _
    exact ((hc i).mul (hc j)).mul (hK.comp ((ht i).sub (ht j)))
  have hteacher : Differentiable ℝ
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ∑ i, ∑ k, p.1 i * s k * kernel (p.2 i - beta k)) := by
    apply Differentiable.sum
    intro i _
    apply Differentiable.sum
    intro k _
    exact ((hc i).mul_const (s k)).mul (hK.comp ((ht i).sub_const (beta k)))
  exact (hstudent.const_mul (1 / 2 : ℝ)).sub hteacher

theorem hasDerivAt_variableLoss_line
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => variableLoss s beta
      ((fun i => c i + t * dc i), (fun i => theta i + t * v i)))
      ((1 / 2 : ℝ) * (∑ i, ∑ j,
        ((dc i * c j + c i * dc j) * kernel (theta i - theta j) +
          c i * c j * (kernelD1 (theta i - theta j) * (v i - v j)))) -
        ∑ i, ∑ k, (dc i * s k * kernel (theta i - beta k) +
          c i * s k * (kernelD1 (theta i - beta k) * v i))) 0 := by
  have hc (i : Fin n) : HasDerivAt (fun t : ℝ => c i + t * dc i) (dc i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dc i)).const_add (c i)
  have ht (i : Fin n) : HasDerivAt (fun t : ℝ => theta i + t * v i) (v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (theta i)
  have hss := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun j _ =>
      ((hc i).mul (hc j)).mul
        ((hasDerivAt_kernel (theta i + 0 * v i - (theta j + 0 * v j))).comp 0
          ((ht i).sub (ht j)))))
  have hst := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ =>
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin m))) (fun k _ =>
      ((hc i).mul_const (s k)).mul
        ((hasDerivAt_kernel (theta i + 0 * v i - beta k)).comp 0
          ((ht i).sub_const (beta k)))))
  simpa [variableLoss] using (hss.const_mul (1 / 2 : ℝ)).sub hst

theorem fderiv_variableLoss_apply
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ) :
    fderiv ℝ (variableLoss s beta) (c, theta) (dc, v) =
      (1 / 2 : ℝ) * (∑ i, ∑ j,
        ((dc i * c j + c i * dc j) * kernel (theta i - theta j) +
          c i * c j * (kernelD1 (theta i - theta j) * (v i - v j)))) -
        ∑ i, ∑ k, (dc i * s k * kernel (theta i - beta k) +
          c i * s k * (kernelD1 (theta i - beta k) * v i)) := by
  have hc : HasDerivAt (fun t : ℝ => fun i => c i + t * dc i) dc 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dc i)).const_add (c i)
  have ht : HasDerivAt (fun t : ℝ => fun i => theta i + t * v i) v 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (theta i)
  have hf := (differentiable_variableLoss (n := n) s beta (c, theta)).hasFDerivAt
  have hf' : HasFDerivAt (variableLoss s beta)
      (fderiv ℝ (variableLoss s beta) (c, theta))
      ((fun i => c i + 0 * dc i), (fun i => theta i + 0 * v i)) := by simpa using hf
  have hcomp := hf'.comp_hasDerivAt 0 (hc.prod ht)
  exact hcomp.unique (hasDerivAt_variableLoss_line c dc theta v s beta)

/-- `rem:planar_residual_equivalence`: mass derivative. -/
theorem mass_partial (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (i : Fin n) :
    fderiv ℝ (variableLoss s beta) (c, theta) (Pi.single i 1, 0) =
      residual c theta s beta (theta i) := by
  classical
  rw [fderiv_variableLoss_apply]
  simp only [Pi.zero_apply, sub_self, mul_zero, add_zero]
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero, mul_zero]
  simp_rw [kernel_sub_swap _ (theta i)]
  unfold residual
  ring

/-- `rem:planar_residual_equivalence`: angular derivative. -/
theorem angle_partial (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (i : Fin n) :
    fderiv ℝ (variableLoss s beta) (c, theta) (0, Pi.single i 1) =
      c i * deriv (residual c theta s beta) (theta i) := by
  classical
  rw [fderiv_variableLoss_apply, (hasDerivAt_residual c theta s beta (theta i)).deriv]
  simp only [Pi.zero_apply, zero_mul, mul_zero, zero_add, add_zero]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  have hswap (j : Fin n) : kernelD1 (theta j - theta i) = -kernelD1 (theta i - theta j) := by
    rw [show theta j - theta i = -(theta i - theta j) by ring, kernelD1_neg]
  simp_rw [hswap]
  simp_rw [mul_comm _ (c i)]
  simp_rw [mul_neg, Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem mass_stationarity {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (hcrit : fderiv ℝ (variableLoss s beta) (c, theta) = 0) (i : Fin n) :
    residual c theta s beta (theta i) = 0 := by
  rw [← mass_partial, hcrit, ContinuousLinearMap.zero_apply]

/-- `lem:critical-points-are-double-zeros`, for each active slot individually. -/
theorem critical_point_double_zero {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (hcrit : fderiv ℝ (variableLoss s beta) (c, theta) = 0)
    (i : Fin n) (hi : c i ≠ 0) :
    residual c theta s beta (theta i) = 0 ∧
      deriv (residual c theta s beta) (theta i) = 0 := by
  refine ⟨mass_stationarity hcrit i, ?_⟩
  have h := angle_partial c theta s beta i
  rw [hcrit, ContinuousLinearMap.zero_apply] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hi

end PaperLeanFormalization.Planar



/-!
The line-count and gap-sign steps depend only on double zeros on the positive
net support. In particular, they do not assume a local minimum or invoke the
headline benignity theorem. The reduction below works even for signed raw
masses; the reduced positive and negative masses are positive by construction.
-/

open Real
open PaperLeanFormalization
open scoped BigOperators

noncomputable section

namespace PaperLeanFormalization.Planar

variable {n m : ℕ}

end PaperLeanFormalization.Planar


namespace PaperLeanFormalization.Planar

/-- The literal velocity of `lem:opposed-rotation`. -/
def opposedVelocity {n : ℕ} (c : Fin n → ℝ) (p q : Fin n) (i : Fin n) : ℝ :=
  if i = p then c q else if i = q then -c p else 0

/-- A weighted first-order sum along the opposed velocity has only two terms. -/
theorem weighted_opposed_sum {n : ℕ} (c f : Fin n → ℝ) {p q : Fin n}
    (hpq : p ≠ q) :
    (∑ i, c i * opposedVelocity c p q i * f i) =
      c p * c q * (f p - f q) := by
  classical
  have hsub : ({p, q} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_sdiff hsub, Finset.sum_pair hpq]
  have hz : (∑ i in Finset.univ \ {p, q}, c i * opposedVelocity c p q i * f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hi
    simp only [opposedVelocity, if_neg hi.2.1, if_neg hi.2.2, mul_zero, zero_mul]
  rw [hz]
  simp [opposedVelocity, hpq, hpq.symm]; ring

/-- The diagonal residual-curvature contribution of the opposed velocity. -/
theorem weighted_opposed_square_sum {n : ℕ} (c f : Fin n → ℝ) {p q : Fin n}
    (hpq : p ≠ q) :
    (∑ i, c i * opposedVelocity c p q i ^ 2 * f i) =
      c p * c q ^ 2 * f p + c q * c p ^ 2 * f q := by
  classical
  have hsub : ({p, q} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_sdiff hsub, Finset.sum_pair hpq]
  have hz : (∑ i in Finset.univ \ {p, q}, c i * opposedVelocity c p q i ^ 2 * f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hi
    simp [opposedVelocity, hi.2.1, hi.2.2]
  rw [hz]
  simp [opposedVelocity, hpq, hpq.symm]



end PaperLeanFormalization.Planar

open Filter
open scoped Topology
namespace PaperLeanFormalization.Planar
variable {n m : ℕ}

def kernelD2 (x : ℝ) : ℝ := 2 * |sin x| - kernel x

theorem hasDerivAt_kernelD1 (x : ℝ) : HasDerivAt kernelD1 (kernelD2 x) x :=
  KernelCalculus.hasDerivAt_angularKernel_first x

theorem kernelD2_neg (x : ℝ) : kernelD2 (-x) = kernelD2 x := by
  simp only [kernelD2, sin_neg, abs_neg, kernel_neg]

theorem residual_curvature_eq (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    Beam.finiteResidual kernelD2 c theta s beta x =
      deriv (deriv (residual c theta s beta)) x :=
  (Beam.finiteResidual_second_derivative kernel kernelD1 kernelD2
    hasDerivAt_kernel hasDerivAt_kernelD1 c theta s beta x).symm

theorem eq_diagonal_angle_hessian
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (i : Fin n) :
    2 * π * deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
      (fun j => theta j + t * (Pi.single i (1 : ℝ) : Fin n → ℝ) j))) 0 =
      c i * (deriv (deriv (residual c theta s beta)) (theta i) - c i * kernelD2 0) := by
  classical
  have h := (Beam.hasDerivAt_deriv_angular_finiteKernelLoss kernel kernelD1 kernelD2
    hasDerivAt_kernel hasDerivAt_kernelD1 kernelD1_neg kernelD2_neg
    c theta (Pi.single i 1) s beta).deriv
  rw [h]
  simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : 0 < (2 : ℕ)),
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero, sub_self]
  rw [residual_curvature_eq]
  field_simp [pi_ne_zero]
  ring

/-- Restricting the full finite angular quadratic form to the two nonzero
velocity coordinates gives exactly its diagonal and off-diagonal block. -/
theorem opposed_quadratic_form_two_by_two
    (c theta : Fin n → ℝ) (R J : ℝ → ℝ)
    {p q : Fin n} (hpq : p ≠ q) (hline : theta p = theta q) :
    ((∑ i, c i * opposedVelocity c p q i ^ 2 * R (theta i)) -
      ∑ i, ∑ j, c i * c j * opposedVelocity c p q i * opposedVelocity c p q j *
        J (theta i - theta j)) =
      c p * (R (theta p) - c p * J 0) * c q ^ 2 +
        2 * (-c p * c q * J 0) * c q * (-c p) +
        c q * (R (theta q) - c q * J 0) * c p ^ 2 := by
  have hgram : (∑ i, ∑ j, c i * c j * opposedVelocity c p q i *
      opposedVelocity c p q j * J (theta i - theta j)) =
      c p * c q * (c p * c q * (J (theta p - theta p) - J (theta p - theta q)) -
        c p * c q * (J (theta q - theta p) - J (theta q - theta q))) := by
    calc
      _ = ∑ i, c i * opposedVelocity c p q i *
          (∑ j, c j * opposedVelocity c p q j * J (theta i - theta j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [weighted_opposed_sum c _ hpq, weighted_opposed_sum c _ hpq,
          weighted_opposed_sum c _ hpq]
  rw [hgram, weighted_opposed_square_sum c _ hpq, hline]
  simp only [sub_self]
  ring

/-- `eq:opposed-rotation-computation`: the actual second variation equals
the two-by-two block of actual diagonal coordinate second derivatives. -/
theorem opposed_rotation_eq_coordinate_block
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {p q : Fin n} (hpq : p ≠ q) (hline : theta p = theta q) :
    2 * π * deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
      (fun i => theta i + t * opposedVelocity c p q i))) 0 =
      (2 * π * deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
        (fun i => theta i + t * (Pi.single p (1 : ℝ) : Fin n → ℝ) i))) 0) * c q ^ 2 +
      2 * (-c p * c q * kernelD2 0) * c q * (-c p) +
      (2 * π * deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
        (fun i => theta i + t * (Pi.single q (1 : ℝ) : Fin n → ℝ) i))) 0) * c p ^ 2 := by
  rw [eq_diagonal_angle_hessian, eq_diagonal_angle_hessian]
  have h := (Beam.hasDerivAt_deriv_angular_finiteKernelLoss kernel kernelD1 kernelD2
    hasDerivAt_kernel hasDerivAt_kernelD1 kernelD1_neg kernelD2_neg
    c theta (opposedVelocity c p q) s beta).deriv
  rw [h]
  have hblock := opposed_quadratic_form_two_by_two c theta
    (Beam.finiteResidual kernelD2 c theta s beta) kernelD2 hpq hline
  rw [residual_curvature_eq, residual_curvature_eq] at hblock
  rw [hblock]
  field_simp [pi_ne_zero]
  ring

/-- The final cancellation in `eq:opposed-rotation-computation` uses the
diagonal Hessian equation above, so both manuscript equations feed descent. -/
theorem eq_opposed_rotation_computation
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {p q : Fin n} (hpq : p ≠ q) (hline : theta p = theta q) :
    2 * π * deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
      (fun i => theta i + t * opposedVelocity c p q i))) 0 =
      c p * c q * (c p + c q) * deriv (deriv (residual c theta s beta)) (theta p) := by
  rw [opposed_rotation_eq_coordinate_block c theta s beta hpq hline,
    eq_diagonal_angle_hessian, eq_diagonal_angle_hessian, ← hline]
  ring

/-- Replacement body for the existing loss-level derivative theorem. This
routes its coefficient through both labeled manuscript computations. -/
theorem hasDerivAt_deriv_opposed_rotation
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {p q : Fin n} (hpq : p ≠ q) (hline : theta p = theta q) :
    HasDerivAt (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
      (fun i => theta i + t * opposedVelocity c p q i)))
      (c p * c q * (c p + c q) / (2 * π) *
        deriv (deriv (residual c theta s beta)) (theta p)) 0 := by
  have h := Beam.hasDerivAt_deriv_angular_finiteKernelLoss kernel kernelD1 kernelD2
    hasDerivAt_kernel hasDerivAt_kernelD1 kernelD1_neg kernelD2_neg
    c theta (opposedVelocity c p q) s beta
  have hvalue := eq_opposed_rotation_computation c theta s beta hpq hline
  rw [h.deriv] at hvalue
  rw [← mul_assoc, mul_one_div_cancel (mul_ne_zero (by norm_num) pi_ne_zero), one_mul] at hvalue
  convert h using 1
  rw [hvalue]
  ring
/-- The paper's opposed-rotation formula is the second derivative of the actual
normalized loss. It needs neither criticality nor positivity of other masses. -/
theorem eq_opposed_rotation_curvature
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {p q : Fin n} (hpq : p ≠ q) (hline : theta p = theta q) :
    deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
      (fun i => theta i + t * opposedVelocity c p q i))) 0 =
      c p * c q * (c p + c q) / (2 * π) *
        deriv (deriv (residual c theta s beta)) (theta p) :=
  (hasDerivAt_deriv_opposed_rotation c theta s beta hpq hline).deriv

/-- Both the positive scale and the teacher-only constant are explicit. -/
theorem finiteKernelLoss_eq_variableLoss
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    Beam.finiteKernelLoss kernel s beta c theta =
      variableLoss s beta (c, theta) / (2 * π) +
        (∑ k, ∑ l, s k * s l * kernel (beta k - beta l)) / (4 * π) := by
  unfold Beam.finiteKernelLoss variableLoss
  dsimp only
  ring

theorem opposed_rotation_not_local_min
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {p q : Fin n} (hpq : p ≠ q) (hline : theta p = theta q)
    (hp : 0 < c p) (hq : 0 < c q)
    (hcurvature : deriv (deriv (residual c theta s beta)) (theta p) < 0) :
    ¬ IsLocalMin (variableLoss s beta) (c, theta) := by
  intro hmin
  let path : ℝ → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun t => (c, fun i => theta i + t * opposedVelocity c p q i)
  have hpath : Continuous path := continuous_const.prod_mk (continuous_pi (fun i =>
    continuous_const.add (continuous_id.mul continuous_const)))
  have hbase : path 0 = (c, theta) := by simp [path]
  have hminpath : IsLocalMin (fun t => variableLoss s beta (path t)) 0 := by
    have hh : IsLocalMin (variableLoss s beta) (path 0) := by rw [hbase]; exact hmin
    exact hh.comp_continuous hpath.continuousAt
  let f : ℝ → ℝ := fun t => Beam.finiteKernelLoss kernel s beta c
    (fun i => theta i + t * opposedVelocity c p q i)
  have hminf : IsLocalMin f 0 := by
    apply hminpath.mono
    intro t ht
    dsimp only [f]
    rw [finiteKernelLoss_eq_variableLoss, finiteKernelLoss_eq_variableLoss]
    exact add_le_add_right ((div_le_div_right (by positivity : 0 < 2 * π)).mpr ht) _
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t := by
    filter_upwards [] with t
    have h := (Beam.hasDerivAt_finiteKernelLoss_line kernel kernelD1 hasDerivAt_kernel
      c (fun _ => 0) theta (opposedVelocity c p q) s beta t).differentiableAt
    simpa only [mul_zero, add_zero] using h
  have hsecond := hasDerivAt_deriv_opposed_rotation c theta s beta hpq hline
  have hnegative : c p * c q * (c p + c q) / (2 * π) *
      deriv (deriv (residual c theta s beta)) (theta p) < 0 :=
    mul_neg_of_pos_of_neg (div_pos (mul_pos (mul_pos hp hq) (add_pos hp hq))
      (by positivity)) hcurvature
  exact Preliminaries.negative_second_derivative_not_local_min hdiff
    hminf.deriv_eq_zero hsecond hnegative hminf


end PaperLeanFormalization.Planar

namespace PaperLeanFormalization.Planar

open Gaps

theorem rotated_residual {n m : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (a x : ℝ) :
    BeamGapKernel.residual c (fun i => relativeAngle a (theta i))
      s (fun k => relativeAngle a (beta k)) x = residual c theta s beta (a + x) :=
  periodic_residual_rotate BeamGapKernel.kernel BeamGapKernel.kernel_add_pi c theta s beta a x

theorem rotated_torque {n m : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (a x : ℝ) :
    BeamGapKernel.residualTorque c (fun i => relativeAngle a (theta i))
      s (fun k => relativeAngle a (beta k)) x = BeamGapKernel.residualTorque c theta s beta (a + x) :=
  periodic_residual_rotate BeamGapKernel.torque BeamGapKernel.torque_add_pi c theta s beta a x

theorem rotated_curvature {n m : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (a x : ℝ) :
    (∑ i, c i * BeamGapKernel.curvature (x - relativeAngle a (theta i))) -
      ∑ k, s k * BeamGapKernel.curvature (x - relativeAngle a (beta k)) =
    (∑ i, c i * BeamGapKernel.curvature (a + x - theta i)) -
      ∑ k, s k * BeamGapKernel.curvature (a + x - beta k) :=
  periodic_residual_rotate BeamGapKernel.curvature BeamGapKernel.curvature_add_pi c theta s beta a x

theorem residual_periodic {n m : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (x : ℝ) : residual c theta s beta (x + π) = residual c theta s beta x := by
  unfold residual
  simp_rw [show ∀ t, x + π - t = (x - t) + π by intro t; ring]
  simp only [show ∀ t, kernel (t + π) = kernel t from BeamGapKernel.kernel_add_pi]

theorem torque_periodic {n m : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (x : ℝ) :
    BeamGapKernel.residualTorque c theta s beta (x + π) = BeamGapKernel.residualTorque c theta s beta x := by
  unfold BeamGapKernel.residualTorque
  simp_rw [show ∀ t, x + π - t = (x - t) + π by intro t; ring,
    BeamGapKernel.torque_add_pi]

/-- `stp:green-function`: the actual residual supplies the two clamped
equations, after choosing a sorted projective-circle gap. -/
theorem ordered_gap_local_double_zeros {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (g : Fin (r + 1)) :
    let l := rightEndpoint theta g - theta g
    let th := fun i => relativeAngle (theta g) (theta i)
    let be := fun k => relativeAngle (theta g) (beta k)
    BeamGapKernel.residual c th s be 0 = 0 ∧
    BeamGapKernel.residualTorque c th s be 0 = 0 ∧
    BeamGapKernel.residual c th s be l = 0 ∧
    BeamGapKernel.residualTorque c th s be l = 0 := by
  dsimp only
  have heq : theta g + (rightEndpoint theta g - theta g) = rightEndpoint theta g := by ring
  simp only [rotated_residual, rotated_torque, add_zero, heq, hzero, htorque, true_and]
  exact ⟨periodic_rightEndpoint_zero theta (residual c theta s beta)
    (residual_periodic c theta s beta) hzero g,
    periodic_rightEndpoint_zero theta (BeamGapKernel.residualTorque c theta s beta)
    (torque_periodic c theta s beta) htorque g⟩

theorem ordered_gap_clamps {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (g : Fin (r + 1)) :
    let l := rightEndpoint theta g - theta g
    let th := fun i => relativeAngle (theta g) (theta i)
    let be := fun k => relativeAngle (theta g) (beta k)
    let T := Finset.univ.filter (fun k => 0 < be k ∧ be k < l)
    let U := BeamGapKernel.gapU c th s be
    let V := BeamGapKernel.gapV c th s be
    (U * psi l + V * chi l = 2 * ∑ k in T, s k * psi (l - be k)) ∧
    (U * chi l + V * (sin l + l * cos l) = 2 * ∑ k in T, s k * chi (l - be k)) ∧
    ∀ x, 0 ≤ x → x ≤ l → residual c theta s beta (theta g + x) = response T be s U V x := by
  dsimp only
  have hl := gap_length_range theta hmono htheta g
  have hth (i) := relativeAngle_range (htheta g) (htheta i)
  have hbe (k) := relativeAngle_range (htheta g) (hbeta k)
  have hright := periodic_rightEndpoint_zero theta (residual c theta s beta)
    (residual_periodic c theta s beta) hzero g
  have hrightTorque := periodic_rightEndpoint_zero theta (BeamGapKernel.residualTorque c theta s beta)
    (torque_periodic c theta s beta) htorque g
  have heq : theta g + (rightEndpoint theta g - theta g) = rightEndpoint theta g := by ring
  have hh := BeamGapKernel.critical_gap_clamps c (fun i => relativeAngle (theta g) (theta i))
    s (fun k => relativeAngle (theta g) (beta k)) hl.1 hl.2
    (fun i => ⟨(hth i).1, (hth i).2.le⟩) (positive_nodes_outside_local_gap theta hmono htheta g)
    (fun k => ⟨(hbe k).1, (hbe k).2.le⟩)
    (by rw [rotated_residual, add_zero]; exact hzero g)
    (by rw [rotated_torque, add_zero]; exact htorque g)
    (by rw [rotated_residual, heq]; exact hright)
    (by rw [rotated_torque, heq]; exact hrightTorque)
  refine ⟨hh.1, hh.2.1, ?_⟩
  intro x hx hxl
  simpa only [rotated_residual] using hh.2.2 x hx hxl

end PaperLeanFormalization.Planar

namespace PaperLeanFormalization.BeamGapKernel

/-- A critical clean gap with exactly one teacher has the four literal
residual endpoint jets used by the cyclic beam. -/
theorem single_teacher_gap_jets {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (k : Fin m)
    {l : ℝ} (hl0 : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ j, 0 ≤ beta j ∧ beta j ≤ π)
    (hT : Finset.univ.filter (fun j => 0 < beta j ∧ beta j < l) = {k})
    (hzero : residual c theta s beta 0 = 0)
    (hslopeZero : residualTorque c theta s beta 0 = 0)
    (hend : residual c theta s beta l = 0)
    (hslopeEnd : residualTorque c theta s beta l = 0) :
    ((∑ i, c i * curvature (-theta i)) - ∑ j, s j * curvature (-beta j)) =
        -4 * s k * Beam.m0 l (beta k) ∧
    ((∑ i, c i * curvature (l - theta i)) - ∑ j, s j * curvature (l - beta j)) =
        -4 * s k * Beam.ml l (beta k) ∧
    ((∑ i, c i * cutJerkRight 0 (theta i)) - ∑ j, s j * cutJerkRight 0 (beta j)) =
        -4 * s k * Beam.j0 l (beta k) ∧
    ((∑ i, c i * cutJerkLeft l (theta i)) - ∑ j, s j * cutJerkLeft l (beta j)) =
        -4 * s k * Beam.jl l (beta k) := by
  classical
  have hk : 0 < beta k ∧ beta k < l := by
    have hm : k ∈ Finset.univ.filter (fun j => 0 < beta j ∧ beta j < l) := by
      rw [hT]
      exact Finset.mem_singleton_self k
    exact (Finset.mem_filter.mp hm).2
  obtain ⟨hvalue, hslope, _⟩ := critical_gap_clamps c theta s beta hl0 hlpi
    htheta hgap hbeta hzero hslopeZero hend hslopeEnd
  rw [hT, Finset.sum_singleton] at hvalue hslope
  have hdet : Beam.determinant l ≠ 0 := (Beam.determinant_pos hl0 hlpi).ne'
  have hv : Beam.leftBranch (gapU c theta s beta) (gapV c theta s beta) l =
      2 * s k * Beam.psi (l - beta k) := by
    change gapU c theta s beta * psi l + gapV c theta s beta * chi l = _
    rw [hvalue]
    change 2 * (s k * psi (l - beta k)) = 2 * s k * psi (l - beta k)
    ring
  have hs : Beam.leftSlope (gapU c theta s beta) (gapV c theta s beta) l =
      2 * s k * Beam.chi (l - beta k) := by
    change gapU c theta s beta * chi l + gapV c theta s beta * (sin l + l * cos l) = _
    rw [hslope]
    change 2 * (s k * chi (l - beta k)) = 2 * s k * chi (l - beta k)
    ring
  obtain ⟨hU, hV⟩ := Beam.clamped_coefficients hdet hv hs
  obtain ⟨hcurv0, hjerk0⟩ := critical_gap_initial_jets c theta s beta hl0 hlpi
    htheta hgap hbeta hzero hslopeZero
  have hbefore : ∀ j, ¬(0 < beta j ∧ beta j ≤ 0) := fun j h => (not_lt_of_ge h.2) h.1
  have hval0 := residual_gap_causal c theta s beta (show 0 ≤ (0 : ℝ) by rfl)
    hl0.le hlpi htheta hgap hbeta
  simp only [if_neg (hbefore _), mul_zero, Finset.sum_const_zero, sub_zero] at hval0
  have hsmooth0 : smoothResidual c theta s beta 0 = 0 := hval0.symm.trans hzero
  have htor0 := residual_torque_gap_causal c theta s beta (show 0 ≤ (0 : ℝ) by rfl)
    hl0.le hlpi htheta hgap hbeta
  simp only [if_neg (hbefore _), mul_zero, Finset.sum_const_zero, sub_zero] at htor0
  have hsmooth1 : smoothSlope c theta s beta 0 = 0 := htor0.symm.trans hslopeZero
  obtain ⟨hcurvl, hjerkl⟩ := Beam.right_endpoint_jets hdet hv hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcurv0, hV]
    ring
  · rw [actual_curvature_gap c theta s beta hl0.le le_rfl hlpi htheta hgap hbeta,
      hT, Finset.sum_singleton, if_pos hk.2.le,
      smoothCurvature_expansion, hsmooth0, hsmooth1]
    simpa only [neg_zero, zero_mul, zero_sub, sub_zero, zero_add,
      psiD2, psiD3, Beam.leftCurvature, mul_assoc] using hcurvl
  · rw [hjerk0, hU]
    ring
  · rw [actual_left_jerk_endpoint c theta s beta hl0 (fun i => (htheta i).1)
      hgap (fun j => (hbeta j).1), hT, Finset.sum_singleton,
      smoothJerk_expansion, hsmooth0, hsmooth1]
    simpa only [zero_mul, sub_zero, zero_add, psiD3, chiD3, Beam.leftJerk, mul_assoc] using hjerkl

/-- Once the two adjacent gap computations meet at the same actual student
cut, the network's own finite-sum jump supplies the mass relation. -/
theorem student_mass_from_adjacent_residual_jets {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hinj : Function.Injective theta) (i : Fin n)
    (hsep : ∀ k, beta k ≠ theta i)
    {sigmaPrev sigma lPrev pPrev l p : ℝ}
    (hleft : ((∑ j, c j * cutJerkLeft (theta i) (theta j)) -
      ∑ k, s k * cutJerkLeft (theta i) (beta k)) = -4 * sigmaPrev * Beam.jl lPrev pPrev)
    (hright : ((∑ j, c j * cutJerkRight (theta i) (theta j)) -
      ∑ k, s k * cutJerkRight (theta i) (beta k)) = -4 * sigma * Beam.j0 l p) :
    c i = sigmaPrev * Beam.jl lPrev pPrev - sigma * Beam.j0 l p := by
  classical
  have hmass : Planar.netWeight c theta s beta (theta i) = c i := by
    rw [(Planar.eq_net_weight_main c theta s beta (theta i)).1]
    simp only [Finset.sum_filter, hinj.eq_iff, if_neg (hsep _), Finset.sum_const_zero,
      sub_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hjump := Planar.eq_LFC_jump c theta s beta (theta i)
  rw [hmass] at hjump
  simp_rw [Planar.third_derivative_principal_branch] at hjump
  change ((∑ j, c j * cutJerkRight (theta i) (theta j)) -
      ∑ k, s k * cutJerkRight (theta i) (beta k)) -
    ((∑ j, c j * cutJerkLeft (theta i) (theta j)) -
      ∑ k, s k * cutJerkLeft (theta i) (beta k)) = 4 * c i at hjump
  rw [hleft, hright] at hjump
  linarith only [hjump]

end PaperLeanFormalization.BeamGapKernel

namespace PaperLeanFormalization.Planar

theorem sum_sorted {r : ℕ} (S : Finset ℝ) (hcard : S.card = r) (f : ℝ → ℝ) :
    (∑ i : Fin r, f (S.orderEmbOfFin hcard i)) = ∑ x in S, f x := by
  classical
  have he : (Finset.univ : Finset (Fin r)).image (S.orderEmbOfFin hcard) = S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact (show (∃ i, S.orderEmbOfFin hcard i = x) ↔ x ∈ S from by
      rw [← Set.mem_range, Finset.range_orderEmbOfFin, Finset.mem_coe])
  calc
    (∑ i : Fin r, f (S.orderEmbOfFin hcard i)) =
        ∑ x in Finset.univ.image (S.orderEmbOfFin hcard), f x :=
      (Finset.sum_image (fun _ _ _ _ h => (S.orderEmbOfFin hcard).injective h)).symm
    _ = ∑ x in S, f x := congrArg (fun T : Finset ℝ => ∑ x in T, f x) he

/-- Collect signed atoms once, discard zero net masses, and enumerate the two
remaining signs. This single finite-sum identity is the only net reduction. -/
theorem residual_eq_signed_sorted {n m r : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (hcard : (positiveLines c theta s beta).card = r) :
    residual c theta s beta =
      residual (fun i => netWeight c theta s beta ((positiveLines c theta s beta).orderEmbOfFin hcard i))
        ((positiveLines c theta s beta).orderEmbOfFin hcard)
        (fun k => -netWeight c theta s beta ((negativeLines c theta s beta).orderEmbOfFin rfl k))
        ((negativeLines c theta s beta).orderEmbOfFin rfl) := by
  classical
  ext x
  rw [residual_eq_sum_netWeight]
  unfold residual
  rw [sum_sorted (positiveLines c theta s beta) hcard
    (fun t => netWeight c theta s beta t * kernel (x - t)),
    sum_sorted (negativeLines c theta s beta) rfl
    (fun t => -netWeight c theta s beta t * kernel (x - t))]
  unfold positiveLines negativeLines
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rcases lt_trichotomy (netWeight c theta s beta t) 0 with hn | hz | hp
  · simp [hn, not_lt_of_ge hn.le]
  · simp [hz]
  · simp [hp, not_lt_of_ge hp.le]

theorem signed_sorted_ranges {n m r : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (hcard : (positiveLines c theta s beta).card = r)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π) :
    (∀ i, 0 ≤ (positiveLines c theta s beta).orderEmbOfFin hcard i ∧
      (positiveLines c theta s beta).orderEmbOfFin hcard i < π) ∧
    (∀ k, 0 ≤ (negativeLines c theta s beta).orderEmbOfFin rfl k ∧
      (negativeLines c theta s beta).orderEmbOfFin rfl k < π) := by
  have hrange : ∀ x ∈ Finset.univ.image theta ∪ Finset.univ.image beta, 0 ≤ x ∧ x < π := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact htheta i
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact hbeta k
  exact ⟨fun i => hrange _ (Finset.mem_filter.mp
    (Finset.orderEmbOfFin_mem (positiveLines c theta s beta) hcard i)).1,
    fun k => hrange _ (Finset.mem_filter.mp
    (Finset.orderEmbOfFin_mem (negativeLines c theta s beta) rfl k)).1⟩

end PaperLeanFormalization.Planar


namespace PaperLeanFormalization.Planar.Gaps

/-- The arguments of right-hand kernel jets are unchanged by rotation.
No periodicity of the branch function is needed. -/
theorem right_cut_rotation_argument {a b t : ℝ}
    (ha : 0 ≤ a ∧ a < π) (hb : 0 ≤ b ∧ b < π) (ht : 0 ≤ t ∧ t < π) :
    (if relativeAngle a t ≤ relativeAngle a b
      then relativeAngle a b - relativeAngle a t
      else relativeAngle a b - relativeAngle a t + π) =
      (if t ≤ b then b - t else b - t + π) := by
  unfold relativeAngle
  split_ifs <;> linarith [ha.1, ha.2, hb.1, hb.2, ht.1, ht.2]

/-- Left-hand jets use the strict inequality, hence use the π branch at the
atom itself. This identity also holds when the rotation point equals the cut. -/
theorem left_cut_rotation_argument {a b t : ℝ}
    (ha : 0 ≤ a ∧ a < π) (hb : 0 ≤ b ∧ b < π) (ht : 0 ≤ t ∧ t < π) :
    (if relativeAngle a t < relativeAngle a b
      then relativeAngle a b - relativeAngle a t
      else relativeAngle a b - relativeAngle a t + π) =
      (if t < b then b - t else b - t + π) := by
  unfold relativeAngle
  split_ifs <;> linarith [ha.1, ha.2, hb.1, hb.2, ht.1, ht.2]

theorem right_cut_at_zero_rotation_argument {a t : ℝ}
    (ha : 0 ≤ a ∧ a < π) (ht : 0 ≤ t ∧ t < π) :
    (if relativeAngle a t ≤ 0 then 0 - relativeAngle a t else 0 - relativeAngle a t + π) =
      (if t ≤ a then a - t else a - t + π) := by
  simpa only [relativeAngle, lt_self_iff_false, if_false, sub_self] using
    right_cut_rotation_argument ha ha ht

theorem right_cut_rotate (B : ℝ → ℝ) {a b t : ℝ}
    (ha : 0 ≤ a ∧ a < π) (hb : 0 ≤ b ∧ b < π) (ht : 0 ≤ t ∧ t < π) :
    B (if relativeAngle a t ≤ relativeAngle a b
      then relativeAngle a b - relativeAngle a t
      else relativeAngle a b - relativeAngle a t + π) =
      B (if t ≤ b then b - t else b - t + π) :=
  congrArg B (right_cut_rotation_argument ha hb ht)

theorem left_cut_rotate (B : ℝ → ℝ) {a b t : ℝ}
    (ha : 0 ≤ a ∧ a < π) (hb : 0 ≤ b ∧ b < π) (ht : 0 ≤ t ∧ t < π) :
    B (if relativeAngle a t < relativeAngle a b
      then relativeAngle a b - relativeAngle a t
      else relativeAngle a b - relativeAngle a t + π) =
      B (if t < b then b - t else b - t + π) :=
  congrArg B (left_cut_rotation_argument ha hb ht)

theorem cyclic_successor_ne_self {r : ℕ} (hr : 0 < r) (g : Fin (r + 1)) :
    g + 1 ≠ g := by
  intro h
  have hzero : (1 : Fin (r + 1)) = 0 :=
    add_left_cancel (show g + 1 = g + 0 by simpa using h)
  have hcard := Fin.one_eq_zero_iff.mp hzero
  omega (config := {})

theorem cyclic_successor_eq_next {r : ℕ} (g : Fin (r + 1))
    (hn : g.val + 1 < r + 1) : g + 1 = ⟨g.val + 1, hn⟩ := by
  apply Fin.ext
  exact Fin.val_add_one_of_lt (show g < Fin.last r from Nat.lt_of_succ_lt_succ hn)

theorem cyclic_successor_eq_zero_of_last {r : ℕ} (g : Fin (r + 1))
    (hn : ¬g.val + 1 < r + 1) : g + 1 = 0 := by
  have hg : g = Fin.last r := by
    apply Fin.ext
    change g.val = r
    exact Nat.le_antisymm (Nat.le_of_lt_succ g.isLt)
      (Nat.le_of_not_gt (fun h => hn (Nat.succ_lt_succ h)))
  rw [hg, Fin.last_add_one]

/-- For at least two nodes the positive gap length is the relative angle to
the cyclic successor, including the wrap gap. -/
theorem gap_length_eq_relative_successor {r : ℕ} (hr : 0 < r)
    (angle : Fin (r + 1) → ℝ) (hangle : StrictMono angle) (g : Fin (r + 1)) :
    rightEndpoint angle g - angle g = relativeAngle (angle g) (angle (g + 1)) := by
  by_cases hn : g.val + 1 < r + 1
  · have hlt : angle g < angle ⟨g.val + 1, hn⟩ :=
      hangle (show g < (⟨g.val + 1, hn⟩ : Fin (r + 1)) from Nat.lt_succ_self _)
    rw [rightEndpoint, dif_pos hn, cyclic_successor_eq_next g hn,
      relativeAngle, if_neg (not_lt_of_ge hlt.le)]
  · have hgpos : (0 : Fin (r + 1)) < g := by
      have hbound := g.isLt
      show 0 < g.val
      omega (config := {})
    rw [rightEndpoint, dif_neg hn, cyclic_successor_eq_zero_of_last g hn,
      relativeAngle, if_pos (hangle hgpos)]

/-- Periodic evaluations of the lifted right endpoint agree with those at
the cyclic successor. The statement also covers singleton support. -/
theorem periodic_rightEndpoint_eq_successor {r : ℕ} (angle : Fin (r + 1) → ℝ)
    (f : ℝ → ℝ) (hperiod : ∀ x, f (x + π) = f x) (g : Fin (r + 1)) :
    f (rightEndpoint angle g) = f (angle (g + 1)) := by
  by_cases hn : g.val + 1 < r + 1
  · rw [rightEndpoint, dif_pos hn, cyclic_successor_eq_next g hn]
  · rw [rightEndpoint, dif_neg hn, cyclic_successor_eq_zero_of_last g hn, hperiod]

end PaperLeanFormalization.Planar.Gaps

namespace PaperLeanFormalization.Planar

open Gaps

/-- The actual second angular derivative, written as its literal finite sum. -/
def actualCurvature {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) : ℝ :=
  (∑ i, c i * BeamGapKernel.curvature (x - theta i)) -
    ∑ k, s k * BeamGapKernel.curvature (x - beta k)

/-- The two endpoint formulas are consequences of the actual residual and
torque zero, together with the explicitly solved far-end clamp equations. -/
theorem actual_clean_gap_endpoint_curvatures {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) {l : ℝ}
    (hl : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π)
    (hzero : BeamGapKernel.residual c theta s beta 0 = 0)
    (htorque : BeamGapKernel.residualTorque c theta s beta 0 = 0)
    (hvalue : BeamGapKernel.gapU c theta s beta * psi l +
        BeamGapKernel.gapV c theta s beta * chi l =
      2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l), s k * psi (l - beta k))
    (hslope : BeamGapKernel.gapU c theta s beta * chi l +
        BeamGapKernel.gapV c theta s beta * (sin l + l * cos l) =
      2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l), s k * chi (l - beta k)) :
    actualCurvature c theta s beta 0 =
        -(∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          4 * s k * moment l (beta k) / det l) ∧
      actualCurvature c theta s beta l =
        -(∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          4 * s k * moment l (l - beta k) / det l) := by
  classical
  have hd := ne_of_gt (det_positive hl hlpi)
  constructor
  · have hi := (BeamGapKernel.critical_gap_initial_jets c theta s beta hl hlpi
      htheta hgap hbeta hzero htorque).1
    have hf := clamped_left_curvature_formula
      (Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l)) beta s l
      (BeamGapKernel.gapU c theta s beta) (BeamGapKernel.gapV c theta s beta) hd hvalue hslope
    simpa only [actualCurvature, zero_sub] using hi.trans hf
  · have hbefore : ∀ k, ¬(0 < beta k ∧ beta k ≤ 0) := fun k h => (not_lt_of_ge h.2) h.1
    have hv := BeamGapKernel.residual_gap_causal c theta s beta (le_refl (0 : ℝ))
      hl.le hlpi htheta hgap hbeta
    simp only [if_neg (hbefore _), mul_zero, Finset.sum_const_zero, sub_zero] at hv
    have hv0 : BeamGapKernel.smoothResidual c theta s beta 0 = 0 := hv.symm.trans hzero
    have ht := BeamGapKernel.residual_torque_gap_causal c theta s beta (le_refl (0 : ℝ))
      hl.le hlpi htheta hgap hbeta
    simp only [if_neg (hbefore _), mul_zero, Finset.sum_const_zero, sub_zero] at ht
    have ht0 : BeamGapKernel.smoothSlope c theta s beta 0 = 0 := ht.symm.trans htorque
    have hc := BeamGapKernel.actual_curvature_gap c theta s beta hl.le (le_refl l)
      hlpi htheta hgap hbeta
    have hsum :
        (∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          s k * (if beta k ≤ l then BeamGapKernel.psiD2 (l - beta k) else 0)) =
        ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
          s k * BeamGapKernel.psiD2 (l - beta k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (Finset.mem_filter.mp hk).2.2.le]
    rw [hsum, BeamGapKernel.smoothCurvature_expansion, hv0, ht0] at hc
    have hf := clamped_right_curvature_formula
      (Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l)) beta s l
      (BeamGapKernel.gapU c theta s beta) (BeamGapKernel.gapV c theta s beta) hd hvalue hslope
    calc
      actualCurvature c theta s beta l =
          BeamGapKernel.gapU c theta s beta * (sin l + l * cos l) +
            BeamGapKernel.gapV c theta s beta * (2 * cos l - l * sin l) -
              2 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
                s k * (sin (l - beta k) + (l - beta k) * cos (l - beta k)) := by
        simpa only [actualCurvature, BeamGapKernel.psiD2, BeamGapKernel.psiD3,
          zero_mul, neg_zero, sub_zero, zero_sub, zero_add] using hc
      _ = _ := hf

/-- Rotating an ordered genuine configuration into one clean gap supplies
the actual left and right endpoint curvature sums. -/
theorem second_derivative_eq_actualCurvature {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    deriv (deriv (residual c theta s beta)) x = actualCurvature c theta s beta x := by
  rw [residual_second_derivative]
  unfold actualCurvature BeamGapKernel.curvature
  change 2 * ((∑ i, c i * |sin (x - theta i)|) - ∑ k, s k * |sin (x - beta k)|) -
      ((∑ i, c i * kernel (x - theta i)) - ∑ k, s k * kernel (x - beta k)) =
    (∑ i, c i * (2 * |sin (x - theta i)| - kernel (x - theta i))) -
      ∑ k, s k * (2 * |sin (x - beta k)| - kernel (x - beta k))
  simp_rw [mul_sub, Finset.sum_sub_distrib, mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]
  ring


theorem green_zero_left {l p : ℝ} (hp : 0 < p) : green l p 0 = 0 := by
  simp [green, hp.le, numerator, psi, chi]

theorem green_zero_right {l p : ℝ} (hpl : p < l) : green l p l = 0 := by
  simp [green, not_le.mpr hpl, numerator, moment, jerk, psi, chi]

/-- The Green function in the local manuscript lemma takes values in the
nonnegative reals on the entire closed gap. -/
theorem green_nonnegative_closed {l p x : ℝ} (hp : 0 < p) (hpl : p < l)
    (hlpi : l ≤ π) (hx0 : 0 ≤ x) (hxl : x ≤ l) : 0 ≤ green l p x := by
  by_cases hx : x = 0
  · rw [hx, green_zero_left hp]
  by_cases hx : x = l
  · rw [hx, green_zero_right hpl]
  exact (green_positive (lt_of_le_of_ne hx0 (Ne.symm ‹x ≠ 0›))
    (lt_of_le_of_ne hxl hx) hp hpl hlpi).le

/-- `eq:gap-green-representation`, under double-zero conditions at this gap's
two endpoints only. No stationarity at any other student line is required. -/
theorem eq_gap_green_representation {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) {l : ℝ}
    (hl : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π)
    (hzero : residual c theta s beta 0 = 0)
    (htorque : BeamGapKernel.residualTorque c theta s beta 0 = 0)
    (hend : residual c theta s beta l = 0)
    (htorqueEnd : BeamGapKernel.residualTorque c theta s beta l = 0)
    (x : ℝ) (hx0 : 0 ≤ x) (hxl : x ≤ l) :
    residual c theta s beta x =
      -4 * ∑ k in Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l),
        s k * green l (beta k) x := by
  have hh := BeamGapKernel.critical_gap_clamps c theta s beta hl hlpi
    htheta hgap hbeta hzero htorque hend htorqueEnd
  change residual c theta s beta x = _
  have hrepr : residual c theta s beta x =
      response (Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l)) beta s
        (BeamGapKernel.gapU c theta s beta) (BeamGapKernel.gapV c theta s beta) x :=
    hh.2.2 x hx0 hxl
  rw [hrepr]
  exact stp_green_representation _ beta s l _ _
    (ne_of_gt (det_positive hl hlpi)) hh.1 hh.2.1 x

private theorem left_first (l p x : ℝ) :
    HasDerivAt (fun x => numerator l p x / (2 * det l))
      ((moment l p * (sin x + x * cos x) - jerk l p * chi x) / (2 * det l)) x := by
  exact (((chi_derivative x).const_mul (moment l p)).sub
    ((psi_derivative x).const_mul (jerk l p))).div_const (2 * det l)

private theorem left_second (l p x : ℝ) :
    HasDerivAt (fun x => (moment l p * (sin x + x * cos x) - jerk l p * chi x) / (2 * det l))
      ((moment l p * (2 * cos x - x * sin x) - jerk l p * (sin x + x * cos x)) /
        (2 * det l)) x := by
  have h : HasDerivAt (fun x : ℝ => sin x + x * cos x) (2 * cos x - x * sin x) x := by
    convert (hasDerivAt_sin x).add ((hasDerivAt_id x).mul (hasDerivAt_cos x)) using 1;
      dsimp; ring
  exact ((h.const_mul (moment l p)).sub ((chi_derivative x).const_mul (jerk l p))).div_const _

/-- The actual second derivative at the clamped left endpoint, obtained from
the smooth branch on a neighborhood of zero, not a formal jet declaration. -/
theorem green_second_derivative_zero {l p : ℝ} (hdet : det l ≠ 0) (hp : 0 < p) :
    deriv (deriv (green l p)) 0 = moment l p / det l := by
  have heq : green l p =ᶠ[𝓝 0] (fun x => numerator l p x / (2 * det l)) := by
    filter_upwards [eventually_lt_nhds hp] with x hx
    exact if_pos hx.le
  have hd : deriv (fun x => numerator l p x / (2 * det l)) =
      fun x => (moment l p * (sin x + x * cos x) - jerk l p * chi x) / (2 * det l) :=
    funext (fun x => (left_first l p x).deriv)
  rw [heq.deriv.deriv_eq, hd, (left_second l p 0).deriv]
  simp only [sin_zero, cos_zero, mul_one, zero_mul, sub_zero, zero_add, mul_zero]
  field_simp
  ring

/-- The actual right-end derivative uses the causal continuation and the
reflected-moment identity; it includes the full-period gap. -/
theorem green_second_derivative_right {l p : ℝ} (hdet : det l ≠ 0) (hpl : p < l) :
    deriv (deriv (green l p)) l = moment l (l - p) / det l := by
  let R := fun x => numerator l p x / (2 * det l) + psi (x - p) / 2
  let R1 := fun x =>
    (moment l p * (sin x + x * cos x) - jerk l p * chi x) / (2 * det l) + chi (x - p) / 2
  have heq : green l p =ᶠ[𝓝 l] R := by
    filter_upwards [eventually_gt_nhds hpl] with x hx
    dsimp [green, R]
    rw [if_neg (not_le.mpr hx), ← numerator_reciprocity_of_adjoint hdet]
    field_simp
    ring
  have hfirst (x : ℝ) : HasDerivAt R (R1 x) x := by
    convert (left_first l p x).add
      (((psi_derivative (x - p)).comp x ((hasDerivAt_id x).sub_const p)).div_const 2) using 1;
      simp [R, R1]
  have hsecond : HasDerivAt R1
      ((moment l p * (2 * cos l - l * sin l) - jerk l p * (sin l + l * cos l)) /
        (2 * det l) + (sin (l - p) + (l - p) * cos (l - p)) / 2) l := by
    convert (left_second l p l).add
      (((chi_derivative (l - p)).comp l ((hasDerivAt_id l).sub_const p)).div_const 2) using 1;
      simp [R1]
  have hd : deriv R = R1 := funext (fun x => (hfirst x).deriv)
  rw [heq.deriv.deriv_eq, hd, hsecond.deriv]
  have hid : moment l p * (2 * cos l - l * sin l) - jerk l p * (sin l + l * cos l) +
      det l * (sin (l - p) + (l - p) * cos (l - p)) = 2 * moment l (l - p) := by
    linear_combination -right_curvature_identity l p
  calc
    _ = (moment l p * (2 * cos l - l * sin l) - jerk l p * (sin l + l * cos l) +
        det l * (sin (l - p) + (l - p) * cos (l - p))) / (2 * det l) := by
      field_simp [hdet]
      ring
    _ = _ := by rw [hid]; field_simp [hdet]; ring

/-- `eq:green-endpoint-curvatures`: actual second derivatives, reflection,
and both strict signs for every clamped gap up to a full period. -/
theorem eq_green_endpoint_curvatures {l p : ℝ}
    (hp : 0 < p) (hpl : p < l) (hlpi : l ≤ π) :
    deriv (deriv (green l p)) 0 = moment l p / det l ∧
      0 < deriv (deriv (green l p)) 0 ∧
      deriv (deriv (green l p)) l = deriv (deriv (green l (l - p))) 0 ∧
      deriv (deriv (green l p)) l = moment l (l - p) / det l ∧
      0 < deriv (deriv (green l p)) l := by
  have hd := det_positive (lt_trans hp hpl) hlpi
  have hleft := green_second_derivative_zero hd.ne' hp
  have hright := green_second_derivative_right hd.ne' hpl
  have href := green_second_derivative_zero hd.ne' (sub_pos.mpr hpl)
  exact ⟨hleft, by rw [hleft]; exact div_pos (moment_positive hp hpl hlpi) hd,
    hright.trans href.symm, hright, by
      rw [hright]
      exact div_pos (moment_positive (sub_pos.mpr hpl) (by linarith) hlpi) hd⟩

/-- `eq:green-sign-claims`: strict interior positivity of the clamped Green
function together with both strict endpoint curvatures. -/
theorem eq_green_sign_claims {l p : ℝ}
    (hp : 0 < p) (hpl : p < l) (hlpi : l ≤ π) :
    (∀ x, 0 < x → x < l → 0 < green l p x) ∧
      0 < deriv (deriv (green l p)) 0 ∧ 0 < deriv (deriv (green l p)) l :=
  ⟨fun _ hx hxl => green_positive hx hxl hp hpl hlpi,
    (eq_green_endpoint_curvatures hp hpl hlpi).2.1,
    (eq_green_endpoint_curvatures hp hpl hlpi).2.2.2.2⟩

/-- `eq:gap-second-derivative-green`, with actual derivatives of both the
residual and the Green function, and the symmetric endpoint identity too. -/
theorem eq_gap_second_derivative_green {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) {l : ℝ}
    (hl : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π)
    (hzero : residual c theta s beta 0 = 0)
    (htorque : BeamGapKernel.residualTorque c theta s beta 0 = 0)
    (hend : residual c theta s beta l = 0)
    (htorqueEnd : BeamGapKernel.residualTorque c theta s beta l = 0) :
    let T := Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l)
    deriv (deriv (residual c theta s beta)) 0 =
        -4 * ∑ k in T, s k * deriv (deriv (green l (beta k))) 0 ∧
      deriv (deriv (residual c theta s beta)) l =
        -4 * ∑ k in T, s k * deriv (deriv (green l (beta k))) l := by
  classical
  dsimp only
  have hh := BeamGapKernel.critical_gap_clamps c theta s beta hl hlpi
    htheta hgap hbeta hzero htorque hend htorqueEnd
  have hc := actual_clean_gap_endpoint_curvatures c theta s beta hl hlpi
    htheta hgap hbeta hzero htorque hh.1 hh.2.1
  constructor
  · rw [second_derivative_eq_actualCurvature, hc.1]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [(eq_green_endpoint_curvatures (Finset.mem_filter.mp hk).2.1
      (Finset.mem_filter.mp hk).2.2 hlpi).1]
    ring
  · rw [second_derivative_eq_actualCurvature, hc.2]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [(eq_green_endpoint_curvatures (Finset.mem_filter.mp hk).2.1
      (Finset.mem_filter.mp hk).2.2 hlpi).2.2.2.1]
    ring

/-- `eq:gap-derivative`: absence and presence of an interior negative load
give exactly the two endpoint alternatives in the line-count sketch. -/
theorem eq_gap_derivative {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) {l : ℝ}
    (hl : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π) (hs : ∀ k, 0 < s k)
    (hzero : residual c theta s beta 0 = 0)
    (htorque : BeamGapKernel.residualTorque c theta s beta 0 = 0)
    (hend : residual c theta s beta l = 0)
    (htorqueEnd : BeamGapKernel.residualTorque c theta s beta l = 0) :
    let T := Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l)
    (T = ∅ → deriv (deriv (residual c theta s beta)) 0 = 0 ∧
        deriv (deriv (residual c theta s beta)) l = 0) ∧
      (T.Nonempty → deriv (deriv (residual c theta s beta)) 0 < 0 ∧
        deriv (deriv (residual c theta s beta)) l < 0) := by
  classical
  let T := Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l)
  change (T = ∅ → _) ∧ (T.Nonempty → _)
  have heq := eq_gap_second_derivative_green c theta s beta hl hlpi htheta hgap hbeta
    hzero htorque hend htorqueEnd
  have hdet := ne_of_gt (det_positive hl hlpi)
  have hp (k) (hk : k ∈ T) : 0 < beta k ∧ beta k < l := (Finset.mem_filter.mp hk).2
  constructor
  · intro hempty
    change Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l) = ∅ at hempty
    dsimp only at heq
    rw [hempty] at heq
    simpa only [Finset.sum_empty, mul_zero] using heq
  · intro hne
    have hsum (x : ℝ)
        (hgreen : ∀ k ∈ T, 0 < deriv (deriv (green l (beta k))) x) :
        0 < ∑ k in T, s k * deriv (deriv (green l (beta k))) x := by
      apply Finset.sum_pos'
      · intro k hk
        exact (mul_pos (hs k) (hgreen k hk)).le
      · obtain ⟨k, hk⟩ := hne
        exact ⟨k, hk, mul_pos (hs k) (hgreen k hk)⟩
    have hleft : 0 < ∑ k in T, s k * deriv (deriv (green l (beta k))) 0 := by
      apply hsum
      intro k hk
      rw [green_second_derivative_zero hdet (hp k hk).1]
      exact div_pos (moment_positive (hp k hk).1 (hp k hk).2 hlpi) (det_positive hl hlpi)
    have hright : 0 < ∑ k in T, s k * deriv (deriv (green l (beta k))) l := by
      apply hsum
      intro k hk
      rw [green_second_derivative_right hdet (hp k hk).2]
      exact div_pos (moment_positive (sub_pos.mpr (hp k hk).2)
        (sub_lt_self l (hp k hk).1) hlpi) (det_positive hl hlpi)
    constructor
    · rw [heq.1]
      linarith
    · rw [heq.2]
      linarith


/-- `lem:gap-sign`, the genuinely local statement. The only zero assumptions
are at `0` and `l`; student masses may have either sign and need not be positive.
The finite set in the conclusion contains exactly the teachers in the open gap.
-/
theorem gap_sign_of_clean_config {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) {l : ℝ}
    (hl : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k ≤ π)
    (hs : ∀ k, 0 < s k)
    (hzero : residual c theta s beta 0 = 0)
    (htorque : BeamGapKernel.residualTorque c theta s beta 0 = 0)
    (hend : residual c theta s beta l = 0)
    (htorqueEnd : BeamGapKernel.residualTorque c theta s beta l = 0) :
    let T := Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l)
    (T = ∅ ↔ ∀ x, 0 ≤ x → x ≤ l → residual c theta s beta x = 0) ∧
      (T.Nonempty →
        (∀ x, 0 < x → x < l → residual c theta s beta x < 0) ∧
        deriv (deriv (residual c theta s beta)) 0 < 0 ∧
        deriv (deriv (residual c theta s beta)) l < 0) := by
  classical
  let T := Finset.univ.filter (fun k => 0 < beta k ∧ beta k < l)
  change (T = ∅ ↔ ∀ x, 0 ≤ x → x ≤ l → residual c theta s beta x = 0) ∧ _
  have hp (k) (hk : k ∈ T) : 0 < beta k ∧ beta k < l := (Finset.mem_filter.mp hk).2
  have hrepr (x : ℝ) (hx0 : 0 ≤ x) (hxl : x ≤ l) :
      residual c theta s beta x = -4 * ∑ k in T, s k * green l (beta k) x :=
    eq_gap_green_representation c theta s beta hl hlpi htheta hgap hbeta
      hzero htorque hend htorqueEnd x hx0 hxl
  have hstrict (hne : T.Nonempty) (x : ℝ) (hx0 : 0 < x) (hxl : x < l) :
      residual c theta s beta x < 0 := by
    rw [hrepr x hx0.le hxl.le]
    have hsum : 0 < ∑ k in T, s k * green l (beta k) x := by
      apply Finset.sum_pos'
      · intro k hk
        exact mul_nonneg (hs k).le
          (green_nonnegative_closed (hp k hk).1 (hp k hk).2 hlpi hx0.le hxl.le)
      · obtain ⟨k, hk⟩ := hne
        exact ⟨k, hk, mul_pos (hs k) (green_positive hx0 hxl (hp k hk).1 (hp k hk).2 hlpi)⟩
    linarith
  constructor
  · constructor
    · intro hempty x hx0 hxl
      rw [hrepr x hx0 hxl, hempty]
      simp
    · intro hz
      by_contra hne
      have hneg := hstrict (Finset.nonempty_iff_ne_empty.mpr hne) (l / 2)
        (by linarith) (by linarith)
      have hmid := hz (l / 2) (by linarith) (by linarith)
      linarith
  · intro hne
    have hd := eq_gap_derivative c theta s beta hl hlpi htheta hgap hbeta hs
      hzero htorque hend htorqueEnd
    exact ⟨hstrict hne, (hd.2 hne).1, (hd.2 hne).2⟩


theorem ordered_gap_green_representation {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (g : Fin (r + 1)) (x : ℝ) (hx : 0 ≤ x) (hxl : x ≤ rightEndpoint theta g - theta g) :
    residual c theta s beta (theta g + x) =
      -4 * ∑ k in Finset.univ.filter (fun k => 0 < relativeAngle (theta g) (beta k) ∧
          relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g),
        s k * green (rightEndpoint theta g - theta g) (relativeAngle (theta g) (beta k)) x := by
  have hl := gap_length_range theta hmono htheta g
  obtain ⟨h0, h1, h2, h3⟩ := ordered_gap_local_double_zeros c theta s beta hzero htorque g
  rw [← rotated_residual c theta s beta (theta g) x]
  exact eq_gap_green_representation c (fun i => relativeAngle (theta g) (theta i))
    s (fun k => relativeAngle (theta g) (beta k)) hl.1 hl.2
    (fun i => ⟨(relativeAngle_range (htheta g) (htheta i)).1,
      (relativeAngle_range (htheta g) (htheta i)).2.le⟩)
    (positive_nodes_outside_local_gap theta hmono htheta g)
    (fun k => ⟨(relativeAngle_range (htheta g) (hbeta k)).1,
      (relativeAngle_range (htheta g) (hbeta k)).2.le⟩)
    h0 h1 h2 h3 x hx hxl


theorem ordered_gap_curvature_formulas {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (g : Fin (r + 1)) :
    let l := rightEndpoint theta g - theta g
    let be := fun k => relativeAngle (theta g) (beta k)
    let T := Finset.univ.filter (fun k => 0 < be k ∧ be k < l)
    actualCurvature c theta s beta (theta g) = -(∑ k in T, 4 * s k * moment l (be k) / det l) ∧
      actualCurvature c theta s beta (rightEndpoint theta g) =
        -(∑ k in T, 4 * s k * moment l (l - be k) / det l) := by
  dsimp only
  have hl := gap_length_range theta hmono htheta g
  have hth (i) := relativeAngle_range (htheta g) (htheta i)
  have hbe (k) := relativeAngle_range (htheta g) (hbeta k)
  have hc := ordered_gap_clamps c theta s beta hmono htheta hbeta hzero htorque g
  dsimp only at hc
  have hh := actual_clean_gap_endpoint_curvatures c
    (fun i => relativeAngle (theta g) (theta i)) s (fun k => relativeAngle (theta g) (beta k))
    hl.1 hl.2 (fun i => ⟨(hth i).1, (hth i).2.le⟩)
    (positive_nodes_outside_local_gap theta hmono htheta g)
    (fun k => ⟨(hbe k).1, (hbe k).2.le⟩)
    (by rw [rotated_residual, add_zero]; exact hzero g)
    (by rw [rotated_torque, add_zero]; exact htorque g) hc.1 hc.2.1
  simpa only [actualCurvature, rotated_curvature, add_zero,
    show theta g + (rightEndpoint theta g - theta g) = rightEndpoint theta g by ring] using hh

/-- A canonical point off an ordered node list has exactly one local gap. -/
theorem ordered_circle_unique_local_gap {r : ℕ} (theta : Fin (r + 1) → ℝ)
    (hmono : StrictMono theta) (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    {x : ℝ} (hx : 0 ≤ x ∧ x < π) (hoff : ∀ i, theta i ≠ x) :
    ∃! g, 0 < relativeAngle (theta g) x ∧
      relativeAngle (theta g) x < rightEndpoint theta g - theta g := by
  have hg : ∃! g, theta g < liftAngle (theta 0) x ∧
      liftAngle (theta 0) x < rightEndpoint theta g := by
    apply unique_gap_of_ordered_angles theta hmono
    · unfold liftAngle
      split
      · linarith [(htheta 0).2, hx.1]
      · rename_i hn
        exact lt_of_le_of_ne (le_of_not_gt hn) (hoff 0)
    · unfold liftAngle
      split
      · rename_i hn
        linarith
      · linarith [(htheta 0).1, hx.2]
    · intro i
      unfold liftAngle
      split
      · linarith [(htheta i).2, hx.1]
      · exact hoff i
  simpa only [local_gap_mem_iff theta hmono htheta] using hg

theorem ordered_local_gap_assignment {r m : ℕ} (theta : Fin (r + 1) → ℝ)
    (beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π) (hsep : ∀ i k, theta i ≠ beta k) :
    ∃ gap : Fin m → Fin (r + 1), ∀ k g, gap k = g ↔
      0 < relativeAngle (theta g) (beta k) ∧
        relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g := by
  classical
  have hu (k) := ordered_circle_unique_local_gap theta hmono htheta (hbeta k) (fun i => hsep i k)
  choose gap hgap huniq using hu
  refine ⟨gap, ?_⟩
  intro k g
  constructor
  · intro h
    rw [← h]
    exact hgap k
  · intro h
    exact (huniq k g h).symm

/-- A positive student residual cannot vanish without at least one teacher. -/
theorem positive_students_force_teacher_nonempty {r m : ℕ}
    (c theta : Fin (r + 1) → ℝ) (s beta : Fin m → ℝ)
    (hc : ∀ i, 0 < c i) (hzero : residual c theta s beta (theta 0) = 0) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  have hsum : 0 < ∑ i, c i * kernel (theta 0 - theta i) := by
    apply Finset.sum_pos'
    · intro i _
      exact (mul_pos (hc i) (centered_kernel_pos (theta 0 - theta i))).le
    · exact ⟨0, Finset.mem_univ _, mul_pos (hc 0) (centered_kernel_pos (theta 0 - theta 0))⟩
  have hz : (∑ i, c i * kernel (theta 0 - theta i)) = 0 := by
    simpa only [residual, Finset.univ_eq_empty, Finset.sum_empty, sub_zero] using hzero
  linarith

/-- The genuine line-count theorem: the actual residual's endpoint curvature
is shared by adjacent gaps, so every teacher-free gap would force all gaps
to be teacher-free. Positive student mass excludes that possibility. -/
theorem ordered_count_of_double_zeros {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k) (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0) :
    ∃ gap : Fin m → Fin (r + 1),
      (∀ k g, gap k = g ↔ 0 < relativeAngle (theta g) (beta k) ∧
        relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g) ∧
      Function.Surjective gap ∧ r + 1 ≤ m := by
  classical
  obtain ⟨gap, hgap⟩ := ordered_local_gap_assignment theta beta hmono htheta hbeta hsep
  let left := fun g => actualCurvature c theta s beta (theta g)
  let right := fun g => actualCurvature c theta s beta (rightEndpoint theta g)
  let loadLeft := fun g k => 4 * s k *
    moment (rightEndpoint theta g - theta g) (relativeAngle (theta g) (beta k)) /
      det (rightEndpoint theta g - theta g)
  let loadRight := fun g k => 4 * s k *
    moment (rightEndpoint theta g - theta g)
      (rightEndpoint theta g - theta g - relativeAngle (theta g) (beta k)) /
      det (rightEndpoint theta g - theta g)
  have hloadLeft : ∀ g k, gap k = g → 0 < loadLeft g k := by
    intro g k hk
    have hp := (hgap k g).mp hk
    have hl := gap_length_range theta hmono htheta g
    exact div_pos (mul_pos (mul_pos (by norm_num) (hs k))
      (moment_positive hp.1 hp.2 hl.2)) (det_positive hl.1 hl.2)
  have hloadRight : ∀ g k, gap k = g → 0 < loadRight g k := by
    intro g k hk
    have hp := (hgap k g).mp hk
    have hl := gap_length_range theta hmono htheta g
    exact div_pos (mul_pos (mul_pos (by norm_num) (hs k))
      (moment_positive (by linarith) (by linarith) hl.2)) (det_positive hl.1 hl.2)
  have hfilter (g) :
      Finset.univ.filter (fun k => 0 < relativeAngle (theta g) (beta k) ∧
        relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g) =
      Finset.univ.filter (fun k => gap k = g) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hgap k g).symm
  have hleft : ∀ g, left g = -(∑ k in Finset.univ.filter (fun k => gap k = g), loadLeft g k) := by
    intro g
    have hf := (ordered_gap_curvature_formulas c theta s beta hmono htheta hbeta hzero htorque g).1
    dsimp only at hf
    rw [hfilter g] at hf
    exact hf
  have hright : ∀ g, right g = -(∑ k in Finset.univ.filter (fun k => gap k = g), loadRight g k) := by
    intro g
    have hf := (ordered_gap_curvature_formulas c theta s beta hmono htheta hbeta hzero htorque g).2
    dsimp only at hf
    rw [hfilter g] at hf
    exact hf
  have hcontinuous : ∀ g : Fin r, right g.castSucc = left g.succ := by
    intro g
    dsimp only [left, right]
    rw [rightEndpoint_castSucc]
  have hh := line_count_of_endpoint_curvature_formulas gap left right loadLeft loadRight
    hloadLeft hloadRight hleft hright hcontinuous
    (positive_students_force_teacher_nonempty c theta s beta hc (hzero 0))
  exact ⟨gap, hgap, hh.1, hh.2⟩

/-- Every canonical direction outside the ordered positive support has
strictly negative residual, directly from the occupied-gap Green formula. -/
theorem ordered_residual_negative_off_nodes {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k) (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    {x : ℝ} (hx : 0 ≤ x ∧ x < π) (hoff : ∀ i, theta i ≠ x) :
    residual c theta s beta x < 0 := by
  classical
  obtain ⟨gap, hgap, hsurj, _⟩ :=
    ordered_count_of_double_zeros c theta s beta hmono htheta hbeta hc hs hsep hzero htorque
  obtain ⟨g, hg, _⟩ := ordered_circle_unique_local_gap theta hmono htheta hx hoff
  have hl := gap_length_range theta hmono htheta g
  have hrepr := ordered_gap_green_representation c theta s beta hmono htheta hbeta hzero htorque
    g (relativeAngle (theta g) x) hg.1.le hg.2.le
  rw [periodic_add_relative (residual c theta s beta) (residual_periodic c theta s beta)] at hrepr
  rw [hrepr]
  apply negative_green_sum _ _ _ hg.1 hg.2 hl.2
  · intro k hk
    exact (Finset.mem_filter.mp hk).2
  · intro k _
    exact (hs k).le
  · obtain ⟨k, hk⟩ := hsurj g
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hgap k g).mp hk⟩, hs k⟩

/-- The same occupied-gap calculation gives strict curvature at every
positive node, including the full-period singleton configuration. -/
theorem ordered_curvature_negative_at_nodes {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k) (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (g : Fin (r + 1)) : actualCurvature c theta s beta (theta g) < 0 := by
  classical
  obtain ⟨gap, hgap, hsurj, _⟩ :=
    ordered_count_of_double_zeros c theta s beta hmono htheta hbeta hc hs hsep hzero htorque
  obtain ⟨k, hk⟩ := hsurj g
  have hsource : (Finset.univ.filter (fun j => 0 < relativeAngle (theta g) (beta j) ∧
      relativeAngle (theta g) (beta j) < rightEndpoint theta g - theta g)).Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hgap k g).mp hk⟩⟩
  have hl := gap_length_range theta hmono htheta g
  obtain ⟨h0, h1, h2, h3⟩ := ordered_gap_local_double_zeros c theta s beta hzero htorque g
  have hlocal := (gap_sign_of_clean_config c (fun i => relativeAngle (theta g) (theta i))
    s (fun k => relativeAngle (theta g) (beta k)) hl.1 hl.2
    (fun i => ⟨(relativeAngle_range (htheta g) (htheta i)).1,
      (relativeAngle_range (htheta g) (htheta i)).2.le⟩)
    (positive_nodes_outside_local_gap theta hmono htheta g)
    (fun k => ⟨(relativeAngle_range (htheta g) (hbeta k)).1,
      (relativeAngle_range (htheta g) (hbeta k)).2.le⟩)
    hs h0 h1 h2 h3).2 hsource
  have hleft := hlocal.2.1
  rw [second_derivative_eq_actualCurvature] at hleft
  simpa only [actualCurvature, rotated_curvature, add_zero] using hleft

end PaperLeanFormalization.Planar


open Real Filter
open scoped Topology
noncomputable section

namespace PaperLeanFormalization.Planar.Gaps

private theorem green_coefficients_as_single_source {l : ℝ} (hdet : det l ≠ 0) (p : ℝ) :
    Beam.leftBranch (greenU l p) (greenV l p) l =
      2 * (-1 / 4 : ℝ) * Beam.psi (l - p) ∧
    Beam.leftSlope (greenU l p) (greenV l p) l =
      2 * (-1 / 4 : ℝ) * Beam.chi (l - p) := by
  obtain ⟨hvalue, hslope⟩ := eq_green_linear_system hdet p
  constructor
  · change greenU l p * psi l + greenV l p * chi l = _
    rw [hvalue]
    change -psi (l - p) / 2 = 2 * (-1 / 4 : ℝ) * psi (l - p)
    ring
  · change greenU l p * chi l + greenV l p * (sin l + l * cos l) = _
    rw [hslope]
    change -chi (l - p) / 2 = 2 * (-1 / 4 : ℝ) * chi (l - p)
    ring

/-- At zero the Green function agrees with its smooth left branch on an
open neighborhood, so its actual third derivative is the left jerk coefficient. -/
theorem green_third_derivative_zero {l p : ℝ} (hdet : det l ≠ 0) (hp : 0 < p) :
    deriv (deriv (deriv (green l p))) 0 = Beam.j0 l p := by
  have heq : green l p =ᶠ[𝓝 0] greenLeft l p := by
    filter_upwards [eventually_lt_nhds hp] with x hx
    rw [green, if_pos hx.le, greenLeft_eq_numerator]
  have hfirst : deriv (greenLeft l p) = greenLeft1 l p :=
    funext (fun x => (greenLeft_derivative l p x).deriv)
  have hsecond : deriv (greenLeft1 l p) = greenLeft2 l p :=
    funext (fun x => (greenLeft1_derivative l p x).deriv)
  rw [heq.deriv.deriv.deriv_eq, hfirst, hsecond, (greenLeft2_derivative l p 0).deriv]
  obtain ⟨hvalue, hslope⟩ := green_coefficients_as_single_source hdet p
  have hj := (Beam.left_endpoint_jets (show Beam.determinant l ≠ 0 from hdet)
    hvalue hslope).2
  change Beam.leftJerk (greenU l p) (greenV l p) 0 = _
  convert hj using 1; ring

/-- At the far endpoint the causal right branch is smooth; reciprocity
identifies it with the piecewise Green definition before differentiating. -/
theorem green_third_derivative_right {l p : ℝ} (hdet : det l ≠ 0) (hpl : p < l) :
    deriv (deriv (deriv (green l p))) l = Beam.jl l p := by
  have heq : green l p =ᶠ[𝓝 l] greenRight l p := by
    filter_upwards [eventually_gt_nhds hpl] with x hx
    rw [green, if_neg (not_le.mpr hx), green_branch_reciprocity hdet,
      greenLeft_eq_numerator]
  have hfirst : deriv (greenRight l p) = greenRight1 l p :=
    funext (fun x => (greenRight_derivative l p x).deriv)
  have hsecond : deriv (greenRight1 l p) = greenRight2 l p :=
    funext (fun x => (greenRight1_derivative l p x).deriv)
  rw [heq.deriv.deriv.deriv_eq, hfirst, hsecond, (greenRight2_derivative l p l).deriv]
  obtain ⟨hvalue, hslope⟩ := green_coefficients_as_single_source hdet p
  have hj := (Beam.right_endpoint_jets (show Beam.determinant l ≠ 0 from hdet)
    hvalue hslope).2
  dsimp only [greenRight3, greenLeft3]
  convert hj using 1 <;> ring

/-- All four actual endpoint derivatives in the beam coefficient display. -/
theorem green_endpoint_derivatives {l p : ℝ}
    (hdet : det l ≠ 0) (hp : 0 < p) (hpl : p < l) :
    deriv (deriv (green l p)) 0 = Beam.m0 l p ∧
      deriv (deriv (green l p)) l = Beam.ml l p ∧
      deriv (deriv (deriv (green l p))) 0 = Beam.j0 l p ∧
      deriv (deriv (deriv (green l p))) l = Beam.jl l p := by
  exact ⟨green_second_derivative_zero hdet hp,
    green_second_derivative_right hdet hpl,
    green_third_derivative_zero hdet hp, green_third_derivative_right hdet hpl⟩

end PaperLeanFormalization.Planar.Gaps

noncomputable section
open Real
open scoped BigOperators

namespace PaperLeanFormalization.Planar

/-- `eq:beam-gap-data`: all four endpoint derivatives of the actual residual
and Green profile on a one-teacher gap. At residual knots the third derivatives
are the derivatives of the explicit one-sided analytic principal branches,
not an assertion about the total third derivative at a nonsmooth knot. -/
theorem eq_beam_gap_data {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (k : Fin m)
    {l : ℝ} (hl0 : 0 < l) (hlpi : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i ≤ π)
    (hgap : ∀ i, theta i = 0 ∨ l ≤ theta i)
    (hbeta : ∀ j, 0 ≤ beta j ∧ beta j ≤ π)
    (hT : Finset.univ.filter (fun j => 0 < beta j ∧ beta j < l) = {k})
    (hzero : residual c theta s beta 0 = 0)
    (hslopeZero : BeamGapKernel.residualTorque c theta s beta 0 = 0)
    (hend : residual c theta s beta l = 0)
    (hslopeEnd : BeamGapKernel.residualTorque c theta s beta l = 0) :
    deriv (deriv (residual c theta s beta)) 0 =
        -4 * s k * deriv (deriv (Gaps.green l (beta k))) 0 ∧
    deriv (deriv (residual c theta s beta)) l =
        -4 * s k * deriv (deriv (Gaps.green l (beta k))) l ∧
    ((∑ i, c i * deriv (deriv (deriv Beam.branch))
        (if theta i ≤ 0 then 0 - theta i else 0 - theta i + π)) -
      ∑ j, s j * deriv (deriv (deriv Beam.branch))
        (if beta j ≤ 0 then 0 - beta j else 0 - beta j + π)) =
        -4 * s k * deriv (deriv (deriv (Gaps.green l (beta k)))) 0 ∧
    ((∑ i, c i * deriv (deriv (deriv Beam.branch))
        (if theta i < l then l - theta i else l - theta i + π)) -
      ∑ j, s j * deriv (deriv (deriv Beam.branch))
        (if beta j < l then l - beta j else l - beta j + π)) =
        -4 * s k * deriv (deriv (deriv (Gaps.green l (beta k)))) l := by
  have hk : 0 < beta k ∧ beta k < l := by
    have hm : k ∈ Finset.univ.filter (fun j => 0 < beta j ∧ beta j < l) := by
      rw [hT]
      exact Finset.mem_singleton_self k
    exact (Finset.mem_filter.mp hm).2
  have hjets := BeamGapKernel.single_teacher_gap_jets c theta s beta k hl0 hlpi
    htheta hgap hbeta hT hzero hslopeZero hend hslopeEnd
  have hdet : Gaps.det l ≠ 0 := (Gaps.det_positive hl0 hlpi).ne'
  obtain ⟨hm0, hml, hj0, hjl⟩ := Gaps.green_endpoint_derivatives hdet hk.1 hk.2
  rw [second_derivative_eq_actualCurvature, second_derivative_eq_actualCurvature,
    hm0, hml, hj0, hjl]
  simp_rw [third_derivative_principal_branch]
  simpa only [actualCurvature, BeamGapKernel.cutJerkRight, BeamGapKernel.cutJerkLeft,
    BeamGapKernel.branchD3, Beam.branchD3, zero_sub] using hjets

end PaperLeanFormalization.Planar

namespace PaperLeanFormalization.Planar
open Gaps

theorem ordered_single_teacher_local_jets {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (g : Fin (r + 1)) (k : Fin m)
    (hT : Finset.univ.filter (fun j => 0 < relativeAngle (theta g) (beta j) ∧
      relativeAngle (theta g) (beta j) < rightEndpoint theta g - theta g) = {k}) :
    let l := rightEndpoint theta g - theta g
    let th := fun i => relativeAngle (theta g) (theta i)
    let be := fun j => relativeAngle (theta g) (beta j)
    ((∑ i, c i * BeamGapKernel.curvature (-th i)) - ∑ j, s j * BeamGapKernel.curvature (-be j)) =
        -4 * s k * Beam.m0 l (be k) ∧
    ((∑ i, c i * BeamGapKernel.curvature (l - th i)) - ∑ j, s j * BeamGapKernel.curvature (l - be j)) =
        -4 * s k * Beam.ml l (be k) ∧
    ((∑ i, c i * BeamGapKernel.cutJerkRight 0 (th i)) - ∑ j, s j * BeamGapKernel.cutJerkRight 0 (be j)) =
        -4 * s k * Beam.j0 l (be k) ∧
    ((∑ i, c i * BeamGapKernel.cutJerkLeft l (th i)) - ∑ j, s j * BeamGapKernel.cutJerkLeft l (be j)) =
        -4 * s k * Beam.jl l (be k) := by
  dsimp only
  have hl := gap_length_range theta hmono htheta g
  obtain ⟨h0, h1, h2, h3⟩ := ordered_gap_local_double_zeros c theta s beta hzero htorque g
  have h := eq_beam_gap_data c (fun i => relativeAngle (theta g) (theta i))
    s (fun j => relativeAngle (theta g) (beta j)) k hl.1 hl.2
    (fun i => ⟨(relativeAngle_range (htheta g) (htheta i)).1,
      (relativeAngle_range (htheta g) (htheta i)).2.le⟩)
    (positive_nodes_outside_local_gap theta hmono htheta g)
    (fun j => ⟨(relativeAngle_range (htheta g) (hbeta j)).1,
      (relativeAngle_range (htheta g) (hbeta j)).2.le⟩)
    hT h0 h1 h2 h3
  have hk : 0 < relativeAngle (theta g) (beta k) ∧
      relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g := by
    have hm : k ∈ Finset.univ.filter (fun j => 0 < relativeAngle (theta g) (beta j) ∧
        relativeAngle (theta g) (beta j) < rightEndpoint theta g - theta g) := by
      rw [hT]
      exact Finset.mem_singleton_self k
    exact (Finset.mem_filter.mp hm).2
  obtain ⟨hm0, hml, hj0, hjl⟩ := green_endpoint_derivatives
    (ne_of_gt (det_positive hl.1 hl.2)) hk.1 hk.2
  rw [second_derivative_eq_actualCurvature, second_derivative_eq_actualCurvature,
    hm0, hml, hj0, hjl] at h
  simp_rw [third_derivative_principal_branch] at h
  simpa only [actualCurvature, BeamGapKernel.cutJerkRight, BeamGapKernel.cutJerkLeft,
    BeamGapKernel.branchD3, Beam.branchD3, zero_sub] using h

/-- Both curvature readings are transported back to the actual global
residual, including the lifted terminal endpoint of the last gap. -/
theorem ordered_single_teacher_curvatures {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (g : Fin (r + 1)) (k : Fin m)
    (hT : Finset.univ.filter (fun j => 0 < relativeAngle (theta g) (beta j) ∧
      relativeAngle (theta g) (beta j) < rightEndpoint theta g - theta g) = {k}) :
    ((∑ i, c i * BeamGapKernel.curvature (theta g - theta i)) -
      ∑ j, s j * BeamGapKernel.curvature (theta g - beta j)) =
        -4 * s k * Beam.m0 (rightEndpoint theta g - theta g) (relativeAngle (theta g) (beta k)) ∧
    ((∑ i, c i * BeamGapKernel.curvature (rightEndpoint theta g - theta i)) -
      ∑ j, s j * BeamGapKernel.curvature (rightEndpoint theta g - beta j)) =
        -4 * s k * Beam.ml (rightEndpoint theta g - theta g) (relativeAngle (theta g) (beta k)) := by
  obtain ⟨hL, hR, _, _⟩ := ordered_single_teacher_local_jets c theta s beta hmono
    htheta hbeta hzero htorque g k hT
  have htL := rotated_curvature c theta s beta (theta g) 0
  simp only [zero_sub, add_zero] at htL
  have htR := rotated_curvature c theta s beta (theta g) (rightEndpoint theta g - theta g)
  simp only [show theta g + (rightEndpoint theta g - theta g) = rightEndpoint theta g by ring] at htR
  exact ⟨htL.symm.trans hL, htR.symm.trans hR⟩

theorem kernel_eq_circle_moment (x : ℝ) : BeamGapKernel.kernel x = CircleMoments.K x := by
  unfold BeamGapKernel.kernel CircleMoments.K
  rw [show 1 - cos x ^ 2 = sin x ^ 2 by nlinarith only [sin_sq_add_cos_sq x],
    sqrt_sq_eq_abs]

theorem curvature_eq_circle_moment (x : ℝ) :
    BeamGapKernel.curvature x = CircleMoments.K2 x := by
  simp only [BeamGapKernel.curvature, CircleMoments.K2, kernel_eq_circle_moment]

theorem ordered_initial_curvature_beam {r m : ℕ} (c theta : Fin (r + 1) → ℝ)
    (s beta : Fin m → ℝ) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (g : Fin (r + 1)) (k : Fin m)
    (hT : Finset.univ.filter (fun j => 0 < relativeAngle (theta g) (beta j) ∧
      relativeAngle (theta g) (beta j) < rightEndpoint theta g - theta g) = {k}) :
    Beam.finiteResidual CircleMoments.K2 c theta s beta (theta g) =
      -4 * s k * Beam.m0 (Beam.cyclicGapLength theta g) (relativeAngle (theta g) (beta k)) := by
  have h := (ordered_single_teacher_curvatures c theta s beta hmono htheta hbeta
    hzero htorque g k hT).1
  simp only [curvature_eq_circle_moment] at h
  exact h

/-- The complete cyclic endpoint data come from actual criticality and one
teacher per open gap. Both adjacent jets are rotated to the same student cut,
so the last-to-first boundary needs no separate analytic argument. -/
theorem ordered_gap_matching_and_jumps {r m : ℕ} (hr : 0 < r)
    (c theta : Fin (r + 1) → ℝ) (s beta : Fin m → ℝ) (teacher : Fin (r + 1) → Fin m)
    (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hsep : ∀ i k, beta k ≠ theta i)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (hT : ∀ g, Finset.univ.filter (fun j => 0 < relativeAngle (theta g) (beta j) ∧
      relativeAngle (theta g) (beta j) < rightEndpoint theta g - theta g) = {teacher g}) :
    let l := fun g => Beam.cyclicGapLength theta g
    let p := fun g => relativeAngle (theta g) (beta (teacher g))
    let sigma := fun g => s (teacher g)
    (∀ g, Beam.finiteResidual CircleMoments.K2 c theta s beta (theta g) =
      -4 * sigma g * Beam.m0 (l g) (p g)) ∧
    (∀ g, sigma g * Beam.ml (l g) (p g) =
      sigma (g + 1) * Beam.m0 (l (g + 1)) (p (g + 1))) ∧
    (∀ g, c (g + 1) = sigma g * Beam.jl (l g) (p g) -
      sigma (g + 1) * Beam.j0 (l (g + 1)) (p (g + 1))) := by
  dsimp only
  have hlocal (g) := ordered_single_teacher_local_jets c theta s beta hmono
    htheta hbeta hzero htorque g (teacher g) (hT g)
  have hcurvature (g) := ordered_single_teacher_curvatures c theta s beta hmono
    htheta hbeta hzero htorque g (teacher g) (hT g)
  have hright (g : Fin (r + 1)) :
      ((∑ i, c i * BeamGapKernel.cutJerkRight (theta g) (theta i)) -
        ∑ k, s k * BeamGapKernel.cutJerkRight (theta g) (beta k)) =
        -4 * s (teacher g) * Beam.j0 (rightEndpoint theta g - theta g)
          (relativeAngle (theta g) (beta (teacher g))) := by
    have h := (hlocal g).2.2.1
    dsimp only at h
    unfold BeamGapKernel.cutJerkRight at h ⊢
    simp only [right_cut_at_zero_rotation_argument (htheta g) (htheta _),
      right_cut_at_zero_rotation_argument (htheta g) (hbeta _)] at h
    exact h
  have hleft (g : Fin (r + 1)) :
      ((∑ i, c i * BeamGapKernel.cutJerkLeft (theta (g + 1)) (theta i)) -
        ∑ k, s k * BeamGapKernel.cutJerkLeft (theta (g + 1)) (beta k)) =
        -4 * s (teacher g) * Beam.jl (rightEndpoint theta g - theta g)
          (relativeAngle (theta g) (beta (teacher g))) := by
    have h := (hlocal g).2.2.2
    dsimp only at h
    rw [gap_length_eq_relative_successor hr theta hmono g] at h ⊢
    unfold BeamGapKernel.cutJerkLeft at h ⊢
    simp only [left_cut_rotation_argument (htheta g) (htheta (g + 1)) (htheta _),
      left_cut_rotation_argument (htheta g) (htheta (g + 1)) (hbeta _)] at h
    exact h
  refine ⟨fun g => ordered_initial_curvature_beam c theta s beta hmono htheta hbeta
    hzero htorque g (teacher g) (hT g), ?_, ?_⟩
  · intro g
    have hL := (hcurvature g).2
    have hR := (hcurvature (g + 1)).1
    let F := fun x => ((∑ i, c i * BeamGapKernel.curvature (x - theta i)) -
      ∑ k, s k * BeamGapKernel.curvature (x - beta k))
    have hp : ∀ x, F (x + π) = F x := by
      intro x
      dsimp [F]
      simp_rw [show ∀ t, x + π - t = (x - t) + π by intro t; ring,
        BeamGapKernel.curvature_add_pi]
    have hsame := periodic_rightEndpoint_eq_successor theta F hp g
    dsimp [F] at hsame
    rw [hsame] at hL
    change s (teacher g) * Beam.ml (rightEndpoint theta g - theta g)
      (relativeAngle (theta g) (beta (teacher g))) =
      s (teacher (g + 1)) * Beam.m0 (rightEndpoint theta (g + 1) - theta (g + 1))
        (relativeAngle (theta (g + 1)) (beta (teacher (g + 1))))
    linarith only [hL, hR]
  · intro g
    exact BeamGapKernel.student_mass_from_adjacent_residual_jets c theta s beta
      hmono.injective (g + 1) (hsep (g + 1)) (hleft g) (hright (g + 1))

/-- The one-teacher-per-gap condition now yields an actual negative second
variation. All geometric beam inputs are discharged above from the critical
residual; the two ordinary kernel derivative facts are explicit parameters. -/
theorem ordered_beam_descent_of_single_teacher_gaps {r m : ℕ}
    (hK : ∀ t, HasDerivAt CircleMoments.K (CircleMoments.K1 t) t)
    (hK1 : ∀ t, HasDerivAt CircleMoments.K1 (CircleMoments.K2 t) t)
    (hr : 0 < r) (c theta : Fin (r + 1) → ℝ) (s beta : Fin m → ℝ)
    (teacher : Fin (r + 1) → Fin m) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hsep : ∀ i k, beta k ≠ theta i)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (hT : ∀ g, Finset.univ.filter (fun j => 0 < relativeAngle (theta g) (beta j) ∧
      relativeAngle (theta g) (beta j) < rightEndpoint theta g - theta g) = {teacher g}) :
    ∃ dc dtheta : Fin (r + 1) → ℝ,
      deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss CircleMoments.K s beta
        (fun i => c i + t * dc i) (fun i => theta i + t * dtheta i))) 0 < 0 := by
  classical
  have hspan : theta (Fin.last r) < theta 0 + π := by
    linarith only [(htheta (Fin.last r)).2, (htheta 0).1]
  have hinside (g : Fin (r + 1)) : 0 < relativeAngle (theta g) (beta (teacher g)) ∧
      relativeAngle (theta g) (beta (teacher g)) < Beam.cyclicGapLength theta g := by
    have hk : teacher g ∈ Finset.univ.filter (fun j => 0 < relativeAngle (theta g) (beta j) ∧
        relativeAngle (theta g) (beta j) < rightEndpoint theta g - theta g) := by
      rw [hT g]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hk).2
  obtain ⟨hcurvature, hmatch, hjump⟩ := ordered_gap_matching_and_jumps hr c theta s beta teacher
    hmono htheta hbeta hsep hzero htorque hT
  exact Beam.ordered_beam_descent_of_kernel_calculus hK hK1 hr c theta
    (fun g => relativeAngle (theta g) (beta (teacher g))) (fun g => s (teacher g)) s beta
    hmono hspan hc (fun g => hs (teacher g)) (fun g => (hinside g).1) (fun g => (hinside g).2)
    htorque hcurvature hmatch hjump

end PaperLeanFormalization.Planar

namespace PaperLeanFormalization.Planar
open Gaps
variable {n m : ℕ}

theorem signed_sorted_positive_data {n m r : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (hcard : (positiveLines c theta s beta).card = r)
    (hzeros : ∀ x ∈ positiveLines c theta s beta,
      residual c theta s beta x = 0 ∧ deriv (residual c theta s beta) x = 0) :
    let a := (positiveLines c theta s beta).orderEmbOfFin hcard
    let b := (negativeLines c theta s beta).orderEmbOfFin rfl
    let u := fun i => netWeight c theta s beta (a i)
    let v := fun k => -netWeight c theta s beta (b k)
    (∀ i, 0 < u i) ∧ (∀ k, 0 < v k) ∧ (∀ i k, a i ≠ b k) ∧
      (∀ i, residual u a v b (a i) = 0) ∧
      (∀ i, BeamGapKernel.residualTorque u a v b (a i) = 0) := by
  classical
  dsimp only
  have heq := residual_eq_signed_sorted c theta s beta hcard
  have hp (i : Fin r) := Finset.orderEmbOfFin_mem (positiveLines c theta s beta) hcard i
  have hn (k : Fin (negativeLines c theta s beta).card) :=
    Finset.orderEmbOfFin_mem (negativeLines c theta s beta) rfl k
  refine ⟨fun i => (Finset.mem_filter.mp (hp i)).2,
    fun k => neg_pos.mpr (Finset.mem_filter.mp (hn k)).2, ?_, ?_, ?_⟩
  · intro i k h
    exact Finset.disjoint_left.mp (positive_negative_disjoint c theta s beta) (hp i) (h.symm ▸ hn k)
  · intro i
    rw [← heq]
    exact (hzeros _ (hp i)).1
  · intro i
    have hd := (hasDerivAt_residual
      (fun j => netWeight c theta s beta ((positiveLines c theta s beta).orderEmbOfFin hcard j))
      ((positiveLines c theta s beta).orderEmbOfFin hcard)
      (fun k => -netWeight c theta s beta ((negativeLines c theta s beta).orderEmbOfFin rfl k))
      ((negativeLines c theta s beta).orderEmbOfFin rfl)
      ((positiveLines c theta s beta).orderEmbOfFin hcard i)).deriv
    rw [← heq] at hd
    exact hd.symm.trans (hzeros _ (hp i)).2

/-- Same public count statement, now proved by sorted net atoms and the
fresh actual endpoint-curvature count, including empty positive support. -/
theorem positive_line_count_le_negative {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzeros : ∀ x ∈ positiveLines c theta s beta,
      residual c theta s beta x = 0 ∧ deriv (residual c theta s beta) x = 0) :
    (positiveLines c theta s beta).card ≤ (negativeLines c theta s beta).card := by
  classical
  by_cases hp : (positiveLines c theta s beta).card = 0
  · rw [hp]
    exact Nat.zero_le _
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hp
  have hd := signed_sorted_positive_data c theta s beta hr hzeros
  have hrange := signed_sorted_ranges c theta s beta hr htheta hbeta
  dsimp only at hd hrange
  obtain ⟨_, _, _, hcount⟩ := ordered_count_of_double_zeros
    (fun i => netWeight c theta s beta ((positiveLines c theta s beta).orderEmbOfFin hr i))
    ((positiveLines c theta s beta).orderEmbOfFin hr)
    (fun k => -netWeight c theta s beta ((negativeLines c theta s beta).orderEmbOfFin rfl k))
    ((negativeLines c theta s beta).orderEmbOfFin rfl)
    ((positiveLines c theta s beta).orderEmbOfFin hr).strictMono
    hrange.1 hrange.2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2
  simpa only [hr, Nat.succ_eq_add_one] using hcount

/-- Same public off-support sign statement, obtained from the actual Green
sum of the sorted net atoms. Singleton support needs no separate proof. -/
theorem residual_negative_off_positive_lines {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzeros : ∀ x ∈ positiveLines c theta s beta,
      residual c theta s beta x = 0 ∧ deriv (residual c theta s beta) x = 0)
    (hne : (positiveLines c theta s beta).Nonempty)
    (x : ℝ) (hx : 0 ≤ x ∧ x < π) (hoff : x ∉ positiveLines c theta s beta) :
    residual c theta s beta x < 0 := by
  classical
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr hne))
  have hd := signed_sorted_positive_data c theta s beta hr hzeros
  have hrange := signed_sorted_ranges c theta s beta hr htheta hbeta
  dsimp only at hd hrange
  rw [residual_eq_signed_sorted c theta s beta hr]
  apply ordered_residual_negative_off_nodes _ _ _ _
    ((positiveLines c theta s beta).orderEmbOfFin hr).strictMono
    hrange.1 hrange.2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 hx
  intro i hi
  exact hoff (hi ▸ Finset.orderEmbOfFin_mem (positiveLines c theta s beta) hr i)

/-- Same public strict-curvature statement, using the actual endpoint sum
and transporting derivatives through the proved net-sum equality. -/
theorem residual_second_derivative_negative_at_positive_line {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hzeros : ∀ x ∈ positiveLines c theta s beta,
      residual c theta s beta x = 0 ∧ deriv (residual c theta s beta) x = 0)
    (x : ℝ) (hx : x ∈ positiveLines c theta s beta) :
    deriv (deriv (residual c theta s beta)) x < 0 := by
  classical
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero
    (ne_of_gt (Finset.card_pos.mpr ⟨x, hx⟩))
  have hd := signed_sorted_positive_data c theta s beta hr hzeros
  have hrange := signed_sorted_ranges c theta s beta hr htheta hbeta
  dsimp only at hd hrange
  have hxrange : x ∈ Set.range ((positiveLines c theta s beta).orderEmbOfFin hr) := by
    rw [Finset.range_orderEmbOfFin]
    exact hx
  obtain ⟨i, hi⟩ := hxrange
  rw [residual_eq_signed_sorted c theta s beta hr, second_derivative_eq_actualCurvature, ← hi]
  exact ordered_curvature_negative_at_nodes _ _ _ _
    ((positiveLines c theta s beta).orderEmbOfFin hr).strictMono
    hrange.1 hrange.2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 i


theorem positive_lines_eq_student_lines
    {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 ≤ s k)
    (hcrit : fderiv ℝ (variableLoss s beta) (c, theta) = 0)
    (hne : (positiveLines c theta s beta).Nonempty) :
    positiveLines c theta s beta = Finset.univ.image theta := by
  classical
  have hsub := positiveLines_subset_students c theta s beta hs
  have hzeros : ∀ x ∈ positiveLines c theta s beta,
      residual c theta s beta x = 0 ∧ deriv (residual c theta s beta) x = 0 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hsub hx)
    exact critical_point_double_zero hcrit i (ne_of_gt (hc i))
  apply Finset.Subset.antisymm hsub
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  by_contra hoff
  have hneg := residual_negative_off_positive_lines c theta s beta htheta hbeta
    hzeros hne (theta i) (htheta i) hoff
  rw [mass_stationarity hcrit i] at hneg
  exact (lt_irrefl 0) hneg

theorem no_collisions_of_nonempty_positive_lines
    {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 ≤ s k)
    (hmin : IsLocalMin (variableLoss s beta) (c, theta))
    (hne : (positiveLines c theta s beta).Nonempty) :
    Function.Injective theta := by
  classical
  have hcrit : fderiv ℝ (variableLoss s beta) (c, theta) = 0 := hmin.fderiv_eq_zero
  have hsupport := positive_lines_eq_student_lines htheta hbeta hc hs hcrit hne
  have hzeros : ∀ x ∈ positiveLines c theta s beta,
      residual c theta s beta x = 0 ∧ deriv (residual c theta s beta) x = 0 := by
    intro x hx
    rw [hsupport] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact critical_point_double_zero hcrit i (ne_of_gt (hc i))
  intro p q hpq
  by_contra hnepq
  have hmem : theta p ∈ positiveLines c theta s beta := by
    rw [hsupport]
    exact Finset.mem_image_of_mem theta (Finset.mem_univ p)
  have hcurv := residual_second_derivative_negative_at_positive_line
    c theta s beta htheta hbeta hzeros (theta p) hmem
  exact opposed_rotation_not_local_min c theta s beta hnepq hpq (hc p) (hc q) hcurv hmin


theorem empty_positive_support_residual_zero
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hempty : positiveLines c theta s beta = ∅)
    (x0 : ℝ) (hzero : residual c theta s beta x0 = 0) :
    ∀ x, residual c theta s beta x = 0 := by
  classical
  let S := Finset.univ.image theta ∪ Finset.univ.image beta
  have hnonpos : ∀ t ∈ S, netWeight c theta s beta t ≤ 0 := by
    intro t ht
    by_contra hnot
    have hmem : t ∈ positiveLines c theta s beta :=
      Finset.mem_filter.mpr ⟨ht, lt_of_not_ge hnot⟩
    rw [hempty] at hmem
    exact Finset.not_mem_empty t hmem
  have hkernel : ∀ x, 0 < kernel x := Gaps.centered_kernel_pos
  have hsum : (∑ t in S, -(netWeight c theta s beta t * kernel (x0 - t))) = 0 := by
    rw [Finset.sum_neg_distrib]
    change -(∑ t in Finset.univ.image theta ∪ Finset.univ.image beta,
      netWeight c theta s beta t * kernel (x0 - t)) = 0
    rw [← residual_eq_sum_netWeight, hzero, neg_zero]
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun t ht =>
    neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (hnonpos t ht) (le_of_lt (hkernel (x0 - t)))))).mp hsum
  have hweights : ∀ t ∈ S, netWeight c theta s beta t = 0 := by
    intro t ht
    have hterm := neg_eq_zero.mp (hterms t ht)
    exact (mul_eq_zero.mp hterm).resolve_right (ne_of_gt (hkernel (x0 - t)))
  intro x
  rw [residual_eq_sum_netWeight]
  apply Finset.sum_eq_zero
  intro t ht
  rw [hweights t ht, zero_mul]

theorem small_positive_support_residual_zero_of_two_students
    {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (hn : 2 ≤ n)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 ≤ s k)
    (hmin : IsLocalMin (variableLoss s beta) (c, theta))
    (hsmall : (positiveLines c theta s beta).card ≤ 1) :
    ∀ x, residual c theta s beta x = 0 := by
  classical
  have hcrit : fderiv ℝ (variableLoss s beta) (c, theta) = 0 := hmin.fderiv_eq_zero
  have hempty : positiveLines c theta s beta = ∅ := by
    by_contra hnot
    have hne := Finset.nonempty_iff_ne_empty.mpr hnot
    have hinj := no_collisions_of_nonempty_positive_lines htheta hbeta hc hs hmin hne
    have heq := positive_lines_eq_student_lines htheta hbeta hc hs hcrit hne
    have hcard : (positiveLines c theta s beta).card = n := by
      rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    omega (config := {})
  exact empty_positive_support_residual_zero c theta s beta hempty
    (theta ⟨0, by omega (config := {})⟩) (mass_stationarity hcrit ⟨0, by omega (config := {})⟩)

theorem line_separated_of_nonempty_positive_lines
    {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (hmn : m ≤ n)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hmin : IsLocalMin (variableLoss s beta) (c, theta))
    (hne : (positiveLines c theta s beta).Nonempty) :
    n = m ∧ Function.Injective theta ∧ Function.Injective beta ∧
      (∀ i k, theta i ≠ beta k) := by
  classical
  have hcrit : fderiv ℝ (variableLoss s beta) (c, theta) = 0 := hmin.fderiv_eq_zero
  have hthetaInj := no_collisions_of_nonempty_positive_lines htheta hbeta hc
    (fun k => le_of_lt (hs k)) hmin hne
  have hsupport := positive_lines_eq_student_lines htheta hbeta hc
    (fun k => le_of_lt (hs k)) hcrit hne
  have hzeros : ∀ x ∈ positiveLines c theta s beta,
      residual c theta s beta x = 0 ∧ deriv (residual c theta s beta) x = 0 := by
    intro x hx
    rw [hsupport] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact critical_point_double_zero hcrit i (ne_of_gt (hc i))
  have hstudentCard : (Finset.univ.image theta).card = n := by
    rw [Finset.card_image_of_injective _ hthetaInj, Finset.card_univ, Fintype.card_fin]
  have hcount := positive_line_count_le_negative c theta s beta htheta hbeta hzeros
  have hteacherBound := negative_line_count c theta s beta (fun i => le_of_lt (hc i))
  obtain ⟨hequal, hnegativeEq, hdisjoint⟩ := equality_in_line_count_chain
    (positiveLines c theta s beta) (negativeLines c theta s beta)
    (Finset.univ.image theta) (Finset.univ.image beta)
    (positive_negative_disjoint c theta s beta) hsupport
    (negativeLines_subset_teachers c theta s beta (fun i => le_of_lt (hc i)))
    hstudentCard hcount hteacherBound.2 hmn
  have hbetaCard : (Finset.univ.image beta).card = (Finset.univ : Finset (Fin m)).card := by
    rw [hsupport, hstudentCard, hnegativeEq] at hcount
    rw [Finset.card_univ, Fintype.card_fin]
    omega (config := {})
  have hbetaInj : Function.Injective beta := by
    have hinjOn := Finset.injOn_of_card_image_eq hbetaCard
    intro i j hij
    exact hinjOn (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hsep : ∀ i k, theta i ≠ beta k := by
    intro i k hik
    exact (Finset.disjoint_left.mp hdisjoint)
      (Finset.mem_image_of_mem theta (Finset.mem_univ i))
      (hik ▸ Finset.mem_image_of_mem beta (Finset.mem_univ k))
  exact ⟨hequal, hthetaInj, hbetaInj, hsep⟩

end PaperLeanFormalization.Planar

namespace PaperLeanFormalization.Planar

open Gaps

/-- At balanced widths, the actual double-zero gap count identifies one
teacher index in each strict local gap. This is the singleton source filter
required by the explicit beam endpoint formulas. -/
theorem ordered_singleton_teacher_gaps {r m : ℕ}
    (c theta : Fin (r + 1) → ℝ) (s beta : Fin m → ℝ)
    (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (hmn : m ≤ r + 1) :
    ∃ teacher : Fin (r + 1) → Fin m, ∀ g,
      Finset.univ.filter (fun k => 0 < relativeAngle (theta g) (beta k) ∧
        relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g) =
      {teacher g} := by
  classical
  obtain ⟨gap, hgap, hsurj, hcard⟩ :=
    ordered_count_of_double_zeros c theta s beta hmono htheta hbeta hc hs hsep hzero htorque
  have hbij : Function.Bijective gap := by
    apply (Fintype.bijective_iff_surjective_and_card gap).mpr
    exact ⟨hsurj, by simpa only [Fintype.card_fin] using Nat.le_antisymm hmn hcard⟩
  let e : Fin m ≃ Fin (r + 1) := Equiv.ofBijective gap hbij
  refine ⟨e.symm, ?_⟩
  intro g
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [← hgap k g]
  constructor
  · intro h
    apply e.injective
    exact h.trans (e.apply_symm_apply g).symm
  · intro h
    rw [h]
    exact e.apply_symm_apply g

/-- The existing strict-interlacing predicate is only a display of the
canonical sorted gap relation. This adapter uses its definitions alone. -/
theorem strict_interlaces_of_sorted_local_gaps {r m : ℕ}
    (theta : Fin (r + 1) → ℝ) (beta : Fin m → ℝ)
    (hinj : Function.Injective theta) (ordered : Fin (r + 1) → ℝ)
    (hordered : ordered = PaperLeanFormalization.orderedStudent theta hinj)
    (hmono : StrictMono ordered)
    (hrange : ∀ i, 0 ≤ ordered i ∧ ordered i < π)
    (hlocal : ∀ g, ∃! k, 0 < relativeAngle (ordered g) (beta k) ∧
      relativeAngle (ordered g) (beta k) < rightEndpoint ordered g - ordered g) :
    StrictlyInterlaces theta beta := by
  refine ⟨hinj, ?_⟩
  intro g
  have h := hlocal g
  simp_rw [local_gap_mem_iff ordered hmono hrange] at h
  simpa only [PaperLeanFormalization.cyclicGapLeft,
    PaperLeanFormalization.cyclicGapRight, ← hordered,
    PaperLeanFormalization.liftAbove, rightEndpoint, liftAngle] using h

/-- An already increasing student list is its canonical sorted enumeration. -/
theorem orderedStudent_eq_of_strictMono {n : ℕ} (theta : Fin n → ℝ)
    (hmono : StrictMono theta) :
    PaperLeanFormalization.orderedStudent theta hmono.injective = theta := by
  classical
  have hcard : (Finset.univ.image theta).card = n := by
    rw [Finset.card_image_of_injective _ hmono.injective,
      Finset.card_univ, Fintype.card_fin]
  change ((Finset.univ.image theta).orderEmbOfFin hcard : Fin n → ℝ) = theta
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image_of_mem theta (Finset.mem_univ i)
  · exact hmono

/-- Fresh analytic gap occupancy and finite balance imply the exact old
strict-interlacing predicate, with no old interlacing theorem invoked. -/
theorem ordered_strict_interlaces_of_double_zeros {r m : ℕ}
    (c theta : Fin (r + 1) → ℝ) (s beta : Fin m → ℝ)
    (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (hmn : m ≤ r + 1) : StrictlyInterlaces theta beta := by
  classical
  obtain ⟨teacher, hteacher⟩ := ordered_singleton_teacher_gaps c theta s beta
    hmono htheta hbeta hc hs hsep hzero htorque hmn
  apply strict_interlaces_of_sorted_local_gaps theta beta hmono.injective theta
    (orderedStudent_eq_of_strictMono theta hmono).symm hmono htheta
  intro g
  refine ⟨teacher g, ?_, ?_⟩
  · have hmem : teacher g ∈ Finset.univ.filter (fun k =>
        0 < relativeAngle (theta g) (beta k) ∧
          relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g) := by
      rw [hteacher g]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hmem).2
  · intro k hk
    have hmem : k ∈ Finset.univ.filter (fun k =>
        0 < relativeAngle (theta g) (beta k) ∧
          relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
    rw [hteacher g] at hmem
    exact Finset.mem_singleton.mp hmem

end PaperLeanFormalization.Planar


namespace PaperLeanFormalization.Planar

theorem exists_sorting_permutation {n : ℕ} (theta : Fin n → ℝ)
    (hinj : Function.Injective theta) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (fun i ↦ theta (e i)) := by
  classical
  let A := Finset.univ.image theta
  have hcard : A.card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let a : Fin n ↪o ℝ := A.orderEmbOfFin hcard
  have hex (i : Fin n) : ∃ j : Fin n, theta j = a i := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.orderEmbOfFin_mem A hcard i)
    exact ⟨j, hj⟩
  choose sigma hsigma using hex
  have hsigmaInj : Function.Injective sigma := by
    intro i j hij
    apply a.injective
    rw [← hsigma i, ← hsigma j, hij]
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective sigma
    ⟨hsigmaInj, Finite.surjective_of_injective hsigmaInj⟩
  refine ⟨e, ?_⟩
  intro i j hij
  change theta (sigma i) < theta (sigma j)
  rw [hsigma i, hsigma j]
  exact a.strictMono hij


end PaperLeanFormalization.Planar

namespace PaperLeanFormalization.Planar

open Gaps

/-- Relabeling students preserves the literal residual at every point. -/
theorem residual_student_permutation {n m : ℕ} (e : Equiv.Perm (Fin n))
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    residual (fun i => c (e i)) (fun i => theta (e i)) s beta =
      residual c theta s beta := by
  funext x
  unfold residual
  congr 1
  exact Equiv.sum_comp e (fun i : Fin n => c i * kernel (x - theta i))

/-- The same finite reindexing preserves the actual residual torque. -/
theorem torque_student_permutation {n m : ℕ} (e : Equiv.Perm (Fin n))
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    BeamGapKernel.residualTorque (fun i => c (e i)) (fun i => theta (e i)) s beta =
      BeamGapKernel.residualTorque c theta s beta := by
  funext x
  unfold BeamGapKernel.residualTorque
  congr 1
  exact Equiv.sum_comp e (fun i : Fin n => c i * BeamGapKernel.torque (x - theta i))

/-- The exact unsorted strict-interlacing statement follows by one student
permutation, the fresh ordered double-zero count, and finite cardinality
balance. The old strict-interlacing object is used only as a predicate. -/
theorem raw_strict_interlaces_of_double_zeros {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hn : 0 < n) (hinj : Function.Injective theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0)
    (hmn : m ≤ n) : StrictlyInterlaces theta beta := by
  classical
  cases n with
  | zero => exact False.elim ((Nat.lt_irrefl 0) hn)
  | succ r =>
    obtain ⟨e, hmono⟩ := exists_sorting_permutation theta hinj
    let sorted := fun i => theta (e i)
    have hsorted : sorted = PaperLeanFormalization.orderedStudent theta hinj := by
      have hcard : (Finset.univ.image theta).card = r + 1 := by
        rw [Finset.card_image_of_injective _ hinj,
          Finset.card_univ, Fintype.card_fin]
      change sorted = ((Finset.univ.image theta).orderEmbOfFin hcard : Fin (r + 1) → ℝ)
      apply Finset.orderEmbOfFin_unique
      · intro i
        exact Finset.mem_image_of_mem theta (Finset.mem_univ (e i))
      · exact hmono
    have hzero' : ∀ i, residual (fun i => c (e i)) sorted s beta (sorted i) = 0 := by
      intro i
      rw [residual_student_permutation e c theta s beta]
      exact hzero (e i)
    have htorque' : ∀ i,
        BeamGapKernel.residualTorque (fun i => c (e i)) sorted s beta (sorted i) = 0 := by
      intro i
      rw [torque_student_permutation e c theta s beta]
      exact htorque (e i)
    obtain ⟨teacher, hteacher⟩ := ordered_singleton_teacher_gaps (fun i => c (e i)) sorted
      s beta hmono (fun i => htheta (e i)) hbeta (fun i => hc (e i)) hs
      (fun i k => hsep (e i) k) hzero' htorque' hmn
    apply strict_interlaces_of_sorted_local_gaps theta beta hinj sorted hsorted hmono
      (fun i => htheta (e i))
    intro g
    refine ⟨teacher g, ?_, ?_⟩
    · have hmem : teacher g ∈ Finset.univ.filter (fun k =>
          0 < relativeAngle (sorted g) (beta k) ∧
            relativeAngle (sorted g) (beta k) < rightEndpoint sorted g - sorted g) := by
        rw [hteacher g]
        exact Finset.mem_singleton_self _
      exact (Finset.mem_filter.mp hmem).2
    · intro k hk
      have hmem : k ∈ Finset.univ.filter (fun k =>
          0 < relativeAngle (sorted g) (beta k) ∧
            relativeAngle (sorted g) (beta k) < rightEndpoint sorted g - sorted g) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      rw [hteacher g] at hmem
      exact Finset.mem_singleton.mp hmem

end PaperLeanFormalization.Planar

namespace PaperLeanFormalization.Planar

/-- The complete line-separation conclusion, assembled from support equality,
collision exclusion, the finite count chain, and strict gap ownership. -/
theorem clean_structure_of_nonempty_positive_lines {n m : ℕ}
    {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (hmn : m ≤ n)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hmin : IsLocalMin (variableLoss s beta) (c, theta))
    (hne : (positiveLines c theta s beta).Nonempty) :
    n = m ∧ Function.Injective theta ∧ Function.Injective beta ∧
      (∀ i k, theta i ≠ beta k) ∧ StrictlyInterlaces theta beta := by
  obtain ⟨hnm, hinj, hbinj, hsep⟩ :=
    line_separated_of_nonempty_positive_lines hmn htheta hbeta hc hs hmin hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, _, _⟩ := Finset.mem_image.mp
    (positiveLines_subset_students c theta s beta (fun k => (hs k).le) hx)
  have hcrit := hmin.fderiv_eq_zero
  refine ⟨hnm, hinj, hbinj, hsep, raw_strict_interlaces_of_double_zeros
    c theta s beta i.pos hinj htheta hbeta hc hs hsep
    (fun j => mass_stationarity hcrit j) ?_ hmn⟩
  intro j
  have hd := (hasDerivAt_residual c theta s beta (theta j)).deriv
  exact hd.symm.trans (critical_point_double_zero hcrit j (ne_of_gt (hc j))).2

end PaperLeanFormalization.Planar


noncomputable section
open Real
open scoped BigOperators

namespace PaperLeanFormalization.Planar.NetSurface

open Gaps

/-- Filtering the canonical enumeration is exactly filtering the original
finite support. This is a finite-sum identity, with no geometric assumptions. -/
theorem sum_sorted_filter {r : ℕ} (S : Finset ℝ) (hcard : S.card = r)
    (P : ℝ → Prop) [DecidablePred P] (f : ℝ → ℝ) :
    (∑ i in Finset.univ.filter (fun i => P (S.orderEmbOfFin hcard i)),
      f (S.orderEmbOfFin hcard i)) = ∑ x in S.filter P, f x := by
  classical
  simpa only [Finset.sum_filter] using
    sum_sorted S hcard (fun x => if P x then f x else 0)

theorem filtered_sorted_nonempty_iff {r : ℕ} (S : Finset ℝ) (hcard : S.card = r)
    (P : ℝ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (S.orderEmbOfFin hcard i))).Nonempty ↔
      (S.filter P).Nonempty := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨S.orderEmbOfFin hcard i, Finset.mem_filter.mpr
      ⟨Finset.orderEmbOfFin_mem S hcard i, (Finset.mem_filter.mp hi).2⟩⟩
  · rintro ⟨x, hx⟩
    have hrange : x ∈ Set.range (S.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact (Finset.mem_filter.mp hx).1
    obtain ⟨i, hi⟩ := hrange
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hi]
    exact (Finset.mem_filter.mp hx).2

/-- One shared reduction of raw net atoms to a clean clamped gap. Both the
labeled representation and the manuscript gap theorem use these same data. -/
theorem signed_sorted_clean_gap_data {n m : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) (l : ℝ)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hgap : ∀ x ∈ positiveLines c theta s beta, ¬ (0 < x ∧ x < l))
    (hz0 : residual c theta s beta 0 = 0 ∧ deriv (residual c theta s beta) 0 = 0)
    (hzl : residual c theta s beta l = 0 ∧ deriv (residual c theta s beta) l = 0) :
    let a := (positiveLines c theta s beta).orderEmbOfFin rfl
    let b := (negativeLines c theta s beta).orderEmbOfFin rfl
    let u := fun i => netWeight c theta s beta (a i)
    let v := fun k => -netWeight c theta s beta (b k)
    (∀ i, 0 ≤ a i ∧ a i ≤ π) ∧ (∀ k, 0 ≤ b k ∧ b k ≤ π) ∧
      (∀ i, a i = 0 ∨ l ≤ a i) ∧ (∀ k, 0 < v k) ∧
      residual u a v b 0 = 0 ∧ BeamGapKernel.residualTorque u a v b 0 = 0 ∧
      residual u a v b l = 0 ∧ BeamGapKernel.residualTorque u a v b l = 0 := by
  classical
  let a := (positiveLines c theta s beta).orderEmbOfFin rfl
  let b := (negativeLines c theta s beta).orderEmbOfFin rfl
  let u := fun i => netWeight c theta s beta (a i)
  let v := fun k => -netWeight c theta s beta (b k)
  have heq : residual c theta s beta = residual u a v b :=
    residual_eq_signed_sorted c theta s beta rfl
  have hrange := signed_sorted_ranges c theta s beta rfl htheta hbeta
  have ha (i) : 0 ≤ a i ∧ a i ≤ π := ⟨(hrange.1 i).1, (hrange.1 i).2.le⟩
  have hb (k) : 0 ≤ b k ∧ b k ≤ π := ⟨(hrange.2 k).1, (hrange.2 k).2.le⟩
  have hclean (i) : a i = 0 ∨ l ≤ a i := by
    rcases eq_or_lt_of_le (ha i).1 with hi | hi
    · exact Or.inl hi.symm
    · right
      by_contra hli
      exact hgap (a i) (Finset.orderEmbOfFin_mem (positiveLines c theta s beta) rfl i)
        ⟨hi, lt_of_not_ge hli⟩
  have hv (k) : 0 < v k :=
    neg_pos.mpr (Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem (negativeLines c theta s beta) rfl k)).2
  have htorque (x : ℝ) (hx : deriv (residual c theta s beta) x = 0) :
      BeamGapKernel.residualTorque u a v b x = 0 := by
    have hd := (hasDerivAt_residual u a v b x).deriv
    rw [← heq] at hd
    exact hd.symm.trans hx
  exact ⟨ha, hb, hclean, hv, by rw [← heq]; exact hz0.1,
    htorque 0 hz0.2, by rw [← heq]; exact hzl.1, htorque l hzl.2⟩

/-- `eq:gap-green-representation`, in the manuscript's exact raw-net form.
The coefficient is `+4ω` and the sum ranges over negative net lines, rather
than a chosen enumeration of positive teacher loads. -/
theorem eq_gap_green_representation {n m : ℕ} (c theta : Fin n → ℝ)
    (s beta : Fin m → ℝ) {l : ℝ} (hl0 : 0 < l) (hlπ : l ≤ π)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (_hbase : 0 ∈ positiveLines c theta s beta)
    (hgap : ∀ x ∈ positiveLines c theta s beta, ¬ (0 < x ∧ x < l))
    (hz0 : residual c theta s beta 0 = 0 ∧ deriv (residual c theta s beta) 0 = 0)
    (hzl : residual c theta s beta l = 0 ∧ deriv (residual c theta s beta) l = 0)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγl : γ ≤ l) :
    residual c theta s beta γ =
      4 * ∑ x in (negativeLines c theta s beta).filter (fun x => 0 < x ∧ x < l),
        netWeight c theta s beta x * green l x γ := by
  classical
  let a := (positiveLines c theta s beta).orderEmbOfFin rfl
  let b := (negativeLines c theta s beta).orderEmbOfFin rfl
  let u := fun i => netWeight c theta s beta (a i)
  let v := fun k => -netWeight c theta s beta (b k)
  let T := Finset.univ.filter (fun k => 0 < b k ∧ b k < l)
  let N := (negativeLines c theta s beta).filter (fun x => 0 < x ∧ x < l)
  have heq : residual c theta s beta = residual u a v b :=
    residual_eq_signed_sorted c theta s beta rfl
  obtain ⟨ha, hb, hclean, _, hv0, ht0, hvl, htl⟩ :=
    signed_sorted_clean_gap_data c theta s beta l htheta hbeta hgap hz0 hzl
  have hrepr := Planar.eq_gap_green_representation u a v b hl0 hlπ ha hclean hb
    hv0 ht0 hvl htl γ hγ0 hγl
  change residual u a v b γ = -4 * ∑ k in T, v k * green l (b k) γ at hrepr
  have hsum : (∑ k in T, v k * green l (b k) γ) =
      -(∑ x in N, netWeight c theta s beta x * green l x γ) := by
    calc
      (∑ k in T, v k * green l (b k) γ) =
          ∑ x in N, (-netWeight c theta s beta x) * green l x γ :=
        sum_sorted_filter (negativeLines c theta s beta) rfl
          (fun x => 0 < x ∧ x < l) (fun x => (-netWeight c theta s beta x) * green l x γ)
      _ = _ := by simp only [neg_mul, Finset.sum_neg_distrib]
  rw [heq, hrepr, hsum]
  ring

/-- The full manuscript gap statement. The Green function is chosen before
the raw network data and depends only on the gap length. The only geometric
assumption is absence of positive *net* atoms from the open gap. -/
theorem lem_gap_sign {l : ℝ} (hl0 : 0 < l) (hlπ : l ≤ π) :
    ∃ G : ℝ → ℝ → ℝ,
      (∀ p, 0 < p → p < l → ∀ γ, 0 ≤ γ → γ ≤ l → 0 ≤ G γ p) ∧
      ∀ {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ),
        (∀ i, 0 ≤ theta i ∧ theta i < π) → (∀ k, 0 ≤ beta k ∧ beta k < π) →
        0 ∈ positiveLines c theta s beta →
        (∀ a ∈ positiveLines c theta s beta, ¬ (0 < a ∧ a < l)) →
        (residual c theta s beta 0 = 0 ∧ deriv (residual c theta s beta) 0 = 0) →
        (residual c theta s beta l = 0 ∧ deriv (residual c theta s beta) l = 0) →
        (∀ γ, 0 ≤ γ → γ ≤ l → residual c theta s beta γ =
          4 * ∑ a in (negativeLines c theta s beta).filter (fun a => 0 < a ∧ a < l),
            netWeight c theta s beta a * G γ a) ∧
        ((∀ γ, 0 ≤ γ → γ ≤ l → residual c theta s beta γ = 0) ↔
          (negativeLines c theta s beta).filter (fun a => 0 < a ∧ a < l) = ∅) ∧
        (((negativeLines c theta s beta).filter (fun a => 0 < a ∧ a < l)).Nonempty →
          (∀ γ, 0 < γ → γ < l → residual c theta s beta γ < 0) ∧
          deriv (deriv (residual c theta s beta)) 0 < 0 ∧
          deriv (deriv (residual c theta s beta)) l < 0) := by
  refine ⟨fun γ p => green l p γ, ?_, ?_⟩
  · intro p hp hpl γ hγ0 hγl
    exact green_nonnegative_closed hp hpl hlπ hγ0 hγl
  · intro n m c theta s beta htheta hbeta hbase hgap hz0 hzl
    classical
    let a := (positiveLines c theta s beta).orderEmbOfFin rfl
    let b := (negativeLines c theta s beta).orderEmbOfFin rfl
    let u := fun i => netWeight c theta s beta (a i)
    let v := fun k => -netWeight c theta s beta (b k)
    let T := Finset.univ.filter (fun k => 0 < b k ∧ b k < l)
    let N := (negativeLines c theta s beta).filter (fun x => 0 < x ∧ x < l)
    have heq : residual c theta s beta = residual u a v b :=
      residual_eq_signed_sorted c theta s beta rfl
    obtain ⟨ha, hb, hclean, hv, hv0, ht0, hvl, htl⟩ :=
      signed_sorted_clean_gap_data c theta s beta l htheta hbeta hgap hz0 hzl
    have hlocal := gap_sign_of_clean_config u a v b hl0 hlπ ha hclean hb hv
      hv0 ht0 hvl htl
    change (T = ∅ ↔ ∀ γ, 0 ≤ γ → γ ≤ l → residual u a v b γ = 0) ∧
      (T.Nonempty → (∀ γ, 0 < γ → γ < l → residual u a v b γ < 0) ∧
        deriv (deriv (residual u a v b)) 0 < 0 ∧
        deriv (deriv (residual u a v b)) l < 0) at hlocal
    rw [← heq] at hlocal
    have hn : T.Nonempty ↔ N.Nonempty :=
      filtered_sorted_nonempty_iff (negativeLines c theta s beta) rfl (fun x => 0 < x ∧ x < l)
    have hempty : T = ∅ ↔ N = ∅ := by
      simpa only [Finset.not_nonempty_iff_eq_empty] using not_congr hn
    exact ⟨eq_gap_green_representation c theta s beta hl0 hlπ htheta hbeta hbase hgap hz0 hzl,
      hlocal.1.symm.trans hempty, fun hN => hlocal.2 (hn.mpr hN)⟩

end PaperLeanFormalization.Planar.NetSurface




noncomputable section
open Real
open scoped BigOperators

namespace PaperLeanFormalization.Planar

open Gaps

/-- The shared weak-interlacing predicate displays the same strict local
gap relation. Only its definitions, not an old interlacing theorem, are used. -/
theorem weak_interlaces_of_ordered_local_hits {r m : ℕ}
    (theta : Fin (r + 1) → ℝ) (beta : Fin m → ℝ)
    (hmono : StrictMono theta)
    (hrange : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hlocal : ∀ g, ∃ k, 0 < relativeAngle (theta g) (beta k) ∧
      relativeAngle (theta g) (beta k) < rightEndpoint theta g - theta g) :
    cyclically_weakly_interlaces_general theta beta hmono.injective := by
  intro g
  have h := hlocal g
  have hordered : PaperLeanFormalization.orderedStudent theta hmono.injective = theta :=
    orderedStudent_eq_of_strictMono theta hmono
  simp_rw [local_gap_mem_iff theta hmono hrange] at h
  simpa only [PaperLeanFormalization.cyclicGapLeft, PaperLeanFormalization.cyclicGapRight, hordered,
    PaperLeanFormalization.liftAbove, rightEndpoint, liftAngle] using h

/-- Fresh double-zero gap occupancy gives the precise shared weak
interlacing conclusion and the count, with no reindexing of finite sets. -/
theorem ordered_weak_interlaces_and_count_of_double_zeros {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hn : 0 < n) (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0) :
    cyclically_weakly_interlaces_general theta beta hmono.injective ∧ n ≤ m := by
  cases n with
  | zero => exact False.elim ((Nat.lt_irrefl 0) hn)
  | succ r =>
    obtain ⟨gap, hgap, hsurj, hcount⟩ := ordered_count_of_double_zeros
      c theta s beta hmono htheta hbeta hc hs hsep hzero htorque
    refine ⟨weak_interlaces_of_ordered_local_hits theta beta hmono htheta ?_, hcount⟩
    intro g
    obtain ⟨k, hk⟩ := hsurj g
    exact ⟨k, (hgap k g).mp hk⟩

namespace LineSurface

open PaperLeanFormalization.Definitions

/-- Exact shared `lem:line-count` statement, proved entirely from the new
signed finite-sum reduction and the local double-zero gap argument. -/
theorem lem_line_count {n m : ℕ} (c θ : Fin n → ℝ) (s β : Fin m → ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i < π) (hβ : ∀ k, 0 ≤ β k ∧ β k < π)
    (hcard : 2 ≤ (PositiveLines c θ s β).card)
    (hzeros : ∀ x ∈ PositiveLines c θ s β,
      PlanarResidual .centered c θ s β x = 0 ∧
        deriv (PlanarResidual .centered c θ s β) x = 0) :
    (∃ hα : Function.Injective ((PositiveLines c θ s β).orderEmbOfFin rfl),
      cyclically_weakly_interlaces_general
        ((PositiveLines c θ s β).orderEmbOfFin rfl)
        ((NegativeLines c θ s β).orderEmbOfFin rfl) hα) ∧
    (PositiveLines c θ s β).card ≤ (NegativeLines c θ s β).card := by
  classical
  have hd := signed_sorted_positive_data c θ s β rfl hzeros
  have hrange := signed_sorted_ranges c θ s β rfl hθ hβ
  dsimp only at hd hrange
  have hn : 0 < (positiveLines c θ s β).card :=
    lt_of_lt_of_le (by decide : 0 < 2) hcard
  have hresult := ordered_weak_interlaces_and_count_of_double_zeros
    (fun i => netWeight c θ s β ((positiveLines c θ s β).orderEmbOfFin rfl i))
    ((positiveLines c θ s β).orderEmbOfFin rfl)
    (fun k => -netWeight c θ s β ((negativeLines c θ s β).orderEmbOfFin rfl k))
    ((negativeLines c θ s β).orderEmbOfFin rfl) hn
    ((positiveLines c θ s β).orderEmbOfFin rfl).strictMono
    hrange.1 hrange.2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2
  exact ⟨⟨_, hresult.1⟩, hresult.2⟩

end LineSurface
end PaperLeanFormalization.Planar




open Real Filter
open scoped BigOperators Topology
noncomputable section

namespace PaperLeanFormalization.Planar.GenericResidualPartials

variable {n m : ℕ}

theorem differentiable_finiteKernelLoss (K : ℝ → ℝ)
    (hK : Differentiable ℝ K) (s beta : Fin m → ℝ) :
    Differentiable ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Beam.finiteKernelLoss K s beta p.1 p.2) :=
  differentiable_finite_kernel_loss K hK s beta

theorem fderiv_finiteKernelLoss_apply (K K1 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x)
    (c dc theta v : Fin n → ℝ) (s beta : Fin m → ℝ) :
    fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Beam.finiteKernelLoss K s beta p.1 p.2) (c, theta) (dc, v) =
        Beam.finiteKernelSlope K K1 c dc theta v s beta 0 := by
  have hc : HasDerivAt (fun t : ℝ => fun i => c i + t * dc i) dc 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dc i)).const_add (c i)
  have ht : HasDerivAt (fun t : ℝ => fun i => theta i + t * v i) v 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (theta i)
  have hf := (differentiable_finiteKernelLoss K (fun x => (hK x).differentiableAt)
    s beta (c, theta)).hasFDerivAt
  have hf' : HasFDerivAt (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Beam.finiteKernelLoss K s beta p.1 p.2)
      (fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Beam.finiteKernelLoss K s beta p.1 p.2) (c, theta))
      ((fun i => c i + 0 * dc i), (fun i => theta i + 0 * v i)) := by simpa using hf
  have hcomp := hf'.comp_hasDerivAt 0 (hc.prod ht)
  exact hcomp.unique (Beam.hasDerivAt_finiteKernelLoss_line K K1 hK c dc theta v s beta 0)

/-- The normalized mass coordinate derivative; no mass signs are assumed. -/
theorem mass_partial (K K1 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x) (hEven : ∀ x, K (-x) = K x)
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (i : Fin n) :
    fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Beam.finiteKernelLoss K s beta p.1 p.2) (c, theta) (Pi.single i 1, 0) =
      (1 / (2 * π)) * Beam.finiteResidual K c theta s beta (theta i) := by
  classical
  rw [fderiv_finiteKernelLoss_apply K K1 hK]
  simp only [Beam.finiteKernelSlope, Pi.zero_apply, sub_self, mul_zero, zero_mul, add_zero]
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero, mul_zero]
  have hswap (j : Fin n) : K (theta j - theta i) = K (theta i - theta j) := by
    rw [show theta j - theta i = -(theta i - theta j) by ring, hEven]
  simp_rw [hswap]
  unfold Beam.finiteResidual
  ring

/-- The normalized angular coordinate derivative, valid even at zero masses. -/
theorem angle_partial (K K1 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x) (hOdd : ∀ x, K1 (-x) = -K1 x)
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (i : Fin n) :
    fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Beam.finiteKernelLoss K s beta p.1 p.2) (c, theta) (0, Pi.single i 1) =
      (1 / (2 * π)) * c i * Beam.finiteResidual K1 c theta s beta (theta i) := by
  classical
  rw [fderiv_finiteKernelLoss_apply K K1 hK]
  simp only [Beam.finiteKernelSlope, Pi.zero_apply, zero_mul, mul_zero, zero_add, add_zero]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  have hswap (j : Fin n) : K1 (theta j - theta i) = -K1 (theta i - theta j) := by
    rw [show theta j - theta i = -(theta i - theta j) by ring, hOdd]
  simp_rw [hswap]
  simp_rw [mul_comm _ (c i)]
  simp_rw [mul_neg, Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum]
  unfold Beam.finiteResidual
  ring

/-- The same angular derivative expressed through the actual residual derivative. -/
theorem angle_partial_residual_deriv (K K1 : ℝ → ℝ)
    (hK : ∀ x, HasDerivAt K (K1 x) x) (hOdd : ∀ x, K1 (-x) = -K1 x)
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (i : Fin n) :
    fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Beam.finiteKernelLoss K s beta p.1 p.2) (c, theta) (0, Pi.single i 1) =
      (1 / (2 * π)) * c i * deriv (Beam.finiteResidual K c theta s beta) (theta i) := by
  rw [angle_partial K K1 hK hOdd,
    (Beam.hasDerivAt_finiteResidual K K1 hK c theta s beta (theta i)).deriv]

end PaperLeanFormalization.Planar.GenericResidualPartials

namespace PaperLeanFormalization.Planar.GaussianSurface

open PaperLeanFormalization.Definitions
variable {n m : ℕ}

def modelKernel (q : PaperLeanFormalization.Model) (x : ℝ) : ℝ := Kernel q (cos x)

def modelSlope : PaperLeanFormalization.Model → ℝ → ℝ
  | .centered, x => kernelD1 x
  | .plainRelu, x => kernelD1 x - (π / 2) * sin x

theorem hasDerivAt_modelKernel (q : PaperLeanFormalization.Model) (x : ℝ) :
    HasDerivAt (modelKernel q) (modelSlope q x) x := by
  cases q with
  | centered => exact hasDerivAt_kernel x
  | plainRelu =>
    convert (hasDerivAt_kernel x).add ((hasDerivAt_cos x).const_mul (π / 2)) using 1
    dsimp only [modelSlope]
    ring

theorem modelKernel_even (q : PaperLeanFormalization.Model) (x : ℝ) :
    modelKernel q (-x) = modelKernel q x := by
  simp only [modelKernel, cos_neg]

theorem modelSlope_odd (q : PaperLeanFormalization.Model) (x : ℝ) :
    modelSlope q (-x) = -modelSlope q x := by
  cases q with
  | centered => exact kernelD1_neg x
  | plainRelu => simp only [modelSlope, kernelD1_neg, sin_neg]; ring

theorem modelLoss_eq_finiteKernelLoss (q : PaperLeanFormalization.Model)
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    Loss q c (fun i => Angle (theta i)) s (fun k => Angle (beta k)) =
      Beam.finiteKernelLoss (modelKernel q) s beta c theta := by
  rw [Preliminaries.loss_eq_kernelEnergy (by norm_num) q c _ s _
    (fun i => Preliminaries.angle_unit (theta i)) (fun k => Preliminaries.angle_unit (beta k))]
  simp only [Preliminaries.KernelEnergy, Beam.finiteKernelLoss,
    Preliminaries.angle_inner, modelKernel]

/-- `rem:planar_residual_equivalence`: the ambient chart identity and both
actual coordinate evaluations of the full Fréchet derivative, for either model. -/
theorem rem_planar_residual_equivalence (q : PaperLeanFormalization.Model)
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) :
    (∀ γ : ℝ,
      Residual q c (fun i => Angle (θ i)) s (fun k => Angle (β k)) (Angle γ) =
        PlanarResidual q c θ s β γ) ∧
    (∀ i : Fin n,
      fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Loss q p.1 (fun j => Angle (p.2 j)) s (fun k => Angle (β k)))
        (c, θ) (Pi.single i 1, 0) = (1 / (2 * π)) * PlanarResidual q c θ s β (θ i)) ∧
    (∀ i : Fin n,
      fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Loss q p.1 (fun j => Angle (p.2 j)) s (fun k => Angle (β k)))
        (c, θ) (0, Pi.single i 1) =
          (1 / (2 * π)) * c i * deriv (PlanarResidual q c θ s β) (θ i)) := by
  have heq : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Loss q p.1 (fun j => Angle (p.2 j)) s (fun k => Angle (β k))) =
      (fun p => Beam.finiteKernelLoss (modelKernel q) s β p.1 p.2) := by
    funext p
    exact modelLoss_eq_finiteKernelLoss q p.1 p.2 s β
  refine ⟨Preliminaries.ambient_residual_eq_planar q c θ s β, ?_, ?_⟩
  · intro i
    rw [heq]
    exact GenericResidualPartials.mass_partial (modelKernel q) (modelSlope q)
      (hasDerivAt_modelKernel q) (modelKernel_even q) c θ s β i
  · intro i
    rw [heq]
    exact GenericResidualPartials.angle_partial_residual_deriv (modelKernel q) (modelSlope q)
      (hasDerivAt_modelKernel q) (modelSlope_odd q) c θ s β i

/-- The literal Gaussian loss and the finite angular formula differ by exactly
the displayed positive scale and teacher-only constant. -/
theorem centeredLoss_eq_variableLoss
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    CenteredLoss c (fun i => Angle (theta i)) s (fun k => Angle (beta k)) =
      (1 / (2 * π)) * (variableLoss s beta (c, theta) - variableLoss s beta (s, beta)) := by
  change Loss .centered c (fun i => Angle (theta i)) s (fun k => Angle (beta k)) = _
  rw [Preliminaries.loss_eq_kernelEnergy (by norm_num) .centered c _ s _
    (fun i => Preliminaries.angle_unit (theta i)) (fun k => Preliminaries.angle_unit (beta k))]
  simp only [Preliminaries.KernelEnergy, Preliminaries.angle_inner, Kernel, variableLoss, kernel]
  ring

theorem centeredLoss_isLocalMin_iff
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (beta k))) (c, theta) ↔
      IsLocalMin (variableLoss s beta) (c, theta) := by
  have heq : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (beta k))) =
      fun p => (1 / (2 * π)) * (variableLoss s beta p - variableLoss s beta (s, beta)) := by
    funext p
    exact centeredLoss_eq_variableLoss p.1 p.2 s beta
  rw [heq]
  change (∀ᶠ p in 𝓝 (c, theta),
    (1 / (2 * π)) * (variableLoss s beta (c, theta) - variableLoss s beta (s, beta)) ≤
      (1 / (2 * π)) * (variableLoss s beta p - variableLoss s beta (s, beta))) ↔ _
  simp only [mul_le_mul_left (by positivity : 0 < (1 / (2 * π) : ℝ)),
    sub_le_sub_iff_right]
  rfl

theorem centeredLoss_critical_iff
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (beta k))) (c, theta) = 0 ↔
      fderiv ℝ (variableLoss s beta) (c, theta) = 0 := by
  have heq : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (beta k))) =
      fun p => (1 / (2 * π)) * (variableLoss s beta p - variableLoss s beta (s, beta)) := by
    funext p
    exact centeredLoss_eq_variableLoss p.1 p.2 s beta
  rw [heq, (((differentiable_variableLoss s beta (c, theta)).hasFDerivAt.sub_const
    (variableLoss s beta (s, beta))).const_mul (1 / (2 * π) : ℝ)).fderiv]
  have hscale : (1 / (2 * π) : ℝ) ≠ 0 :=
    div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero)
  simp only [smul_eq_zero, hscale, false_or]

theorem lem_critical_points_are_double_zeros
    {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hcrit : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (β k))) (c, θ) = 0)
    (i : Fin n) (hi : c i ≠ 0) :
    PlanarResidual .centered c θ s β (θ i) = 0 ∧
      deriv (PlanarResidual .centered c θ s β) (θ i) = 0 := by
  have h := rem_planar_residual_equivalence .centered c θ s β
  have hm := h.2.1 i
  have ha := h.2.2 i
  change fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
    CenteredLoss p.1 (fun j => Angle (p.2 j)) s (fun k => Angle (β k))) (c, θ)
      (Pi.single i 1, 0) = _ at hm
  change fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
    CenteredLoss p.1 (fun j => Angle (p.2 j)) s (fun k => Angle (β k))) (c, θ)
      (0, Pi.single i 1) = _ at ha
  rw [hcrit, ContinuousLinearMap.zero_apply] at hm ha
  have hscale : (1 / (2 * π) : ℝ) ≠ 0 :=
    div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero)
  exact ⟨(mul_eq_zero.mp hm.symm).resolve_left hscale,
    (mul_eq_zero.mp ha.symm).resolve_left (mul_ne_zero hscale hi)⟩

theorem centeredLoss_eq_finiteKernelLoss
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    CenteredLoss c (fun i => Angle (theta i)) s (fun k => Angle (beta k)) =
      Beam.finiteKernelLoss kernel s beta c theta := by
  rw [centeredLoss_eq_variableLoss, finiteKernelLoss_eq_variableLoss]
  unfold variableLoss
  dsimp only
  ring

theorem kernel_angle_shift_sub (x y : ℝ) (a b : ℤ) :
    kernel ((x + (a : ℝ) * π) - (y + (b : ℝ) * π)) = kernel (x - y) := by
  have hp : Function.Periodic kernel π := BeamGapKernel.kernel_add_pi
  convert hp.int_mul (a - b) (x - y) using 1
  congr 1
  push_cast
  ring

theorem finiteKernelLoss_angle_int_shifts
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (a : Fin n → ℤ) :
    Beam.finiteKernelLoss kernel s beta c (fun i => theta i + (a i : ℝ) * π) =
      Beam.finiteKernelLoss kernel s beta c theta := by
  have hs (i j : Fin n) := kernel_angle_shift_sub (theta i) (theta j) (a i) (a j)
  have ht (i : Fin n) (k : Fin m) :
      kernel (theta i + (a i : ℝ) * π - beta k) = kernel (theta i - beta k) := by
    simpa using kernel_angle_shift_sub (theta i) (beta k) (a i) 0
  simp only [Beam.finiteKernelLoss, hs, ht]

theorem residual_angle_int_shifts
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (a : Fin n → ℤ) :
    residual c (fun i => theta i + (a i : ℝ) * π) s beta = residual c theta s beta := by
  funext x
  unfold residual
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simpa using kernel_angle_shift_sub x (theta i) 0 (a i)

/-- The first step of the opposed-rotation sketch: integer π shifts preserve
the actual loss and residual, so a common line can be represented by equal angles. -/
theorem opposed_rotation_curvature_of_int_shift
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (p q : Fin n)
    (hpq : p ≠ q) (hline : ∃ k : ℤ, theta p = theta q + (k : ℝ) * π) :
    deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
      (fun i => theta i + t * opposedVelocity c p q i))) 0 =
      c p * c q * (c p + c q) / (2 * π) *
        deriv (deriv (residual c theta s beta)) (theta p) := by
  classical
  obtain ⟨k, hk⟩ := hline
  let a : Fin n → ℤ := fun i => if i = q then k else 0
  let shifted : Fin n → ℝ := fun i => theta i + (a i : ℝ) * π
  have hp : shifted p = theta p := by simp [shifted, a, hpq]
  have hq : shifted q = theta p := by simpa [shifted, a] using hk.symm
  have heq : (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
      (fun i => shifted i + t * opposedVelocity c p q i)) =
      (fun t : ℝ => Beam.finiteKernelLoss kernel s beta c
        (fun i => theta i + t * opposedVelocity c p q i)) := by
    funext t
    convert finiteKernelLoss_angle_int_shifts c
      (fun i => theta i + t * opposedVelocity c p q i) s beta a using 1
    congr 1
    funext i
    dsimp [shifted]
    ring
  have hres : residual c shifted s beta = residual c theta s beta :=
    residual_angle_int_shifts c theta s beta a
  have h := eq_opposed_rotation_curvature c shifted s beta hpq (hp.trans hq.symm)
  rw [heq, hres, hp] at h
  exact h

theorem lem_opposed_rotation
    (c θ : Fin n → ℝ) (s β : Fin m → ℝ) (p q : Fin n)
    (hpq : p ≠ q) (hline : ∃ k : ℤ, θ p = θ q + (k : ℝ) * π) :
    let dθ : Fin n → ℝ := fun i => if i = p then c q else if i = q then -c p else 0
    deriv (deriv (fun t : ℝ =>
      CenteredLoss c (fun i => Angle (θ i + t * dθ i)) s (fun k => Angle (β k)))) 0 =
      c p * c q * (c p + c q) / (2 * π) *
        deriv (deriv (PlanarResidual .centered c θ s β)) (θ p) := by
  change deriv (deriv (fun t : ℝ =>
    CenteredLoss c (fun i => Angle (θ i + t * opposedVelocity c p q i))
      s (fun k => Angle (β k)))) 0 = _
  have heq : (fun t : ℝ =>
      CenteredLoss c (fun i => Angle (θ i + t * opposedVelocity c p q i))
        s (fun k => Angle (β k))) =
      (fun t : ℝ => Beam.finiteKernelLoss kernel s β c
        (fun i => θ i + t * opposedVelocity c p q i)) := by
    funext t
    exact centeredLoss_eq_finiteKernelLoss c _ s β
  rw [heq]
  exact opposed_rotation_curvature_of_int_shift c θ s β p q hpq hline

theorem prop_S_plus_eq_student_lines
    {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i < π) (hβ : ∀ k, 0 ≤ β k ∧ β k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hcrit : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (β k))) (c, θ) = 0)
    (hcard : 2 ≤ (PositiveLines c θ s β).card) :
    PositiveLines c θ s β = Finset.univ.image θ := by
  exact positive_lines_eq_student_lines hθ hβ hc (fun k => (hs k).le)
    ((centeredLoss_critical_iff c θ s β).mp hcrit)
    (Finset.card_pos.mp (lt_of_lt_of_le (by norm_num : 0 < 2) hcard))

theorem positive_lines_nonempty_of_spurious
    (hn : 0 < n) (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hmin : IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (beta k))) (c, theta))
    (hspur : 0 < CenteredLoss c (fun i => Angle (theta i)) s (fun k => Angle (beta k))) :
    (positiveLines c theta s beta).Nonempty := by
  by_contra hnot
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
  have hminFinite := (centeredLoss_isLocalMin_iff c theta s beta).mp hmin
  let i : Fin n := ⟨0, hn⟩
  have hres := empty_positive_support_residual_zero c theta s beta hempty
    (theta i) (mass_stationarity hminFinite.fderiv_eq_zero i)
  have hequal := variableLoss_eq_exact_fit_of_residual_zero c theta s beta hres
  rw [centeredLoss_eq_variableLoss, hequal, sub_self, mul_zero] at hspur
  exact lt_irrefl 0 hspur

theorem lem_no_collisions {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i < π) (hβ : ∀ k, 0 ≤ β k ∧ β k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hmin : IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (β k))) (c, θ))
    (hspur : 0 < CenteredLoss c (fun i => Angle (θ i)) s (fun k => Angle (β k))) :
    (Finset.univ.image θ).card = n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hne := positive_lines_nonempty_of_spurious (Nat.pos_of_ne_zero hn) c θ s β hmin hspur
  have hinj := no_collisions_of_nonempty_positive_lines hθ hβ hc (fun k => (hs k).le)
    ((centeredLoss_isLocalMin_iff c θ s β).mp hmin) hne
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

theorem prop_locamin_are_line_separated (hmn : m ≤ n)
    {c θ : Fin n → ℝ} {s β : Fin m → ℝ}
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i < π) (hβ : ∀ k, 0 ≤ β k ∧ β k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hmin : IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (β k))) (c, θ))
    (hspur : 0 < CenteredLoss c (fun i => Angle (θ i)) s (fun k => Angle (β k))) :
    n = m ∧ Function.Injective θ ∧ Function.Injective β ∧
      (∀ i k, θ i ≠ β k) ∧
      ∃ hθinj : Function.Injective θ,
        cyclically_strictly_interlaces_general θ β hθinj := by
  have hn : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    have hmzero : m = 0 := by omega (config := {})
    subst n
    subst m
    simp [CenteredLoss] at hspur
  have hne := positive_lines_nonempty_of_spurious hn c θ s β hmin hspur
  obtain ⟨hnm, hinj, hbinj, hsep, hsi⟩ :=
    clean_structure_of_nonempty_positive_lines hmn hθ hβ hc hs
      ((centeredLoss_isLocalMin_iff c θ s β).mp hmin) hne
  exact ⟨hnm, hinj, hbinj, hsep, hsi.students_injective, hsi.interlaces⟩

end PaperLeanFormalization.Planar.GaussianSurface


open Real Filter Set
open scoped BigOperators Topology
noncomputable section

namespace PaperLeanFormalization.Planar.ZeroSlot

variable {n m : ℕ}

/-- Within an open minimizer neighborhood, every equal-value point is itself
a local minimizer. This uses no differentiability or coordinate assumptions. -/
theorem local_min_near_equal_value {E : Type*} [TopologicalSpace E]
    {f : E → ℝ} {x : E} (hmin : IsLocalMin f x) :
    ∀ᶠ y in 𝓝 x, f y = f x → IsLocalMin f y := by
  obtain ⟨U, hU, hUopen, hx⟩ := mem_nhds_iff.mp hmin
  filter_upwards [hUopen.mem_nhds hx] with y hy heq
  apply IsMinOn.isLocalMin (s := U) _ (hUopen.mem_nhds hy)
  intro z hz
  rw [heq]
  exact hU hz

theorem variableLoss_update_zero_mass
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (j : Fin n) (hj : c j = 0) (t : ℝ) :
    variableLoss s beta (c, Function.update theta j t) = variableLoss s beta (c, theta) := by
  classical
  unfold variableLoss
  dsimp only
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    by_cases hi : i = j
    · subst i
      simp only [hj, zero_mul]
    by_cases hk : k = j
    · subst k
      simp only [hj, mul_zero, zero_mul]
    simp only [Function.update_noteq hi, Function.update_noteq hk]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    by_cases hi : i = j
    · subst i
      simp only [hj, zero_mul]
    simp only [Function.update_noteq hi]

theorem residual_update_zero_mass
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (j : Fin n) (hj : c j = 0) (t x : ℝ) :
    residual c (Function.update theta j t) s beta x = residual c theta s beta x := by
  classical
  unfold residual
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = j
  · subst i
    simp only [hj, zero_mul]
  simp only [Function.update_noteq hi]

/-- A zero-mass slot is free to move along a whole neighborhood of angles.
Stationarity in that slot's mass therefore forces a genuine open zero arc. -/
theorem zero_mass_slot_residual_zero_arc
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (j : Fin n) (hj : c j = 0)
    (hmin : IsLocalMin (variableLoss s beta) (c, theta)) :
    ∃ ε > 0, ∀ x : ℝ, |x - theta j| < ε → residual c theta s beta x = 0 := by
  classical
  let path : ℝ → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun t => (c, Function.update theta j t)
  have hpath : Continuous path := by
    apply Continuous.prod_mk continuous_const
    apply continuous_pi
    intro i
    by_cases hi : i = j
    · subst i
      simpa only [Function.update_same] using (continuous_id : Continuous (fun t : ℝ => t))
    simpa only [Function.update_noteq hi] using
      (continuous_const : Continuous (fun _ : ℝ => theta i))
  have hbase : path (theta j) = (c, theta) := by simp [path]
  have hminbase : IsLocalMin (variableLoss s beta) (path (theta j)) := by
    rw [hbase]
    exact hmin
  have hnear := hpath.continuousAt.eventually (local_min_near_equal_value hminbase)
  have hzero : ∀ᶠ x in 𝓝 (theta j), residual c theta s beta x = 0 := by
    filter_upwards [hnear] with t ht
    have heq : variableLoss s beta (path t) = variableLoss s beta (path (theta j)) := by
      rw [hbase]
      exact variableLoss_update_zero_mass c theta s beta j hj t
    have hminat := ht heq
    have hz := mass_stationarity hminat.fderiv_eq_zero j
    change residual c (Function.update theta j t) s beta ((Function.update theta j t) j) = 0 at hz
    rw [Function.update_same, residual_update_zero_mass c theta s beta j hj t t] at hz
    exact hz
  obtain ⟨ε, hε, hzeroε⟩ := Metric.eventually_nhds_iff.mp hzero
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact hzeroε (by simpa only [Real.dist_eq] using hx)

end PaperLeanFormalization.Planar.ZeroSlot


/-! ## Complete centered descent from clean criticality -/

noncomputable section
open Real
open scoped BigOperators

namespace PaperLeanFormalization.Planar

/-- Once the distinct students are sorted, the fresh double-zero gap census
selects the unique teacher in each gap. No interlacing object or independently
assumed beam data is needed by the actual second-variation construction. -/
theorem ordered_beam_descent_of_double_zeros {r : ℕ} (hr : 0 < r)
    (c theta s beta : Fin (r + 1) → ℝ)
    (hmono : StrictMono theta)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0) :
    ∃ dc dtheta : Fin (r + 1) → ℝ,
      deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta
        (fun i => c i + t * dc i) (fun i => theta i + t * dtheta i))) 0 < 0 := by
  obtain ⟨teacher, hteacher⟩ := ordered_singleton_teacher_gaps c theta s beta
    hmono htheta hbeta hc hs hsep hzero htorque (le_refl _)
  have hkernel : kernel = CircleMoments.K := funext kernel_eq_circle_moment
  have hK (t : ℝ) : HasDerivAt CircleMoments.K (CircleMoments.K1 t) t := by
    rw [← hkernel]
    exact hasDerivAt_kernel t
  have hK1 (t : ℝ) : HasDerivAt CircleMoments.K1 (CircleMoments.K2 t) t := by
    change HasDerivAt kernelD1 (2 * |sin t| - CircleMoments.K t) t
    rw [← hkernel]
    exact hasDerivAt_kernelD1 t
  obtain ⟨dc, dtheta, hnegative⟩ := ordered_beam_descent_of_single_teacher_gaps
    hK hK1 hr c theta s beta teacher hmono htheta hbeta hc hs
    (fun i k => (hsep i k).symm) hzero htorque hteacher
  exact ⟨dc, dtheta, by simpa only [hkernel] using hnegative⟩

end PaperLeanFormalization.Planar

open Real
open scoped BigOperators
noncomputable section

namespace PaperLeanFormalization.Planar.DescentPermutation

variable {n m : ℕ}

/-- Relabeling students preserves the full normalized finite loss, including
the teacher-only term. No symmetry or regularity of the kernel is needed. -/
theorem finiteKernelLoss_student_permutation (K : ℝ → ℝ) (e : Equiv.Perm (Fin n))
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    Beam.finiteKernelLoss K s beta (fun i => c (e i)) (fun i => theta (e i)) =
      Beam.finiteKernelLoss K s beta c theta := by
  have hstudent :
      (∑ i, ∑ j, c (e i) * c (e j) * K (theta (e i) - theta (e j))) =
        ∑ i, ∑ j, c i * c j * K (theta i - theta j) := by
    calc
      _ = ∑ i, ∑ j, c (e i) * c j * K (theta (e i) - theta j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp e
          (fun j : Fin n => c (e i) * c j * K (theta (e i) - theta j))
      _ = _ := Equiv.sum_comp e
        (fun i : Fin n => ∑ j, c i * c j * K (theta i - theta j))
  have hteacher : (∑ i, ∑ k, c (e i) * s k * K (theta (e i) - beta k)) =
      ∑ i, ∑ k, c i * s k * K (theta i - beta k) :=
    Equiv.sum_comp e (fun i : Fin n => ∑ k, c i * s k * K (theta i - beta k))
  simp only [Beam.finiteKernelLoss, hstudent, hteacher]

/-- A direction constructed in sorted coordinates is pulled back by the
inverse permutation. The equality holds for the entire affine loss curve. -/
theorem finiteKernelLoss_affine_path_pullback (K : ℝ → ℝ) (e : Equiv.Perm (Fin n))
    (c theta dcSorted dthetaSorted : Fin n → ℝ) (s beta : Fin m → ℝ) :
    (fun t : ℝ => Beam.finiteKernelLoss K s beta
      (fun i => c (e i) + t * dcSorted i)
      (fun i => theta (e i) + t * dthetaSorted i)) =
    (fun t : ℝ => Beam.finiteKernelLoss K s beta
      (fun i => c i + t * dcSorted (e.symm i))
      (fun i => theta i + t * dthetaSorted (e.symm i))) := by
  funext t
  simpa only [Equiv.symm_apply_apply] using
    finiteKernelLoss_student_permutation K e
      (fun i => c i + t * dcSorted (e.symm i))
      (fun i => theta i + t * dthetaSorted (e.symm i)) s beta

/-- Negativity of the actual second derivative is unchanged by relabeling;
the transport uses equality of scalar loss curves, not a reduced certificate. -/
theorem negative_second_derivative_pullback (K : ℝ → ℝ) (e : Equiv.Perm (Fin n))
    (c theta dcSorted dthetaSorted : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hnegative : deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss K s beta
      (fun i => c (e i) + t * dcSorted i)
      (fun i => theta (e i) + t * dthetaSorted i))) 0 < 0) :
    deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss K s beta
      (fun i => c i + t * dcSorted (e.symm i))
      (fun i => theta i + t * dthetaSorted (e.symm i)))) 0 < 0 := by
  rw [finiteKernelLoss_affine_path_pullback K e c theta dcSorted dthetaSorted s beta] at hnegative
  exact hnegative

theorem exists_negative_second_derivative_pullback (K : ℝ → ℝ) (e : Equiv.Perm (Fin n))
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hnegative : ∃ dc dtheta : Fin n → ℝ,
      deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss K s beta
        (fun i => c (e i) + t * dc i)
        (fun i => theta (e i) + t * dtheta i))) 0 < 0) :
    ∃ dc dtheta : Fin n → ℝ,
      deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss K s beta
        (fun i => c i + t * dc i)
        (fun i => theta i + t * dtheta i))) 0 < 0 := by
  obtain ⟨dc, dtheta, hnegative⟩ := hnegative
  exact ⟨(fun i => dc (e.symm i)), (fun i => dtheta (e.symm i)),
    negative_second_derivative_pullback K e c theta dc dtheta s beta hnegative⟩

end PaperLeanFormalization.Planar.DescentPermutation

noncomputable section
open Real
open scoped BigOperators

namespace PaperLeanFormalization.Planar

/-- A single student permutation puts the configuration into cyclic order.
The residual double zeros and the complete affine loss curve are invariant
under this reindexing, so the constructed direction pulls back directly. -/
theorem clean_beam_descent_of_double_zeros {n : ℕ}
    (c theta s beta : Fin n → ℝ) (hn : 2 ≤ n)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hdist : Function.Injective theta)
    (hsep : ∀ i k, theta i ≠ beta k)
    (hzero : ∀ i, residual c theta s beta (theta i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c theta s beta (theta i) = 0) :
    ∃ dc dtheta : Fin n → ℝ,
      deriv (deriv (fun t : ℝ => Beam.finiteKernelLoss kernel s beta
        (fun i => c i + t * dc i) (fun i => theta i + t * dtheta i))) 0 < 0 := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 1 hn)
  | succ r =>
    have hr : 0 < r := by omega (config := {})
    obtain ⟨e, hmono⟩ := exists_sorting_permutation theta hdist
    have hzero' : ∀ i,
        residual (fun i => c (e i)) (fun i => theta (e i)) s beta (theta (e i)) = 0 := by
      intro i
      rw [residual_student_permutation e c theta s beta]
      exact hzero (e i)
    have htorque' : ∀ i,
        BeamGapKernel.residualTorque (fun i => c (e i)) (fun i => theta (e i))
          s beta (theta (e i)) = 0 := by
      intro i
      rw [torque_student_permutation e c theta s beta]
      exact htorque (e i)
    apply DescentPermutation.exists_negative_second_derivative_pullback kernel e c theta s beta
    exact ordered_beam_descent_of_double_zeros hr (fun i => c (e i))
      (fun i => theta (e i)) s beta hmono (fun i => htheta (e i)) hbeta
      (fun i => hc (e i)) hs (fun i k => hsep (e i) k) hzero' htorque'

namespace GaussianSurface
open PaperLeanFormalization.Definitions

/-- `eq:beam-descent-direction`: the constructed finite-kernel direction
has negative second variation for the actual Gaussian loss as well. The
normalization transport is equality of the entire affine loss curve. -/
theorem eq_beam_descent_direction {n : ℕ} (c θ s β : Fin n → ℝ) (hn : 2 ≤ n)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i < π) (hβ : ∀ k, 0 ≤ β k ∧ β k < π)
    (hdist : Function.Injective θ) (hdisj : ∀ i k, θ i ≠ β k)
    (hzero : ∀ i, residual c θ s β (θ i) = 0)
    (htorque : ∀ i, BeamGapKernel.residualTorque c θ s β (θ i) = 0) :
    ∃ dc dθ : Fin n → ℝ,
      deriv (deriv (fun t : ℝ => CenteredLoss (fun i => c i + t * dc i)
        (fun i => Angle (θ i + t * dθ i)) s (fun k => Angle (β k)))) 0 < 0 := by
  obtain ⟨dc, dθ, hnegative⟩ := clean_beam_descent_of_double_zeros c θ s β hn hc hs
    hθ hβ hdist hdisj hzero htorque
  refine ⟨dc, dθ, ?_⟩
  have heq : (fun t : ℝ => CenteredLoss (fun i => c i + t * dc i)
      (fun i => Angle (θ i + t * dθ i)) s (fun k => Angle (β k))) =
      (fun t : ℝ => Beam.finiteKernelLoss kernel s β
        (fun i => c i + t * dc i) (fun i => θ i + t * dθ i)) := by
    funext t
    exact centeredLoss_eq_finiteKernelLoss _ _ s β
  rw [heq]
  exact hnegative

/-- `prop:beam-descent`: the fresh cyclic construction produces a direction
of negative second variation of the actual normalized Gaussian loss.
Criticality is used only once, to supply the student residual double zeros. -/
theorem prop_beam_descent {n : ℕ} (c θ s β : Fin n → ℝ) (hn : 2 ≤ n)
    (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i < π) (hβ : ∀ k, 0 ≤ β k ∧ β k < π)
    (hdist : Function.Injective θ) (hteach : Function.Injective β)
    (hdisj : ∀ i k, θ i ≠ β k)
    (hcrit : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      CenteredLoss p.1 (fun i => Angle (p.2 i)) s (fun k => Angle (β k))) (c, θ) = 0) :
    ∃ dc dθ : Fin n → ℝ,
      deriv (deriv (fun t : ℝ => CenteredLoss (fun i => c i + t * dc i)
        (fun i => Angle (θ i + t * dθ i)) s (fun k => Angle (β k)))) 0 < 0 := by
  clear hteach
  have hzero (i : Fin n) : residual c θ s β (θ i) = 0 ∧
      deriv (residual c θ s β) (θ i) = 0 :=
    lem_critical_points_are_double_zeros hcrit i (ne_of_gt (hc i))
  have htorque (i : Fin n) : BeamGapKernel.residualTorque c θ s β (θ i) = 0 := by
    have hd : deriv (residual c θ s β) (θ i) =
        BeamGapKernel.residualTorque c θ s β (θ i) :=
      (hasDerivAt_residual c θ s β (θ i)).deriv
    exact hd.symm.trans (hzero i).2
  exact eq_beam_descent_direction c θ s β hn hc hs
    hθ hβ hdist hdisj (fun i => (hzero i).1) htorque

end GaussianSurface
end PaperLeanFormalization.Planar
