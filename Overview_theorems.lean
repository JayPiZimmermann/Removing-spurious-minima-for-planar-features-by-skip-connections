import Theorems

/-!
# The five contributions

The five theorems below are the contribution bullets of the paper, using their
referenced statements in the accompanying paper: `thm:headline`,
`thm:plain-trap`, `prop:teacher-span-confinement`,
`prop:plain-collision-ceiling`, and `thm:fixed-radius-bridge`. Every
definition needed to read them is in `Overview_definitions.lean`; each proof
delegates to the corresponding statement in `Theorems.lean`.

As in the paper, `s : Fin n → ℝ` lists the student masses and
`w : Fin n → Vec d` their directions; `t, v` describe the teacher.
`bStudent` and `bTeacher` are the paper's student and teacher linear skip
vectors. Student angles are `θ`, teacher angles are `β`, and `τ` is a scalar
perturbation parameter. `Angle γ` is the paper's `e(γ)`; `.centered` and
`.plainRelu` denote its features `C` and `R`.
All local minima allow signed mass perturbations.
Nonnegativity is an assumption at the candidate, not a constraint on its
neighborhood. `IsLocalMinOn L S p` means that `L p ≤ L q` for all `q` in some
neighborhood of `p` within `S`; `IsMinOn L S p` requires this for every `q ∈ S`.

## Two conventions a reader should check

* The losses of `Overview_definitions.lean` are literal Bochner integrals, and
  Mathlib's integral of a non-integrable function is `0`.  They are not trivially
  zero: the loss–kernel identity behind `Theorems.lem_pair_moments` and
  `Theorems.prop_loss_in_residual` is proved from
  `Preliminaries.gaussian_loss_eq_kernel_energy_of_pair_moment`, which assumes
  integrability of every feature pair and is discharged by
  `Preliminaries.centered_feature_pair_integrable` and
  `Preliminaries.gaussian_plain_pair_integrable`; the squared centered residual
  and its product with the linear skip are integrable by
  `Skip.centered_residual_square_integrable` and
  `Skip.linear_centered_residual_integrable`; and `PlainTrap` below proves a
  strict inequality `0 < PlainLoss …`.
* Criticality in `EffectiveWidth` is written with `fderiv`, which is `0` at a
  point of non-differentiability.  The hypothesis is not vacuous: in mass–angle
  coordinates the plain loss is an affine rescaling of the finite kernel loss
  (`Plain.plain_loss_eq_excess_div`), which is globally `C²`
  (`Plain.ParameterCalculus.loss_contDiff_two`), so `fderiv ℝ … = 0` states that
  the genuine Fréchet derivative vanishes, equivalently `HasFDerivAt … 0 (s, θ)`.
-/

noncomputable section
open Real Set Filter MeasureTheory Classical
open scoped BigOperators Topology RealInnerProductSpace
open PaperLeanFormalization.Definitions PaperLeanFormalization.Theorems

namespace PaperLeanFormalization.Overview

local instance : DecidableEq (Vec 2) := Classical.decEq (Vec 2)

/-- 1. Linear skip: a positive coplanar teacher has zero loss at every
nonnegative local minimum once the student is at least as wide (`thm:headline`). -/
theorem Main {d n m : ℕ} (hd : 1 ≤ d) (hwidth : m ≤ n)
    {bStudent bTeacher : Vec d} {s : Fin n → ℝ} {w : Fin n → Vec d}
    {t : Fin m → ℝ} {v : Fin m → Vec d}
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hs : ∀ i, 0 ≤ s i) (ht : ∀ k, 0 < t k)
    (hmin : IsLocalMinOn
      (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, (s, w))) :
    SkipLoss bStudent s w bTeacher t v = 0 :=
  thm_headline hd hwidth hplane hv hw hs ht hmin

/-- 2. Spurious local minima at arbitrary overparameterization (`thm:plain-trap`).
The fixed teacher has unit masses at angles `0`, `5π/6`, and `4π/3`.

The three clauses are exactly the theorem's conclusions: at every width at
least three there is a positive-mass spurious minimum; at width three one is
strict; at larger widths one is non-strict. The first clause expresses
spuriousness by exhibiting a feasible point of strictly smaller loss.
The strict and non-strict witnesses have positive loss; copying the teacher
and adding zero-mass units gives a zero-loss competitor at these widths. -/
theorem PlainTrap :
    (∀ {n : ℕ} (_ : 3 ≤ n),
      ∃ s : Fin n → ℝ, ∃ w : Fin n → Vec 2,
        (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < s i) ∧
        IsLocalMinOn (fun p : Parameters 2 n =>
          PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
          {p | ∀ i, ‖p.2 i‖ = 1} (s, w) ∧
        ∃ s₀ : Fin n → ℝ, ∃ w₀ : Fin n → Vec 2,
          (∀ i, ‖w₀ i‖ = 1) ∧
          PlainLoss s₀ w₀ TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)) <
            PlainLoss s w TrapTeacherMass (fun k => Angle (TrapTeacherAngle k))) ∧
    (∃ s : Fin 3 → ℝ, ∃ w : Fin 3 → Vec 2,
        (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < s i) ∧
        IsStrictLocalMinOn (fun p : Parameters 2 3 =>
          PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
          {p | ∀ i, ‖p.2 i‖ = 1} (s, w) ∧
        0 < PlainLoss s w TrapTeacherMass (fun k => Angle (TrapTeacherAngle k))) ∧
    (∀ {n : ℕ} (_ : 3 < n),
      ∃ s : Fin n → ℝ, ∃ w : Fin n → Vec 2,
        (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < s i) ∧
        IsLocalMinOn (fun p : Parameters 2 n =>
          PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
          {p | ∀ i, ‖p.2 i‖ = 1} (s, w) ∧
        0 < PlainLoss s w TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)) ∧
        ¬ IsStrictLocalMinOn (fun p : Parameters 2 n =>
          PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
          {p | ∀ i, ‖p.2 i‖ = 1} (s, w)) :=
  ⟨@thm_plain_trap_spurious, thm_plain_trap_strict, @thm_plain_trap_flat⟩

/-- 3. Teacher-span confinement for both features
(`prop:teacher-span-confinement`).
Every student direction with positive mass lies in the teacher span.
This is containment; it does not assert that the student spans the whole space. -/
theorem Confinement {d n m : ℕ} (hd : 2 ≤ d) (q : Model)
    {s : Fin n → ℝ} {w : Fin n → Vec d} {t : Fin m → ℝ} {v : Fin m → Vec d}
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1) (hs : ∀ i, 0 ≤ s i)
    (hmin : IsLocalMinOn (fun p : Parameters d n => Loss q p.1 p.2 t v)
      {p | ∀ i, ‖p.2 i‖ = 1} (s, w)) :
    ∀ i, 0 < s i → w i ∈ Submodule.span ℝ (Set.range v) := by
  intro i hsi
  have hmem := prop_teacher_span_confinement hd q hv hw hs hmin i
  have hscaled := (Submodule.span ℝ (Set.range v)).smul_mem (s i)⁻¹ hmem
  simpa only [smul_smul, inv_mul_cancel (ne_of_gt hsi), one_smul] using hscaled

/-- 4. Effective width (`prop:plain-collision-ceiling`).
In dimension two, every positive-mass plain-ReLU critical point has at most
`2m` distinct oriented student directions. The second clause supplies
attainment: for every odd teacher width at least three there is a critical
point with exactly `2m` directions. Opposite directions count separately.
The `fderiv` hypothesis is a genuine derivative condition: see the conventions
in the module docstring (`Plain.plain_loss_eq_excess_div`,
`Plain.ParameterCalculus.loss_contDiff_two`). -/
theorem EffectiveWidth :
    (∀ {n m : ℕ} {s θ : Fin n → ℝ} {t β : Fin m → ℝ}
        (_ : ∀ i, 0 < s i)
        (_ : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          PlainLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ) = 0),
      (Finset.univ.image (fun i => Angle (θ i))).card ≤ 2 * m) ∧
    (∀ (m : ℕ) (_ : 3 ≤ m) (_ : Odd m),
      ∃ (s θ : Fin (m + m) → ℝ) (t β : Fin m → ℝ),
        (∀ i, 0 < s i) ∧ (∀ k, 0 < t k) ∧
        fderiv ℝ (fun p : (Fin (m + m) → ℝ) × (Fin (m + m) → ℝ) =>
          PlainLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ) = 0 ∧
        (Finset.univ.image (fun i => Angle (θ i))).card = 2 * m) :=
  ⟨@prop_plain_collision_ceiling, @prop_plain_collision_ceiling_sharp⟩

/-- 5. Transfer to empirical loss (`thm:fixed-radius-bridge`).

Fix the dimensions, teacher hidden units, and a positive radius `r`.
The teacher has positive masses and unit directions spanning at most two
dimensions; the student is at least as wide as the teacher. Every positive
input dimension is covered; in dimension one the conclusion holds for every
dataset, so the tolerance is not needed there.

There is an accuracy tolerance `δ > 0` that works for *every* nonempty dataset
and every candidate student satisfying the displayed conditions. In particular,
`δ` is chosen before the sample size, inputs, labels, skip vectors, and student
parameters. `DataAccuracy` is the explicit Gaussian approximation condition
in `Overview_definitions.lean`, using the observed average squared input radius. -/
theorem EmpiricalTransfer {d n m : ℕ} (hd : 1 ≤ d) (hwidth : m ≤ n)
    {t : Fin m → ℝ} {v : Fin m → Vec d}
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hteacherDirections : ∀ k, ‖v k‖ = 1) (hteacherMasses : ∀ k, 0 < t k)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ) (x : Fin N → Vec d) (y : Fin N → ℝ),
        0 < N → DataAccuracy x δ → ZeroLossForFixedRadiusMinima n x y t v r :=
  thm_fixed_radius_bridge hd hwidth hplane hteacherDirections hteacherMasses hr

end PaperLeanFormalization.Overview
