import Preliminaries
import Skip
import Beam
import Planar
import BentRing
import Geometry
import Plain
import Empirical

/-!
# The statements of the paper

This is the single theorem entry file for the independent formalization.
Every contract is stated explicitly below; its proof delegates only to a chapter
of this tree. The mathematical definitions, including the literal losses, are
collected in `Overview_definitions.lean`; the five contributions are proved
from these statements in `Overview_theorems.lean`. Labeled intermediate
equations remain beside their proofs in the chapters, rather than being mixed
into this statement index.

The population clauses retain their dimensions, sign assumptions, normalization,
and perturbation topology. The data clauses state their stochastic assumptions
explicitly. Several paper labels have more than one clause.
-/

noncomputable section
open Real Set Filter MeasureTheory
open scoped BigOperators Topology RealInnerProductSpace
open PaperLeanFormalization.Definitions

universe u

namespace PaperLeanFormalization.Theorems

local instance : DecidableEq (Vec 2) := Classical.decEq (Vec 2)

/-! ## Raw coordinates and the linear skip -/

/-- `lem:raw-transfer`: critical points, local minima, and spurious local minima. -/
theorem lem_raw_transfer :
    ∀ {d n m : ℕ} (q : Model) (o : Fin n → ℝ) (a : Fin n → Vec d)
      (t : Fin m → ℝ) (v : Fin m → Vec d) (_ : ∀ i, a i ≠ 0),
    (HasFDerivAt (fun p : Parameters d n => Loss q p.1 p.2 t v)
        (0 : Parameters d n →L[ℝ] ℝ) (o, a) ↔
      HasFDerivWithinAt (fun p : Parameters d n => Loss q p.1 p.2 t v)
        (0 : Parameters d n →L[ℝ] ℝ) {p | ∀ i, ‖p.2 i‖ = 1} (Normalize o a)) ∧
    (IsLocalMin (fun p : Parameters d n => Loss q p.1 p.2 t v) (o, a) ↔
      IsLocalMinOn (fun p : Parameters d n => Loss q p.1 p.2 t v)
        {p | ∀ i, ‖p.2 i‖ = 1} (Normalize o a)) ∧
    ((IsLocalMin (fun p : Parameters d n => Loss q p.1 p.2 t v) (o, a) ∧
        ¬ IsMinOn (fun p : Parameters d n => Loss q p.1 p.2 t v) Set.univ (o, a)) ↔
      (IsLocalMinOn (fun p : Parameters d n => Loss q p.1 p.2 t v)
          {p | ∀ i, ‖p.2 i‖ = 1} (Normalize o a) ∧
        ¬ IsMinOn (fun p : Parameters d n => Loss q p.1 p.2 t v)
          {p | ∀ i, ‖p.2 i‖ = 1} (Normalize o a))) :=
  @Preliminaries.lem_raw_transfer

/-- The linear skip clause of `lem:raw-transfer`. -/
theorem lem_raw_transfer_skip :
    ∀ {d n m : ℕ} (bStudent : Vec d) (o : Fin n → ℝ) (a : Fin n → Vec d)
      (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) (_ : ∀ i, a i ≠ 0),
    (HasFDerivAt (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
        (0 : (Vec d × Parameters d n) →L[ℝ] ℝ) (bStudent, (o, a)) ↔
      HasFDerivWithinAt
        (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
        (0 : (Vec d × Parameters d n) →L[ℝ] ℝ)
        {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, Normalize o a)) ∧
    (IsLocalMin (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
        (bStudent, (o, a)) ↔
      IsLocalMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
        {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, Normalize o a)) ∧
    ((IsLocalMin (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
        (bStudent, (o, a)) ∧
      ¬ IsMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
        Set.univ (bStudent, (o, a))) ↔
      (IsLocalMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
          {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, Normalize o a) ∧
        ¬ IsMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
          {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, Normalize o a))) :=
  @Preliminaries.lem_raw_transfer_skip

/-- The two exact identities in `lem:equivalence_loss_skip_centered`. -/
theorem lem_equivalence_loss_skip_centered :
    ∀ {d n m : ℕ} (_ : 2 ≤ d) (bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d)
      (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d),
    (SkipLoss bStudent s w bTeacher t v = CenteredLoss s w t v +
      (1 / 2 : ℝ) * ‖bStudent - MatchingSkip bTeacher t v s w‖ ^ 2) ∧
    (PlainLoss s w t v = CenteredLoss s w t v +
      (1 / 8 : ℝ) * ‖(∑ i, s i • w i) - ∑ k, t k • v k‖ ^ 2) :=
  @Skip.lem_equivalence_loss_skip_centered

/-- The ordinary-local-minimum clause of `lem:equivalence_loss_skip_centered`. -/
theorem lem_skip_local_minimum_iff :
    ∀ {d n m : ℕ} (_ : 2 ≤ d) (bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d)
      (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) (_ : ∀ i, ‖w i‖ = 1),
    IsLocalMinOn (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, (s, w)) ↔
    bStudent = MatchingSkip bTeacher t v s w ∧
      IsLocalMinOn (fun p : Parameters d n => CenteredLoss p.1 p.2 t v)
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w) :=
  @Skip.skip_local_minimum_iff

/-- The strict-local-minimum clause of `lem:equivalence_loss_skip_centered`. -/
theorem lem_skip_strict_local_minimum_iff :
    ∀ {d n m : ℕ} (_ : 2 ≤ d) (bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d)
      (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) (_ : ∀ i, ‖w i‖ = 1),
    IsStrictLocalMinOn
      (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, (s, w)) ↔
    bStudent = MatchingSkip bTeacher t v s w ∧
      IsStrictLocalMinOn (fun p : Parameters d n => CenteredLoss p.1 p.2 t v)
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w) :=
  @Skip.skip_strict_local_minimum_iff

/-- The critical-point clause of `lem:equivalence_loss_skip_centered`. -/
theorem lem_skip_critical_iff :
    ∀ {d n m : ℕ} (_ : 2 ≤ d) (bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d)
      (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) (_ : ∀ i, ‖w i‖ = 1),
    HasFDerivWithinAt
      (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
      (0 : (Vec d × Parameters d n) →L[ℝ] ℝ) {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, (s, w)) ↔
    bStudent = MatchingSkip bTeacher t v s w ∧
      HasFDerivWithinAt (fun p : Parameters d n => CenteredLoss p.1 p.2 t v)
        (0 : Parameters d n →L[ℝ] ℝ) {p | ∀ i, ‖p.2 i‖ = 1} (s, w) :=
  @Skip.skip_critical_point_iff

/-! ## Pair moments and the residual -/

/-- `lem:pair-moments`, including the literal Gaussian normalization. The integrand
is integrable (`Preliminaries.centered_feature_pair_integrable`,
`Preliminaries.gaussian_plain_pair_integrable`), so the Bochner integral is the
genuine expectation. -/
theorem lem_pair_moments :
    ∀ {d : ℕ} (_ : 2 ≤ d) (q : Model) (ξ ζ : Vec d)
      (_ : ‖ξ‖ = 1) (_ : ‖ζ‖ = 1),
    2 * π * (∫ x : Vec d,
      Feature q ⟪ξ, x⟫_ℝ * Feature q ⟪ζ, x⟫_ℝ * stdGaussianDensity x) =
      Kernel q ⟪ξ, ζ⟫_ℝ :=
  @Preliminaries.lem_pair_moments

/-- `prop:loss_in_residual`: loss, mass derivative, and spherical derivative. The loss
is a Bochner integral of an integrable function: the identity rests on
`Preliminaries.gaussian_loss_eq_kernel_energy_of_pair_moment`, whose integrability
hypothesis is discharged by the two pair-integrability lemmas named at
`lem_pair_moments`. -/
theorem prop_loss_in_residual :
    ∀ {d n m : ℕ} (hd : 2 ≤ d) (q : Model) (s : Fin n → ℝ) (w : Fin n → Vec d)
      (t : Fin m → ℝ) (v : Fin m → Vec d)
      (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1),
    (Loss q s w t v = (1 / (4 * π)) *
      ((∑ i, s i * Residual q s w t v (w i)) -
        ∑ k, t k * Residual q s w t v (v k))) ∧
    (∀ i : Fin n, HasDerivAt (fun τ : ℝ => Loss q (Function.update s i τ) w t v)
      ((1 / (2 * π)) * Residual q s w t v (w i)) (s i)) ∧
    (∀ (i : Fin n) (ξ : Vec d), ‖ξ‖ = 1 → ⟪ξ, w i⟫_ℝ = 0 →
      HasDerivAt
        (fun τ : ℝ => Loss q s (Function.update w i (cos τ • w i + sin τ • ξ)) t v)
        ((1 / (2 * π)) * s i *
          deriv (fun τ : ℝ => Residual q s w t v (cos τ • w i + sin τ • ξ)) 0) 0) := by
  intro d n m hd q s w t v hw hv
  obtain ⟨hvalue, hmass, hdirection⟩ :=
    Preliminaries.prop_loss_in_residual hd q s w t v hw hv
  refine ⟨hvalue, hmass, ?_⟩
  intro i ξ hξ htan
  apply hdirection i ξ hξ
  rw [real_inner_comm]
  exact htan

/-- `rem:planar_residual_equivalence`, with genuine Fréchet coordinate derivatives. -/
theorem rem_planar_residual_equivalence :
    ∀ {n m : ℕ} (q : Model) (s θ : Fin n → ℝ) (t β : Fin m → ℝ),
    (∀ γ : ℝ,
      Residual q s (fun i => Angle (θ i)) t (fun k => Angle (β k)) (Angle γ) =
        PlanarResidual q s θ t β γ) ∧
    (∀ i : Fin n,
      fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Loss q p.1 (fun j => Angle (p.2 j)) t (fun k => Angle (β k)))
        (s, θ) (Pi.single i 1, 0) = (1 / (2 * π)) * PlanarResidual q s θ t β (θ i)) ∧
    (∀ i : Fin n,
      fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Loss q p.1 (fun j => Angle (p.2 j)) t (fun k => Angle (β k)))
        (s, θ) (0, Pi.single i 1) =
          (1 / (2 * π)) * s i * deriv (PlanarResidual q s θ t β) (θ i)) :=
  @Planar.GaussianSurface.rem_planar_residual_equivalence

/-! ## Confinement and zero-mass students -/

/-- `prop:teacher-span-confinement` and `prop:nc-teacher-span-confinement`. -/
theorem prop_teacher_span_confinement :
    ∀ {d n m : ℕ} (_ : 2 ≤ d) (q : Model)
      {s : Fin n → ℝ} {w : Fin n → Vec d} {t : Fin m → ℝ} {v : Fin m → Vec d}
      (_ : ∀ k, ‖v k‖ = 1) (_ : ∀ i, ‖w i‖ = 1) (_ : ∀ i, 0 ≤ s i)
      (_ : IsLocalMinOn (fun p : Parameters d n => Loss q p.1 p.2 t v)
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w)),
    ∀ i, s i • w i ∈ Submodule.span ℝ (Set.range v) :=
  @Geometry.prop_teacher_span_confinement

/-- `prop:zero_mass_exact_fit`; only dimension two needs nonnegative teachers. -/
theorem prop_zero_mass_exact_fit :
    ∀ {d n m : ℕ} (_ : 1 ≤ d)
      {s : Fin n → ℝ} {w : Fin n → Vec d} {t : Fin m → ℝ} {v : Fin m → Vec d}
      (_ : d = 2 → ∀ k, 0 ≤ t k) (_ : ∀ k, ‖v k‖ = 1) (_ : ∀ i, ‖w i‖ = 1)
      {i : Fin n} (_ : s i = 0)
      (_ : IsLocalMinOn (fun p : Parameters d n => CenteredLoss p.1 p.2 t v)
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w)),
    CenteredLoss s w t v = 0 := by
  intro d n m hd s w t v ht₂ hv hw i hsi hmin
  exact Geometry.prop_zero_mass_exact_fit hd ht₂ hv hw hsi hmin

/-- `prop:nc-dead-student`, without sign or width assumptions. -/
theorem prop_nc_dead_student :
    ∀ {d n m : ℕ} (_ : 3 ≤ d)
      {s : Fin n → ℝ} {w : Fin n → Vec d} {t : Fin m → ℝ} {v : Fin m → Vec d}
      (_ : ∀ k, ‖v k‖ = 1) (_ : ∀ i, ‖w i‖ = 1) {i : Fin n} (_ : s i = 0)
      (_ : IsLocalMinOn (fun p : Parameters d n => PlainLoss p.1 p.2 t v)
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w)),
    PlainLoss s w t v = 0 := by
  intro d n m hd s w t v hv hw i hsi hmin
  exact Geometry.prop_nc_dead_student hd hv hw hsi hmin

/-- `lem:nc-dead-counterexamples`. (a) On the line, the zero-mass student
opposed to the unit teacher is a local minimum of the plain loss on the
unit-direction parameter space with loss `1/4`, the opposed student of mass
`s` has loss `(s^2 + 1)/4`, and the teacher copy has loss `0`. (b) In the plane,
the fixed five-unit signed teacher makes every zero-mass one-student parameter
with angle in `(-π/6, π/6)` a local minimum of both losses, with positive loss
and a lower-loss one-student competitor. -/
theorem lem_nc_dead_counterexamples :
    (∃ v : Vec 1, ‖v‖ = 1 ∧
      IsLocalMinOn (fun p : Parameters 1 1 =>
          PlainLoss p.1 p.2 (fun _ : Fin 1 => (1:ℝ)) (fun _ : Fin 1 => v))
        {p | ∀ i, ‖p.2 i‖ = 1} (fun _ => 0, fun _ => -v) ∧
      (∀ s : ℝ, PlainLoss (fun _ : Fin 1 => s) (fun _ : Fin 1 => -v)
        (fun _ : Fin 1 => (1:ℝ)) (fun _ : Fin 1 => v) = (s ^ 2 + 1) / 4) ∧
      PlainLoss (fun _ : Fin 1 => (1:ℝ)) (fun _ : Fin 1 => v)
        (fun _ : Fin 1 => (1:ℝ)) (fun _ : Fin 1 => v) = 0) ∧
    (∀ (q : Model) (τ : ℝ), |τ| < π / 6 →
      IsLocalMinOn (fun p : Parameters 2 1 => Loss q p.1 p.2
          Plain.ZeroMassExample.teacherMass
          (fun k => Angle (Plain.ZeroMassExample.teacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (fun _ => 0, fun _ => Angle τ) ∧
      0 < Loss q (fun _ : Fin 1 => (0:ℝ)) (fun _ => Angle τ)
        Plain.ZeroMassExample.teacherMass
        (fun k => Angle (Plain.ZeroMassExample.teacherAngle k)) ∧
      ∃ s θ : ℝ, Loss q (fun _ : Fin 1 => s) (fun _ => Angle θ)
          Plain.ZeroMassExample.teacherMass
          (fun k => Angle (Plain.ZeroMassExample.teacherAngle k)) <
        Loss q (fun _ : Fin 1 => (0:ℝ)) (fun _ => Angle τ)
          Plain.ZeroMassExample.teacherMass
          (fun k => Angle (Plain.ZeroMassExample.teacherAngle k))) :=
  ⟨⟨Plain.LineExample.e, Plain.LineExample.e_unit, Plain.LineExample.opposed_local_minimum,
    Plain.LineExample.loss_opposed_value, Plain.LineExample.teacher_copy_zero⟩,
   fun q _ hτ => Plain.ZeroMassExample.zero_mass_spurious_minimum q hτ⟩

/-! ## The planar beam argument -/

/-- `lem:critical-points-are-double-zeros`. -/
theorem lem_critical_points_are_double_zeros :
    ∀ {n m : ℕ} {s θ : Fin n → ℝ} {t β : Fin m → ℝ}
      (_ : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        CenteredLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ) = 0)
      (i : Fin n) (_ : s i ≠ 0),
    PlanarResidual .centered s θ t β (θ i) = 0 ∧
      deriv (PlanarResidual .centered s θ t β) (θ i) = 0 :=
  @Planar.GaussianSurface.lem_critical_points_are_double_zeros

/-- `lem:beam-kernel`, with the differential operator written out. -/
theorem lem_beam_kernel :
    ∀ {f : ℝ → ℝ} (_ : ContDiff ℝ 4 f),
    (∀ x, deriv (deriv (deriv (deriv f))) x + 2 * deriv (deriv f) x + f x = 0) ↔
      ∃ A B C D : ℝ, ∀ x, f x = A * cos x + B * sin x + C * x * cos x + D * x * sin x :=
  @BeamKernel.lem_beam_kernel

/-- `lem:gap-sign`: one Green function for every configuration on the fixed gap. -/
theorem lem_gap_sign :
    ∀ {l : ℝ} (_ : 0 < l) (_ : l ≤ π),
    ∃ G : ℝ → ℝ → ℝ,
      (∀ p, 0 < p → p < l → ∀ γ, 0 ≤ γ → γ ≤ l → 0 ≤ G γ p) ∧
      ∀ {n m : ℕ} (s θ : Fin n → ℝ) (t β : Fin m → ℝ),
        (∀ i, 0 ≤ θ i ∧ θ i < π) → (∀ k, 0 ≤ β k ∧ β k < π) →
        0 ∈ PositiveLines s θ t β →
        (∀ α ∈ PositiveLines s θ t β, ¬ (0 < α ∧ α < l)) →
        (PlanarResidual .centered s θ t β 0 = 0 ∧
          deriv (PlanarResidual .centered s θ t β) 0 = 0) →
        (PlanarResidual .centered s θ t β l = 0 ∧
          deriv (PlanarResidual .centered s θ t β) l = 0) →
        (∀ γ, 0 ≤ γ → γ ≤ l → PlanarResidual .centered s θ t β γ =
          4 * ∑ α in (NegativeLines s θ t β).filter (fun α => 0 < α ∧ α < l),
            NetWeight s θ t β α * G γ α) ∧
        ((∀ γ, 0 ≤ γ → γ ≤ l → PlanarResidual .centered s θ t β γ = 0) ↔
          (NegativeLines s θ t β).filter (fun α => 0 < α ∧ α < l) = ∅) ∧
        (((NegativeLines s θ t β).filter (fun α => 0 < α ∧ α < l)).Nonempty →
          (∀ γ, 0 < γ → γ < l → PlanarResidual .centered s θ t β γ < 0) ∧
          deriv (deriv (PlanarResidual .centered s θ t β)) 0 < 0 ∧
          deriv (deriv (PlanarResidual .centered s θ t β)) l < 0) :=
  @Planar.NetSurface.lem_gap_sign

/-- `lem:line-count`, including weak cyclic interlacing. -/
theorem lem_line_count :
    ∀ {n m : ℕ} (s θ : Fin n → ℝ) (t β : Fin m → ℝ)
      (_ : ∀ i, 0 ≤ θ i ∧ θ i < π) (_ : ∀ k, 0 ≤ β k ∧ β k < π)
      (_ : 2 ≤ (PositiveLines s θ t β).card)
      (_ : ∀ x ∈ PositiveLines s θ t β,
        PlanarResidual .centered s θ t β x = 0 ∧
          deriv (PlanarResidual .centered s θ t β) x = 0),
    (∃ hα : Function.Injective ((PositiveLines s θ t β).orderEmbOfFin rfl),
      cyclically_weakly_interlaces_general
        ((PositiveLines s θ t β).orderEmbOfFin rfl)
        ((NegativeLines s θ t β).orderEmbOfFin rfl) hα) ∧
    (PositiveLines s θ t β).card ≤ (NegativeLines s θ t β).card :=
  @Planar.LineSurface.lem_line_count

/-- `lem:opposed-rotation`, for coincident unoriented lines. -/
theorem lem_opposed_rotation :
    ∀ {n m : ℕ} (s θ : Fin n → ℝ) (t β : Fin m → ℝ) (p q : Fin n)
      (_ : p ≠ q) (_ : ∃ k : ℤ, θ p = θ q + (k : ℝ) * π),
    let dθ : Fin n → ℝ := fun i => if i = p then s q else if i = q then -s p else 0
    deriv (deriv (fun τ : ℝ =>
      CenteredLoss s (fun i => Angle (θ i + τ * dθ i)) t (fun k => Angle (β k)))) 0 =
      s p * s q * (s p + s q) / (2 * π) *
        deriv (deriv (PlanarResidual .centered s θ t β)) (θ p) :=
  @Planar.GaussianSurface.lem_opposed_rotation

/-- `prop:S-plus-eq-student-lines`. -/
theorem prop_S_plus_eq_student_lines :
    ∀ {n m : ℕ} {s θ : Fin n → ℝ} {t β : Fin m → ℝ}
      (_ : ∀ i, 0 ≤ θ i ∧ θ i < π) (_ : ∀ k, 0 ≤ β k ∧ β k < π)
      (_ : ∀ i, 0 < s i) (_ : ∀ k, 0 < t k)
      (_ : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        CenteredLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ) = 0)
      (_ : 2 ≤ (PositiveLines s θ t β).card),
    PositiveLines s θ t β = Finset.univ.image θ :=
  @Planar.GaussianSurface.prop_S_plus_eq_student_lines

/-- `lem:no-collisions`, at a positive-loss local minimum. -/
theorem lem_no_collisions :
    ∀ {n m : ℕ} {s θ : Fin n → ℝ} {t β : Fin m → ℝ}
      (_ : ∀ i, 0 ≤ θ i ∧ θ i < π) (_ : ∀ k, 0 ≤ β k ∧ β k < π)
      (_ : ∀ i, 0 < s i) (_ : ∀ k, 0 < t k)
      (_ : IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        CenteredLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ))
      (_ : 0 < CenteredLoss s (fun i => Angle (θ i)) t (fun k => Angle (β k))),
    (Finset.univ.image θ).card = n :=
  @Planar.GaussianSurface.lem_no_collisions

/-- `lem:S-is-small`, including zero student masses. -/
theorem lem_S_is_small :
    ∀ {n m : ℕ} (_ : m ≤ n) {s θ : Fin n → ℝ} {t β : Fin m → ℝ}
      (_ : ∀ i, 0 ≤ θ i ∧ θ i < π) (_ : ∀ k, 0 ≤ β k ∧ β k < π)
      (_ : ∀ i, 0 ≤ s i) (_ : ∀ k, 0 < t k)
      (_ : IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        CenteredLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ))
      (_ : (PositiveLines s θ t β).card ≤ 1),
    CenteredLoss s (fun i => Angle (θ i)) t (fun k => Angle (β k)) = 0 :=
  @Geometry.lem_S_is_small

/-- `prop:locamin_are_line_separated`, including strict cyclic interlacing. -/
theorem prop_locamin_are_line_separated :
    ∀ {n m : ℕ} (_ : m ≤ n) {s θ : Fin n → ℝ} {t β : Fin m → ℝ}
      (_ : ∀ i, 0 ≤ θ i ∧ θ i < π) (_ : ∀ k, 0 ≤ β k ∧ β k < π)
      (_ : ∀ i, 0 < s i) (_ : ∀ k, 0 < t k)
      (_ : IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        CenteredLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ))
      (_ : 0 < CenteredLoss s (fun i => Angle (θ i)) t (fun k => Angle (β k))),
    n = m ∧ Function.Injective θ ∧ Function.Injective β ∧ (∀ i k, θ i ≠ β k) ∧
      ∃ hθinj : Function.Injective θ, cyclically_strictly_interlaces_general θ β hθinj :=
  @Planar.GaussianSurface.prop_locamin_are_line_separated

/-- `prop:beam-descent`: actual negative second variation of the Gaussian loss. -/
theorem prop_beam_descent :
    ∀ {n : ℕ} (s θ t β : Fin n → ℝ) (_ : 2 ≤ n)
      (_ : ∀ i, 0 < s i) (_ : ∀ k, 0 < t k)
      (_ : ∀ i, 0 ≤ θ i ∧ θ i < π) (_ : ∀ k, 0 ≤ β k ∧ β k < π)
      (_ : Function.Injective θ) (_ : Function.Injective β)
      (_ : ∀ i k, θ i ≠ β k)
      (_ : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        CenteredLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ) = 0),
    ∃ ds dθ : Fin n → ℝ,
      deriv (deriv (fun τ : ℝ => CenteredLoss (fun i => s i + τ * ds i)
        (fun i => Angle (θ i + τ * dθ i)) t (fun k => Angle (β k)))) 0 < 0 :=
  @Planar.GaussianSurface.prop_beam_descent

/-! ## The residual as a bent ring -/

/-- `rem:ring`, `eq:ring-operator`: Love's ring operator on the tangential displacement
`w` is the derivative of the beam operator on the radial displacement `u = w'`. -/
theorem eq_ring_operator :
    ∀ (w : ℝ → ℝ), ContDiff ℝ 6 w → ∀ x : ℝ,
      deriv (fun y => iteratedDeriv 4 (deriv w) y + 2 * iteratedDeriv 2 (deriv w) y +
        deriv w y) x =
        iteratedDeriv 6 w x + 2 * iteratedDeriv 4 w x + iteratedDeriv 2 w x :=
  @BentRing.eq_ring_operator

/-! ## The population conclusions -/

/-- `thm:centered`, for a teacher whose span has dimension at most two. -/
theorem thm_centered :
    ∀ {d n m : ℕ} (_ : 1 ≤ d) (_ : m ≤ n)
      {s : Fin n → ℝ} {w : Fin n → Vec d} {t : Fin m → ℝ} {v : Fin m → Vec d}
      (_ : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
      (_ : ∀ k, ‖v k‖ = 1) (_ : ∀ i, ‖w i‖ = 1)
      (_ : ∀ i, 0 ≤ s i) (_ : ∀ k, 0 < t k)
      (_ : IsLocalMinOn (fun p : Parameters d n => CenteredLoss p.1 p.2 t v)
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w)),
    CenteredLoss s w t v = 0 := by
  intro d n m hd hmn s w t v hplane hv hw hs ht hmin
  exact Geometry.centered_benign_pos_dimension hd hmn hv hw hs ht hplane hmin

/-- `thm:headline`, with the linear skip optimized jointly. -/
theorem thm_headline :
    ∀ {d n m : ℕ} (_ : 1 ≤ d) (_ : m ≤ n)
      {bStudent bTeacher : Vec d} {s : Fin n → ℝ} {w : Fin n → Vec d}
      {t : Fin m → ℝ} {v : Fin m → Vec d}
      (_ : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
      (_ : ∀ k, ‖v k‖ = 1) (_ : ∀ i, ‖w i‖ = 1)
      (_ : ∀ i, 0 ≤ s i) (_ : ∀ k, 0 < t k)
      (_ : IsLocalMinOn
        (fun p : Vec d × Parameters d n => SkipLoss p.1 p.2.1 p.2.2 bTeacher t v)
        {p | ∀ i, ‖p.2.2 i‖ = 1} (bStudent, (s, w))),
    SkipLoss bStudent s w bTeacher t v = 0 :=
  @Geometry.skip_benign_pos_dimension

/-! ## Generic certificates and positive-curvature splitting -/

/-- `lem:box-certificate`: in these finite coordinate spaces the norm is the
maximum coordinate norm, so the closed ball is precisely the coordinate box.
The final inequality makes its interior strict minimum unique on the whole box. -/
theorem lem_box_certificate :
    ∀ {a b : ℕ} {f : ((Fin a → ℝ) × (Fin b → ℝ)) → ℝ}
      (_ : ContDiff ℝ 2 f) {z₀ : (Fin a → ℝ) × (Fin b → ℝ)}
      {r lam g : ℝ} (_ : 0 < r) (_ : 0 < lam) (_ : 0 ≤ g)
      (_ : ∀ z ∈ Metric.closedBall z₀ r, ∀ h : (Fin a → ℝ) × (Fin b → ℝ),
        lam * ((∑ i, h.1 i ^ 2) + ∑ j, h.2 j ^ 2) ≤
          (fderiv ℝ (fderiv ℝ f) z h) h)
      (_ : ∀ h : (Fin a → ℝ) × (Fin b → ℝ),
        |fderiv ℝ f z₀ h| ≤ g * sqrt ((∑ i, h.1 i ^ 2) + ∑ j, h.2 j ^ 2))
      (_ : 2 * g < lam * r),
    ∃ z : (Fin a → ℝ) × (Fin b → ℝ),
      ‖z - z₀‖ < r ∧ fderiv ℝ f z = 0 ∧
      (∀ᶠ y in 𝓝 z, y ≠ z → f z < f y) ∧
      (∀ y ∈ Metric.closedBall z₀ r, y ≠ z → f z < f y) :=
  @Plain.box_strict_minimum

/-- The spuriousness clause of `lem:box-certificate`: the actual loss is a
positive affine normalization, is positive throughout the box, and admits an
exact-fit competitor. Positivity of the first coordinate block is an optional
additional consequence, not an assumption needed for spuriousness. -/
theorem lem_box_certificate_spurious :
    ∀ {a b : ℕ} {f L : ((Fin a → ℝ) × (Fin b → ℝ)) → ℝ}
      {z₀ z : (Fin a → ℝ) × (Fin b → ℝ)} {r scale shift : ℝ}
      (_ : z ∈ Metric.closedBall z₀ r)
      (_ : ∀ᶠ y in 𝓝 z, y ≠ z → f z < f y)
      (_ : 0 < scale) (_ : ∀ y, f y = scale * L y + shift)
      (_ : ∀ y ∈ Metric.closedBall z₀ r, 0 < L y)
      (_ : ∃ y, L y = 0),
    (∀ᶠ y in 𝓝 z, y ≠ z → L z < L y) ∧
      0 < L z ∧
      ((∀ y ∈ Metric.closedBall z₀ r, ∀ i, 0 < y.1 i) → ∀ i, 0 < z.1 i) ∧
      ∃ y, L y = 0 ∧ L y < L z :=
  @Plain.box_minimum_affine_spurious

/-- `lem:positive-curvature-splitting`: replace any chosen student by any
positive partition of its mass. The curve for two or more children transfers
mass while keeping every direction, the network, and the actual loss fixed. -/
theorem lem_positive_curvature_splitting :
    ∀ {n k m : ℕ} (_ : 0 < k)
      (s θ : Fin (n + 1) → ℝ) (t β : Fin m → ℝ)
      (i : Fin (n + 1)) (a : Fin k → ℝ)
      (_ : 0 < s i) (_ : ∀ j, 0 < a j) (_ : (∑ j, a j) = s i)
      (_ : IsLocalMin (fun p : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        PlainLoss p.1 (fun j => Angle (p.2 j)) t (fun l => Angle (β l))) (s, θ))
      (_ : 0 < deriv (deriv (PlanarResidual .plainRelu s θ t β)) (θ i)),
    let s' := Fin.append a (fun l => s (i.succAbove l))
    let θ' := Fin.append (fun _ : Fin k => θ i) (fun l => θ (i.succAbove l))
    (∀ x : Vec 2, Network .plainRelu s' (fun j => Angle (θ' j)) x =
      Network .plainRelu s (fun j => Angle (θ j)) x) ∧
    PlainLoss s' (fun j => Angle (θ' j)) t (fun l => Angle (β l)) =
      PlainLoss s (fun j => Angle (θ j)) t (fun l => Angle (β l)) ∧
    IsLocalMin (fun p : (Fin (k + n) → ℝ) × (Fin (k + n) → ℝ) =>
      PlainLoss p.1 (fun j => Angle (p.2 j)) t (fun l => Angle (β l))) (s', θ') ∧
    (2 ≤ k →
      (∃ γ : ℝ → (Fin (k + n) → ℝ) × (Fin (k + n) → ℝ),
        Continuous γ ∧ Function.Injective γ ∧ γ 0 = (s', θ') ∧
        (∀ τ, (γ τ).2 = θ') ∧
        (∀ τ x, Network .plainRelu (γ τ).1 (fun j => Angle ((γ τ).2 j)) x =
          Network .plainRelu s' (fun j => Angle (θ' j)) x) ∧
        (∀ τ, PlainLoss (γ τ).1 (fun j => Angle ((γ τ).2 j)) t
          (fun l => Angle (β l)) =
            PlainLoss s' (fun j => Angle (θ' j)) t (fun l => Angle (β l)))) ∧
      ¬ IsStrictLocalMinPoint
        (fun p : (Fin (k + n) → ℝ) × (Fin (k + n) → ℝ) =>
          PlainLoss p.1 (fun j => Angle (p.2 j)) t (fun l => Angle (β l))) (s', θ')) := by
  intro n k m hk s θ t β i a hi ha hsum hmin hcurv
  cases k with
  | zero => exact False.elim ((Nat.lt_irrefl 0) hk)
  | succ k =>
    obtain ⟨hnetwork, hloss, hlocal, hflat⟩ :=
      Plain.positive_curvature_finite_splitting s θ t β i a hi ha hsum hmin hcurv
    exact ⟨hnetwork, hloss, hlocal, fun htwo => hflat (Nat.succ_le_succ_iff.mp htwo)⟩

/-! ## The plain-ReLU conclusions -/

/-- `thm:plain-trap`, at every student width at least three. -/
theorem thm_plain_trap :
    ∀ {n : ℕ} (_ : 3 ≤ n),
    ∃ s : Fin n → ℝ, ∃ w : Fin n → Vec 2,
      (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < s i) ∧
      IsLocalMinOn (fun p : Parameters 2 n =>
        PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w) ∧
      0 < PlainLoss s w TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)) :=
  @Plain.thm_plain_trap

/-- The spuriousness clause of `thm:plain-trap`: a feasible competitor at the
same width has strictly smaller loss. -/
theorem thm_plain_trap_spurious :
    ∀ {n : ℕ} (_ : 3 ≤ n),
    ∃ s : Fin n → ℝ, ∃ w : Fin n → Vec 2,
      (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < s i) ∧
      IsLocalMinOn (fun p : Parameters 2 n =>
        PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w) ∧
      ∃ s₀ : Fin n → ℝ, ∃ w₀ : Fin n → Vec 2,
        (∀ i, ‖w₀ i‖ = 1) ∧
        PlainLoss s₀ w₀ TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)) <
          PlainLoss s w TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)) :=
  @Plain.thm_plain_trap_spurious

/-- The strict width-three clause of `thm:plain-trap`. -/
theorem thm_plain_trap_strict :
    ∃ s : Fin 3 → ℝ, ∃ w : Fin 3 → Vec 2,
      (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < s i) ∧
      IsStrictLocalMinOn (fun p : Parameters 2 3 =>
        PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w) ∧
      0 < PlainLoss s w TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)) :=
  Plain.thm_plain_trap_strict

/-- The non-strict wider-minimum clause of `thm:plain-trap`. -/
theorem thm_plain_trap_flat :
    ∀ {n : ℕ} (_ : 3 < n),
    ∃ s : Fin n → ℝ, ∃ w : Fin n → Vec 2,
      (∀ i, ‖w i‖ = 1) ∧ (∀ i, 0 < s i) ∧
      IsLocalMinOn (fun p : Parameters 2 n =>
        PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w) ∧
      0 < PlainLoss s w TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)) ∧
      ¬ IsStrictLocalMinOn (fun p : Parameters 2 n =>
        PlainLoss p.1 p.2 TrapTeacherMass (fun k => Angle (TrapTeacherAngle k)))
        {p | ∀ i, ‖p.2 i‖ = 1} (s, w) :=
  @Plain.thm_plain_trap_flat

/-- The bound in `prop:plain-collision-ceiling`, counting oriented directions. The
`fderiv` hypothesis is not vacuous: the plain loss in mass–angle coordinates is an
affine rescaling (`Plain.plain_loss_eq_excess_div`) of a globally `C²` function
(`Plain.ParameterCalculus.loss_contDiff_two`). -/
theorem prop_plain_collision_ceiling :
    ∀ {n m : ℕ} {s θ : Fin n → ℝ} {t β : Fin m → ℝ}
      (_ : ∀ i, 0 < s i)
      (_ : fderiv ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        PlainLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ) = 0),
    (Finset.univ.image (fun i => Angle (θ i))).card ≤ 2 * m :=
  @Plain.prop_plain_collision_ceiling

/-- The sharpness clause of `prop:plain-collision-ceiling`. -/
theorem prop_plain_collision_ceiling_sharp :
    ∀ (m : ℕ) (_ : 3 ≤ m) (_ : Odd m),
    ∃ (s θ : Fin (m + m) → ℝ) (t β : Fin m → ℝ),
      (∀ i, 0 < s i) ∧ (∀ k, 0 < t k) ∧
      fderiv ℝ (fun p : (Fin (m + m) → ℝ) × (Fin (m + m) → ℝ) =>
        PlainLoss p.1 (fun i => Angle (p.2 i)) t (fun k => Angle (β k))) (s, θ) = 0 ∧
      (Finset.univ.image (fun i => Angle (θ i))).card = 2 * m := by
  intro m hm hodd
  obtain ⟨s, θ, t, β, hs, ht, hcard, _hfit, hcrit⟩ :=
    Plain.prop_plain_collision_ceiling_sharp m hm hodd
  exact ⟨s, θ, t, β, hs, ht, hcrit, hcard⟩

/-! ## Fixed-radius empirical minima -/

/-- `thm:minimizer-stability`, for every actual cluster point. -/
theorem thm_minimizer_stability :
    ∀ {E : Type u} [MetricSpace E] {f : E → ℝ} (_ : Continuous f)
      {K : Set E} (_ : IsCompact K) {r : ℝ} (_ : 0 < r)
      {g : ℕ → E → ℝ} {x : ℕ → E} (_ : ∀ j, x j ∈ K)
      (_ : TendstoUniformlyOn g f atTop {y | ∃ z ∈ K, dist y z ≤ r})
      (_ : ∀ j, IsMinOn (g j) (Metric.closedBall (x j) r) (x j))
      {z : E} (_ : MapClusterPt z atTop x),
    IsLocalMin f z :=
  @Empirical.thm_minimizer_stability

/-- `thm:fixed-radius-bridge`: a sufficiently accurate finite dataset admits
only exact-fitting nonnegative fixed-radius minima for teacher-consistent labels. -/
theorem thm_fixed_radius_bridge :
    ∀ {d n m : ℕ} (_ : 1 ≤ d) (_ : m ≤ n)
      {t : Fin m → ℝ} {v : Fin m → Vec d}
      (_ : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
      (_ : ∀ k, ‖v k‖ = 1) (_ : ∀ k, 0 < t k)
      {r : ℝ} (_ : 0 < r),
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ) (x : Fin N → Vec d) (y : Fin N → ℝ),
        0 < N → DataAccuracy x δ →
        ∀ (bTeacher bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d),
          (∀ j, y j = ⟪bTeacher, x j⟫_ℝ + ∑ k, t k * max 0 ⟪v k, x j⟫_ℝ) →
          (∀ i, 0 ≤ s i) → (∀ i, ‖w i‖ = 1) →
          IsMinOn (fun p : Vec d × Parameters d n => DataLoss x y p.1 p.2.1 p.2.2)
            {p | (∀ i, ‖p.2.2 i‖ = 1) ∧ JointDistance bTeacher t v p (bStudent, (s, w)) ≤ r}
            (bStudent, (s, w)) →
          DataLoss x y bStudent s w = 0 :=
  @Empirical.thm_fixed_radius_bridge

/-- `rem:finite-data-accuracy`: the sampling assumptions yield accuracy of
the raw finite datasets, independently of any student or teacher network. -/
theorem rem_finite_data_accuracy :
    ∀ {d : ℕ} (_ : 2 ≤ d)
      {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
      (X : ℕ → Ω → Vec d) (_ : ∀ j, Measurable (X j))
      (μ : Measure (Vec d)) (_ : Measure.map (X 0) volume = μ)
      (_ : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
      (_ : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
      {M : ℝ} (_ : 0 < M)
      (_ : Integrable (fun x : Vec d => (‖x‖ ^ (2 : ℕ) : ℝ)) μ)
      (_ : (∫ x : Vec d, (‖x‖ ^ (2 : ℕ) : ℝ) ∂μ) = M)
      (_ : ∀ Q : Vec d ≃ₗᵢ[ℝ] Vec d, MeasurePreserving Q μ μ)
      {δ η : ℝ} (_ : 0 < δ) (_ : 0 < η),
    ∃ N₀ : ℕ, ∃ G : Set Ω, MeasurableSet G ∧ volume Gᶜ < ENNReal.ofReal η ∧
      ∀ ω ∈ G, ∀ N, N₀ ≤ N → DataAccuracy (fun j : Fin N => X j ω) δ :=
  @Empirical.rem_finite_data_accuracy

/-- Stochastic `rem:finite-data-accuracy`: the common law is orthogonally
invariant with finite positive second moment. Pairwise independence suffices. -/
theorem rem_finite_data_accuracy_high_probability :
    ∀ {d n m : ℕ} (_ : 1 ≤ d) (_ : m ≤ n)
      {t : Fin m → ℝ} {v : Fin m → Vec d}
      (_ : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
      (_ : ∀ k, ‖v k‖ = 1) (_ : ∀ k, 0 < t k)
      {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
      (X : ℕ → Ω → Vec d) (_ : ∀ j, Measurable (X j))
      (μ : Measure (Vec d)) (_ : Measure.map (X 0) volume = μ)
      (_ : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
      (_ : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
      {M : ℝ} (_ : 0 < M)
      (_ : Integrable (fun x : Vec d => (‖x‖ ^ (2 : ℕ) : ℝ)) μ)
      (_ : (∫ x : Vec d, (‖x‖ ^ (2 : ℕ) : ℝ) ∂μ) = M)
      (_ : ∀ Q : Vec d ≃ₗᵢ[ℝ] Vec d, MeasurePreserving Q μ μ)
      {r η : ℝ} (_ : 0 < r) (_ : 0 < η),
    ∃ N₀ : ℕ, ∃ G : Set Ω, MeasurableSet G ∧ volume Gᶜ < ENNReal.ofReal η ∧
      ∀ ω ∈ G, ∀ N, N₀ ≤ N →
      ∀ (y : Fin N → ℝ) (bTeacher bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d),
        (∀ j, y j = ⟪bTeacher, X j ω⟫_ℝ + ∑ k, t k * max 0 ⟪v k, X j ω⟫_ℝ) →
        (∀ i, 0 ≤ s i) → (∀ i, ‖w i‖ = 1) →
        IsMinOn (fun p : Vec d × Parameters d n =>
          DataLoss (fun j : Fin N => X j ω) y p.1 p.2.1 p.2.2)
          {p | (∀ i, ‖p.2.2 i‖ = 1) ∧ JointDistance bTeacher t v p (bStudent, (s, w)) ≤ r}
          (bStudent, (s, w)) →
        DataLoss (fun j : Fin N => X j ω) y bStudent s w = 0 :=
  @Empirical.rem_finite_data_accuracy_high_probability

end PaperLeanFormalization.Theorems
