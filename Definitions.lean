import Overview_definitions

/-!
# The mathematical model

The contribution definitions and literal Gaussian losses are in
`Overview_definitions.lean`.
This file supplies the additional definitions used by the proof chapters.
Masses are signed coordinates; nonnegativity at a candidate does not restrict
its perturbation neighborhood. Angular kernels distinguish projective period
`π` from the full oriented period `2 * π`.
-/

open Real Set Filter MeasureTheory Classical
open scoped BigOperators Topology RealInnerProductSpace

noncomputable section

namespace PaperLeanFormalization

namespace Definitions

def UnitDirections {d n : ℕ} (w : Fin n → Vec d) : Prop := ∀ i, ‖w i‖ = 1

def Feature : Model → ℝ → ℝ
  | .centered, z => |z| / 2
  | .plainRelu, z => max 0 z

def Network {d n : ℕ} (q : Model) (s : Fin n → ℝ)
    (w : Fin n → Vec d) (x : Vec d) : ℝ :=
  ∑ i, s i * Feature q ⟪w i, x⟫_ℝ

/-- At a zero row the normalized direction is zero, not a unit vector. -/
def Normalize {d n : ℕ} (o : Fin n → ℝ) (a : Fin n → Vec d) : Parameters d n :=
  (fun i => o i * ‖a i‖, fun i => ‖a i‖⁻¹ • a i)

def Kernel : Model → ℝ → ℝ
  | .centered, ρ => ρ * arcsin ρ + sqrt (1 - ρ ^ 2)
  | .plainRelu, ρ => ρ * arcsin ρ + sqrt (1 - ρ ^ 2) + (π / 2) * ρ

def Residual {d n m : ℕ} (q : Model) (s : Fin n → ℝ)
    (w : Fin n → Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) (u : Vec d) : ℝ :=
  (∑ i, s i * Kernel q ⟪u, w i⟫_ℝ) - ∑ k, t k * Kernel q ⟪u, v k⟫_ℝ

def PlanarResidual {n m : ℕ} (q : Model) (s θ : Fin n → ℝ)
    (t β : Fin m → ℝ) (x : ℝ) : ℝ :=
  (∑ i, s i * Kernel q (cos (x - θ i))) -
    ∑ k, t k * Kernel q (cos (x - β k))

/-- Tangential criticality includes an actual Frechet derivative witness. -/
def Critical {d n : ℕ} (L : Parameters d n → ℝ) (p : Parameters d n) : Prop :=
  (∀ i, ‖p.2 i‖ = 1) ∧ ∃ D : Parameters d n →L[ℝ] ℝ,
    HasFDerivAt L D p ∧ ∀ δ : Parameters d n,
      (∀ i, ⟪δ.2 i, p.2 i⟫_ℝ = 0) → D δ = 0

/-- The arguments are canonical representatives when used as line positions. -/
def NetWeight {n m : ℕ} (s θ : Fin n → ℝ) (t β : Fin m → ℝ) (x : ℝ) : ℝ :=
  (∑ i in Finset.univ.filter (fun i => θ i = x), s i) -
    ∑ k in Finset.univ.filter (fun k => β k = x), t k

def PositiveLines {n m : ℕ} (s θ : Fin n → ℝ) (t β : Fin m → ℝ) : Finset ℝ :=
  (Finset.univ.image θ ∪ Finset.univ.image β).filter (fun x => 0 < NetWeight s θ t β x)

def NegativeLines {n m : ℕ} (s θ : Fin n → ℝ) (t β : Fin m → ℝ) : Finset ℝ :=
  (Finset.univ.image θ ∪ Finset.univ.image β).filter (fun x => NetWeight s θ t β x < 0)

/-- Normalized surface integral; its measure and normalization are explicit. -/
def SphereAverage (d : ℕ) (f : Vec d → ℝ) : ℝ :=
  (∫ y : Metric.sphere (0 : Vec d) 1, f y ∂(volume : Measure (Vec d)).toSphere) /
    (((volume : Measure (Vec d)).toSphere) Set.univ).toReal

end Definitions

open Definitions

/-! ## Scalar kernels, Gaussian moments, and sphere functionals -/

def orthantPhi (ρ : ℝ) : ℝ := ρ * arcsin ρ + sqrt (1 - ρ ^ 2)
def reluPhi (ρ : ℝ) : ℝ := orthantPhi ρ + (π / 2) * ρ
def phiCos (x : ℝ) : ℝ := orthantPhi (cos x)
def phiCosJ (x : ℝ) : ℝ := reluPhi (cos x)
def couplingH (x : ℝ) : ℝ := sin x * arcsin (cos x)
def couplingHJ (x : ℝ) : ℝ := couplingH x + (π / 2) * sin x

def gaussianVecAbsMoment (d : ℕ) (w u : Vec d) : ℝ :=
  ∫ x : Vec d, |⟪w, x⟫_ℝ| * |⟪u, x⟫_ℝ| * stdGaussianDensity x

def sphereSurfaceMeasure (d : ℕ) : Measure (Metric.sphere (0 : Vec d) 1) :=
  (volume : Measure (Vec d)).toSphere

def uniformSphereFunctional (d : ℕ) (f : Vec d → ℝ) : ℝ :=
  (∫ y, f (y : Vec d) ∂(sphereSurfaceMeasure d)) /
    ((sphereSurfaceMeasure d) Set.univ).toReal

/-! ## Finite kernel energies, with the teacher constant omitted -/

def massNetLossKernel {d n m : ℕ} (kf : ℝ → ℝ) (s : Fin n → ℝ)
    (w : Fin n → Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, s i * s j * kf (inner (w i) (w j)) -
    ∑ i, ∑ k, s i * t k * kf (inner (w i) (v k))

def massNetLossCentered {d n m : ℕ} (s : Fin n → ℝ) (w : Fin n → Vec d)
    (t : Fin m → ℝ) (v : Fin m → Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, s i * s j * orthantPhi (inner (w i) (w j)) -
    ∑ i, ∑ k, s i * t k * orthantPhi (inner (w i) (v k))

def massNetLossPair {d n m : ℕ} (t : Fin m → ℝ) (v : Fin m → Vec d)
    (p : Parameters d n) : ℝ := massNetLossCentered p.1 p.2 t v

def massTeacherPotential {d m : ℕ} (t : Fin m → ℝ) (v : Fin m → Vec d)
    (x : Vec d) : ℝ := ∑ k, t k * orthantPhi (inner x (v k))

def massResidualField {d n m : ℕ} (s : Fin n → ℝ) (w : Fin n → Vec d)
    (t : Fin m → ℝ) (v : Fin m → Vec d) (x : Vec d) : ℝ :=
  ∑ j, s j * orthantPhi (inner x (w j)) - massTeacherPotential t v x

def IsMassNetLocalMin {d n m : ℕ} (t : Fin m → ℝ) (v : Fin m → Vec d)
    (s : Fin n → ℝ) (w : Fin n → Vec d) : Prop :=
  IsLocalMinOn (massNetLossPair t v) {p : Parameters d n | ∀ i, ‖p.2 i‖ = 1} (s, w)

def kernelMassLoss {n m : ℕ} (kf : ℝ → ℝ) (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, s i * s j * kf (θ i - θ j) -
    ∑ i, ∑ k, s i * t k * kf (θ i - β k)

def kernelTeacherSelfEnergy {m : ℕ} (kf : ℝ → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, ∑ l, t k * t l * kf (β k - β l)

def kernelMassLossPair {n m : ℕ} (kf : ℝ → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  kernelMassLoss kf p.1 β t p.2

def kernelResidual {n m : ℕ} (kf : ℝ → ℝ) (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) (γ : ℝ) : ℝ :=
  ∑ j, s j * kf (γ - θ j) - ∑ k, t k * kf (γ - β k)

/-- When the kernel derivative is `-kd`, this field is minus residual slope. -/
def kernelTorqueField {n m : ℕ} (kd : ℝ → ℝ) (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) (γ : ℝ) : ℝ :=
  ∑ j, s j * kd (γ - θ j) - ∑ k, t k * kd (γ - β k)

def kernelExcessLoss {n m : ℕ} (kf : ℝ → ℝ) (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) : ℝ :=
  kernelMassLoss kf s β t θ + kernelTeacherSelfEnergy kf β t

def residualPotential {n m : ℕ} (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) (γ : ℝ) : ℝ :=
  ∑ j, s j * phiCos (γ - θ j) - ∑ k, t k * phiCos (γ - β k)

def signedMassLossNoncentered {n m : ℕ} (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) : ℝ := kernelMassLoss phiCosJ s β t θ

def signedMassLossPairNoncentered {n m : ℕ} (β : Fin m → ℝ) (t : Fin m → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ := signedMassLossNoncentered p.1 β t p.2

def IsSignedMassCriticalNoncentered {n m : ℕ} (β : Fin m → ℝ) (t : Fin m → ℝ)
    (s θ : Fin n → ℝ) : Prop := fderiv ℝ (kernelMassLossPair phiCosJ β t) (s, θ) = 0

def residualPotentialJ {n m : ℕ} (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) (γ : ℝ) : ℝ :=
  kernelResidual phiCosJ s β t θ γ

def massTorqueFieldJ {n m : ℕ} (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) (γ : ℝ) : ℝ :=
  kernelTorqueField couplingHJ s β t θ γ

def teacherSelfEnergyJ {m : ℕ} (β : Fin m → ℝ) (t : Fin m → ℝ) : ℝ :=
  kernelTeacherSelfEnergy phiCosJ β t

def noncenteredExcessLoss {n m : ℕ} (s : Fin n → ℝ) (β : Fin m → ℝ)
    (t : Fin m → ℝ) (θ : Fin n → ℝ) : ℝ := kernelExcessLoss phiCosJ s β t θ

/-! ## Local-minimum topology -/

def IsStrictLocalMinPoint {X : Type*} [TopologicalSpace X] (f : X → ℝ) (x : X) : Prop :=
  ∀ᶠ y in 𝓝 x, y ≠ x → f x < f y



/-! A projective direction is represented by an angle in `[0, π)`.
The increasing enumeration below closes its final gap at the first angle plus
`π`. Strict interlacing means exactly one teacher in each open student gap. -/

def studentPositions {n : ℕ} (α : Fin n → ℝ) : Finset ℝ := Finset.univ.image α

def orderedStudent {n : ℕ} (α : Fin n → ℝ) (hα : Function.Injective α) : Fin n → ℝ :=
  (studentPositions α).orderEmbOfFin (by
    rw [studentPositions, Finset.card_image_of_injective _ hα]
    simp)

def cyclicGapLeft {n : ℕ} (α : Fin n → ℝ) (hα : Function.Injective α)
    (g : Fin n) : ℝ := orderedStudent α hα g

def cyclicGapRight {n : ℕ} (α : Fin n → ℝ) (hα : Function.Injective α)
    (g : Fin n) : ℝ :=
  if h : g.1 + 1 < n then orderedStudent α hα ⟨g.1 + 1, h⟩
  else orderedStudent α hα ⟨0, lt_of_le_of_lt (Nat.zero_le g.1) g.2⟩ + π

def liftAbove (first γ : ℝ) : ℝ := if γ < first then γ + π else γ

def cyclically_strictly_interlaces_general {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : Function.Injective α) : Prop :=
  ∀ g : Fin m, ∃! j : Fin n,
    cyclicGapLeft α hα g <
      liftAbove (orderedStudent α hα ⟨0, lt_of_le_of_lt (Nat.zero_le g.1) g.2⟩) (β j) ∧
    liftAbove (orderedStudent α hα ⟨0, lt_of_le_of_lt (Nat.zero_le g.1) g.2⟩) (β j) <
      cyclicGapRight α hα g

def cyclically_weakly_interlaces_general {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ)
    (hα : Function.Injective α) : Prop :=
  ∀ g : Fin m, ∃ j : Fin n,
    cyclicGapLeft α hα g <
      liftAbove (orderedStudent α hα ⟨0, lt_of_le_of_lt (Nat.zero_le g.1) g.2⟩) (β j) ∧
    liftAbove (orderedStudent α hα ⟨0, lt_of_le_of_lt (Nat.zero_le g.1) g.2⟩) (β j) <
      cyclicGapRight α hα g

structure StrictlyInterlaces {m n : ℕ} (α : Fin m → ℝ) (β : Fin n → ℝ) : Prop where
  students_injective : Function.Injective α
  interlaces : cyclically_strictly_interlaces_general α β students_injective

end PaperLeanFormalization
