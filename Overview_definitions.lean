import Mathlib

/-!
# Definitions for the five contributions

Every project-specific definition needed to read the five theorems in
`Overview_theorems.lean`, in the order in which the theorems need them: the
model with its two population losses first, then one section per contribution.

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
-/

noncomputable section
open Real Set Filter MeasureTheory Classical
open scoped BigOperators Topology RealInnerProductSpace

namespace PaperLeanFormalization

/-! ## The model: two features, one Gaussian input law, two population losses -/

/-- The two hidden-unit features of the paper: the centered feature
`C(z) = |z| / 2` and the plain ReLU `R(z) = max 0 z`. -/
inductive Model where
  | centered
  | plainRelu
  deriving DecidableEq

/-- Standard Gaussian density with respect to Euclidean Lebesgue measure. -/
def stdGaussianDensity {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (sqrt (2 * π))⁻¹ ^ d * exp (-‖x‖ ^ 2 / 2)

namespace Definitions

/-- Input space `ℝ^d`. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A width-`n` student: its masses `s` and its directions `w`. -/
abbrev Parameters (d n : ℕ) := (Fin n → ℝ) × (Fin n → Vec d)

/-- Centered population loss: the full formula in one place. -/
def CenteredLoss {d n m : ℕ} (s : Fin n → ℝ) (w : Fin n → Vec d)
    (t : Fin m → ℝ) (v : Fin m → Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : Vec d,
    ((∑ i, s i * (|⟪w i, x⟫_ℝ| / 2)) -
      ∑ k, t k * (|⟪v k, x⟫_ℝ| / 2)) ^ 2 * stdGaussianDensity x

/-- Plain-ReLU population loss: the full formula in one place. -/
def PlainLoss {d n m : ℕ} (s : Fin n → ℝ) (w : Fin n → Vec d)
    (t : Fin m → ℝ) (v : Fin m → Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : Vec d,
    ((∑ i, s i * max 0 ⟪w i, x⟫_ℝ) -
      ∑ k, t k * max 0 ⟪v k, x⟫_ℝ) ^ 2 * stdGaussianDensity x

/-! ## 1. Linear skip -/

/-- Population loss of a plain-ReLU student with a learned linear skip
`bStudent` against a plain-ReLU teacher with linear skip `bTeacher`. -/
def SkipLoss {d n m : ℕ} (bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d)
    (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : Vec d,
    (⟪bStudent, x⟫_ℝ + (∑ i, s i * max 0 ⟪w i, x⟫_ℝ) -
      (⟪bTeacher, x⟫_ℝ + ∑ k, t k * max 0 ⟪v k, x⟫_ℝ)) ^ 2 *
        stdGaussianDensity x

/-! ## 2. Spurious local minima for plain ReLU -/

/-- The unit direction `e(θ) = (cos θ, sin θ)` of the plane. -/
def Angle (θ : ℝ) : Vec 2 := ![cos θ, sin θ]

/-- The fixed planar teacher of the trap: three units at angles
`0`, `5π/6`, and `4π/3`, ... -/
def TrapTeacherAngle : Fin 3 → ℝ := ![0 * π, (5 / 6 : ℝ) * π, (4 / 3 : ℝ) * π]

/-- ... each of unit mass. -/
def TrapTeacherMass : Fin 3 → ℝ := fun _ => 1

end Definitions

/-- Strict local minimality within a set: all distinct sufficiently nearby
feasible parameters have strictly larger loss. -/
def IsStrictLocalMinOn {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (s : Set X) (x : X) : Prop :=
  ∀ᶠ y in 𝓝[s] x, y ≠ x → f x < f y

namespace Definitions

/-! ## 3. Teacher-span confinement -/

/-- The population loss of either feature, selected by the `Model`. -/
def Loss {d n m : ℕ} : Model → (Fin n → ℝ) → (Fin n → Vec d) →
    (Fin m → ℝ) → (Fin m → Vec d) → ℝ
  | .centered => CenteredLoss
  | .plainRelu => PlainLoss

/-! ## 4. Effective width

The effective-width statement needs no new definition: it is stated for
`PlainLoss` in the plane with directions `Angle θ`, and its critical points
are the zeros of the Fréchet derivative in the mass and angle coordinates. -/

/-! ## 5. Transfer to empirical loss -/

/-- The linear skip that cancels the first Gaussian moment of the residual;
`JointDistance` measures the student's skip relative to it. -/
def MatchingSkip {d n m : ℕ} (bTeacher : Vec d) (t : Fin m → ℝ)
    (v : Fin m → Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d) : Vec d :=
  bTeacher + (1 / 2 : ℝ) • ((∑ k, t k • v k) - ∑ i, s i • w i)

/-- The observed dataset's average squared radius. No directional weights occur. -/
def DataSecondMoment {d N : ℕ} (x : Fin N → Vec d) : ℝ :=
  (∑ j, ‖x j‖ ^ 2) / (N : ℝ)

/-- Ordinary unweighted empirical loss for input vectors and observed labels.
The literal formula also covers zero input vectors; results requiring a
nonempty dataset state `0 < N` explicitly. -/
def DataLoss {d n N : ℕ} (x : Fin N → Vec d) (y : Fin N → ℝ)
    (bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d) : ℝ :=
  ((1 / 2 : ℝ) * ∑ j,
    (⟪bStudent, x j⟫_ℝ + (∑ i, s i * max 0 ⟪w i, x j⟫_ℝ) - y j) ^ 2) / (N : ℝ)

/-- Maximum metric in masses, directions, and matching-skip mismatch. -/
def JointDistance {d n m : ℕ} (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d)
    (p q : Vec d × Parameters d n) : ℝ :=
  max (max (dist p.2.1 q.2.1) (dist p.2.2 q.2.2))
    (dist (p.1 - MatchingSkip bTeacher t v p.2.1 p.2.2)
      (q.1 - MatchingSkip bTeacher t v q.2.1 q.2.2))

end Definitions

open Definitions

/-- The Gaussian expectation of a test function. -/
def gaussianFunctional (d : ℕ) (f : Vec d → ℝ) : ℝ :=
  ∫ x : Vec d, f x * stdGaussianDensity x

/-- Positive homogeneity of degree two, the scaling law shared by every
squared residual of the networks. -/
def IsPosHomogeneousDegTwo {d : ℕ} (F : Vec d → ℝ) : Prop :=
  ∀ τ : ℝ, 0 ≤ τ → ∀ x : Vec d, F (τ • x) = τ ^ 2 * F x

namespace Definitions

/-- Accuracy of the actual unweighted input dataset against the Gaussian
functional for continuous degree-two homogeneous tests. The observed second
moment supplies the radial normalization. This does not construct or assume
a spherical quadrature rule. -/
def DataAccuracy {d N : ℕ} (x : Fin N → Vec d) (δ : ℝ) : Prop :=
  ∀ H : Vec d → ℝ, Continuous H → IsPosHomogeneousDegTwo H →
    ∀ L : ℝ,
      (∀ z z' : Vec d, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 → |H z - H z'| ≤ L * ‖z - z'‖) →
      |(d : ℝ) * ((∑ j, H (x j)) / (N : ℝ)) -
          DataSecondMoment x * gaussianFunctional d H| ≤
        (d : ℝ) * DataSecondMoment x * L * δ

/-- The observed labels come exactly from the teacher's plain-ReLU network
with its linear skip. Here `x j` is input number `j`, `y j` its label,
`t k` the mass of teacher unit `k`, and `v k` its direction.
There is no observation noise in this hypothesis. -/
def TeacherGeneratedLabels {d m N : ℕ} (x : Fin N → Vec d) (y : Fin N → ℝ)
    (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) : Prop :=
  ∀ j, y j = ⟪bTeacher, x j⟫_ℝ + ∑ k, t k * max 0 ⟪v k, x j⟫_ℝ

/-- The candidate minimizes empirical loss over the entire closed ball of
radius `r`, intersected with the unit-direction parameter space.

A parameter is `(linear skip, (masses, directions))`. The distance is
`JointDistance`, defined above: the maximum of the mass distance, direction
distance, and distance between matching-skip mismatches. Thus this is the
paper's joint parameter ball, with its stated choice of coordinates.

`IsMinOn` means the candidate's loss is no larger than the loss at *every*
feasible point in this ball. This is stronger than ordinary local minimality,
which only promises some possibly smaller neighborhood. The ball permits
signed mass perturbations; nonnegative masses are required only at the
candidate in `ZeroLossForFixedRadiusMinima` below. -/
def MinimizesOnJointBall {d n m N : ℕ} (x : Fin N → Vec d) (y : Fin N → ℝ)
    (bTeacher : Vec d) (t : Fin m → ℝ) (v : Fin m → Vec d) (r : ℝ)
    (candidate : Vec d × Parameters d n) : Prop :=
  IsMinOn (fun p : Vec d × Parameters d n => DataLoss x y p.1 p.2.1 p.2.2)
    {p | (∀ i, ‖p.2.2 i‖ = 1) ∧ JointDistance bTeacher t v p candidate ≤ r}
    candidate

/-- The desired deterministic conclusion for one dataset, one teacher's
hidden units, one student width, and one radius.

For every teacher skip and candidate student: if the labels come from that
teacher, the candidate has nonnegative masses and unit directions, and it
minimizes on the prescribed ball, then its empirical loss is zero.
For nonempty data, zero loss means every observed label is fitted exactly. -/
def ZeroLossForFixedRadiusMinima {d m N : ℕ} (n : ℕ)
    (x : Fin N → Vec d) (y : Fin N → ℝ)
    (t : Fin m → ℝ) (v : Fin m → Vec d) (r : ℝ) : Prop :=
  ∀ (bTeacher bStudent : Vec d) (s : Fin n → ℝ) (w : Fin n → Vec d),
    TeacherGeneratedLabels x y bTeacher t v →
    (∀ i, 0 ≤ s i) → (∀ i, ‖w i‖ = 1) →
    MinimizesOnJointBall x y bTeacher t v r (bStudent, (s, w)) →
    DataLoss x y bStudent s w = 0

end Definitions

end PaperLeanFormalization
