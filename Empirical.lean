import Mathlib
import Preliminaries
import Skip
import Geometry

-- The compactness and strong-law proofs need a larger elaboration budget.
set_option maxHeartbeats 800000

/-!
The fixed-radius finite-data argument of the paper, Section `boundaries`.
The loss integrands and finite sums are literal.  The proof follows joint scaling,
compact confinement, uniform approximation, cluster stability, and common zeros.
No antipodal pairing or positive-loss threshold is assumed.
-/

open scoped BigOperators
open MeasureTheory Filter Topology

noncomputable section

namespace PaperLeanFormalization.Empirical

open PaperLeanFormalization

variable {d n m N : ℕ}

/-- Polar coordinates for a degree-two homogeneous integrand, directly from
mathlib's measure-preserving sphere/radius homeomorphism. -/
theorem polar_integral_degree_two (hd : 0 < d)
    (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ 2 * F x)
    (φ : ℝ → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin d), F x * φ ‖x‖) =
      (∫ y, F (y : EuclideanSpace ℝ (Fin d)) ∂(sphereSurfaceMeasure d)) *
      ∫ r : Set.Ioi (0 : ℝ), (r : ℝ) ^ 2 * φ r ∂(Measure.volumeIoiPow (d - 1)) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    FiniteDimensional.nontrivial_of_finrank_pos (K := ℝ)
      (by rw [finrank_euclideanSpace_fin]; exact hd)
  letI : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) :=
    ⟨by
      rw [Measure.toSphere_apply_univ]
      exact ENNReal.mul_lt_top (ENNReal.nat_ne_top _) measure_ball_lt_top.ne⟩
  letI : SigmaFinite ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) :=
    IsFiniteMeasure.toSigmaFinite _
  have hchange :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).measurePreserving_homeomorphUnitSphereProd.integral_comp
      (Homeomorph.measurableEmbedding _)
      (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Set.Ioi (0 : ℝ) =>
        F ((z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin d))) * φ z.2)
  have hintegrand :
      (fun x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set (EuclideanSpace ℝ (Fin d))) =>
        F (((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d)) x).2 : ℝ) •
          ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d)) x).1 :
            EuclideanSpace ℝ (Fin d))) *
          φ ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d)) x).2 : ℝ)) =
      fun x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set (EuclideanSpace ℝ (Fin d))) =>
        F (x : EuclideanSpace ℝ (Fin d)) * φ ‖(x : EuclideanSpace ℝ (Fin d))‖ := by
    funext x
    rw [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe,
      smul_inv_smul₀ (norm_ne_zero_iff.mpr x.2)]
  rw [hintegrand] at hchange
  have hseparate :
      (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Set.Ioi (0 : ℝ) =>
        F ((z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin d))) * φ z.2) =
      fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Set.Ioi (0 : ℝ) =>
        F (z.1 : EuclideanSpace ℝ (Fin d)) * ((z.2 : ℝ) ^ 2 * φ z.2) := by
    funext z
    rw [hF z.2 (Set.mem_Ioi.mp z.2.2).le]
    ring
  rw [hseparate, integral_prod_mul
    (fun y : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 => F y)
    (fun r : Set.Ioi (0 : ℝ) => (r : ℝ) ^ 2 * φ r)] at hchange
  have hpuncture : (∫ x : EuclideanSpace ℝ (Fin d), F x * φ ‖x‖) =
      ∫ x : ({(0 : EuclideanSpace ℝ (Fin d))}ᶜ : Set (EuclideanSpace ℝ (Fin d))),
        F (x : EuclideanSpace ℝ (Fin d)) * φ ‖(x : EuclideanSpace ℝ (Fin d))‖
          ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).comap Subtype.val) := by
    rw [integral_subtype_comap
      (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin d))).compl (fun x => F x * φ ‖x‖),
      restrict_compl_singleton]
  rw [hpuncture, hchange, finrank_euclideanSpace_fin]
  rfl

/-- The radial factor is forced to be `d` by the Gaussian norm-square moment.
This proof evaluates no radial integral and calls no old polar-factorization
theorem. -/
theorem gaussian_sphere_degree_two_of_norm_moment (hd : 0 < d)
    (hnorm : (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 * stdGaussianDensity x) = (d : ℝ))
    (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ t : ℝ, 0 ≤ t → ∀ x, F (t • x) = t ^ 2 * F x) :
    gaussianFunctional d F = (d : ℝ) * uniformSphereFunctional d F := by
  let φ : ℝ → ℝ := fun r => (Real.sqrt (2 * Real.pi))⁻¹ ^ d * Real.exp (-r ^ 2 / 2)
  let M : ℝ := ∫ r : Set.Ioi (0 : ℝ), (r : ℝ) ^ 2 * φ r
    ∂(Measure.volumeIoiPow (d - 1))
  let T : ℝ := ((sphereSurfaceMeasure d) Set.univ).toReal
  have hmeasure : (sphereSurfaceMeasure d) Set.univ ≠ 0 := by
    rw [sphereSurfaceMeasure, Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin d)) one_pos).ne'
    rw [Ne, Nat.cast_eq_zero, finrank_euclideanSpace_fin]
    exact hd.ne'
  have hfinite : (sphereSurfaceMeasure d) Set.univ < ⊤ := by
    unfold sphereSurfaceMeasure
    exact measure_lt_top _ _
  have hT : T ≠ 0 := ne_of_gt (ENNReal.toReal_pos hmeasure hfinite.ne)
  have hunitIntegral : (∫ y, ‖(y : EuclideanSpace ℝ (Fin d))‖ ^ 2
      ∂(sphereSurfaceMeasure d)) = T := by
    have hpoint : (fun y : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        ‖(y : EuclideanSpace ℝ (Fin d))‖ ^ 2) = fun _ => (1 : ℝ) := by
      funext y
      rw [mem_sphere_zero_iff_norm.mp y.2, one_pow]
    rw [hpoint, integral_const]
    change T * 1 = T
    ring
  have hnormHom : ∀ t : ℝ, 0 ≤ t → ∀ x : EuclideanSpace ℝ (Fin d),
      ‖t • x‖ ^ 2 = t ^ 2 * ‖x‖ ^ 2 := by
    intro t ht x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    ring
  have hnormalization := polar_integral_degree_two hd (fun x => ‖x‖ ^ 2) hnormHom φ
  change (∫ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 * stdGaussianDensity x) =
    (∫ y, ‖(y : EuclideanSpace ℝ (Fin d))‖ ^ 2 ∂(sphereSurfaceMeasure d)) * M at hnormalization
  rw [hnorm, hunitIntegral] at hnormalization
  have hsplit := polar_integral_degree_two hd F hF φ
  change gaussianFunctional d F = (∫ y, F (y : EuclideanSpace ℝ (Fin d))
    ∂(sphereSurfaceMeasure d)) * M at hsplit
  rw [hsplit, hnormalization]
  unfold uniformSphereFunctional
  change _ = (T * M) * (_ / T)
  field_simp [hT]
  ring

/-- Gaussian/sphere normalization proved locally from polar coordinates and
the coordinate moment calculation. -/
theorem gaussian_sphere_degree_two (hd : 2 ≤ d)
    (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : IsPosHomogeneousDegTwo F) :
    gaussianFunctional d F = (d : ℝ) * uniformSphereFunctional d F :=
  gaussian_sphere_degree_two_of_norm_moment
    (lt_of_lt_of_le (by norm_num : 0 < 2) hd) (Preliminaries.gaussian_norm_square_moment hd) F hF

/-- Literal Gaussian population loss used throughout the local transfer proof. -/
def populationLoss (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : EuclideanSpace ℝ (Fin d),
    ((∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) -
      ∑ k, s k * (|(inner (v k) x : ℝ)| / 2)) ^ 2 *
        stdGaussianDensity x

/-- The ordinary unweighted empirical loss in sheared coordinates.
The input vectors are the actual data, including their radial magnitudes. -/
def shearedLoss (x : Fin N → Definitions.Vec d)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) : ℝ :=
  ((1 / 2 : ℝ) * ∑ j,
    ((∑ i, c i * (|(inner (w i) (x j) : ℝ)| / 2)) -
      (∑ k, s k * (|(inner (v k) (x j) : ℝ)| / 2)) +
      (inner u (x j) : ℝ)) ^ 2) / (N : ℝ)

/-- The closed joint ball uses exactly the manuscript's max-product distance. -/
theorem eq_max_product_distance
    (p q : ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) ×
      EuclideanSpace ℝ (Fin d)) :
    dist p q = max (max (dist p.1.1 q.1.1) (dist p.1.2 q.1.2)) (dist p.2 q.2) := by
  rw [Prod.dist_eq, Prod.dist_eq]

def residual (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) -
    ∑ k, s k * (|(inner (v k) x : ℝ)| / 2)

theorem relu_eq_even_add_odd (t : ℝ) : max 0 t = |t| / 2 + t / 2 := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_right ht, abs_of_nonneg ht]
    ring
  · rw [max_eq_left ht, abs_of_nonpos ht]
    ring

theorem network_relu_split
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    (∑ i, c i * max 0 (inner (w i) x : ℝ)) =
      (∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) +
      (1 / 2 : ℝ) * (inner (∑ i, c i • w i) x : ℝ) := by
  rw [sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [relu_eq_even_add_odd]; ring

/-- This identity connects the raw skip coordinate to the sheared empirical
loss without any probabilistic or positivity assumption. -/
theorem raw_skip_residual_eq_sheared
    (b bStar : EuclideanSpace ℝ (Fin d))
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    (inner b x : ℝ) + (∑ i, c i * max 0 (inner (w i) x : ℝ)) -
      ((inner bStar x : ℝ) + ∑ k, s k * max 0 (inner (v k) x : ℝ)) =
      residual c w s v x +
      (inner (b - (bStar + (1 / 2 : ℝ) • ((∑ k, s k • v k) - ∑ i, c i • w i))) x : ℝ) := by
  rw [network_relu_split, network_relu_split]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  unfold residual
  ring

/-- Observed labels enter explicitly. Teacher consistency gives exactly the
sheared loss, with no change to the original empirical normalization. -/
theorem raw_empirical_loss_eq_sheared
    (x : Fin N → Definitions.Vec d) (y : Fin N → ℝ)
    (b bStar : Definitions.Vec d) (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d)
    (hy : ∀ j, y j = (inner bStar (x j) : ℝ) + ∑ k, s k * max 0 (inner (v k) (x j) : ℝ)) :
    Definitions.DataLoss x y b c w =
      shearedLoss x c w (b - Definitions.MatchingSkip bStar s v c w) s v := by
  unfold Definitions.DataLoss shearedLoss
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [hy j, raw_skip_residual_eq_sheared]
  rfl

theorem feature_lipschitz {a : EuclideanSpace ℝ (Fin d)} (ha : ‖a‖ = 1)
    (x y : EuclideanSpace ℝ (Fin d)) :
    |(|(inner a x : ℝ)| / 2) - (|(inner a y : ℝ)| / 2)| ≤ ‖x - y‖ / 2 := by
  have hreverse := abs_abs_sub_abs_le_abs_sub (inner a x : ℝ) (inner a y : ℝ)
  have hinner := abs_real_inner_le_norm a (x - y)
  rw [ha, one_mul, inner_sub_right] at hinner
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [hreverse, hinner]


def massSphereBox (d n : ℕ) (C : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) :=
  (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) C) ×ˢ
    (Set.univ.pi fun _ : Fin n => Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)

theorem massSphereBox_compact (d n : ℕ) (C : ℝ) : IsCompact (massSphereBox d n C) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).prod
    (isCompact_univ_pi fun _ => isCompact_sphere _ _)

theorem mem_massSphereBox {C : ℝ}
    {p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))} :
    p ∈ massSphereBox d n C ↔
      (∀ i, 0 ≤ p.1 i) ∧ (∀ i, p.1 i ≤ C) ∧ (∀ i, ‖p.2 i‖ = 1) := by
  exact Preliminaries.nonnegative_parameter_box C p

theorem network_lipschitz
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (x y : EuclideanSpace ℝ (Fin d)) :
    |(∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) -
      (∑ i, c i * (|(inner (w i) y : ℝ)| / 2))| ≤
      ((∑ i, |c i|) / 2) * ‖x - y‖ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |c i * (|(inner (w i) x : ℝ)| / 2) -
        c i * (|(inner (w i) y : ℝ)| / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * (‖x - y‖ / 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (feature_lipschitz (hw i) x y) (abs_nonneg _)
    _ = ((∑ i, |c i|) / 2) * ‖x - y‖ := by rw [← Finset.sum_mul]; ring

theorem residual_lipschitz
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (x y : EuclideanSpace ℝ (Fin d)) :
    |residual c w s v x - residual c w s v y| ≤
      ((∑ i, |c i|) + ∑ k, |s k|) / 2 * ‖x - y‖ := by
  have hstudent := network_lipschitz c w hw x y
  have hteacher := network_lipschitz s v hv x y
  have htri := abs_sub
    ((∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) -
      ∑ i, c i * (|(inner (w i) y : ℝ)| / 2))
    ((∑ k, s k * (|(inner (v k) x : ℝ)| / 2)) -
      ∑ k, s k * (|(inner (v k) y : ℝ)| / 2))
  have hid : residual c w s v x - residual c w s v y =
      ((∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) -
        ∑ i, c i * (|(inner (w i) y : ℝ)| / 2)) -
      ((∑ k, s k * (|(inner (v k) x : ℝ)| / 2)) -
        ∑ k, s k * (|(inner (v k) y : ℝ)| / 2)) := by unfold residual; ring
  rw [hid]
  nlinarith only [htri, hstudent, hteacher]

/-- Squaring a bounded Lipschitz residual gives the constant `B²`. -/
theorem half_square_lipschitz {a b B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (ha : |a| ≤ B) (hb : |b| ≤ B)
    (hab : |a - b| ≤ B * D) :
    |(1 / 2 : ℝ) * a ^ 2 - (1 / 2 : ℝ) * b ^ 2| ≤ B ^ 2 * D := by
  have hsum : |a + b| ≤ 2 * B := by
    linarith only [abs_add a b, ha, hb]
  have hmul := mul_le_mul hab hsum (abs_nonneg (a + b)) (mul_nonneg hB hD)
  rw [show (1 / 2 : ℝ) * a ^ 2 - (1 / 2 : ℝ) * b ^ 2 =
    (1 / 2 : ℝ) * ((a - b) * (a + b)) by ring,
    abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith only [hmul]

/-- The comparison must also cover competitors: their mass magnitudes are
bounded by `C + r`, even when their masses have either sign. -/
theorem competitor_mass_bound
    {p q : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))}
    {C r : ℝ} (hp0 : ∀ i, 0 ≤ p.1 i) (hpC : ∀ i, p.1 i ≤ C)
    (hnear : dist q p ≤ r) (i : Fin n) : |q.1 i| ≤ C + r := by
  have hcoord : dist (q.1 i) (p.1 i) ≤ dist q p := by
    exact le_trans (dist_le_pi_dist q.1 p.1 i)
      (by rw [Prod.dist_eq]; exact le_max_left _ _)
  rw [Real.dist_eq] at hcoord
  have htri : |q.1 i| ≤ |q.1 i - p.1 i| + |p.1 i| := by
    simpa only [sub_add_cancel] using abs_add (q.1 i - p.1 i) (p.1 i)
  rw [abs_of_nonneg (hp0 i)] at htri
  linarith only [htri, hcoord, hnear, hpC i]

/-- The finite kernel energy is continuous, directly by its displayed sums.
The fresh Gaussian/kernel identity supplies continuity of the literal population
loss on the sphere constraint without a global differentiability detour. -/
theorem finite_kernel_energy_continuous (K : ℝ → ℝ) (hK : Continuous K)
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d)) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
      (1 / (4 * Real.pi)) *
      ((∑ i, ∑ j, p.1 i * p.1 j * K (inner (p.2 i) (p.2 j) : ℝ)) -
        2 * (∑ i, ∑ k, p.1 i * s k * K (inner (p.2 i) (v k) : ℝ)) +
        ∑ k, ∑ l, s k * s l * K (inner (v k) (v l) : ℝ))) := by
  have hc (i : Fin n) : Continuous
      (fun p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d)) => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hw (i : Fin n) : Continuous
      (fun p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d)) => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hstudent : Continuous
      (fun p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
        ∑ i, ∑ j, p.1 i * p.1 j * K (inner (p.2 i) (p.2 j) : ℝ)) := by
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact ((hc i).mul (hc j)).mul (hK.comp ((hw i).inner (hw j)))
  have hcross : Continuous
      (fun p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d)) =>
        ∑ i, ∑ k, p.1 i * s k * K (inner (p.2 i) (v k) : ℝ)) := by
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro k _
    exact ((hc i).mul continuous_const).mul (hK.comp ((hw i).inner continuous_const))
  exact continuous_const.mul
    ((hstudent.sub (continuous_const.mul hcross)).add continuous_const)



/-- The manuscript's fixed-radius minimizer-stability theorem.  The conclusion
uses an actual cluster point, not an assumed convergent sequence. -/
theorem thm_minimizer_stability
    {E : Type*} [MetricSpace E] {f : E → ℝ} (hf : Continuous f)
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    {g : ℕ → E → ℝ} {x : ℕ → E} (hx : ∀ j, x j ∈ K)
    (happrox : TendstoUniformlyOn g f atTop
      {y | ∃ z ∈ K, dist y z ≤ r})
    (hmin : ∀ j, IsMinOn (g j) (Metric.closedBall (x j) r) (x j))
    {z : E} (hz : MapClusterPt z atTop x) : IsLocalMin f z := by
  obtain ⟨φ, hφ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hz
  have hzK : z ∈ K := hK.isClosed.mem_of_tendsto hlim
    (eventually_of_forall fun j => hx (φ j))
  have hunif := happrox.seq_tendstoUniformlyOn φ hφ.tendsto_atTop
  have hxlim : Tendsto (fun j => g (φ j) (x (φ j))) atTop (𝓝 (f z)) :=
    hunif.tendsto_comp hf.continuousAt.continuousWithinAt
      (tendsto_nhdsWithin_iff.mpr ⟨hlim, eventually_of_forall fun j =>
        ⟨x (φ j), hx (φ j), by simpa only [dist_self] using hr.le⟩⟩)
  refine Filter.eventually_of_mem
    (Metric.ball_mem_nhds z (half_pos hr)) ?_
  intro y hy
  have hyz : dist y z < r / 2 := Metric.mem_ball.mp hy
  have hyK : y ∈ {y | ∃ z ∈ K, dist y z ≤ r} :=
    ⟨z, hzK, le_trans hyz.le (by linarith only [hr])⟩
  have hylim : Tendsto (fun j => g (φ j) y) atTop (𝓝 (f y)) :=
    hunif.tendsto_at hyK
  have hnear : ∀ᶠ j in atTop, dist (x (φ j)) z < r / 2 := by
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim (r / 2) (half_pos hr)
    exact eventually_atTop.mpr ⟨M, hM⟩
  apply le_of_tendsto_of_tendsto hxlim hylim
  refine hnear.mono fun j hj => hmin (φ j) (Metric.mem_closedBall.mpr ?_)
  have htriangle := dist_triangle y z (x (φ j))
  rw [dist_comm z (x (φ j))] at htriangle
  linarith only [htriangle, hyz, hj]

/-- The final contradiction in the sketch: the cluster point is a common zero,
and eventually lies inside the fixed-radius ball of its approximating minima. -/
theorem common_zero_cluster_contradiction
    {E : Type*} [MetricSpace E] {f : E → ℝ} (hf : Continuous f)
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    {g : ℕ → E → ℝ} {x : ℕ → E} (hx : ∀ j, x j ∈ K)
    (happrox : TendstoUniformlyOn g f atTop
      {y | ∃ z ∈ K, dist y z ≤ r})
    (hmin : ∀ j, IsMinOn (g j) (Metric.closedBall (x j) r) (x j))
    (hpositive : ∀ j, 0 < g j (x j))
    (hcommon : ∀ z ∈ K, IsLocalMin f z → ∀ j, g j z = 0) : False := by
  obtain ⟨z, hzK, φ, hφ, hlim⟩ := hK.tendsto_subseq hx
  have hzmin := thm_minimizer_stability hf hK hr hx happrox hmin
    (mapClusterPt_of_comp hφ.tendsto_atTop hlim)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim r hr
  have hzball : z ∈ Metric.closedBall (x (φ M)) r := by
    rw [Metric.mem_closedBall, dist_comm]
    exact (hM M le_rfl).le
  have hle : g (φ M) (x (φ M)) ≤ g (φ M) z := hmin (φ M) hzball
  rw [hcommon z hzK hzmin (φ M)] at hle
  exact (not_lt_of_ge hle) (hpositive (φ M))

/-- Uniform approximation and common exact zeros sharpen cluster-point
stability to exact finite-data loss, with no positive-loss threshold. -/
theorem fixed_radius_exactness_of_uniform_common_zeros
    {E I : Type*} [MetricSpace E] {f : E → ℝ} (hf : Continuous f)
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (g : I → E → ℝ) (Fine : ℝ → I → Prop)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a, Fine δ a → ∀ y, (∃ z ∈ K, dist y z ≤ r) → |g a y - f y| ≤ ε)
    (hcommon : ∀ z ∈ K, IsLocalMin f z → ∀ a, g a z = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a, Fine δ a → ∀ x ∈ K,
      IsMinOn (g a) (Metric.closedBall x r) x → g a x ≤ 0 := by
  classical
  by_contra hno
  push_neg at hno
  have hchoices : ∀ j : ℕ, ∃ a : I, ∃ x ∈ K,
      IsMinOn (g a) (Metric.closedBall x r) x ∧ 0 < g a x ∧
      ∀ y, (∃ z ∈ K, dist y z ≤ r) →
        |g a y - f y| ≤ 1 / ((j : ℝ) + 1) := by
    intro j
    obtain ⟨δ, hδ, hbound⟩ := happrox (1 / ((j : ℝ) + 1)) (by positivity)
    obtain ⟨a, ha, x, hx, hmin, hpositive⟩ := hno δ hδ
    exact ⟨a, x, hx, hmin, hpositive, hbound a ha⟩
  choose a x hx hmin hpositive hbound using hchoices
  have hunif : TendstoUniformlyOn (fun j => g (a j)) f atTop
      {y | ∃ z ∈ K, dist y z ≤ r} := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hsmall : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
      (tendsto_order.mp tendsto_one_div_add_atTop_nhds_0_nat).2 ε hε
    refine hsmall.mono fun j hj y hy => ?_
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hbound j y hy) hj
  exact common_zero_cluster_contradiction hf hK hr hx hunif hmin hpositive
    (fun z hz hlocal j => hcommon z hz hlocal (a j))

/-- Constraint-set version, obtained by making the unit-direction constraint
the ambient metric space.  Competitor masses remain completely unrestricted. -/
theorem fixed_radius_exactness_on_of_uniform_common_zeros
    {E I : Type*} [MetricSpace E] {f : E → ℝ}
    {S K : Set E} (hf : ContinuousOn f S) (hKS : K ⊆ S) (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (g : I → E → ℝ) (Fine : ℝ → I → Prop)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a, Fine δ a → ∀ y ∈ S,
        (∃ z ∈ K, dist y z ≤ r) → |g a y - f y| ≤ ε)
    (hcommon : ∀ z ∈ K, IsLocalMinOn f S z → ∀ a, g a z = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a, Fine δ a → ∀ x ∈ K,
      IsMinOn (g a) (S ∩ Metric.closedBall x r) x → g a x ≤ 0 := by
  let KS : Set S := (fun p : S => (p : E)) ⁻¹' K
  have himage : (fun p : S => (p : E)) '' KS = K := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hz
      exact ⟨⟨z, hKS hz⟩, hz, rfl⟩
  have hcompact : IsCompact KS := by
    rw [embedding_subtype_val.isCompact_iff, himage]
    exact hK
  have happroxS : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a, Fine δ a → ∀ y : S, (∃ z ∈ KS, dist y z ≤ r) →
        |g a y - f y| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := happrox ε hε
    refine ⟨δ, hδ, ?_⟩
    rintro a ha y ⟨z, hz, hdist⟩
    exact hbound a ha y y.2 ⟨z, hz, hdist⟩
  have hcommonS : ∀ z ∈ KS, IsLocalMin (fun p : S => f p) z →
      ∀ a, g a z = 0 := by
    intro z hz hlocal a
    apply hcommon z hz ?_ a
    rw [IsLocalMinOn, IsMinFilter, nhdsWithin_eq_map_subtype_coe z.2,
      Filter.eventually_map]
    simpa only [Subtype.coe_eta] using hlocal
  obtain ⟨δ, hδ, hexact⟩ := fixed_radius_exactness_of_uniform_common_zeros
    (continuousOn_iff_continuous_restrict.mp hf) hcompact hr
    (fun a (p : S) => g a p) Fine happroxS hcommonS
  refine ⟨δ, hδ, ?_⟩
  intro a ha x hx hmin
  apply hexact a ha ⟨x, hKS hx⟩ hx
  intro y hy
  exact hmin ⟨y.2, hy⟩

open PaperLeanFormalization

variable {d n m N : ℕ}

/-- The joint population loss in the manuscript's sheared coordinate `u`.
The complete integrand is visible in this definition. -/
def jointPopulationLoss (c : Fin n → ℝ)
    (w : Fin n → EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : EuclideanSpace ℝ (Fin d),
    ((∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) -
      (∑ k, s k * (|(inner (v k) x : ℝ)| / 2)) + (inner u x : ℝ)) ^ 2 *
      stdGaussianDensity x

/-- Positive homogeneity gives the exact factor `d` for the joint loss. -/
theorem joint_gaussian_sphere_normalization (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d)) :
    jointPopulationLoss c w u s v = (d : ℝ) * uniformSphereFunctional d
      (fun x => (1 / 2 : ℝ) * (residual c w s v x + (inner u x : ℝ)) ^ 2) := by
  have hres : ∀ t : ℝ, 0 ≤ t → ∀ x,
      residual c w s v (t • x) = t * residual c w s v x := by
    intro t ht x
    unfold residual
    simp only [real_inner_smul_right, abs_mul, abs_of_nonneg ht]
    simp_rw [mul_div_assoc]
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  have hhom : IsPosHomogeneousDegTwo
      (fun x => (1 / 2 : ℝ) * (residual c w s v x + (inner u x : ℝ)) ^ 2) := by
    intro t ht x
    dsimp only
    rw [hres t ht x, real_inner_smul_right]
    ring
  rw [← gaussian_sphere_degree_two hd _ hhom]
  unfold jointPopulationLoss gaussianFunctional residual
  rw [← integral_mul_left]
  congr 1
  funext x
  ring

theorem joint_residual_lipschitz
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (x y : EuclideanSpace ℝ (Fin d)) :
    |(residual c w s v x + (inner u x : ℝ)) -
      (residual c w s v y + (inner u y : ℝ))| ≤
      (((∑ i, |c i|) + ∑ k, |s k|) / 2 + ‖u‖) * ‖x - y‖ := by
  have hres := residual_lipschitz c w s v hw hv x y
  have hlinear := abs_real_inner_le_norm u (x - y)
  rw [inner_sub_right] at hlinear
  have htri := abs_add (residual c w s v x - residual c w s v y)
    ((inner u x : ℝ) - inner u y)
  rw [show residual c w s v x + (inner u x : ℝ) -
    (residual c w s v y + (inner u y : ℝ)) =
    (residual c w s v x - residual c w s v y) +
    ((inner u x : ℝ) - inner u y) by ring]
  nlinarith only [htri, hres, hlinear]

theorem joint_residual_growth_bound
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (x : EuclideanSpace ℝ (Fin d)) :
    |residual c w s v x + (inner u x : ℝ)| ≤
      (((∑ i, |c i|) + ∑ k, |s k|) / 2 + ‖u‖) * ‖x‖ := by
  have h := joint_residual_lipschitz c w u s v hw hv x 0
  simpa only [residual, inner_zero_right, abs_zero, zero_div, mul_zero,
    Finset.sum_const_zero, sub_zero, add_zero] using h


/-- The observed second moment is nonnegative even for empty or zero data. -/
theorem data_second_moment_nonnegative (x : Fin N → Definitions.Vec d) :
    0 ≤ Definitions.DataSecondMoment x :=
  div_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg ‖x j‖) (Nat.cast_nonneg N)

/-- Zero observed second moment forces every actual input vector to vanish. -/
theorem data_second_moment_eq_zero (x : Fin N → Definitions.Vec d) (hN : 0 < N)
    (hx : Definitions.DataSecondMoment x = 0) : ∀ j, x j = 0 := by
  have hN' : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hsum : (∑ j, ‖x j‖ ^ 2) = 0 := (div_eq_zero_iff.mp hx).resolve_right hN'
  intro j
  have hj : ‖x j‖ ^ 2 ≤ 0 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖x i‖) (Finset.mem_univ j)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hj (sq_nonneg _)))

/-- `eq:data-second-moment`: the normalization uses actual sample magnitudes. -/
theorem eq_data_second_moment (x : Fin N → Definitions.Vec d) :
    Definitions.DataSecondMoment x = (∑ j, ‖x j‖ ^ 2) / (N : ℝ) := rfl

/-- `eq:modulus`: accuracy is an inequality on raw data and a Gaussian integral. -/
theorem eq_modulus {x : Fin N → Definitions.Vec d} {δ : ℝ}
    (haccuracy : Definitions.DataAccuracy x δ)
    (H : Definitions.Vec d → ℝ) (hcontinuous : Continuous H)
    (hhomogeneous : IsPosHomogeneousDegTwo H) (L : ℝ)
    (hlip : ∀ z z', ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 → |H z - H z'| ≤ L * ‖z - z'‖) :
    |(d : ℝ) * ((∑ j, H (x j)) / (N : ℝ)) -
      Definitions.DataSecondMoment x * gaussianFunctional d H| ≤
      (d : ℝ) * Definitions.DataSecondMoment x * L * δ :=
  haccuracy H hcontinuous hhomogeneous L hlip

/-- Dividing by the positive observed second moment gives a model-independent
comparison with the Gaussian functional. -/
theorem data_accuracy_scaled {x : Fin N → Definitions.Vec d} {δ : ℝ}
    (hx : 0 < Definitions.DataSecondMoment x) (haccuracy : Definitions.DataAccuracy x δ)
    (H : Definitions.Vec d → ℝ) (hcontinuous : Continuous H)
    (hhomogeneous : IsPosHomogeneousDegTwo H) (L : ℝ)
    (hlip : ∀ z z', ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 → |H z - H z'| ≤ L * ‖z - z'‖) :
    |((d : ℝ) / Definitions.DataSecondMoment x) * ((∑ j, H (x j)) / (N : ℝ)) -
      gaussianFunctional d H| ≤ (d : ℝ) * L * δ := by
  have h := eq_modulus haccuracy H hcontinuous hhomogeneous L hlip
  have hid : (d : ℝ) * ((∑ j, H (x j)) / (N : ℝ)) -
      Definitions.DataSecondMoment x * gaussianFunctional d H =
      Definitions.DataSecondMoment x *
        (((d : ℝ) / Definitions.DataSecondMoment x) * ((∑ j, H (x j)) / (N : ℝ)) -
          gaussianFunctional d H) := by
    rw [mul_sub, ← mul_assoc, mul_div_cancel' _ hx.ne']
  rw [hid, abs_mul, abs_of_pos hx] at h
  apply (mul_le_mul_left hx).mp
  convert h using 1; ring

/-- `eq:empirical-loss`: the raw average is a finite average of half-squares. -/
theorem eq_empirical_loss (x : Fin N → Definitions.Vec d)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) :
    shearedLoss x c w u s v =
      (∑ j, (1 / 2 : ℝ) * (residual c w s v (x j) + (inner u (x j) : ℝ)) ^ 2) /
        (N : ℝ) := by
  unfold shearedLoss residual
  rw [Finset.mul_sum]

theorem joint_residual_continuous
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) :
    Continuous (fun x => residual c w s v x + (inner u x : ℝ)) := by
  unfold residual
  exact ((continuous_finset_sum _ fun i _ =>
    continuous_const.mul ((continuous_const.inner continuous_id).abs.div_const 2)).sub
    (continuous_finset_sum _ fun k _ =>
      continuous_const.mul ((continuous_const.inner continuous_id).abs.div_const 2))).add
    (continuous_const.inner continuous_id)

theorem joint_residual_half_square_homogeneous
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) :
    IsPosHomogeneousDegTwo
      (fun x => (1 / 2 : ℝ) * (residual c w s v x + (inner u x : ℝ)) ^ 2) := by
  intro t ht x
  have hres : residual c w s v (t • x) = t * residual c w s v x := by
    unfold residual
    simp only [real_inner_smul_right, abs_mul, abs_of_nonneg ht]
    simp_rw [mul_div_assoc]
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  dsimp only
  rw [hres, real_inner_smul_right]
  ring

theorem joint_half_square_gaussian
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) :
    gaussianFunctional d
      (fun x => (1 / 2 : ℝ) * (residual c w s v x + (inner u x : ℝ)) ^ 2) =
      jointPopulationLoss c w u s v := by
  unfold jointPopulationLoss gaussianFunctional residual
  rw [← integral_mul_left]
  congr 1
  funext x
  ring

/-- `eq:uniform-comparison`: the same explicit bound covers signed-mass
competitors, while the loss remains the actual unweighted data average. -/
theorem eq_uniform_comparison
    {x : Fin N → Definitions.Vec d} {δ C U : ℝ}
    (hx : 0 < Definitions.DataSecondMoment x) (hδ : 0 ≤ δ)
    (haccuracy : Definitions.DataAccuracy x δ)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d)
    (hc : ∀ i, |c i| ≤ C) (hu : ‖u‖ ≤ U)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    |((d : ℝ) / Definitions.DataSecondMoment x) * shearedLoss x c w u s v -
      jointPopulationLoss c w u s v| ≤
      (d : ℝ) * ((((n : ℝ) * C + ∑ k, |s k|) / 2 + U) ^ 2 * δ) := by
  let B := ((∑ i, |c i|) + ∑ k, |s k|) / 2 + ‖u‖
  have hB : 0 ≤ B := add_nonneg
    (div_nonneg (add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (c i))
      (Finset.sum_nonneg fun k _ => abs_nonneg (s k))) (by norm_num)) (norm_nonneg u)
  have hbound : ∀ z : Definitions.Vec d, ‖z‖ ≤ 1 →
      |residual c w s v z + (inner u z : ℝ)| ≤ B := by
    intro z hz
    exact le_trans (joint_residual_growth_bound c w u s v hw hv z)
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hB)
  have hlip : ∀ z z' : Definitions.Vec d, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 →
      |(1 / 2 : ℝ) * (residual c w s v z + (inner u z : ℝ)) ^ 2 -
        (1 / 2 : ℝ) * (residual c w s v z' + (inner u z' : ℝ)) ^ 2| ≤
      B ^ 2 * ‖z - z'‖ := by
    intro z z' hz hz'
    exact half_square_lipschitz hB (norm_nonneg _)
      (hbound z hz) (hbound z' hz') (joint_residual_lipschitz c w u s v hw hv z z')
  have hraw := data_accuracy_scaled hx haccuracy
    (fun z => (1 / 2 : ℝ) * (residual c w s v z + (inner u z : ℝ)) ^ 2)
    (continuous_const.mul ((joint_residual_continuous c w u s v).pow 2))
    (joint_residual_half_square_homogeneous c w u s v) (B ^ 2) hlip
  rw [← eq_empirical_loss, joint_half_square_gaussian] at hraw
  have hsum : (∑ i, |c i|) ≤ (n : ℝ) * C := by
    calc
      _ ≤ (∑ _i : Fin n, C) := Finset.sum_le_sum fun i _ => hc i
      _ = (n : ℝ) * C := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hcap : B ≤ ((n : ℝ) * C + ∑ k, |s k|) / 2 + U := by
    dsimp [B]
    linarith only [hsum, hu]
  exact hraw.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (pow_le_pow_left hB hcap 2) hδ) (Nat.cast_nonneg d))

theorem thickened_box_uniform_comparison
    {x : Fin N → Definitions.Vec d} {δ C U r : ℝ}
    (hx : 0 < Definitions.DataSecondMoment x) (hδ : 0 ≤ δ)
    (haccuracy : Definitions.DataAccuracy x δ)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) (hv : ∀ k, ‖v k‖ = 1)
    {p q : ((Fin n → ℝ) × (Fin n → Definitions.Vec d)) × Definitions.Vec d}
    (hp : p ∈ massSphereBox d n C ×ˢ Metric.closedBall 0 U)
    (hnear : dist q p ≤ r) (hq : ∀ i, ‖q.1.2 i‖ = 1) :
    |((d : ℝ) / Definitions.DataSecondMoment x) * shearedLoss x q.1.1 q.1.2 q.2 s v -
      jointPopulationLoss q.1.1 q.1.2 q.2 s v| ≤
      (d : ℝ) * ((((n : ℝ) * (C + r) + ∑ k, |s k|) / 2 + (U + r)) ^ 2 * δ) := by
  have hdist : max (max (dist q.1.1 p.1.1) (dist q.1.2 p.1.2))
      (dist q.2 p.2) ≤ r := by rwa [← eq_max_product_distance]
  have hmassdist : dist q.1 p.1 ≤ r := by
    rw [Prod.dist_eq]
    exact (max_le_iff.mp hdist).1
  have hpdata := mem_massSphereBox.mp hp.1
  have hmass : ∀ i, |q.1.1 i| ≤ C + r :=
    competitor_mass_bound hpdata.1 hpdata.2.1 hmassdist
  have hskip : ‖q.2‖ ≤ U + r := by
    have hpU : ‖p.2‖ ≤ U := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2
    have hskipdist := (max_le_iff.mp hdist).2
    rw [dist_eq_norm] at hskipdist
    have htriangle : ‖q.2‖ ≤ ‖q.2 - p.2‖ + ‖p.2‖ := by
      simpa only [sub_add_cancel] using norm_add_le (q.2 - p.2) p.2
    linarith only [htriangle, hskipdist, hpU]
  exact eq_uniform_comparison hx hδ haccuracy q.1.1 q.1.2 q.2 s v hmass hskip hq hv

theorem shearedLoss_nonnegative (x : Fin N → Definitions.Vec d)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) : 0 ≤ shearedLoss x c w u s v := by
  unfold shearedLoss
  exact div_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (Nat.cast_nonneg N)

theorem all_zero_sheared_loss (x : Fin N → Definitions.Vec d) (hx : ∀ j, x j = 0)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) : shearedLoss x c w u s v = 0 := by
  simp [shearedLoss, hx]

theorem continuous_gaussian_square_zero
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    (hint : Integrable (fun x => g x ^ 2 * stdGaussianDensity x))
    (hzero : (∫ x : EuclideanSpace ℝ (Fin d), g x ^ 2 * stdGaussianDensity x) = 0) :
    ∀ x, g x = 0 := by
  have hdens : ∀ x : EuclideanSpace ℝ (Fin d), 0 < stdGaussianDensity x := by
    intro x
    unfold stdGaussianDensity
    exact mul_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr
      (mul_pos (by norm_num) Real.pi_pos))) d) (Real.exp_pos _)
  have hae : (fun x => g x ^ 2 * stdGaussianDensity x) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg (sq_nonneg _) (hdens x).le) hint).mp hzero
  have hgzero : g =ᵐ[volume] 0 := hae.mono fun x hx =>
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hx).resolve_right (hdens x).ne')
  have heq : g = 0 := MeasureTheory.Measure.eq_of_ae_eq hgzero hg continuous_const
  intro x
  exact congrFun heq x

/-- A population exact fit is a common zero for every actual finite dataset. -/
theorem joint_population_zero_is_common_empirical_zero
    (hd : 2 ≤ d) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (hzero : jointPopulationLoss c w u s v = 0) :
    shearedLoss x c w u s v = 0 := by
  let g := fun x => residual c w s v x + (inner u x : ℝ)
  have hg : Continuous g := by
    dsimp only [g, residual]
    exact ((continuous_finset_sum _ fun i _ =>
      continuous_const.mul ((continuous_const.inner continuous_id).abs.div_const 2)).sub
      (continuous_finset_sum _ fun k _ =>
        continuous_const.mul ((continuous_const.inner continuous_id).abs.div_const 2))).add
      (continuous_const.inner continuous_id)
  have hint := Preliminaries.gaussian_growth_square_integrable hd hg
    (joint_residual_growth_bound c w u s v hw hv)
  have hzero' : (∫ x : EuclideanSpace ℝ (Fin d), g x ^ 2 * stdGaussianDensity x) = 0 := by
    change (1 / 2 : ℝ) * (∫ x, g x ^ 2 * stdGaussianDensity x) = 0 at hzero
    linarith only [hzero]
  have hfit := continuous_gaussian_square_zero hg hint hzero'
  unfold shearedLoss
  have hsum : (∑ j,
      ((∑ i, c i * (|(inner (w i) (x j) : ℝ)| / 2)) -
        (∑ k, s k * (|(inner (v k) (x j) : ℝ)| / 2)) +
        (inner u (x j) : ℝ)) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    change  (g (x j)) ^ 2 = 0
    rw [hfit (x j)]
    ring
  rw [hsum, mul_zero, zero_div]


end PaperLeanFormalization.Empirical
end

open Real Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace PaperLeanFormalization.Empirical

open PaperLeanFormalization Definitions

variable {d n m N : ℕ}

/-- The student part in the sheared coordinate. -/
def jointStudent (c : Fin n → ℝ) (w : Fin n → Vec d) (u x : Vec d) : ℝ :=
  (∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) + (inner u x : ℝ)

theorem jointStudent_scale (c : Fin n → ℝ) (w : Fin n → Vec d)
    (u x : Vec d) (a : ℝ) :
    jointStudent (fun i => a * c i) w (a • u) x = a * jointStudent c w u x := by
  unfold jointStudent
  rw [real_inner_smul_left, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Joint scaling is a scalar quadratic in the original unweighted average. -/
theorem shearedLoss_joint_scaling (x : Fin N → Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (a : ℝ) :
    shearedLoss x (fun i => a * c i) w (a • u) s v =
      ((1 / 2 : ℝ) * ∑ j,
        (a * jointStudent c w u (x j) - jointStudent s v 0 (x j)) ^ 2) / (N : ℝ) := by
  simp only [shearedLoss, residual]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [← jointStudent_scale]
  simp only [jointStudent, inner_zero_left, real_inner_smul_left, add_zero]
  congr 1
  ring

private theorem hasDerivAt_sample_scaling (G H : Fin N → ℝ) :
    HasDerivAt (fun a : ℝ => ((1 / 2 : ℝ) * ∑ j, (a * G j - H j) ^ 2) / (N : ℝ))
      (((∑ j, G j ^ 2) / (N : ℝ)) - (∑ j, G j * H j) / (N : ℝ)) 1 := by
  have h := ((HasDerivAt.sum (u := (Finset.univ : Finset (Fin N))) (fun j _ =>
    (((hasDerivAt_id (1 : ℝ)).mul_const (G j)).sub_const (H j)).pow 2)).const_mul
      (1 / 2 : ℝ)).div_const (N : ℝ)
  convert h using 1
  rw [← sub_div]
  congr 1
  simp only [id_eq, one_mul, pow_one, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A fixed-radius minimum satisfies exact joint scaling stationarity. -/
theorem eq_data_scaling (x : Fin N → Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) {r : ℝ} (hr : 0 < r)
    (hmin : IsMinOn
      (fun p : Parameters d n × Vec d => shearedLoss x p.1.1 p.1.2 p.2 s v)
      ({p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r) ((c, w), u)) :
    (∑ j, jointStudent c w u (x j) ^ 2) / (N : ℝ) =
      (∑ j, jointStudent c w u (x j) * jointStudent s v 0 (x j)) / (N : ℝ) := by
  let path : ℝ → Parameters d n × Vec d := fun a => ((fun i => a * c i, w), a • u)
  have hpath : Continuous path :=
    ((continuous_pi (fun i => continuous_id.mul continuous_const)).prod_mk continuous_const).prod_mk
      (continuous_id.smul continuous_const)
  have hone : path 1 = ((c, w), u) := by simp [path]
  have hnear : ∀ᶠ a in 𝓝 (1 : ℝ), path a ∈ Metric.closedBall ((c, w), u) r := by
    rw [← hone]
    exact hpath.continuousAt.eventually (Metric.closedBall_mem_nhds (path 1) hr)
  have hscalar : IsLocalMin
      (fun a : ℝ => ((1 / 2 : ℝ) * ∑ j,
        (a * jointStudent c w u (x j) - jointStudent s v 0 (x j)) ^ 2) / (N : ℝ)) 1 := by
    filter_upwards [hnear] with a ha
    have hle := hmin (show path a ∈
      {p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r from ⟨hw, ha⟩)
    rw [← hone] at hle
    change shearedLoss x (fun i => 1 * c i) w (1 • u) s v ≤
      shearedLoss x (fun i => a * c i) w (a • u) s v at hle
    simpa only [shearedLoss_joint_scaling] using hle
  exact sub_eq_zero.mp (hscalar.hasDerivAt_eq_zero
    (hasDerivAt_sample_scaling (fun j => jointStudent c w u (x j))
      (fun j => jointStudent s v 0 (x j))))

/-- `eq:data-scaling-loss`: stationarity turns the empirical loss into
half the difference between teacher and student sample moments. -/
theorem eq_data_scaling_loss {G H : Fin N → ℝ}
    (hscale : (∑ j, G j ^ 2) / (N : ℝ) = (∑ j, G j * H j) / (N : ℝ)) :
    ((1 / 2 : ℝ) * (∑ j, (G j - H j) ^ 2)) / (N : ℝ) =
      (1 / 2 : ℝ) * ((∑ j, H j ^ 2) / (N : ℝ) - (∑ j, G j ^ 2) / (N : ℝ)) := by
  have hexpand : (∑ j, (G j - H j) ^ 2) =
      (∑ j, G j ^ 2) - 2 * (∑ j, G j * H j) + ∑ j, H j ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexpand]
  have hscale' : (∑ j, G j ^ 2) * (N : ℝ)⁻¹ =
      (∑ j, G j * H j) * (N : ℝ)⁻¹ := hscale
  simp only [div_eq_mul_inv, add_mul, sub_mul, mul_assoc]
  rw [← hscale']
  ring

/-- Residual-square nonnegativity replaces the Cauchy--Schwarz detour. -/
theorem sample_student_moment_le_teacher {G H : Fin N → ℝ}
    (hscale : (∑ j, G j ^ 2) / (N : ℝ) = (∑ j, G j * H j) / (N : ℝ)) :
    (∑ j, G j ^ 2) / (N : ℝ) ≤ (∑ j, H j ^ 2) / (N : ℝ) := by
  have hnonneg : 0 ≤ ((1 / 2 : ℝ) * ∑ j, (G j - H j) ^ 2) / (N : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun j _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hidentity := eq_data_scaling_loss hscale
  linarith only [hnonneg, hidentity]

/-- Empty teachers require only scaling, without a data-accuracy assumption. -/
theorem empty_teacher_joint_ball_minimum_zero (x : Fin N → Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (s : Fin 0 → ℝ) (v : Fin 0 → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) {r : ℝ} (hr : 0 < r)
    (hmin : IsMinOn
      (fun p : Parameters d n × Vec d => shearedLoss x p.1.1 p.1.2 p.2 s v)
      ({p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r) ((c, w), u)) :
    shearedLoss x c w u s v = 0 := by
  have hscale := eq_data_scaling x c w u s v hw hr hmin
  simp only [jointStudent, Fin.sum_univ_zero, inner_zero_left, zero_add, mul_zero,
    Finset.sum_const_zero, zero_div] at hscale
  simp only [shearedLoss, residual, Fin.sum_univ_zero, sub_zero]
  rw [mul_div_assoc, hscale, mul_zero]

theorem jointStudent_lipschitz (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (x y : Vec d) :
    |jointStudent c w u x - jointStudent c w u y| ≤
      ((∑ i, |c i|) / 2 + ‖u‖) * ‖x - y‖ := by
  have hnet := network_lipschitz c w hw x y
  have hlin := abs_real_inner_le_norm u (x - y)
  rw [inner_sub_right] at hlin
  have htri := abs_add
    ((∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) -
      ∑ i, c i * (|(inner (w i) y : ℝ)| / 2))
    ((inner u x : ℝ) - inner u y)
  have heq : jointStudent c w u x - jointStudent c w u y =
      ((∑ i, c i * (|(inner (w i) x : ℝ)| / 2)) -
        ∑ i, c i * (|(inner (w i) y : ℝ)| / 2)) + ((inner u x : ℝ) - inner u y) := by
    unfold jointStudent
    ring
  rw [heq]
  nlinarith only [hnet, hlin, htri]

theorem jointStudent_growth (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (x : Vec d) :
    |jointStudent c w u x| ≤ ((∑ i, |c i|) / 2 + ‖u‖) * ‖x‖ := by
  simpa only [jointStudent, inner_zero_right, abs_zero, zero_div, mul_zero,
    Finset.sum_const_zero, zero_add, sub_zero] using jointStudent_lipschitz c w u hw x 0

theorem jointStudent_continuous (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d) :
    Continuous (jointStudent c w u) := by
  unfold jointStudent
  exact (continuous_finset_sum _ (fun i _ => continuous_const.mul
    ((continuous_const.inner continuous_id).abs.div_const 2))).add
    (continuous_const.inner continuous_id)

theorem jointStudent_input_homogeneous (c : Fin n → ℝ) (w : Fin n → Vec d)
    (u x : Vec d) (t : ℝ) (ht : 0 ≤ t) :
    jointStudent c w u (t • x) = t * jointStudent c w u x := by
  unfold jointStudent
  simp only [real_inner_smul_right, abs_mul, abs_of_nonneg ht]
  rw [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem jointStudent_square_lipschitz (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (x y : Vec d) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |jointStudent c w u x ^ 2 - jointStudent c w u y ^ 2| ≤
      (2 * ((∑ i, |c i|) / 2 + ‖u‖) ^ 2) * ‖x - y‖ := by
  let A := (∑ i, |c i|) / 2 + ‖u‖
  have hA : 0 ≤ A := add_nonneg
    (div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (c i)) (by norm_num)) (norm_nonneg _)
  have hb (x : Vec d) (hx : ‖x‖ ≤ 1) : |jointStudent c w u x| ≤ A :=
    (jointStudent_growth c w u hw x).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hx hA)
  have h := half_square_lipschitz hA (norm_nonneg (x - y)) (hb x hx) (hb y hy)
    (jointStudent_lipschitz c w u hw x y)
  rw [show jointStudent c w u x ^ 2 - jointStudent c w u y ^ 2 =
    2 * ((1 / 2 : ℝ) * jointStudent c w u x ^ 2 - (1 / 2 : ℝ) * jointStudent c w u y ^ 2) by ring,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans_eq (by dsimp [A]; ring)

/-- Teacher growth on arbitrary samples, without a support or pairing restriction. -/
theorem sample_teacher_moment_bound (x : Fin N → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (hv : ∀ k, ‖v k‖ = 1) :
    (∑ j, jointStudent s v 0 (x j) ^ 2) / (N : ℝ) ≤
      DataSecondMoment x * (∑ k, |s k|) ^ 2 / 4 := by
  have hterm (j : Fin N) : jointStudent s v 0 (x j) ^ 2 ≤
      ‖x j‖ ^ 2 * (∑ k, |s k|) ^ 2 / 4 := by
    have hb := jointStudent_growth s v 0 hv (x j)
    simp only [norm_zero, add_zero] at hb
    have hnonneg : 0 ≤ ((∑ k, |s k|) / 2) * ‖x j‖ :=
      mul_nonneg (div_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg (s k))
        (by norm_num)) (norm_nonneg _)
    have hsq : jointStudent s v 0 (x j) ^ 2 ≤ (((∑ k, |s k|) / 2) * ‖x j‖) ^ 2 :=
      sq_le_sq.mpr (by simpa only [abs_of_nonneg hnonneg] using hb)
    exact hsq.trans_eq (by ring)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
  have hdiv := div_le_div_of_le (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hsum
  apply hdiv.trans_eq
  rw [← Finset.sum_div, ← Finset.sum_mul]
  rw [eq_data_second_moment]
  ring

/-- `eq:data-teacher-bound`: at a scaling-stationary point the sample student
moment is bounded by the teacher moment, which the sample second moment bounds. -/
theorem eq_data_teacher_bound (x : Fin N → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hv : ∀ k, ‖v k‖ = 1) {G : Fin N → ℝ}
    (hscale : (∑ j, G j ^ 2) / (N : ℝ) =
      (∑ j, G j * jointStudent s v 0 (x j)) / (N : ℝ)) :
    (∑ j, G j ^ 2) / (N : ℝ) ≤ (∑ j, jointStudent s v 0 (x j) ^ 2) / (N : ℝ) ∧
      (∑ j, jointStudent s v 0 (x j) ^ 2) / (N : ℝ) ≤
        DataSecondMoment x * (∑ k, |s k|) ^ 2 / 4 :=
  ⟨sample_student_moment_le_teacher hscale, sample_teacher_moment_bound x s v hv⟩

/-- Relative-error absorption, kept as scalar algebra. -/
theorem coercivity_absorbs_relative_error {D W C U P Q δ : ℝ}
    (hD : 0 < D) (hW : 1 ≤ W) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (8 * D * W))
    (hlower : C ^ 2 / (4 * D * W) + U ^ 2 / D ≤ P)
    (herror : |Q - P| ≤ 2 * (C / 2 + U) ^ 2 * δ) : P ≤ 2 * Q := by
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hDW : 0 < D * W := mul_pos hD hWpos
  have hlower' : C ^ 2 / 4 + W * U ^ 2 ≤ D * W * P := by
    have h := mul_le_mul_of_nonneg_left hlower hDW.le
    have heq : D * W * (C ^ 2 / (4 * D * W) + U ^ 2 / D) = C ^ 2 / 4 + W * U ^ 2 := by
      field_simp [hD.ne', hWpos.ne']
      ring
    rwa [heq] at h
  have hP : 0 ≤ P := (add_nonneg
    (div_nonneg (sq_nonneg C) (by positivity)) (div_nonneg (sq_nonneg U) hD.le)).trans hlower
  have hA : (C / 2 + U) ^ 2 ≤ 2 * D * W * P := by
    have hu := mul_le_mul_of_nonneg_right hW (sq_nonneg U)
    nlinarith only [hlower', hu, sq_nonneg (C / 2 - U)]
  have hAscaled := mul_le_mul_of_nonneg_right hA hδ
  have hsmall' := (le_div_iff (show 0 < 8 * D * W by positivity)).mp hsmall
  have hsmallP := mul_le_mul_of_nonneg_right hsmall' hP
  have hback := (abs_le.mp herror).1
  nlinarith only [hback, hAscaled, hsmallP]

/-- One compact set simultaneously bounds masses, unit directions, and skip. -/
def jointCompactBox (d n : ℕ) (C U : ℝ) : Set (Parameters d n × Vec d) :=
  massSphereBox d n C ×ˢ Metric.closedBall 0 U

theorem jointCompactBox_compact (d n : ℕ) (C U : ℝ) : IsCompact (jointCompactBox d n C U) :=
  (massSphereBox_compact d n C).prod (isCompact_closedBall _ _)

theorem jointCompactBox_of_square_bounds (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (hc : ∀ i, 0 ≤ c i) (hw : ∀ i, ‖w i‖ = 1) {BC BU : ℝ}
    (hC : (∑ i, c i) ^ 2 ≤ BC) (hU : ‖u‖ ^ 2 ≤ BU) :
    ((c, w), u) ∈ jointCompactBox d n (sqrt BC) (sqrt BU) := by
  refine ⟨mem_massSphereBox.mpr ⟨hc, ?_, hw⟩, ?_⟩
  · intro i
    exact (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)).trans (le_sqrt_of_sq_le hC)
  · simpa only [Metric.mem_closedBall, dist_zero_right] using le_sqrt_of_sq_le hU

/-- Pointwise nonnegative features cannot cancel each other's squares. -/
theorem nonnegative_sum_diagonal_bound (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ 2) ≤ (∑ i, a i) ^ 2 := by
  calc
    _ ≤ ∑ i, a i * (∑ j, a j) := by
      apply Finset.sum_le_sum
      intro i _
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)) (ha i)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem gaussian_joint_student_even_odd_split (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (hw : ∀ i, ‖w i‖ = 1) :
    (∫ x : Vec d, jointStudent c w u x ^ 2 * stdGaussianDensity x) =
      (∫ x : Vec d, jointStudent c w 0 x ^ 2 * stdGaussianDensity x) +
      ∫ x : Vec d, (inner u x : ℝ) ^ 2 * stdGaussianDensity x := by
  have h := Preliminaries.gaussian_even_add_linear_square_split hd (jointStudent_continuous c w 0)
    (show ∀ x, jointStudent c w 0 (-x) = jointStudent c w 0 x by
      intro x
      simp only [jointStudent, inner_neg_right, abs_neg, inner_zero_left, neg_zero])
    (jointStudent_growth c w 0 hw) u
  simpa only [jointStudent, inner_zero_left, add_zero] using h

/-- Gaussian coercivity is direct: even--odd splitting, diagonal positivity,
and the covariance of a linear form. -/
theorem eq_data_coercivity (hd : 2 ≤ d) (hn : 0 < n)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (hc : ∀ i, 0 ≤ c i) (hw : ∀ i, ‖w i‖ = 1) :
    (∑ i, c i) ^ 2 / (4 * (n : ℝ)) + ‖u‖ ^ 2 ≤
      gaussianFunctional d (fun x => jointStudent c w u x ^ 2) := by
  have hsecond (z : Vec d) :
      (∫ x : Vec d, (inner z x : ℝ) ^ 2 * stdGaussianDensity x) = ‖z‖ ^ 2 := by
    simpa only [pow_two] using Preliminaries.gaussian_square_moment hd z
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcenter := Preliminaries.gaussian_growth_square_integrable hd (jointStudent_continuous c w 0)
    (jointStudent_growth c w 0 hw)
  have hlinear (i : Fin n) : Integrable (fun x : Vec d =>
      (inner (w i) x : ℝ) ^ 2 * stdGaussianDensity x) := by
    simpa only [id_eq] using Preliminaries.gaussian_growth_square_integrable hd
      (continuous_const.inner continuous_id) (fun x => abs_real_inner_le_norm (w i) x)
  have hdiag : Integrable (fun x : Vec d =>
      ∑ i, (c i ^ 2 / 4) * ((inner (w i) x : ℝ) ^ 2 * stdGaussianDensity x)) :=
    integrable_finset_sum _ fun i _ => (hlinear i).const_mul (c i ^ 2 / 4)
  have hpoint (x : Vec d) :
      (∑ i, (c i ^ 2 / 4) * ((inner (w i) x : ℝ) ^ 2 * stdGaussianDensity x)) ≤
      jointStudent c w 0 x ^ 2 * stdGaussianDensity x := by
    have h := nonnegative_sum_diagonal_bound
      (fun i => c i * (|(inner (w i) x : ℝ)| / 2))
      (fun i => mul_nonneg (hc i) (div_nonneg (abs_nonneg _) (by norm_num)))
    have hden : 0 ≤ stdGaussianDensity x := by unfold stdGaussianDensity; positivity
    have hscaled := mul_le_mul_of_nonneg_right h hden
    simp only [jointStudent, inner_zero_left, add_zero]
    convert hscaled using 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, div_pow, sq_abs]
    ring
  have hdiagInt := integral_mono hdiag hcenter hpoint
  rw [integral_finset_sum Finset.univ (fun i _ => (hlinear i).const_mul (c i ^ 2 / 4))] at hdiagInt
  simp only [integral_mul_left, hsecond, hw, one_pow, mul_one] at hdiagInt
  have hsum : (∑ i, c i) ^ 2 ≤ (n : ℝ) * ∑ i, c i ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := c))
  have hsumDiv : (∑ i, c i) ^ 2 / (4 * (n : ℝ)) ≤ ∑ i, c i ^ 2 / 4 := by
    rw [← Finset.sum_div]
    apply (div_le_iff (mul_pos (by norm_num : (0 : ℝ) < 4) hN)).mpr
    nlinarith only [hsum]
  unfold gaussianFunctional
  rw [gaussian_joint_student_even_odd_split hd c w u hw, hsecond]
  exact add_le_add_right (hsumDiv.trans hdiagInt) _

/-- The data criterion controls the actual student moment after positive
radial rescaling; the test function is the squared joint student. -/
theorem jointStudent_square_data_accuracy {x : Fin N → Vec d} {δ : ℝ}
    (hx : 0 < DataSecondMoment x) (hacc : DataAccuracy x δ)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (hw : ∀ i, ‖w i‖ = 1) :
    |((d : ℝ) / DataSecondMoment x) * ((∑ j, jointStudent c w u (x j) ^ 2) / (N : ℝ)) -
      gaussianFunctional d (fun z => jointStudent c w u z ^ 2)| ≤
      (d : ℝ) * (2 * ((∑ i, |c i|) / 2 + ‖u‖) ^ 2) * δ := by
  have hhom : IsPosHomogeneousDegTwo (fun z => jointStudent c w u z ^ 2) := by
    intro t ht z
    dsimp only
    rw [jointStudent_input_homogeneous c w u z t ht, mul_pow]
  exact data_accuracy_scaled hx hacc (fun z => jointStudent c w u z ^ 2)
    ((jointStudent_continuous c w u).pow 2) hhom
    (2 * ((∑ i, |c i|) / 2 + ‖u‖) ^ 2)
    (jointStudent_square_lipschitz c w u hw)

/-- The actual Gaussian moment is bounded by twice the rescaled sample
moment, itself bounded by half the squared teacher-mass sum times dimension.
Both inequalities are used by the compactness proof. -/
theorem eq_data_moment_absorption (hd : 2 ≤ d) (hn : 0 < n)
    {x : Fin N → Vec d} {δ : ℝ}
    (hx : 0 < DataSecondMoment x) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * (d : ℝ) * (n : ℝ))) (hacc : DataAccuracy x δ)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hc : ∀ i, 0 ≤ c i) (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    {r : ℝ} (hr : 0 < r)
    (hmin : IsMinOn
      (fun p : Parameters d n × Vec d => shearedLoss x p.1.1 p.1.2 p.2 s v)
      ({p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r) ((c, w), u)) :
    gaussianFunctional d (fun z => jointStudent c w u z ^ 2) ≤
        (2 * (d : ℝ) / DataSecondMoment x) *
          ((∑ j, jointStudent c w u (x j) ^ 2) / (N : ℝ)) ∧
      (2 * (d : ℝ) / DataSecondMoment x) *
          ((∑ j, jointStudent c w u (x j) ^ 2) / (N : ℝ)) ≤
        (d : ℝ) * (∑ k, |s k|) ^ 2 / 2 := by
  have hD : (0 : ℝ) < d := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hscale := eq_data_scaling x c w u s v hw hr hmin
  have hteacher := (sample_student_moment_le_teacher hscale).trans
    (sample_teacher_moment_bound x s v hv)
  have hlower := eq_data_coercivity hd hn c w u hc hw
  have herror := jointStudent_square_data_accuracy hx hacc c w u hw
  have habs : (∑ i, |c i|) = ∑ i, c i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hc i)
  rw [habs] at herror
  have hsmall' : (d : ℝ) * δ ≤ 1 / (8 * (1 : ℝ) * (n : ℝ)) := by
    have h := (le_div_iff (show 0 < 8 * (d : ℝ) * (n : ℝ) by positivity)).mp hsmall
    apply (le_div_iff (show 0 < 8 * (1 : ℝ) * (n : ℝ) by positivity)).mpr
    nlinarith only [h]
  have hlower' : (∑ i, c i) ^ 2 / (4 * (1 : ℝ) * (n : ℝ)) + ‖u‖ ^ 2 / (1 : ℝ) ≤
      gaussianFunctional d (fun z => jointStudent c w u z ^ 2) := by
    simpa only [mul_one, div_one] using hlower
  have herror' :
      |((d : ℝ) / DataSecondMoment x) * ((∑ j, jointStudent c w u (x j) ^ 2) / (N : ℝ)) -
        gaussianFunctional d (fun z => jointStudent c w u z ^ 2)| ≤
      2 * ((∑ i, c i) / 2 + ‖u‖) ^ 2 * ((d : ℝ) * δ) := by
    exact herror.trans_eq (by ring)
  have hcompare := coercivity_absorbs_relative_error (by norm_num : (0 : ℝ) < 1)
    (show (1 : ℝ) ≤ n by exact_mod_cast hn) (mul_nonneg hD.le hδ)
    hsmall' hlower' herror'
  have hteacher' : ((d : ℝ) / DataSecondMoment x) *
      ((∑ j, jointStudent c w u (x j) ^ 2) / (N : ℝ)) ≤ (d : ℝ) * (∑ k, |s k|) ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_left hteacher (div_nonneg hD.le hx.le)
    convert h using 1
    field_simp [hx.ne']
    ring
  constructor
  · exact hcompare.trans_eq (by ring)
  · calc
      _ = 2 * (((d : ℝ) / DataSecondMoment x) *
          ((∑ j, jointStudent c w u (x j) ^ 2) / (N : ℝ))) := by ring
      _ ≤ 2 * ((d : ℝ) * (∑ k, |s k|) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hteacher' (by norm_num)
      _ = _ := by ring

/-- Data accuracy, scaling stationarity, and Gaussian coercivity give the
same exact compact caps for arbitrary finite inputs. -/
theorem eq_data_parameter_bounds (hd : 2 ≤ d) (hn : 0 < n)
    {x : Fin N → Vec d} {δ : ℝ}
    (hx : 0 < DataSecondMoment x) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * (d : ℝ) * (n : ℝ))) (hacc : DataAccuracy x δ)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (u : Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hc : ∀ i, 0 ≤ c i) (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    {r : ℝ} (hr : 0 < r)
    (hmin : IsMinOn
      (fun p : Parameters d n × Vec d => shearedLoss x p.1.1 p.1.2 p.2 s v)
      ({p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r) ((c, w), u)) :
    (∑ i, c i) ^ 2 ≤ 2 * (d : ℝ) * (n : ℝ) * (∑ k, |s k|) ^ 2 ∧
      ‖u‖ ^ 2 ≤ (d : ℝ) * (∑ k, |s k|) ^ 2 / 2 ∧
      ((c, w), u) ∈ jointCompactBox d n
        (sqrt (2 * (d : ℝ) * (n : ℝ) * (∑ k, |s k|) ^ 2))
        (sqrt ((d : ℝ) * (∑ k, |s k|) ^ 2 / 2)) := by
  have hmoment := eq_data_moment_absorption hd hn hx hδ hsmall hacc
    c w u s v hc hw hv hr hmin
  have hP := hmoment.1.trans hmoment.2
  have hlower := eq_data_coercivity hd hn c w u hc hw
  have hC : (∑ i, c i) ^ 2 ≤ 2 * (d : ℝ) * (n : ℝ) * (∑ k, |s k|) ^ 2 := by
    have hfrac : (∑ i, c i) ^ 2 / (4 * (n : ℝ)) ≤ (d : ℝ) * (∑ k, |s k|) ^ 2 / 2 := by
      linarith only [hlower, hP, sq_nonneg ‖u‖]
    have h := (div_le_iff (show 0 < 4 * (n : ℝ) by positivity)).mp hfrac
    nlinarith only [h]
  have hU : ‖u‖ ^ 2 ≤ (d : ℝ) * (∑ k, |s k|) ^ 2 / 2 := by
    have hcfrac : 0 ≤ (∑ i, c i) ^ 2 / (4 * (n : ℝ)) := by positivity
    linarith only [hlower, hP, hcfrac]
  exact ⟨hC, hU, jointCompactBox_of_square_bounds c w u hc hw hC hU⟩

end PaperLeanFormalization.Empirical

end

open Real Set Filter MeasureTheory Classical
open scoped BigOperators Topology RealInnerProductSpace

noncomputable section
namespace PaperLeanFormalization.Empirical

variable {d n m : ℕ}

/-- The compactness argument is indexed by actual finite datasets. Its three
inputs follow the sketch: confinement, uniform comparison on the thickening,
then cluster-point stability and the common exact-zero contradiction. -/
theorem joint_exactness_of_population_and_confinement
    (hd : 2 ≤ d) (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d)
    (hv : ∀ k, ‖v k‖ = 1) {r C U cap : ℝ} (hr : 0 < r) (hcap : 0 < cap)
    (hcontinuous : ContinuousOn
      (fun p : Definitions.Parameters d n × Definitions.Vec d =>
        jointPopulationLoss p.1.1 p.1.2 p.2 s v) {p | ∀ i, ‖p.1.2 i‖ = 1})
    (hbenign : ∀ (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
        (u : Definitions.Vec d), (∀ i, 0 ≤ c i) → (∀ i, ‖w i‖ = 1) →
      IsLocalMinOn
        (fun p : Definitions.Parameters d n × Definitions.Vec d =>
          jointPopulationLoss p.1.1 p.1.2 p.2 s v)
        {p | ∀ i, ‖p.1.2 i‖ = 1} ((c, w), u) → jointPopulationLoss c w u s v = 0)
    (hconfinement : ∀ (N : ℕ) (x : Fin N → Definitions.Vec d) (ε : ℝ),
      0 < Definitions.DataSecondMoment x → 0 ≤ ε → ε ≤ cap → Definitions.DataAccuracy x ε →
      ∀ (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
        (u : Definitions.Vec d), (∀ i, 0 ≤ c i) → (∀ i, ‖w i‖ = 1) →
      IsMinOn
        (fun p : Definitions.Parameters d n × Definitions.Vec d =>
          shearedLoss x p.1.1 p.1.2 p.2 s v)
        ({p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r) ((c, w), u) →
      ((c, w), u) ∈ jointCompactBox d n C U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (x : Fin N → Definitions.Vec d),
      0 < Definitions.DataSecondMoment x → Definitions.DataAccuracy x δ →
      ∀ (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
        (u : Definitions.Vec d), (∀ i, 0 ≤ c i) → (∀ i, ‖w i‖ = 1) →
      IsMinOn
        (fun p : Definitions.Parameters d n × Definitions.Vec d =>
          shearedLoss x p.1.1 p.1.2 p.2 s v)
        ({p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r) ((c, w), u) →
      shearedLoss x c w u s v = 0 := by
  let E := Definitions.Parameters d n × Definitions.Vec d
  let I := Σ N : ℕ, Fin N → Definitions.Vec d
  let S : Set E := {p | ∀ i, ‖p.1.2 i‖ = 1}
  let K : Set E := jointCompactBox d n C U
  let f : E → ℝ := fun p => jointPopulationLoss p.1.1 p.1.2 p.2 s v
  let g : I → E → ℝ := fun a p =>
    ((d : ℝ) / Definitions.DataSecondMoment a.2) * shearedLoss a.2 p.1.1 p.1.2 p.2 s v
  let Fine : ℝ → I → Prop := fun δ a =>
    0 < Definitions.DataSecondMoment a.2 ∧
      ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ cap ∧ ε ≤ δ ∧ Definitions.DataAccuracy a.2 ε
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hKS : K ⊆ S := fun p hp => (mem_massSphereBox.mp hp.1).2.2
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a, Fine δ a → ∀ y ∈ S, (∃ z ∈ K, dist y z ≤ r) → |g a y - f y| ≤ ε := by
    intro ε hε
    let B := (d : ℝ) * (((n : ℝ) * (C + r) + ∑ k, |s k|) / 2 + (U + r)) ^ 2
    have hB : 0 ≤ B := mul_nonneg hdpos.le (sq_nonneg _)
    have hB1 : 0 < B + 1 := by linarith only [hB]
    refine ⟨ε / (B + 1), div_pos hε hB1, ?_⟩
    rintro a ⟨ha, εa, hεa, _hcap, hsmall, haccuracy⟩ y hy ⟨z, hz, hnear⟩
    have hbound := thickened_box_uniform_comparison ha hεa haccuracy s v hv hz hnear hy
    have hsmall' : εa * (B + 1) ≤ ε := (le_div_iff hB1).mp hsmall
    change |g a y - f y| ≤ _ at hbound
    have hbound' : |g a y - f y| ≤ B * εa := by
      convert hbound using 1
      dsimp [B]
      ring
    exact hbound'.trans (by nlinarith only [hsmall', hεa])
  have hcommon : ∀ z ∈ K, IsLocalMinOn f S z → ∀ a, g a z = 0 := by
    intro z hz hmin a
    have hzdata := mem_massSphereBox.mp hz.1
    have hzero := hbenign z.1.1 z.1.2 z.2 hzdata.1 hzdata.2.2 hmin
    have heq := joint_population_zero_is_common_empirical_zero hd
      a.2 z.1.1 z.1.2 z.2 s v hzdata.2.2 hv hzero
    change ((d : ℝ) / Definitions.DataSecondMoment a.2) * shearedLoss a.2 z.1.1 z.1.2 z.2 s v = 0
    rw [heq, mul_zero]
  obtain ⟨δ, hδ, hexact⟩ := fixed_radius_exactness_on_of_uniform_common_zeros
    hcontinuous hKS (jointCompactBox_compact d n C U) hr g Fine happrox hcommon
  refine ⟨min cap δ, lt_min hcap hδ, ?_⟩
  intro N x hx haccuracy c w u hc hw hmin
  let a : I := ⟨N, x⟩
  have hε : 0 ≤ min cap δ := (lt_min hcap hδ).le
  have hfine : Fine δ a :=
    ⟨hx, min cap δ, hε, min_le_left _ _, min_le_right _ _, haccuracy⟩
  have hpK := hconfinement N x (min cap δ) hx hε (min_le_left _ _) haccuracy c w u hc hw hmin
  have hfactor : 0 < (d : ℝ) / Definitions.DataSecondMoment x := div_pos hdpos hx
  have hscaled : IsMinOn (g a) (S ∩ Metric.closedBall ((c, w), u) r) ((c, w), u) := by
    intro p hp
    have hle : shearedLoss x c w u s v ≤ shearedLoss x p.1.1 p.1.2 p.2 s v := hmin hp
    exact mul_le_mul_of_nonneg_left hle hfactor.le
  have hzero := hexact a hfine ((c, w), u) hpK hscaled
  have hnonpositive : shearedLoss x c w u s v ≤ 0 := by
    exact (mul_le_mul_left hfactor).mp (by simpa only [mul_zero] using hzero)
  exact le_antisymm hnonpositive (shearedLoss_nonnegative x c w u s v)

/-- The raw empirical argument has now supplied all non-population inputs.
No spherical sampling object appears in the compactness index or the loss. -/
theorem data_fixed_radius_bridge_of_population_benignity
    (hd : 2 ≤ d) (hn : 0 < n)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d) (hv : ∀ k, ‖v k‖ = 1)
    (hcontinuous : ContinuousOn
      (fun p : Definitions.Parameters d n × Definitions.Vec d =>
        jointPopulationLoss p.1.1 p.1.2 p.2 s v) {p | ∀ i, ‖p.1.2 i‖ = 1})
    (hbenign : ∀ (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
        (u : Definitions.Vec d), (∀ i, 0 ≤ c i) → (∀ i, ‖w i‖ = 1) →
      IsLocalMinOn
        (fun p : Definitions.Parameters d n × Definitions.Vec d =>
          jointPopulationLoss p.1.1 p.1.2 p.2 s v)
        {p | ∀ i, ‖p.1.2 i‖ = 1} ((c, w), u) → jointPopulationLoss c w u s v = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (x : Fin N → Definitions.Vec d),
      0 < Definitions.DataSecondMoment x → Definitions.DataAccuracy x δ →
      ∀ (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
        (u : Definitions.Vec d), (∀ i, 0 ≤ c i) → (∀ i, ‖w i‖ = 1) →
      IsMinOn
        (fun p : Definitions.Parameters d n × Definitions.Vec d =>
          shearedLoss x p.1.1 p.1.2 p.2 s v)
        ({p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r) ((c, w), u) →
      shearedLoss x c w u s v = 0 := by
  let C := Real.sqrt (2 * (d : ℝ) * (n : ℝ) * (∑ k, |s k|) ^ 2)
  let U := Real.sqrt ((d : ℝ) * (∑ k, |s k|) ^ 2 / 2)
  have hcap : 0 < 1 / (8 * (d : ℝ) * (n : ℝ)) := by positivity
  apply joint_exactness_of_population_and_confinement hd s v hv hr hcap
    hcontinuous hbenign (C := C) (U := U)
  intro N x ε hx hε hsmall haccuracy c w u hc hw hmin
  exact (eq_data_parameter_bounds hd hn hx hε hsmall haccuracy
    c w u s v hc hw hv hr hmin).2.2

end PaperLeanFormalization.Empirical
end

open Real Set Filter MeasureTheory Classical
open scoped BigOperators Topology RealInnerProductSpace
noncomputable section
namespace PaperLeanFormalization.Empirical
variable {d n m : ℕ}

theorem joint_population_split (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d)) :
    jointPopulationLoss c w u s v = populationLoss c w s v + (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
  let M := PaperLeanFormalization.Definitions.MatchingSkip 0 s v c w
  have hraw : jointPopulationLoss c w u s v =
      PaperLeanFormalization.Definitions.SkipLoss (u + M) c w 0 s v := by
    unfold jointPopulationLoss PaperLeanFormalization.Definitions.SkipLoss
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    rw [raw_skip_residual_eq_sheared]
    change (residual c w s v x + (inner u x : ℝ)) ^ 2 * stdGaussianDensity x =
      (residual c w s v x + (inner ((u + M) - M) x : ℝ)) ^ 2 * stdGaussianDensity x
    rw [add_sub_cancel]
  rw [hraw, Skip.eq_skip_connection hd]
  change populationLoss c w s v + (1 / 2 : ℝ) * ‖(u + M) - M‖ ^ 2 = _
  rw [add_sub_cancel]

/-- Literal population-loss continuity is derived from the displayed finite
kernel energy, so no globally smooth loss extension is assumed. -/
theorem centered_population_continuousOn (hd : 2 ≤ d)
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hv : ∀ k, ‖v k‖ = 1) :
    ContinuousOn
      (fun p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d)) => populationLoss p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} := by
  have hkernel : Continuous (PaperLeanFormalization.Definitions.Kernel .centered) :=
    KernelCalculus.continuous_centeredKernel
  apply (finite_kernel_energy_continuous _ hkernel s v).continuousOn.congr
  intro p hp
  exact Preliminaries.loss_eq_kernelEnergy hd .centered p.1 p.2 s v hp hv

theorem joint_population_continuousOn (hd : 2 ≤ d)
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hv : ∀ k, ‖v k‖ = 1) :
    ContinuousOn
      (fun p : ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d) => jointPopulationLoss p.1.1 p.1.2 p.2 s v)
      {p | ∀ i, ‖p.1.2 i‖ = 1} := by
  have hcenter : ContinuousOn
      (fun p : ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d) => populationLoss p.1.1 p.1.2 s v)
      {p | ∀ i, ‖p.1.2 i‖ = 1} :=
    (centered_population_continuousOn hd s v hv).comp continuous_fst.continuousOn
      (fun _ hp => hp)
  have hlinear : Continuous
      (fun p : ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d) => (1 / 2 : ℝ) * ‖p.2‖ ^ 2) :=
    continuous_const.mul (continuous_snd.norm.pow 2)
  apply (hcenter.add hlinear.continuousOn).congr
  intro p _hp
  exact joint_population_split hd p.1.1 p.1.2 p.2 s v

/-- The local quadratic-product theorem removes the free skip and leaves a
centered local minimum. This consumes the fresh population even/odd split. -/
theorem joint_population_local_minimum_reduces (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hw : ∀ i, ‖w i‖ = 1)
    (hmin : IsLocalMinOn
      (fun p : ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) ×
        EuclideanSpace ℝ (Fin d) => jointPopulationLoss p.1.1 p.1.2 p.2 s v)
      {p | ∀ i, ‖p.1.2 i‖ = 1} ((c, w), u)) :
    u = 0 ∧ IsLocalMinOn
      (fun p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d)) => populationLoss p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w) := by
  let T : Set ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) :=
    {p | ∀ i, ‖p.2 i‖ = 1}
  have hswap : Tendsto
      (Prod.swap : EuclideanSpace ℝ (Fin d) ×
        ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) → _)
      (𝓝[Prod.snd ⁻¹' T] (u, (c, w)))
      (𝓝[{p | ∀ i, ‖p.1.2 i‖ = 1}] ((c, w), u)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact continuous_swap.continuousAt.mono_left nhdsWithin_le_nhds
    · exact self_mem_nhdsWithin
  have hpoly : IsLocalMinOn
      (fun q : EuclideanSpace ℝ (Fin d) ×
        ((Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) =>
          populationLoss q.2.1 q.2.2 s v + (1 / 2 : ℝ) * ‖q.1‖ ^ 2)
      (Prod.snd ⁻¹' T) (u, (c, w)) := by
    have hcomp := hswap.eventually hmin
    filter_upwards [hcomp] with q hq
    change jointPopulationLoss c w u s v ≤ jointPopulationLoss q.2.1 q.2.2 q.1 s v at hq
    rw [joint_population_split hd c w u s v,
      joint_population_split hd q.2.1 q.2.2 q.1 s v] at hq
    exact hq
  exact (Skip.quadratic_product_local_min_iff
    (fun p : (Fin n → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d)) => populationLoss p.1 p.2 s v)
    (κ := (1 / 2 : ℝ)) (by norm_num) (T := T) (u := u) (z := (c, w)) hw).mp hpoly


/-- Along the mass path from a candidate to an exact centered fit with the
same directions, the matching skip transported with the residual, every
empirical residual scales by `1 - t`; the empirical loss scales by its square.
No accuracy hypothesis enters. -/
theorem data_loss_along_fit_path {N : ℕ}
    (x : Fin N → Definitions.Vec d) (y : Fin N → ℝ)
    (b bStar : Definitions.Vec d) (c cFit : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d)
    (hy : ∀ j, y j = ⟪bStar, x j⟫_ℝ + ∑ k, s k * max 0 ⟪v k, x j⟫_ℝ)
    (hfit : ∀ z, (∑ i, cFit i * (|⟪w i, z⟫_ℝ| / 2)) =
      ∑ k, s k * (|⟪v k, z⟫_ℝ| / 2)) (t : ℝ) :
    Definitions.DataLoss x y
      (Definitions.MatchingSkip bStar s v (fun i => (1 - t) * c i + t * cFit i) w +
        (1 - t) • (b - Definitions.MatchingSkip bStar s v c w))
      (fun i => (1 - t) * c i + t * cFit i) w =
    (1 - t) ^ 2 * Definitions.DataLoss x y b c w := by
  have hres (j : Fin N) :
      ⟪Definitions.MatchingSkip bStar s v (fun i => (1 - t) * c i + t * cFit i) w +
          (1 - t) • (b - Definitions.MatchingSkip bStar s v c w), x j⟫_ℝ +
        (∑ i, ((1 - t) * c i + t * cFit i) * max 0 ⟪w i, x j⟫_ℝ) - y j =
      (1 - t) * (⟪b, x j⟫_ℝ + (∑ i, c i * max 0 ⟪w i, x j⟫_ℝ) - y j) := by
    rw [hy j, Skip.residual_even_odd, Skip.residual_even_odd, add_sub_cancel',
      real_inner_smul_left]
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, hfit (x j)]
    ring
  unfold Definitions.DataLoss
  simp_rw [hres, mul_pow, ← Finset.mul_sum]
  ring

/-- Dimension one: the student directions are `±1`, so a total mass equal to
the teacher's, with the matching skip, fits every dataset exactly. A minimum
on any fixed-radius joint ball therefore has zero empirical loss, for every
dataset and without an accuracy hypothesis. -/
theorem data_fixed_radius_dimension_one {n m N : ℕ} (hmn : m ≤ n)
    (x : Fin N → Definitions.Vec 1) (y : Fin N → ℝ)
    (b bStar : Definitions.Vec 1) (c : Fin n → ℝ) (w : Fin n → Definitions.Vec 1)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec 1)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (hy : ∀ j, y j = ⟪bStar, x j⟫_ℝ + ∑ k, s k * max 0 ⟪v k, x j⟫_ℝ)
    {r : ℝ} (hr : 0 < r)
    (hmin : IsMinOn (fun p : Definitions.Vec 1 × Definitions.Parameters 1 n =>
        Definitions.DataLoss x y p.1 p.2.1 p.2.2)
      {p | (∀ i, ‖p.2.2 i‖ = 1) ∧ Definitions.JointDistance bStar s v p (b, (c, w)) ≤ r}
      (b, (c, w))) :
    Definitions.DataLoss x y b c w = 0 := by
  classical
  obtain ⟨cFit, hsum⟩ : ∃ cFit : Fin n → ℝ, (∑ i, cFit i) = ∑ k, s k := by
    by_cases hn : n = 0
    · have hm : m = 0 := by omega (config := {})
      subst n; subst m
      exact ⟨c, by simp⟩
    · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      refine ⟨Function.update (fun _ ↦ 0) i (∑ k, s k), ?_⟩
      simpa using Geometry.sum_mass_update_add (fun _ : Fin n ↦ (0 : ℝ)) i (∑ k, s k)
  have hfit : ∀ z, (∑ i, cFit i * (|⟪w i, z⟫_ℝ| / 2)) =
      ∑ k, s k * (|⟪v k, z⟫_ℝ| / 2) := by
    intro z
    simp_rw [Geometry.centered_feature_dimension_one _ z (hw _),
      Geometry.centered_feature_dimension_one _ z (hv _), ← Finset.sum_mul, hsum]
  set a := b - Definitions.MatchingSkip bStar s v c w
  set D := max (dist cFit c) ‖a‖
  have hD0 : 0 ≤ D := le_max_of_le_right (norm_nonneg a)
  set t := min 1 (r / (D + 1))
  have ht0 : 0 < t := lt_min one_pos (div_pos hr (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htD : t * D ≤ r := by
    calc t * D ≤ r / (D + 1) * D := by
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) hD0
      _ ≤ r := by
          rw [div_mul_eq_mul_div, div_le_iff (by linarith)]
          nlinarith only [hr, hD0]
  set masses : Fin n → ℝ := fun i => (1 - t) * c i + t * cFit i with hmasses
  have hmem : (Definitions.MatchingSkip bStar s v masses w + (1 - t) • a, (masses, w)) ∈
      {p : Definitions.Vec 1 × Definitions.Parameters 1 n |
        (∀ i, ‖p.2.2 i‖ = 1) ∧ Definitions.JointDistance bStar s v p (b, (c, w)) ≤ r} := by
    refine ⟨hw, ?_⟩
    unfold Definitions.JointDistance
    simp only [add_sub_cancel']
    have h1 : dist masses c = t * dist cFit c := by
      rw [dist_eq_norm, dist_eq_norm]
      have : masses - c = t • (cFit - c) := by
        funext i; simp only [hmasses, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have h3 : dist ((1 - t) • a) a = t * ‖a‖ := by
      rw [dist_eq_norm]
      have : (1 - t) • a - a = (-t) • a := by
        rw [sub_smul, one_smul, neg_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
    rw [h1, dist_self, h3]
    refine max_le (max_le ?_ (le_of_lt hr)) ?_
    · exact le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0.le) htD
    · exact le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0.le) htD
  have hstep := hmin hmem
  simp only [Set.mem_setOf_eq] at hstep
  rw [data_loss_along_fit_path x y b bStar c cFit w s v hy hfit t] at hstep
  have hnonneg : 0 ≤ Definitions.DataLoss x y b c w := by
    unfold Definitions.DataLoss
    apply div_nonneg _ (Nat.cast_nonneg N)
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hkey : Definitions.DataLoss x y b c w * (t * (2 - t)) ≤ 0 := by
    have hring : Definitions.DataLoss x y b c w * (t * (2 - t)) =
        Definitions.DataLoss x y b c w - (1 - t) ^ 2 * Definitions.DataLoss x y b c w := by
      ring
    rw [hring]
    linarith only [hstep]
  have h2 : 0 < t * (2 - t) := mul_pos ht0 (by linarith only [ht1])
  refine le_antisymm ?_ hnonneg
  by_contra hpos
  exact absurd hkey (not_le.2 (mul_pos (lt_of_not_le hpos) h2))

set_option maxHeartbeats 800000 in
/-- Every sufficiently accurate actual dataset has only exact-fitting
nonnegative fixed-radius minima for teacher-consistent observed labels. The
competitors have signed masses, and the empirical loss is unweighted.
Dimension one needs no accuracy at all: the scalar fit argument applies to
every dataset, so the tolerance `δ = 1` is returned there. -/
theorem thm_fixed_radius_bridge (hd : 1 ≤ d) (hmn : m ≤ n)
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hv : ∀ k, ‖v k‖ = 1) (hs : ∀ k, 0 < s k) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (x : Fin N → Definitions.Vec d) (y : Fin N → ℝ),
      0 < N → Definitions.DataAccuracy x δ →
      ∀ (bStar b : Definitions.Vec d) (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d),
        (∀ j, y j = (inner bStar (x j) : ℝ) + ∑ k, s k * max 0 (inner (v k) (x j) : ℝ)) →
        (∀ i, 0 ≤ c i) → (∀ i, ‖w i‖ = 1) →
        IsMinOn (fun p : Definitions.Vec d × Definitions.Parameters d n =>
          Definitions.DataLoss x y p.1 p.2.1 p.2.2)
          {p | (∀ i, ‖p.2.2 i‖ = 1) ∧ Definitions.JointDistance bStar s v p (b, (c, w)) ≤ r}
          (b, (c, w)) → Definitions.DataLoss x y b c w = 0 := by
  by_cases hd1 : d = 1
  · subst hd1
    refine ⟨1, one_pos, ?_⟩
    intro N x y _hN _haccuracy bStar b c w hy _hc hw hmin
    exact data_fixed_radius_dimension_one hmn x y b bStar c w s v hw hv hy hr hmin
  have hd : 2 ≤ d := by omega (config := {})
  have hsheared : ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) (x : Fin N → Definitions.Vec d),
      0 < Definitions.DataSecondMoment x → Definitions.DataAccuracy x δ →
      ∀ (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d) (u : Definitions.Vec d),
        (∀ i, 0 ≤ c i) → (∀ i, ‖w i‖ = 1) →
      IsMinOn
        (fun p : Definitions.Parameters d n × Definitions.Vec d =>
          shearedLoss x p.1.1 p.1.2 p.2 s v)
        ({p | ∀ i, ‖p.1.2 i‖ = 1} ∩ Metric.closedBall ((c, w), u) r) ((c, w), u) →
      shearedLoss x c w u s v = 0 := by
    by_cases hm : m = 0
    · subst m
      refine ⟨1, one_pos, ?_⟩
      intro N x _hx _haccuracy c w u _hc hw hmin
      exact empty_teacher_joint_ball_minimum_zero x c w u s v hw hr hmin
    · have hn : 0 < n := lt_of_lt_of_le (Nat.pos_of_ne_zero hm) hmn
      apply data_fixed_radius_bridge_of_population_benignity hd hn
        s v hv (joint_population_continuousOn hd s v hv) (r := r) ?_ hr
      intro c w u hc hw hmin
      obtain ⟨hu, hcenter⟩ := joint_population_local_minimum_reduces hd c w u s v hw hmin
      have hcenterZero : populationLoss c w s v = 0 :=
        Geometry.centered_benign hd hmn hv hw hc hs hplane hcenter
      rw [joint_population_split hd c w u s v, hcenterZero, hu, norm_zero]
      norm_num
  obtain ⟨δ, hδ, hexact⟩ := hsheared
  refine ⟨δ, hδ, ?_⟩
  intro N x y hN haccuracy bStar b c w hy hc hw hmin
  rw [raw_empirical_loss_eq_sheared x y b bStar c w s v hy]
  by_cases hx : Definitions.DataSecondMoment x = 0
  · exact all_zero_sheared_loss x (data_second_moment_eq_zero x hN hx)
      c w (b - Definitions.MatchingSkip bStar s v c w) s v
  have hxpos : 0 < Definitions.DataSecondMoment x :=
    lt_of_le_of_ne (data_second_moment_nonnegative x) (Ne.symm hx)
  apply hexact N x hxpos haccuracy c w
    (b - Definitions.MatchingSkip bStar s v c w) hc hw
  intro z hz
  have hnear : Definitions.JointDistance bStar s v
      (z.2 + Definitions.MatchingSkip bStar s v z.1.1 z.1.2, z.1)
      (b, (c, w)) ≤ r := by
    have hdist := Metric.mem_closedBall.mp hz.2
    rw [eq_max_product_distance] at hdist
    simpa only [Definitions.JointDistance, add_sub_cancel] using hdist
  have hcomparison : Definitions.DataLoss x y b c w ≤
      Definitions.DataLoss x y (z.2 + Definitions.MatchingSkip bStar s v z.1.1 z.1.2)
        z.1.1 z.1.2 := (isMinOn_iff.mp hmin)
      (z.2 + Definitions.MatchingSkip bStar s v z.1.1 z.1.2, z.1) (show
      (z.2 + Definitions.MatchingSkip bStar s v z.1.1 z.1.2, z.1) ∈
        {p : Definitions.Vec d × Definitions.Parameters d n |
          (∀ i, ‖p.2.2 i‖ = 1) ∧ Definitions.JointDistance bStar s v p (b, (c, w)) ≤ r}
      from ⟨hz.1, hnear⟩)
  rw [raw_empirical_loss_eq_sheared x y b bStar c w s v hy,
    raw_empirical_loss_eq_sheared x y _ bStar z.1.1 z.1.2 s v hy,
    add_sub_cancel] at hcomparison
  exact hcomparison

end PaperLeanFormalization.Empirical
end

/-! ## General data: radial normalization, invariant angular law, and high-probability transfer -/

noncomputable section

open scoped BigOperators

namespace PaperLeanFormalization.Empirical.RadialData

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}

/-- A zero sample is assigned an arbitrary fixed unit direction. Its squared radius
is zero, so this choice cannot affect the analytic weighted average. -/
def unitDirection (e x : E) : E := by
  classical
  exact if x = 0 then e else ‖x‖⁻¹ • x

theorem norm_unitDirection (e : E) (he : ‖e‖ = 1) (x : E) :
    ‖unitDirection e x‖ = 1 := by
  by_cases hx : x = 0
  · simpa only [unitDirection, if_pos hx] using he
  · rw [unitDirection, if_neg hx, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel (norm_ne_zero_iff.mpr hx)]

theorem radial_reconstruction (e x : E) : ‖x‖ • unitDirection e x = x := by
  by_cases hx : x = 0
  · simp only [unitDirection, if_pos hx, hx, norm_zero, zero_smul]
  · rw [unitDirection, if_neg hx, smul_smul,
      mul_inv_cancel (norm_ne_zero_iff.mpr hx), one_smul]

end PaperLeanFormalization.Empirical.RadialData

end


noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology BigOperators ProbabilityTheory BoundedContinuousFunction

namespace PaperLeanFormalization.Empirical.RadialData

/-- Constants are anchored before compactness is invoked. The unanchored
class of all one-Lipschitz real functions is not bounded. -/
def anchoredLipschitzProbes (S : Type*) [PseudoMetricSpace S] (e : S) :
    Set (S →ᵇ ℝ) := {f | LipschitzWith 1 f ∧ f e = 0}

theorem anchoredLipschitzProbes_isCompact
    {S : Type*} [PseudoMetricSpace S] [CompactSpace S] (e : S)
    {B : ℝ} (hB : ∀ x : S, dist x e ≤ B) :
    IsCompact (anchoredLipschitzProbes S e) := by
  have hlip : IsClosed {f : S →ᵇ ℝ | LipschitzWith 1 f} :=
    (isClosed_setOf_lipschitzWith (α := S) (β := ℝ) (1 : NNReal)).preimage
      BoundedContinuousFunction.continuous_coe
  have hzero : IsClosed {f : S →ᵇ ℝ | f e = 0} :=
    isClosed_eq BoundedContinuousFunction.continuous_eval_const continuous_const
  have hclosed : IsClosed (anchoredLipschitzProbes S e) := hlip.inter hzero
  apply BoundedContinuousFunction.arzela_ascoli₂ (Set.Icc (-B) B) isCompact_Icc
    (anchoredLipschitzProbes S e) hclosed
  · intro f x hf
    have h := hf.1.dist_le_mul x e
    rw [hf.2, dist_zero_right, Real.norm_eq_abs, NNReal.coe_one, one_mul] at h
    exact abs_le.mp (h.trans (hB x))
  · apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => t) tendsto_id
    rintro x y ⟨f, hf⟩
    simpa only [NNReal.coe_one, one_mul] using hf.1.dist_le_mul x y

variable {Ω A : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (volume : Measure Ω)] [MeasurableSpace A]

set_option maxHeartbeats 800000 in
/-- The actual self-normalized strong law. In the radial application `R` is
the squared norm and `H(x)=R(x)f(x/‖x‖)`. The denominator must have a finite,
strictly positive expectation; unnormalized radial weights do not converge to
a normalized sample average. Pairwise independence already suffices. -/
theorem eq_weighted_sampling_limits
    (X : ℕ → Ω → A) (R H : A → ℝ)
    (hR : Measurable R) (hH : Measurable H)
    (hintR : Integrable (fun ω => R (X 0 ω)))
    (hintH : Integrable (fun ω => H (X 0 ω)))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j))
    (hident : ∀ i, IdentDistrib (X i) (X 0))
    (hmean : 0 < ∫ ω, R (X 0 ω)) :
    ∀ᵐ ω,
      Tendsto (fun N : ℕ => (∑ j in range N, R (X j ω)) / (N : ℝ))
        atTop (𝓝 (∫ ω, R (X 0 ω))) ∧
      Tendsto (fun N : ℕ =>
        (∑ j in range N, H (X j ω)) / (∑ j in range N, R (X j ω)))
        atTop (𝓝 ((∫ ω, H (X 0 ω)) / (∫ ω, R (X 0 ω)))) := by
  have hsumR := strong_law_ae_real (fun i ω => R (X i ω)) hintR
    (fun i j hij => (hindep hij).comp hR hR) (fun i => (hident i).comp hR)
  have hsumH := strong_law_ae_real (fun i ω => H (X i ω)) hintH
    (fun i j hij => (hindep hij).comp hH hH) (fun i => (hident i).comp hH)
  filter_upwards [hsumR, hsumH] with ω hωR hωH
  refine ⟨hωR, ?_⟩
  have hquot := hωH.div hωR (ne_of_gt hmean)
  change Tendsto (fun N : ℕ =>
    ((∑ j in range N, H (X j ω)) / (N : ℝ)) /
      ((∑ j in range N, R (X j ω)) / (N : ℝ)))
    atTop _ at hquot
  have heq : (fun N : ℕ =>
      ((∑ j in range N, H (X j ω)) / (N : ℝ)) /
        ((∑ j in range N, R (X j ω)) / (N : ℝ))) =
      fun N : ℕ => (∑ j in range N, H (X j ω)) / (∑ j in range N, R (X j ω)) := by
    funext N
    by_cases hN : N = 0
    · simp only [hN, range_zero, sum_empty, Nat.cast_zero, zero_div]
    · exact div_div_div_cancel_right _ (Nat.cast_ne_zero.mpr hN)
  rwa [heq] at hquot

/-- The actual self-normalized strong law, including eventual positivity of
its denominator. It consumes both limits in the sampling display. -/
theorem weighted_ratio_strong_law
    (X : ℕ → Ω → A) (R H : A → ℝ)
    (hR : Measurable R) (hH : Measurable H)
    (hintR : Integrable (fun ω => R (X 0 ω)))
    (hintH : Integrable (fun ω => H (X 0 ω)))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j))
    (hident : ∀ i, IdentDistrib (X i) (X 0))
    (hmean : 0 < ∫ ω, R (X 0 ω)) :
    ∀ᵐ ω,
      (∀ᶠ N : ℕ in atTop, 0 < ∑ j in range N, R (X j ω)) ∧
      Tendsto (fun N : ℕ =>
        (∑ j in range N, H (X j ω)) / (∑ j in range N, R (X j ω)))
        atTop (𝓝 ((∫ ω, H (X 0 ω)) / (∫ ω, R (X 0 ω)))) := by
  filter_upwards [eq_weighted_sampling_limits X R H hR hH hintR hintH
    hindep hident hmean] with ω hω
  refine ⟨?_, hω.2⟩
  filter_upwards [hω.1.eventually (eventually_gt_nhds hmean)] with N hN
  rcases div_pos_iff.mp hN with h | h
  · exact h.1
  · exact False.elim ((not_lt_of_ge (Nat.cast_nonneg N)) h.2)

/-- Compact probe spaces have a countable sequence of finite meshes. This is
the countability step needed before intersecting almost-sure limit events. -/
theorem exists_compact_metric_nets (T : Type*) [PseudoMetricSpace T] [CompactSpace T] :
    ∃ net : ℕ → Finset T, ∀ k : ℕ, ∀ t : T,
      ∃ u ∈ net k, dist t u < 1 / (k + 1 : ℝ) := by
  classical
  have hcover (k : ℕ) : ∃ s : Set T, s ⊆ Set.univ ∧ s.Finite ∧
      Set.univ ⊆ ⋃ t ∈ s, Metric.ball t (1 / (k + 1 : ℝ)) :=
    isCompact_univ.finite_cover_balls (one_div_pos.mpr (by positivity))
  choose s _hs hfinite hcover using hcover
  refine ⟨fun k => (hfinite k).toFinset, ?_⟩
  intro k t
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp (hcover k (Set.mem_univ t))
  obtain ⟨hus, htu⟩ := Set.mem_iUnion.mp hu
  exact ⟨u, (hfinite k).mem_toFinset.mpr hus, htu⟩

/-- Pointwise almost-sure convergence becomes uniform on a compact probe
space when both empirical and limiting functionals are uniformly Lipschitz.
The proof intersects only the countably many finite-mesh events. -/
theorem ae_uniform_of_compact_lipschitz
    {T : Type*} [PseudoMetricSpace T] [CompactSpace T]
    (F : ℕ → Ω → T → ℝ) (f : T → ℝ)
    (hf : LipschitzWith 1 f)
    (hLip : ∀ᵐ ω, ∀ᶠ N : ℕ in atTop, LipschitzWith 1 (F N ω))
    (hpoint : ∀ t, ∀ᵐ ω, Tendsto (fun N => F N ω t) atTop (𝓝 (f t))) :
    ∀ᵐ ω, TendstoUniformly (fun N => F N ω) f atTop := by
  classical
  obtain ⟨net, hnet⟩ := exists_compact_metric_nets T
  have hall : ∀ᵐ ω, ∀ k : ℕ, ∀ t : {t : T // t ∈ net k},
      Tendsto (fun N => F N ω t) atTop (𝓝 (f t)) :=
    ae_all_iff.mpr fun k => ae_all_iff.mpr fun t => hpoint t
  filter_upwards [hall, hLip] with ω hω hLipω
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith only [hε]
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hthird
  have hmesh : ∀ᶠ N : ℕ in atTop, ∀ u ∈ net k,
      dist (F N ω u) (f u) < ε / 3 := by
    apply (Filter.eventually_all_finset (net k)).mpr
    intro u hu
    exact (hω k ⟨u, hu⟩).eventually (Metric.ball_mem_nhds (f u) hthird)
  filter_upwards [hmesh, hLipω] with N hN hLipN
  intro t
  obtain ⟨u, hu, htu⟩ := hnet k t
  have hleft : dist (F N ω t) (F N ω u) ≤ dist t u := by
    simpa only [NNReal.coe_one, one_mul] using hLipN.dist_le_mul t u
  have hright : dist (f u) (f t) ≤ dist u t := by
    simpa only [NNReal.coe_one, one_mul] using hf.dist_le_mul u t
  have hmiddle := hN u hu
  have htriangle : dist (F N ω t) (f t) ≤
      dist (F N ω t) (F N ω u) + dist (F N ω u) (f u) + dist (f u) (f t) :=
    le_trans (dist_triangle _ (f u) _) (add_le_add_right (dist_triangle _ (F N ω u) _) _)
  rw [dist_comm u t] at hright
  rw [dist_comm]
  linarith only [htriangle, hleft, hright, hmiddle, htu, hk]

set_option maxHeartbeats 800000 in
/-- Uniform self-normalized strong law for a compact family of weighted
probes. For radial data, take `R(x)=‖x‖²` and `H(t,x)=R(x)φ_t(x/‖x‖)`;
the probe metric is the uniform distance between the normalized functions.
All integrability and positive-moment assumptions are explicit. -/
theorem weighted_uniform_strong_law
    {T : Type*} [PseudoMetricSpace T] [CompactSpace T]
    (X : ℕ → Ω → A) (R : A → ℝ) (H : T → A → ℝ)
    (hR : Measurable R) (hH : ∀ t, Measurable (H t))
    (hintR : Integrable (fun ω => R (X 0 ω)))
    (hintH : ∀ t, Integrable (fun ω => H t (X 0 ω)))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j))
    (hident : ∀ i, IdentDistrib (X i) (X 0))
    (hmean : 0 < ∫ ω, R (X 0 ω))
    (hprobe : ∀ a t u, |H t a - H u a| ≤ R a * dist t u) :
    ∀ᵐ ω, TendstoUniformly
      (fun N : ℕ => fun t : T =>
        (∑ j in range N, H t (X j ω)) / (∑ j in range N, R (X j ω)))
      (fun t => (∫ ω, H t (X 0 ω)) / (∫ ω, R (X 0 ω))) atTop := by
  let F : ℕ → Ω → T → ℝ := fun N ω t =>
    (∑ j in range N, H t (X j ω)) / (∑ j in range N, R (X j ω))
  let f : T → ℝ := fun t => (∫ ω, H t (X 0 ω)) / (∫ ω, R (X 0 ω))
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    have habs := norm_integral_le_integral_norm (μ := volume)
      (fun ω => H t (X 0 ω) - H u (X 0 ω))
    have hmono := integral_mono ((hintH t).sub (hintH u)).norm
      (hintR.mul_const (dist t u)) (fun ω => by
        simpa only [Real.norm_eq_abs] using hprobe (X 0 ω) t u)
    rw [integral_mul_right] at hmono
    have hbound := habs.trans hmono
    rw [integral_sub (hintH t) (hintH u), Real.norm_eq_abs] at hbound
    change |f t - f u| ≤ (1 : ℝ) * dist t u
    dsimp only [f]
    rw [one_mul, ← sub_div, abs_div, abs_of_pos hmean]
    apply (div_le_iff hmean).mpr
    simpa only [mul_comm] using hbound
  have hpositive := weighted_ratio_strong_law X R R hR hR hintR hintR hindep hident hmean
  have hLip : ∀ᵐ ω, ∀ᶠ N : ℕ in atTop, LipschitzWith 1 (F N ω) := by
    filter_upwards [hpositive] with ω hω
    filter_upwards [hω.1] with N hN
    apply LipschitzWith.of_dist_le_mul
    intro t u
    have hbound : |(∑ j in range N, H t (X j ω)) - (∑ j in range N, H u (X j ω))| ≤
        (∑ j in range N, R (X j ω)) * dist t u := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => hprobe (X j ω) t u)
    change |F N ω t - F N ω u| ≤ (1 : ℝ) * dist t u
    dsimp only [F]
    rw [one_mul, ← sub_div, abs_div, abs_of_pos hN]
    apply (div_le_iff hN).mpr
    simpa only [mul_comm] using hbound
  apply ae_uniform_of_compact_lipschitz F f hf hLip
  intro t
  filter_upwards [weighted_ratio_strong_law X R (H t) hR (hH t)
    hintR (hintH t) hindep hident hmean] with ω hω
  exact hω.2

/-- Uniform weighted angular law over the entire anchored unit-Lipschitz
class. Only the first moment of the weight is required. Taking the weight to
be squared radius is precisely the finite-second-moment assumption.

The limit here is stated honestly as the weighted angular expectation.
Identifying it with uniform sphere average is a separate rotation-invariance
argument, not an unproved hypothesis hidden in this theorem. -/
theorem weighted_angular_lipschitz_strong_law
    {S : Type*} [PseudoMetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (e : S) {B : ℝ} (hB : ∀ u : S, dist u e ≤ B)
    (X : ℕ → Ω → A) (hX : Measurable (X 0))
    (R : A → ℝ) (unit : A → S)
    (hR : Measurable R) (hunit : Measurable unit) (hRnonneg : ∀ a, 0 ≤ R a)
    (hintR : Integrable (fun ω => R (X 0 ω)))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j))
    (hident : ∀ i, IdentDistrib (X i) (X 0))
    (hmean : 0 < ∫ ω, R (X 0 ω)) :
    ∀ᵐ ω, TendstoUniformly
      (fun N : ℕ => fun f : anchoredLipschitzProbes S e =>
        (∑ j in range N, R (X j ω) * f.val (unit (X j ω))) /
          (∑ j in range N, R (X j ω)))
      (fun f : anchoredLipschitzProbes S e =>
        (∫ ω, R (X 0 ω) * f.val (unit (X 0 ω))) / (∫ ω, R (X 0 ω))) atTop := by
  let T := anchoredLipschitzProbes S e
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp
    (anchoredLipschitzProbes_isCompact e hB)
  let H : T → A → ℝ := fun f a => R a * f.val (unit a)
  have hH : ∀ f, Measurable (H f) := fun f =>
    hR.mul (f.val.continuous.measurable.comp hunit)
  have hbound (f : T) (u : S) : |f.val u| ≤ B := by
    have h := f.property.1.dist_le_mul u e
    rw [f.property.2, dist_zero_right, Real.norm_eq_abs, NNReal.coe_one, one_mul] at h
    exact h.trans (hB u)
  have hintH : ∀ f, Integrable (fun ω => H f (X 0 ω)) := by
    intro f
    apply (hintR.mul_const B).mono' ((hH f).comp hX).aestronglyMeasurable
    apply Filter.eventually_of_forall
    intro ω
    change ‖R (X 0 ω) * f.val (unit (X 0 ω))‖ ≤ R (X 0 ω) * B
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hRnonneg _)]
    exact mul_le_mul_of_nonneg_left (hbound f _) (hRnonneg _)
  have hprobe : ∀ a (f g : T), |H f a - H g a| ≤ R a * dist f g := by
    intro a f g
    have hsup := BoundedContinuousFunction.dist_coe_le_dist
      (f := f.val) (g := g.val) (unit a)
    change |f.val (unit a) - g.val (unit a)| ≤ dist f g at hsup
    dsimp only [H]
    rw [← mul_sub, abs_mul, abs_of_nonneg (hRnonneg a)]
    exact mul_le_mul_of_nonneg_left hsup (hRnonneg a)
  exact weighted_uniform_strong_law X R H hR hH hintR hintH hindep hident hmean hprobe

end PaperLeanFormalization.Empirical.RadialData

end


noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Topology BigOperators

namespace PaperLeanFormalization.Empirical.RadialData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A measurable sphere-valued radial map. The fallback is used only at zero. -/
def sphereDirection (e : sphere (0 : E) 1) (x : E) : sphere (0 : E) 1 :=
  ⟨unitDirection e.val x, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_unitDirection e.val (mem_sphere_zero_iff_norm.mp e.property) x⟩

theorem measurable_sphereDirection (e : sphere (0 : E) 1) :
    Measurable (sphereDirection e) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (measurableSet_singleton (0 : E)) measurable_const
    (measurable_norm.inv.smul measurable_id)

def sphereAction (Q : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨Q x.val, by simpa only [mem_sphere_zero_iff_norm, Q.norm_map] using x.property⟩

theorem continuous_sphereAction (Q : E ≃ₗᵢ[ℝ] E) : Continuous (sphereAction Q) :=
  (Q.continuous.comp continuous_subtype_val).subtype_mk _

theorem sphereDirection_equivariant (e : sphere (0 : E) 1) (Q : E ≃ₗᵢ[ℝ] E)
    {x : E} (hx : x ≠ 0) :
    sphereAction Q (sphereDirection e x) = sphereDirection e (Q x) := by
  apply Subtype.ext
  have hQx : Q x ≠ 0 := by
    intro h
    apply hx
    exact Q.injective (h.trans Q.map_zero.symm)
  simp only [sphereAction, sphereDirection, unitDirection, if_neg hx,
    if_neg hQx, Q.norm_map, Q.map_smul]

/-- The probability normalization is the actual finite positive second moment. -/
def radialDensity (M : ℝ) (x : E) : ℝ≥0∞ := ENNReal.ofReal (‖x‖ ^ 2 / M)

def radialWeightedMeasure (μ : Measure E) (M : ℝ) : Measure E :=
  μ.withDensity (radialDensity M)

def weightedAngularMeasure (μ : Measure E) (M : ℝ) (e : sphere (0 : E) 1) :
    Measure (sphere (0 : E) 1) :=
  (radialWeightedMeasure μ M).map (sphereDirection e)

theorem measurable_radialDensity (M : ℝ) : Measurable (radialDensity (E := E) M) :=
  (measurable_norm.pow_const 2 |>.div_const M).ennreal_ofReal

theorem radialWeightedMeasure_isProbability (μ : Measure E) {M : ℝ} (hM : 0 < M)
    (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ)
    (hmean : ∫ x, ‖x‖ ^ 2 ∂μ = M) :
    IsProbabilityMeasure (radialWeightedMeasure μ M) := by
  constructor
  rw [radialWeightedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2 / M) ∂μ) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.div_const M)
    (Filter.eventually_of_forall fun x => div_nonneg (sq_nonneg _) hM.le),
    integral_div, hmean, div_self (ne_of_gt hM), ENNReal.ofReal_one]

theorem weightedAngularMeasure_isProbability (μ : Measure E) {M : ℝ} (hM : 0 < M)
    (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ)
    (hmean : ∫ x, ‖x‖ ^ 2 ∂μ = M) (e : sphere (0 : E) 1) :
    IsProbabilityMeasure (weightedAngularMeasure μ M e) := by
  letI := radialWeightedMeasure_isProbability μ hM hint hmean
  constructor
  change Measure.map (sphereDirection e) (radialWeightedMeasure μ M) Set.univ = 1
  rw [Measure.map_apply (measurable_sphereDirection e) MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

theorem radialWeightedMeasure_ae_ne_zero (μ : Measure E) (M : ℝ) :
    ∀ᵐ x ∂radialWeightedMeasure μ M, x ≠ 0 := by
  rw [radialWeightedMeasure, ae_withDensity_iff (measurable_radialDensity M)]
  apply Filter.eventually_of_forall
  intro x hd hx
  subst x
  exact hd (by simp only [radialDensity, norm_zero, zero_pow (by decide : 0 < (2 : ℕ)),
    zero_div, ENNReal.ofReal_zero])

/-- Radial reweighting preserves every orthogonal symmetry of the input law. -/
theorem radialWeightedMeasure_preserving (μ : Measure E) (M : ℝ)
    (Q : E ≃ₗᵢ[ℝ] E) (hQ : MeasurePreserving Q μ μ) :
    MeasurePreserving Q (radialWeightedMeasure μ M) (radialWeightedMeasure μ M) := by
  refine ⟨hQ.measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hQ.measurable hs, radialWeightedMeasure,
    withDensity_apply _ (hQ.measurable hs), withDensity_apply _ hs]
  simpa only [radialDensity, Q.norm_map] using
    hQ.set_lintegral_comp_preimage hs (measurable_radialDensity M)

/-- Zero data carry zero radial mass, so arbitrary zero fallback does not
spoil orthogonal invariance of the weighted angular probability law. -/
theorem weightedAngularMeasure_preserving (μ : Measure E) (M : ℝ)
    (e : sphere (0 : E) 1) (Q : E ≃ₗᵢ[ℝ] E) (hQ : MeasurePreserving Q μ μ) :
    MeasurePreserving (sphereAction Q) (weightedAngularMeasure μ M e)
      (weightedAngularMeasure μ M e) := by
  have hSm := (continuous_sphereAction Q).measurable
  have hDm := measurable_sphereDirection e
  have hW := radialWeightedMeasure_preserving μ M Q hQ
  refine ⟨hSm, ?_⟩
  change Measure.map (sphereAction Q)
    (Measure.map (sphereDirection e) (radialWeightedMeasure μ M)) = _
  rw [Measure.map_map hSm hDm]
  calc
    Measure.map (sphereAction Q ∘ sphereDirection e) (radialWeightedMeasure μ M) =
        Measure.map (sphereDirection e ∘ Q) (radialWeightedMeasure μ M) := by
      apply Measure.map_congr
      filter_upwards [radialWeightedMeasure_ae_ne_zero μ M] with x hx
      exact sphereDirection_equivariant e Q hx
    _ = Measure.map (sphereDirection e) (Measure.map Q (radialWeightedMeasure μ M)) :=
      (Measure.map_map hDm hQ.measurable).symm
    _ = weightedAngularMeasure μ M e := by rw [hW.map_eq]; rfl

/-- Literal weighted-expectation formula for continuous spherical probes. -/
theorem integral_weightedAngularMeasure (μ : Measure E) {M : ℝ} (hM : 0 < M)
    (e : sphere (0 : E) 1) (f : sphere (0 : E) 1 → ℝ) (hf : Continuous f) :
    (∫ u, f u ∂weightedAngularMeasure μ M e) =
      (∫ x, ‖x‖ ^ 2 * f (sphereDirection e x) ∂μ) / M := by
  rw [weightedAngularMeasure,
    integral_map (measurable_sphereDirection e).aemeasurable hf.aestronglyMeasurable]
  change (∫ x, f (sphereDirection e x) ∂μ.withDensity
    (fun x => ((Real.toNNReal (‖x‖ ^ 2 / M) : NNReal) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_norm.pow_const 2).div_const M).real_toNNReal]
  have heq (x : E) : (Real.toNNReal (‖x‖ ^ 2 / M)) • f (sphereDirection e x) =
      (‖x‖ ^ 2 * f (sphereDirection e x)) / M := by
    rw [NNReal.smul_def, Real.toNNReal_of_nonneg (div_nonneg (sq_nonneg _) hM.le)]
    change (‖x‖ ^ 2 / M) * f (sphereDirection e x) = _
    ring
  simp only [heq, integral_div]

/-- Concrete radial normalization of Euclidean samples converges uniformly
over the full anchored unit-Lipschitz class to its weighted angular law.
The finite positive second moment is explicit; no fourth moment is required. -/
theorem radial_angular_uniform_strong_law [ProperSpace E]
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → E) (hX : Measurable (X 0)) (μ : Measure E)
    (hlaw : Measure.map (X 0) volume = μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
    {M : ℝ} (hM : 0 < M) (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ)
    (hmean : ∫ x, ‖x‖ ^ 2 ∂μ = M) (e : sphere (0 : E) 1) :
    ∀ᵐ ω, TendstoUniformly
      (fun N : ℕ => fun f : anchoredLipschitzProbes (sphere (0 : E) 1) e =>
        (∑ j in Finset.range N, ‖X j ω‖ ^ 2 * f.val (sphereDirection e (X j ω))) /
          (∑ j in Finset.range N, ‖X j ω‖ ^ 2))
      (fun f : anchoredLipschitzProbes (sphere (0 : E) 1) e =>
        ∫ u, f.val u ∂weightedAngularMeasure μ M e) Filter.atTop := by
  letI : CompactSpace (sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  have hB (u : sphere (0 : E) 1) : dist u e ≤ (2 : ℝ) := by
    change dist (u : E) (e : E) ≤ 2
    calc
      dist (u : E) (e : E) ≤ dist (u : E) 0 + dist 0 (e : E) := dist_triangle _ _ _
      _ = 2 := by
        rw [dist_zero_right, dist_zero_left,
          mem_sphere_zero_iff_norm.mp u.property, mem_sphere_zero_iff_norm.mp e.property]
        norm_num
  have hintX : Integrable (fun ω => ‖X 0 ω‖ ^ 2) := by
    have h := hint
    rw [← hlaw] at h
    exact h.comp_measurable hX
  have hmeanX : (∫ ω, ‖X 0 ω‖ ^ 2) = M := by
    rw [← integral_map hX.aemeasurable (continuous_norm.pow 2).aestronglyMeasurable,
      hlaw, hmean]
  have hlimit (f : anchoredLipschitzProbes (sphere (0 : E) 1) e) :
      (∫ ω, ‖X 0 ω‖ ^ 2 * f.val (sphereDirection e (X 0 ω))) /
        (∫ ω, ‖X 0 ω‖ ^ 2) =
        ∫ u, f.val u ∂weightedAngularMeasure μ M e := by
    rw [hmeanX, integral_weightedAngularMeasure μ hM e f.val f.val.continuous]
    congr 1
    have hchange := integral_map (μ := (volume : Measure Ω)) hX.aemeasurable
      ((measurable_norm.pow_const 2).mul
        (f.val.continuous.measurable.comp (measurable_sphereDirection e))).aestronglyMeasurable
    simpa only [hlaw, Function.comp_apply] using hchange.symm
  have h := weighted_angular_lipschitz_strong_law e hB X hX
    (fun x : E => ‖x‖ ^ 2) (sphereDirection e) (measurable_norm.pow_const 2)
    (measurable_sphereDirection e) (fun _ => sq_nonneg _)
    hintX hindep hident (hmeanX.symm ▸ hM)
  simpa only [hlimit] using h

end PaperLeanFormalization.Empirical.RadialData

end


noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal

namespace PaperLeanFormalization.Empirical.RadialData.InvariantSphere

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Continuous cap kernel: unlike sharp caps, it has no boundary-measure issue. -/
def cap (r : ℝ) (x y : S) : ℝ := max 0 (r - dist x y)

theorem continuous_cap (r : ℝ) : Continuous (fun p : S × S => cap r p.1 p.2) :=
  continuous_const.max (continuous_const.sub (continuous_fst.dist continuous_snd))

theorem cap_symm (r : ℝ) (x y : S) : cap r x y = cap r y x := by
  simp only [cap, dist_comm]

theorem cap_nonneg (r : ℝ) (x y : S) : 0 ≤ cap r x y := le_max_left _ _

theorem integrable_continuous {μ : Measure S} [IsFiniteMeasure μ]
    {f : S → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

/-- Homogeneity is used only through measure-preserving metric isometries,
not through a topology or Haar measure on an isometry group. -/
theorem cap_integral_constant (μ : Measure S) [IsProbabilityMeasure μ]
    (htrans : ∀ x y : S, ∃ T : S ≃ᵢ S, T x = y ∧ MeasurePreserving T μ μ)
    (r : ℝ) (x y : S) :
    (∫ z, cap r x z ∂μ) = ∫ z, cap r y z ∂μ := by
  obtain ⟨T, hT, hμ⟩ := htrans x y
  rw [← hμ.integral_comp T.toHomeomorph.measurableEmbedding (cap r y)]
  apply integral_congr_ae
  apply Filter.eventually_of_forall
  intro z
  rw [← hT]
  simp only [cap, T.dist_eq]

theorem cap_integral_pos (μ : Measure S) [IsProbabilityMeasure μ]
    (htrans : ∀ x y : S, ∃ T : S ≃ᵢ S, T x = y ∧ MeasurePreserving T μ μ)
    (e : S) {r : ℝ} (hr : 0 < r) : 0 < ∫ z, cap r e z ∂μ := by
  have hn : 0 ≤ ∫ z, cap r e z ∂μ := integral_nonneg (cap_nonneg r e)
  by_contra hpos
  have hz : (∫ z, cap r e z ∂μ) = 0 := le_antisymm (le_of_not_gt hpos) hn
  have hae (x : S) : (fun z => cap r x z) =ᵐ[μ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg (cap_nonneg r x)
      (integrable_continuous ((continuous_cap r).comp (continuous_const.prod_mk continuous_id)))).mp
    exact (cap_integral_constant μ htrans r x e).trans hz
  obtain ⟨s, _, hs, hcover⟩ :=
    isCompact_univ.finite_cover_balls (s := (Set.univ : Set S)) hr
  have hall : ∀ᵐ z ∂μ, ∀ x ∈ hs.toFinset, cap r x z = 0 :=
    (Filter.eventually_all_finset hs.toFinset).mpr (fun x _ => hae x)
  obtain ⟨z, hz⟩ := hall.exists
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ z))
  obtain ⟨hxs, hzx⟩ := Set.mem_iUnion.mp hx
  have hzero := hz x (hs.mem_toFinset.mpr hxs)
  have hdist : dist x z < r := by simpa only [Metric.mem_ball, dist_comm] using hzx
  have hcap : 0 < cap r x z := lt_of_lt_of_le (sub_pos.mpr hdist) (le_max_right _ _)
  exact (ne_of_gt hcap) hzero

/-- Fubini identifies the common cap masses of two homogeneous probabilities. -/
theorem cap_integral_eq (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x y : S, ∃ T : S ≃ᵢ S, T x = y ∧ MeasurePreserving T μ μ)
    (hν : ∀ x y : S, ∃ T : S ≃ᵢ S, T x = y ∧ MeasurePreserving T ν ν)
    (e : S) (r : ℝ) :
    (∫ z, cap r e z ∂μ) = ∫ z, cap r e z ∂ν := by
  have hswap := integral_integral_swap
    (μ := μ) (ν := ν) (f := cap r) (integrable_continuous (continuous_cap r))
  have hx (x : S) := cap_integral_constant ν hν r x e
  have hy (y : S) : (∫ x, cap r x y ∂μ) = ∫ x, cap r e x ∂μ := by
    simp_rw [cap_symm r _ y]
    exact cap_integral_constant μ hμ r y e
  simp_rw [hx, hy, integral_const, measure_univ, ENNReal.one_toReal, one_smul] at hswap
  exact hswap.symm

theorem cap_lipschitz_error {f : S → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {r : ℝ} (_hr : 0 < r) (x y : S) :
    |cap r x y * (f x-f y)| ≤ ((L:ℝ)*r) * cap r x y := by
  by_cases hdist : dist x y < r
  · rw [abs_mul, abs_of_nonneg (cap_nonneg _ _ _)]
    have h := hf.dist_le_mul x y
    rw [Real.dist_eq] at h
    have he := mul_le_mul_of_nonneg_left
      (h.trans (mul_le_mul_of_nonneg_left hdist.le L.coe_nonneg)) (cap_nonneg r x y)
    simpa only [mul_comm] using he
  · have hc : cap r x y = 0 := max_eq_left (sub_nonpos.mpr (le_of_not_gt hdist))
    simp only [hc, zero_mul, abs_zero, mul_zero, le_refl]

/-- Cap averaging controls the difference of integrals by the cap radius. -/
theorem integral_lipschitz_difference_le
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x y : S, ∃ T : S ≃ᵢ S, T x = y ∧ MeasurePreserving T μ μ)
    (hν : ∀ x y : S, ∃ T : S ≃ᵢ S, T x = y ∧ MeasurePreserving T ν ν)
    (e : S) {f : S → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {r : ℝ} (hr : 0 < r) : |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)| ≤ (L:ℝ)*r := by
  let c := ∫ z, cap r e z ∂ν
  have hc : 0 < c := cap_integral_pos ν hν e hr
  have hn (x : S) : (∫ y, cap r x y ∂ν) = c := cap_integral_constant ν hν r x e
  have hm (y : S) : (∫ x, cap r x y ∂μ) = c := by
    simp_rw [cap_symm r _ y]
    exact (cap_integral_constant μ hμ r y e).trans (cap_integral_eq μ ν hμ hν e r)
  have hK : Integrable (fun p : S × S => cap r p.1 p.2) (μ.prod ν) :=
    integrable_continuous (continuous_cap r)
  have hleft : Integrable (fun p : S × S => cap r p.1 p.2 * f p.1) (μ.prod ν) :=
    integrable_continuous ((continuous_cap r).mul (hf.continuous.comp continuous_fst))
  have hright : Integrable (fun p : S × S => cap r p.1 p.2 * f p.2) (μ.prod ν) :=
    integrable_continuous ((continuous_cap r).mul (hf.continuous.comp continuous_snd))
  have hdiff : Integrable (fun p : S × S => cap r p.1 p.2 * (f p.1-f p.2)) (μ.prod ν) :=
    integrable_continuous ((continuous_cap r).mul
      ((hf.continuous.comp continuous_fst).sub (hf.continuous.comp continuous_snd)))
  have hmass : (∫ p : S × S, cap r p.1 p.2 ∂μ.prod ν) = c := by
    rw [integral_prod _ hK]
    simp_rw [hn, integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  have hI : (∫ p : S × S, cap r p.1 p.2 * (f p.1-f p.2) ∂μ.prod ν) =
      c * ((∫ x, f x ∂μ)-(∫ x, f x ∂ν)) := by
    simp_rw [mul_sub]
    rw [integral_sub hleft hright, integral_prod _ hleft, integral_prod_symm _ hright]
    simp_rw [integral_mul_right, hn, hm, integral_mul_left]
  have hbound := (norm_integral_le_integral_norm
    (μ := μ.prod ν) (fun p : S × S => cap r p.1 p.2 * (f p.1-f p.2))).trans
    (integral_mono hdiff.norm (hK.const_mul ((L:ℝ)*r))
      (fun p => by simpa only [Real.norm_eq_abs] using cap_lipschitz_error hf hr p.1 p.2))
  rw [hI, Real.norm_eq_abs, abs_mul, abs_of_pos hc, integral_mul_left, hmass] at hbound
  exact (mul_le_mul_left hc).mp (by simpa only [mul_comm] using hbound)

/-- Uniqueness on all Lipschitz probes, with no assumed uniform angular law.
The radii tend to zero only in this final elementary inequality. -/
theorem integral_eq_of_homogeneous_probability
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ x y : S, ∃ T : S ≃ᵢ S, T x = y ∧ MeasurePreserving T μ μ)
    (hν : ∀ x y : S, ∃ T : S ≃ᵢ S, T x = y ∧ MeasurePreserving T ν ν)
    (e : S) {f : S → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  apply eq_of_forall_dist_le
  intro ε hε
  have hr : 0 < ε / ((L:ℝ)+1) := div_pos hε (by positivity)
  have h := integral_lipschitz_difference_le μ ν hμ hν e hf hr
  rw [Real.dist_eq]
  apply h.trans
  rw [← mul_div_assoc]
  apply (div_le_iff (by positivity : 0 < (L:ℝ)+1)).mpr
  nlinarith only [hε]

end PaperLeanFormalization.Empirical.RadialData.InvariantSphere

end


noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal NNReal Pointwise

namespace PaperLeanFormalization.Empirical.RadialData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal coordinates show directly that every linear isometric equivalence preserves volume. -/
theorem orthogonal_volume_preserving (Q : E ≃ₗᵢ[ℝ] E) : MeasurePreserving Q := by
  let b := stdOrthonormalBasis ℝ E
  have h := (b.map Q).measurePreserving_repr_symm.comp b.measurePreserving_repr
  convert h using 1
  funext x
  change Q x = Q (b.repr.symm (b.repr x))
  rw [b.repr.symm_apply_apply]

def sphereActionIsometry (Q : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ᵢ sphere (0 : E) 1 where
  toFun := sphereAction Q
  invFun := sphereAction Q.symm
  left_inv x := Subtype.ext (Q.symm_apply_apply x)
  right_inv x := Subtype.ext (Q.apply_symm_apply x)
  isometry_toFun := fun x y => Q.isometry x.val y.val

theorem sphere_cone_preimage (Q : E ≃ₗᵢ[ℝ] E) (s : Set (sphere (0 : E) 1)) :
    Ioo (0:ℝ) 1 • (Subtype.val '' (sphereAction Q ⁻¹' s)) =
      Q ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, y, hr, hy, rfl⟩ := Set.mem_smul.mp hx
    obtain ⟨u, hu, rfl⟩ := hy
    apply Set.mem_smul.mpr
    exact ⟨r, Q u, hr, ⟨sphereAction Q u, hu, rfl⟩, (Q.map_smul r (u:E)).symm⟩
  · intro hx
    obtain ⟨r, y, hr, hy, hxy⟩ := Set.mem_smul.mp hx
    obtain ⟨u, hu, rfl⟩ := hy
    apply Set.mem_smul.mpr
    refine ⟨r, Q.symm u, hr, ?_, ?_⟩
    · refine ⟨sphereAction Q.symm u, ?_, rfl⟩
      change sphereAction Q (sphereAction Q.symm u) ∈ s
      have heq : sphereAction Q (sphereAction Q.symm u) = u :=
        Subtype.ext (Q.apply_symm_apply u)
      rwa [heq]
    · apply Q.injective
      simpa only [Q.map_smul, Q.apply_symm_apply] using hxy

/-- The cone definition of surface measure is invariant under each orthogonal map. -/
theorem toSphere_preserving (Q : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereAction Q) (volume : Measure E).toSphere
      (volume : Measure E).toSphere := by
  refine ⟨(continuous_sphereAction Q).measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (continuous_sphereAction Q).measurable hs,
    Measure.toSphere_apply' _ ((continuous_sphereAction Q).measurable hs),
    Measure.toSphere_apply' _ hs, sphere_cone_preimage]
  congr 1
  exact (orthogonal_volume_preserving Q).measure_preimage_emb Q.toHomeomorph.measurableEmbedding _

def normalizedSphereMeasure : Measure (sphere (0 : E) 1) :=
  (((volume : Measure E).toSphere) univ)⁻¹ • (volume : Measure E).toSphere

theorem toSphere_mass_ne_zero [Nontrivial E] : (volume : Measure E).toSphere univ ≠ 0 := by
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr FiniteDimensional.finrank_pos.ne')
    (Metric.measure_ball_pos volume (0:E) one_pos).ne'

theorem normalizedSphereMeasure_isProbability [Nontrivial E] :
    IsProbabilityMeasure (normalizedSphereMeasure (E := E)) := by
  constructor
  rw [normalizedSphereMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel toSphere_mass_ne_zero (measure_ne_top _ _)

theorem normalizedSphereMeasure_preserving (Q : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereAction Q) (normalizedSphereMeasure (E := E))
      (normalizedSphereMeasure (E := E)) := by
  refine ⟨(continuous_sphereAction Q).measurable, ?_⟩
  rw [normalizedSphereMeasure, Measure.map_smul, (toSphere_preserving Q).map_eq]

/-- Reflection supplies transitivity without constructing an orthogonal-group topology. -/
theorem sphere_homogeneous (μ : Measure (sphere (0 : E) 1))
    (hμ : ∀ Q : E ≃ₗᵢ[ℝ] E, MeasurePreserving (sphereAction Q) μ μ) :
    ∀ x y : sphere (0 : E) 1, ∃ T : sphere (0 : E) 1 ≃ᵢ sphere (0 : E) 1,
      T x = y ∧ MeasurePreserving T μ μ := by
  intro x y
  let Q := reflection (ℝ ∙ ((x:E)-(y:E)))ᗮ
  refine ⟨sphereActionIsometry Q, ?_, hμ Q⟩
  apply Subtype.ext
  exact reflection_sub ((mem_sphere_zero_iff_norm.mp x.property).trans
    (mem_sphere_zero_iff_norm.mp y.property).symm)

theorem integral_normalizedSphereMeasure (f : sphere (0 : E) 1 → ℝ) :
    (∫ u, f u ∂normalizedSphereMeasure (E := E)) =
      (∫ u, f u ∂(volume : Measure E).toSphere) /
        (((volume : Measure E).toSphere) univ).toReal := by
  rw [normalizedSphereMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  ring

/-- The weighted angular expectation for an arbitrary orthogonally invariant
law equals normalized surface average. Only the finite positive second moment
is required; angular uniformity is proved, not assumed. -/
theorem weighted_angular_expectation_eq_sphere_average [Nontrivial E]
    (μ : Measure E) {M : ℝ} (hM : 0 < M)
    (hint : Integrable (fun x : E => ‖x‖^2) μ)
    (hmean : (∫ x, ‖x‖^2 ∂μ) = M)
    (hrot : ∀ Q : E ≃ₗᵢ[ℝ] E, MeasurePreserving Q μ μ)
    (e : sphere (0 : E) 1) {f : sphere (0 : E) 1 → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    (∫ x, ‖x‖^2 * f (sphereDirection e x) ∂μ) / M =
      (∫ u, f u ∂(volume : Measure E).toSphere) /
        (((volume : Measure E).toSphere) univ).toReal := by
  letI := weightedAngularMeasure_isProbability μ hM hint hmean e
  letI := normalizedSphereMeasure_isProbability (E := E)
  rw [← integral_weightedAngularMeasure μ hM e f hf.continuous,
    ← integral_normalizedSphereMeasure f]
  exact InvariantSphere.integral_eq_of_homogeneous_probability
    (weightedAngularMeasure μ M e) normalizedSphereMeasure
    (sphere_homogeneous _ (fun Q => weightedAngularMeasure_preserving μ M e Q (hrot Q)))
    (sphere_homogeneous _ normalizedSphereMeasure_preserving) e hf

end PaperLeanFormalization.Empirical.RadialData

end


noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology BigOperators BoundedContinuousFunction

namespace PaperLeanFormalization.Empirical.RadialData

/-- An uncountable uniform inequality is measurable because continuity reduces
it to a countable dense set of probes. -/
theorem measurableSet_uniform_le {Ω T : Type*} [MeasurableSpace Ω]
    [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    (F : Ω → T → ℝ) (f : T → ℝ)
    (hFm : ∀ t, Measurable (fun ω => F ω t))
    (hFc : ∀ ω, Continuous (F ω)) (hfc : Continuous f) (ε : ℝ) :
    MeasurableSet {ω | ∀ t, dist (F ω t) (f t) ≤ ε} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense T
  letI := hDc.toEncodable
  have heq : {ω | ∀ t, dist (F ω t) (f t) ≤ ε} =
      {ω | ∀ t : D, dist (F ω t) (f t) ≤ ε} := by
    ext ω
    constructor
    · exact fun h t => h t
    · intro h t
      have hsub : D ⊆ {t | dist (F ω t) (f t) ≤ ε} := fun u hu => h ⟨u, hu⟩
      exact closure_minimal hsub (isClosed_le ((hFc ω).dist hfc) continuous_const)
        (hDd t)
  rw [heq]
  simpa only [setOf_forall] using MeasurableSet.iInter fun t : D =>
    measurableSet_le ((hFm t).dist measurable_const) measurable_const

/-- Almost-sure uniform convergence has a genuine measurable high-probability
tail event. One deterministic sample threshold works for every later sample
size and every probe, outside a set of probability less than `δ`. -/
theorem uniform_tail_high_probability {Ω T : Type*} [MeasurableSpace Ω]
    [TopologicalSpace T] [TopologicalSpace.SeparableSpace T]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : ℕ → Ω → T → ℝ) (f : T → ℝ)
    (hFm : ∀ N t, Measurable (fun ω => F N ω t))
    (hFc : ∀ N ω, Continuous (F N ω)) (hfc : Continuous f)
    (hconv : ∀ᵐ ω ∂μ, TendstoUniformly (fun N => F N ω) f atTop)
    (V : ℕ → Set Ω) (hVm : ∀ N, MeasurableSet (V N))
    (hV : ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, ω ∈ V N)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∃ G : Set Ω, MeasurableSet G ∧ μ Gᶜ < ENNReal.ofReal δ ∧
      ∀ ω ∈ G, ∀ N, N₀ ≤ N → ω ∈ V N ∧ ∀ t, dist (F N ω t) (f t) ≤ ε := by
  classical
  let good (N : ℕ) : Set Ω := V N ∩ {ω | ∀ t, dist (F N ω t) (f t) ≤ ε}
  let bad (n : ℕ) : Set Ω := ⋃ N ≥ n, (good N)ᶜ
  have hg (N : ℕ) : MeasurableSet (good N) :=
    (hVm N).inter (measurableSet_uniform_le (F N) f (hFm N) (hFc N) hfc ε)
  have hb (n : ℕ) : MeasurableSet (bad n) :=
    MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun _ => (hg N).compl
  have hanti : Antitone bad := by
    intro a b hab ω hω
    obtain ⟨N, hN⟩ := mem_iUnion.mp hω
    obtain ⟨hNb, hbad⟩ := mem_iUnion.mp hN
    exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨le_trans hab hNb, hbad⟩⟩
  have hzero : μ (⋂ n, bad n) = 0 := by
    apply measure_mono_null _ (ae_iff.mp (hconv.and hV))
    intro ω hω hωconv
    have hev : ∀ᶠ N : ℕ in atTop, ω ∈ V N ∧ ∀ t, dist (F N ω t) (f t) < ε := by
      filter_upwards [hωconv.2, (Metric.tendstoUniformly_iff.mp hωconv.1) ε hε]
        with N hvalid hN
      exact ⟨hvalid, fun t => by simpa only [dist_comm] using hN t⟩
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
    obtain ⟨N, hN⟩ := mem_iUnion.mp (mem_iInter.mp hω N₀)
    obtain ⟨hle, hbad⟩ := mem_iUnion.mp hN
    exact hbad ⟨(hN₀ N hle).1, fun t => ((hN₀ N hle).2 t).le⟩
  have hlim : Tendsto (fun n => μ (bad n)) atTop (𝓝 0) := by
    simpa only [hzero, Function.comp_apply] using
      tendsto_measure_iInter hb hanti ⟨0, measure_ne_top μ (bad 0)⟩
  obtain ⟨N₀, hN₀⟩ := (hlim.eventually
    (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hδ))).exists
  refine ⟨N₀, (bad N₀)ᶜ, (hb N₀).compl, ?_, ?_⟩
  · simpa only [compl_compl] using hN₀
  · intro ω hω N hN
    by_contra h
    apply hω
    exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨hN, h⟩⟩

theorem lipschitz_integral_probe {S : Type*} [TopologicalSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] :
    LipschitzWith 1 (fun f : S →ᵇ ℝ => ∫ u, f u ∂ν) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
    ← integral_sub (f.integrable ν) (g.integrable ν)]
  exact (f - g).norm_integral_le_norm ν

/-- Anchoring and division by the Lipschitz constant recover the full
angular-average inequality. Constants cancel because both averages have
total mass one. No boundedness assumption on the constants is needed. -/
theorem finite_average_scaled_lipschitz_bound {S ι : Type*} [PseudoMetricSpace S]
    [CompactSpace S] [MeasurableSpace S] [BorelSpace S] [Fintype ι]
    (ν : Measure S) [IsProbabilityMeasure ν] (e : S)
    (weight : ι → ℝ) (node : ι → S) (hsum : ∑ j, weight j = 1) {ε : ℝ}
    (hprobe : ∀ g : anchoredLipschitzProbes S e,
      |(∑ j, weight j * g.val (node j)) - ∫ u, g.val u ∂ν| ≤ ε)
    (f : S → ℝ) {L : NNReal} (hf : LipschitzWith L f) :
    |(∑ j, weight j * f (node j)) - ∫ u, f u ∂ν| ≤ (L : ℝ) * ε := by
  classical
  by_cases hL : L = 0
  · have hconst (u : S) : f u = f e := by
      have h := hf.dist_le_mul u e
      rw [hL, NNReal.coe_zero, zero_mul] at h
      exact dist_le_zero.mp h
    simp only [hconst, ← Finset.sum_mul, hsum, one_mul, integral_const, measure_univ,
      ENNReal.one_toReal, one_smul, sub_self, abs_zero, hL, NNReal.coe_zero, zero_mul, le_refl]
  · have hLpos : (0 : ℝ) < L := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hL)
    let g : S →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun u => (f u - f e) / (L : ℝ), (hf.continuous.sub continuous_const).div_const _⟩
    have hgLip : LipschitzWith 1 g := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      change dist ((f u - f e) / (L : ℝ)) ((f v - f e) / (L : ℝ)) ≤
        (1 : NNReal) * dist u v
      rw [NNReal.coe_one, one_mul, Real.dist_eq, ← sub_div,
        sub_sub_sub_cancel_right, abs_div, abs_of_pos hLpos]
      apply (div_le_iff hLpos).mpr
      simpa only [Real.dist_eq, mul_comm] using hf.dist_le_mul u v
    have hgAnchor : g e = 0 := by
      change (f e - f e) / (L : ℝ) = 0
      rw [sub_self, zero_div]
    have htest := hprobe ⟨g, hgLip, hgAnchor⟩
    have hsample : (∑ j, weight j * g (node j)) =
        ((∑ j, weight j * f (node j)) - f e) / (L : ℝ) := by
      change (∑ j, weight j * ((f (node j) - f e) / (L : ℝ))) = _
      simp_rw [← mul_div_assoc, mul_sub]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    have hfi : Integrable f ν :=
      (BoundedContinuousFunction.mkOfCompact ⟨f, hf.continuous⟩).integrable ν
    have hintg : (∫ u, g u ∂ν) = ((∫ u, f u ∂ν) - f e) / (L : ℝ) := by
      change (∫ u, (f u - f e) / (L : ℝ) ∂ν) = _
      rw [integral_div, integral_sub hfi (integrable_const _)]
      simp only [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
    change |(∑ j, weight j * g (node j)) - ∫ u, g u ∂ν| ≤ ε at htest
    rw [hsample, hintg, ← sub_div, sub_sub_sub_cancel_right,
      abs_div, abs_of_pos hLpos] at htest
    exact (div_le_iff hLpos).mp htest |>.trans_eq (mul_comm _ _)

/-- The finite-positive-second-moment assumption gives a common measurable
high-probability event on which every later radial average is normalized and
uniformly accurate. -/
theorem radial_angular_high_probability
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [ProperSpace E]
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) (μ : Measure E)
    (hlaw : Measure.map (X 0) volume = μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
    {M : ℝ} (hM : 0 < M) (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ)
    (hmean : ∫ x, ‖x‖ ^ 2 ∂μ = M) (e : sphere (0 : E) 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∃ G : Set Ω, MeasurableSet G ∧ volume Gᶜ < ENNReal.ofReal δ ∧
      ∀ ω ∈ G, ∀ N, N₀ ≤ N →
        0 < (∑ j in Finset.range N, ‖X j ω‖ ^ 2) ∧
        ∀ f : anchoredLipschitzProbes (sphere (0 : E) 1) e,
          |(∑ j in Finset.range N, ‖X j ω‖ ^ 2 * f.val (sphereDirection e (X j ω))) /
            (∑ j in Finset.range N, ‖X j ω‖ ^ 2) -
            (∫ u, f.val u ∂weightedAngularMeasure μ M e)| ≤ ε := by
  letI : CompactSpace (sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  have hB (u : sphere (0 : E) 1) : dist u e ≤ (2 : ℝ) := by
    change dist (u : E) (e : E) ≤ 2
    calc
      dist (u : E) (e : E) ≤ dist (u : E) 0 + dist 0 (e : E) := dist_triangle _ _ _
      _ = 2 := by
        rw [dist_zero_right, dist_zero_left,
          mem_sphere_zero_iff_norm.mp u.property, mem_sphere_zero_iff_norm.mp e.property]
        norm_num
  let T := anchoredLipschitzProbes (sphere (0 : E) 1) e
  letI : CompactSpace T := isCompact_iff_compactSpace.mp
    (anchoredLipschitzProbes_isCompact e hB)
  letI := weightedAngularMeasure_isProbability μ hM hint hmean e
  let W (N : ℕ) (ω : Ω) : ℝ := ∑ j in Finset.range N, ‖X j ω‖ ^ 2
  let F (N : ℕ) (ω : Ω) (f : T) : ℝ :=
    (∑ j in Finset.range N, ‖X j ω‖ ^ 2 * f.val (sphereDirection e (X j ω))) / W N ω
  let lim (f : T) : ℝ := ∫ u, f.val u ∂weightedAngularMeasure μ M e
  have hWm (N : ℕ) : Measurable (W N) :=
    Finset.measurable_sum _ fun j _ => (hX j).norm.pow_const 2
  have hFm (N : ℕ) (f : T) : Measurable (fun ω => F N ω f) :=
    (Finset.measurable_sum _ fun j _ => ((hX j).norm.pow_const 2).mul
      (f.val.continuous.measurable.comp ((measurable_sphereDirection e).comp (hX j)))).div (hWm N)
  have hFc (N : ℕ) (ω : Ω) : Continuous (F N ω) :=
    (continuous_finset_sum _ fun j _ => continuous_const.mul
      (BoundedContinuousFunction.continuous_eval_const.comp continuous_subtype_val)).div_const _
  have hlimc : Continuous lim :=
    (lipschitz_integral_probe (weightedAngularMeasure μ M e)).continuous.comp continuous_subtype_val
  have hconv := radial_angular_uniform_strong_law X (hX 0) μ hlaw hindep hident hM hint hmean e
  have hintX : Integrable (fun ω => ‖X 0 ω‖ ^ 2) := by
    have h := hint
    rw [← hlaw] at h
    exact h.comp_measurable (hX 0)
  have hmeanX : (∫ ω, ‖X 0 ω‖ ^ 2) = M := by
    rw [← integral_map (hX 0).aemeasurable (continuous_norm.pow 2).aestronglyMeasurable,
      hlaw, hmean]
  have hvalid : ∀ᵐ ω, ∀ᶠ N : ℕ in atTop, 0 < W N ω := by
    filter_upwards [weighted_ratio_strong_law X (fun x : E => ‖x‖ ^ 2)
      (fun x : E => ‖x‖ ^ 2) (measurable_norm.pow_const 2) (measurable_norm.pow_const 2)
      hintX hintX hindep hident (hmeanX.symm ▸ hM)] with ω hω
    exact hω.1
  have hresult := uniform_tail_high_probability volume F lim hFm hFc hlimc hconv
    (fun N => {ω | 0 < W N ω})
    (fun N => measurableSet_lt measurable_const (hWm N)) hvalid hε hδ
  simpa only [Real.dist_eq] using hresult

/-- The manuscript's stochastic spherical conclusion, with the missing law
and moment assumptions made explicit. The law is invariant under all
orthogonal maps; the limiting spherical measure is proved to be uniform. -/
theorem radial_spherical_uniform_strong_law
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → E) (hX : Measurable (X 0)) (μ : Measure E)
    (hlaw : Measure.map (X 0) volume = μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
    {M : ℝ} (hM : 0 < M) (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ)
    (hmean : ∫ x, ‖x‖ ^ 2 ∂μ = M)
    (hrot : ∀ Q : E ≃ₗᵢ[ℝ] E, MeasurePreserving Q μ μ) (e : sphere (0 : E) 1) :
    ∀ᵐ ω, TendstoUniformly
      (fun N : ℕ => fun f : anchoredLipschitzProbes (sphere (0 : E) 1) e =>
        (∑ j in Finset.range N, ‖X j ω‖ ^ 2 * f.val (sphereDirection e (X j ω))) /
          (∑ j in Finset.range N, ‖X j ω‖ ^ 2))
      (fun f : anchoredLipschitzProbes (sphere (0 : E) 1) e =>
        (∫ u, f.val u ∂(volume : Measure E).toSphere) /
          (((volume : Measure E).toSphere) univ).toReal) atTop := by
  have heq (f : anchoredLipschitzProbes (sphere (0 : E) 1) e) :
      (∫ u, f.val u ∂weightedAngularMeasure μ M e) =
      (∫ u, f.val u ∂(volume : Measure E).toSphere) /
        (((volume : Measure E).toSphere) univ).toReal := by
    rw [integral_weightedAngularMeasure μ hM e f.val f.val.continuous]
    exact weighted_angular_expectation_eq_sphere_average μ hM hint hmean hrot e f.property.1
  simpa only [heq] using
    radial_angular_uniform_strong_law X hX μ hlaw hindep hident hM hint hmean e

theorem radial_spherical_high_probability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) (μ : Measure E)
    (hlaw : Measure.map (X 0) volume = μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
    {M : ℝ} (hM : 0 < M) (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ)
    (hmean : ∫ x, ‖x‖ ^ 2 ∂μ = M)
    (hrot : ∀ Q : E ≃ₗᵢ[ℝ] E, MeasurePreserving Q μ μ) (e : sphere (0 : E) 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∃ G : Set Ω, MeasurableSet G ∧ volume Gᶜ < ENNReal.ofReal δ ∧
      ∀ ω ∈ G, ∀ N, N₀ ≤ N →
        0 < (∑ j in Finset.range N, ‖X j ω‖ ^ 2) ∧
        ∀ f : anchoredLipschitzProbes (sphere (0 : E) 1) e,
          |(∑ j in Finset.range N, ‖X j ω‖ ^ 2 * f.val (sphereDirection e (X j ω))) /
            (∑ j in Finset.range N, ‖X j ω‖ ^ 2) -
            (∫ u, f.val u ∂(volume : Measure E).toSphere) /
              (((volume : Measure E).toSphere) univ).toReal| ≤ ε := by
  have heq (f : anchoredLipschitzProbes (sphere (0 : E) 1) e) :
      (∫ u, f.val u ∂weightedAngularMeasure μ M e) =
      (∫ u, f.val u ∂(volume : Measure E).toSphere) /
        (((volume : Measure E).toSphere) univ).toReal := by
    rw [integral_weightedAngularMeasure μ hM e f.val f.val.continuous]
    exact weighted_angular_expectation_eq_sphere_average μ hM hint hmean hrot e f.property.1
  simpa only [heq] using
    radial_angular_high_probability X hX μ hlaw hindep hident hM hint hmean e hε hδ

/-- Literal closed-unit-ball angular-average bound for normalized radial data.
This is the form consumed by the fixed-radius empirical theorem, rather than
merely a statement about a selected family of probes. -/
theorem radial_angular_accuracy_high_probability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) (μ : Measure E)
    (hlaw : Measure.map (X 0) volume = μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
    {M : ℝ} (hM : 0 < M) (hint : Integrable (fun x : E => ‖x‖ ^ 2) μ)
    (hmean : ∫ x, ‖x‖ ^ 2 ∂μ = M)
    (hrot : ∀ Q : E ≃ₗᵢ[ℝ] E, MeasurePreserving Q μ μ) (e : sphere (0 : E) 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∃ G : Set Ω, MeasurableSet G ∧ volume Gᶜ < ENNReal.ofReal δ ∧
      ∀ ω ∈ G, ∀ N, N₀ ≤ N →
        0 < (∑ j in Finset.range N, ‖X j ω‖ ^ 2) ∧
        ∀ (f : E → ℝ) (L : ℝ),
          (∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → |f x - f y| ≤ L * ‖x - y‖) →
          |(∑ j : Fin N, (‖X j ω‖ ^ 2 / (∑ k in Finset.range N, ‖X k ω‖ ^ 2)) *
              f (sphereDirection e (X j ω))) -
            (∫ u : sphere (0 : E) 1, f u ∂(volume : Measure E).toSphere) /
              (((volume : Measure E).toSphere) univ).toReal| ≤ L * ε := by
  letI : CompactSpace (sphere (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  letI := normalizedSphereMeasure_isProbability (E := E)
  obtain ⟨N₀, G, hGm, hGprob, hG⟩ :=
    radial_spherical_high_probability X hX μ hlaw hindep hident hM hint hmean hrot e hε hδ
  refine ⟨N₀, G, hGm, hGprob, ?_⟩
  intro ω hω N hN
  obtain ⟨hW, hprobe⟩ := hG ω hω N hN
  refine ⟨hW, ?_⟩
  intro f L hf
  have he : ‖(e : E)‖ = 1 := mem_sphere_zero_iff_norm.mp e.property
  have hL : 0 ≤ L := by
    have h := hf e 0 he.le (by simp only [norm_zero, zero_le_one])
    rw [sub_zero, he, mul_one] at h
    exact (abs_nonneg _).trans h
  have hfs : LipschitzWith (Real.toNNReal L)
      (fun u : sphere (0 : E) 1 => f u) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Real.coe_toNNReal L hL, Real.dist_eq]
    change |f (u : E) - f (v : E)| ≤ L * dist (u : E) (v : E)
    rw [dist_eq_norm]
    exact hf u v (mem_sphere_zero_iff_norm.mp u.property).le
      (mem_sphere_zero_iff_norm.mp v.property).le
  let weight (j : Fin N) := ‖X j ω‖ ^ 2 / (∑ k in Finset.range N, ‖X k ω‖ ^ 2)
  let node (j : Fin N) := sphereDirection e (X j ω)
  have hsum : ∑ j, weight j = 1 := by
    dsimp only [weight]
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun j => ‖X j ω‖ ^ 2) N,
      div_self (ne_of_gt hW)]
  have hanchor (g : anchoredLipschitzProbes (sphere (0 : E) 1) e) :
      |(∑ j, weight j * g.val (node j)) -
        ∫ u, g.val u ∂normalizedSphereMeasure (E := E)| ≤ ε := by
    dsimp only [weight, node]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range
      (fun j => ‖X j ω‖ ^ 2 * g.val (sphereDirection e (X j ω))) N,
      integral_normalizedSphereMeasure]
    exact hprobe g
  have h := finite_average_scaled_lipschitz_bound
    (normalizedSphereMeasure (E := E)) e weight node hsum hanchor _ hfs
  rw [integral_normalizedSphereMeasure, Real.coe_toNNReal L hL] at h
  exact h

end PaperLeanFormalization.Empirical.RadialData

end

/-! ## Accuracy and exact fitting for random finite datasets -/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped BigOperators Topology

namespace PaperLeanFormalization.Empirical

open Definitions
open RadialData

/-- The degree-two radial identity is valid even at a zero input. -/
theorem homogeneous_degree_two_radial_value {d : ℕ}
    (H : Vec d → ℝ) (hH : IsPosHomogeneousDegTwo H)
    (e : sphere (0 : Vec d) 1) (x : Vec d) :
    H x = ‖x‖ ^ 2 * H (sphereDirection e x) := by
  calc
    H x = H (‖x‖ • unitDirection (e : Vec d) x) :=
      congrArg H (radial_reconstruction (e : Vec d) x).symm
    _ = ‖x‖ ^ 2 * H (sphereDirection e x) :=
      hH ‖x‖ (norm_nonneg x) _

/-- The homogeneous-test display, with the normalized probe H/L explicit:
the raw Gaussian discrepancy equals its weighted angular discrepancy times
d R₂ L, and an angular error at most δ gives the stated raw-data bound. -/
theorem eq_homogeneous_discrepancy_chain {d N : ℕ} (hd : 2 ≤ d)
    (x : Fin N → Vec d) (e : sphere (0 : Vec d) 1)
    (H : Vec d → ℝ) (hHhom : IsPosHomogeneousDegTwo H) {L δ : ℝ}
    (hL : 0 < L) (hW : 0 < ∑ j, ‖x j‖ ^ 2)
    (hbound : |(∑ j, ‖x j‖ ^ 2 * (H (sphereDirection e (x j)) / L)) /
        (∑ j, ‖x j‖ ^ 2) - uniformSphereFunctional d (fun z => H z / L)| ≤ δ) :
    |(d : ℝ) * ((∑ j, H (x j)) / (N : ℝ)) -
        DataSecondMoment x * gaussianFunctional d H| =
      (d : ℝ) * DataSecondMoment x * L *
        |(∑ j, ‖x j‖ ^ 2 * (H (sphereDirection e (x j)) / L)) /
          (∑ j, ‖x j‖ ^ 2) - uniformSphereFunctional d (fun z => H z / L)| ∧
      |(d : ℝ) * ((∑ j, H (x j)) / (N : ℝ)) -
        DataSecondMoment x * gaussianFunctional d H| ≤
      (d : ℝ) * DataSecondMoment x * L * δ := by
  have hN : 0 < N := by
    by_contra hN
    have hzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    simp only [Finset.univ_eq_empty, Finset.sum_empty, lt_self_iff_false] at hW
  have hR : 0 < DataSecondMoment x := div_pos hW (Nat.cast_pos.mpr hN)
  have hsample :
      (∑ j, ‖x j‖ ^ 2 * (H (sphereDirection e (x j)) / L)) =
        (∑ j, H (x j)) / L := by
    simp_rw [← mul_div_assoc, ← homogeneous_degree_two_radial_value H hHhom e]
    exact Finset.sum_div.symm
  have hsphere : uniformSphereFunctional d (fun z => H z / L) =
      uniformSphereFunctional d H / L := by
    unfold uniformSphereFunctional
    rw [integral_div]
    ring
  have hfactor :
      (d : ℝ) * ((∑ j, H (x j)) / (N : ℝ)) -
          DataSecondMoment x * gaussianFunctional d H =
        (d : ℝ) * DataSecondMoment x * L *
          ((∑ j, ‖x j‖ ^ 2 * (H (sphereDirection e (x j)) / L)) /
            (∑ j, ‖x j‖ ^ 2) - uniformSphereFunctional d (fun z => H z / L)) := by
    rw [hsample, hsphere, gaussian_sphere_degree_two hd H hHhom]
    unfold DataSecondMoment
    field_simp [ne_of_gt hW, ne_of_gt (Nat.cast_pos.mpr hN : (0 : ℝ) < N), hL.ne']
    ring
  have hscale : 0 ≤ (d : ℝ) * DataSecondMoment x * L :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hR.le) hL.le
  have habs := congrArg abs hfactor
  rw [abs_mul, abs_of_nonneg hscale] at habs
  exact ⟨habs, habs.trans_le (mul_le_mul_of_nonneg_left hbound hscale)⟩

/-- Internal analytic conversion: the conclusion concerns the original raw
dataset and its observed average squared radius. -/
theorem data_accuracy_of_angular_bound {d N : ℕ} (hd : 2 ≤ d)
    (x : Fin N → Vec d) (e : sphere (0 : Vec d) 1) {δ : ℝ}
    (hW : 0 < ∑ j, ‖x j‖ ^ 2)
    (hmod : ∀ (H : Vec d → ℝ) (L : ℝ),
      (∀ z z' : Vec d, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 →
        |H z - H z'| ≤ L * ‖z - z'‖) →
      |(∑ j, (‖x j‖ ^ 2 / (∑ k, ‖x k‖ ^ 2)) *
          H (sphereDirection e (x j))) - uniformSphereFunctional d H| ≤ L * δ) :
    0 < DataSecondMoment x ∧ DataAccuracy x δ := by
  have hN : 0 < N := by
    by_contra hN
    have hzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    simp only [Finset.univ_eq_empty, Finset.sum_empty, lt_self_iff_false] at hW
  have hR : 0 < DataSecondMoment x := div_pos hW (Nat.cast_pos.mpr hN)
  refine ⟨hR, ?_⟩
  intro H _hHcont hHhom L hLip
  have hzero : H 0 = 0 := by
    simpa only [zero_smul, zero_pow (by decide : 0 < (2 : ℕ)), zero_mul]
      using hHhom 0 le_rfl 0
  have hLnonneg : 0 ≤ L := by
    have h := hLip e 0 (mem_sphere_zero_iff_norm.mp e.property).le (by simp)
    rw [sub_zero, mem_sphere_zero_iff_norm.mp e.property, mul_one] at h
    exact (abs_nonneg _).trans h
  by_cases hL : 0 < L
  · have hLip' : ∀ z z' : Vec d, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 →
        |H z / L - H z' / L| ≤ 1 * ‖z - z'‖ := by
      intro z z' hz hz'
      rw [← sub_div, abs_div, abs_of_pos hL, one_mul]
      exact (div_le_iff hL).mpr (by simpa only [mul_comm] using hLip z z' hz hz')
    have hbound := hmod (fun z => H z / L) 1 hLip'
    have hbound' :
        |(∑ j, ‖x j‖ ^ 2 * (H (sphereDirection e (x j)) / L)) /
          (∑ j, ‖x j‖ ^ 2) - uniformSphereFunctional d (fun z => H z / L)| ≤ δ := by
      simpa only [div_mul_eq_mul_div, ← Finset.sum_div, one_mul] using hbound
    exact (eq_homogeneous_discrepancy_chain hd x e H hHhom hL hW hbound').2
  · have hLzero : L = 0 := le_antisymm (le_of_not_gt hL) hLnonneg
    have hH0 (z : Vec d) : H z = 0 := by
      have h := hLip (sphereDirection e z) 0
        (mem_sphere_zero_iff_norm.mp (sphereDirection e z).property).le (by simp)
      rw [hLzero, hzero, sub_zero, zero_mul] at h
      have hdir := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      rw [homogeneous_degree_two_radial_value H hHhom e z, hdir, mul_zero]
    simp [hH0, hLzero, gaussianFunctional]

/-- A raw-data accuracy event, uniform over all sufficiently large sample
sizes and all degree-two homogeneous Lipschitz tests. Pairwise independence,
orthogonal invariance, and a positive finite second moment suffice. -/
theorem rem_finite_data_accuracy {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → Vec d) (hX : ∀ j, Measurable (X j))
    (μ : Measure (Vec d)) (hlaw : Measure.map (X 0) volume = μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
    {M : ℝ} (hM : 0 < M)
    (hint : Integrable (β := ℝ) (fun x : Vec d => (‖x‖ ^ (2 : ℕ) : ℝ)) μ)
    (hmean : integral (G := ℝ) μ (fun x : Vec d => (‖x‖ ^ (2 : ℕ) : ℝ)) = M)
    (hrot : ∀ Q : Vec d ≃ₗᵢ[ℝ] Vec d, MeasurePreserving Q μ μ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∃ G : Set Ω, MeasurableSet G ∧ volume Gᶜ < ENNReal.ofReal η ∧
      ∀ ω ∈ G, ∀ N, N₀ ≤ N →
        DataAccuracy (fun j : Fin N => X j ω) δ := by
  letI : Nontrivial (Vec d) :=
    FiniteDimensional.nontrivial_of_finrank_pos (K := ℝ)
      (by rw [finrank_euclideanSpace_fin]; exact lt_of_lt_of_le (by decide : 0 < 2) hd)
  obtain ⟨e, he⟩ := exists_norm_eq (Vec d) (by norm_num : (0 : ℝ) ≤ 1)
  let eS : sphere (0 : Vec d) 1 := ⟨e, mem_sphere_zero_iff_norm.mpr he⟩
  obtain ⟨N₀, G, hGm, hGprob, hG⟩ :=
    RadialData.radial_angular_accuracy_high_probability X hX μ hlaw hindep hident
      hM hint hmean hrot eS hδ hη
  refine ⟨N₀, G, hGm, hGprob, ?_⟩
  intro ω hω N hN
  obtain ⟨hW, hmod⟩ := hG ω hω N hN
  have hsum : (∑ j : Fin N, ‖X j ω‖ ^ 2) =
      ∑ j in Finset.range N, ‖X j ω‖ ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun j => ‖X j ω‖ ^ 2) N
  apply (data_accuracy_of_angular_bound hd (fun j : Fin N => X j ω) eS
    (hsum.symm ▸ hW) ?_).2
  intro H L hLip
  simpa only [hsum, uniformSphereFunctional, sphereSurfaceMeasure] using hmod H L hLip

/-- The teacher-labelled consequence of the model-independent data-accuracy
event. The original averaged loss and its radius are unchanged. In dimension
one the conclusion holds surely and for every sample size, since the
fixed-radius bridge needs no accuracy there. -/
theorem rem_finite_data_accuracy_high_probability {d n m : ℕ}
    (hd : 1 ≤ d) (hmn : m ≤ n)
    {s : Fin m → ℝ} {v : Fin m → Vec d}
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hv : ∀ k, ‖v k‖ = 1) (hs : ∀ k, 0 < s k)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (X : ℕ → Ω → Vec d) (hX : ∀ j, Measurable (X j))
    (μ : Measure (Vec d)) (hlaw : Measure.map (X 0) volume = μ)
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j))
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0))
    {M : ℝ} (hM : 0 < M)
    (hint : Integrable (β := ℝ) (fun x : Vec d => (‖x‖ ^ (2 : ℕ) : ℝ)) μ)
    (hmean : integral (G := ℝ) μ (fun x : Vec d => (‖x‖ ^ (2 : ℕ) : ℝ)) = M)
    (hrot : ∀ Q : Vec d ≃ₗᵢ[ℝ] Vec d, MeasurePreserving Q μ μ)
    {r η : ℝ} (hr : 0 < r) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∃ G : Set Ω, MeasurableSet G ∧ volume Gᶜ < ENNReal.ofReal η ∧
      ∀ ω ∈ G, ∀ N, N₀ ≤ N →
      ∀ (y : Fin N → ℝ) (bStar b : Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d),
        (∀ j, y j = (inner bStar (X j ω) : ℝ) +
          ∑ k, s k * max 0 (inner (v k) (X j ω) : ℝ)) →
        (∀ i, 0 ≤ c i) → (∀ i, ‖w i‖ = 1) →
        IsMinOn (fun p : Vec d × Parameters d n =>
          DataLoss (fun j : Fin N => X j ω) y p.1 p.2.1 p.2.2)
          {p | (∀ i, ‖p.2.2 i‖ = 1) ∧ JointDistance bStar s v p (b, (c, w)) ≤ r}
          (b, (c, w)) → DataLoss (fun j : Fin N => X j ω) y b c w = 0 := by
  by_cases hd1 : d = 1
  · subst hd1
    refine ⟨0, Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [Set.compl_univ, measure_empty]
      exact ENNReal.ofReal_pos.mpr hη
    · intro ω _ N _ y bStar b c w hy _hc hw hmin
      exact data_fixed_radius_dimension_one hmn (fun j : Fin N => X j ω) y b bStar c w s v
        hw hv hy hr hmin
  have hd : 2 ≤ d := by omega (config := {})
  obtain ⟨δ, hδ, hexact⟩ := thm_fixed_radius_bridge (le_trans one_le_two hd) hmn hplane hv hs hr
  obtain ⟨N₀, G, hGm, hGprob, hG⟩ :=
    rem_finite_data_accuracy hd X hX μ hlaw hindep hident
      hM hint hmean hrot hδ hη
  refine ⟨max N₀ 1, G, hGm, hGprob, ?_⟩
  intro ω hω N hN y bStar b c w hy hc hw hmin
  have hacc := hG ω hω N ((le_max_left N₀ 1).trans hN)
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 1)
    ((le_max_right N₀ 1).trans hN)
  exact hexact N (fun j : Fin N => X j ω) y hNpos hacc bStar b c w hy hc hw hmin

end PaperLeanFormalization.Empirical

end
