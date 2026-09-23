import Definitions
import Planar
import Preliminaries
import Skip
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Teacher-span confinement: trace, null normal mode, mixed term, boundary

This follows the normal/amplitude argument mentioned in the paper.
The cleaner final step uses a PSD radical: if `Q(N)=0` and `Q` is nonnegative
on the amplitude/normal plane, its mixed coefficient vanishes. Positivity of
that coefficient then rules out any component orthogonal to the teacher span.
Common linear normal/shear motions also handle colliding directions directly.
The positivity argument concerns only active masses, so zero-mass neurons need
neither deletion nor a separate width induction. Their weighted generators,
not their arbitrary directions, are confined.
-/

noncomputable section
open Real Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace PaperLeanFormalization.KernelAnalytic

/-- Restricting scalar multiplication preserves the convergence radius exactly. -/
theorem analyticAt_complex_to_real {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℝ f z := by
  obtain ⟨p,r,hp⟩ := hf
  let q : FormalMultilinearSeries ℝ ℂ ℂ := fun n => (p n).restrictScalars ℝ
  have hrad : q.radius=p.radius := by
    simp only [FormalMultilinearSeries.radius,q,ContinuousMultilinearMap.norm_restrictScalars]
  refine ⟨q,r,?_⟩
  exact ⟨by rw [hrad]; exact hp.r_le, hp.r_pos, fun hy => hp.hasSum hy⟩

/-- Real restriction and real projection of a holomorphic analytic germ. -/
theorem analyticAt_real_restriction {f : ℂ → ℂ} {r : ℝ}
    (hf : AnalyticAt ℂ f (r:ℂ)) : AnalyticAt ℝ (fun t : ℝ => (f t).re) r := by
  exact (Complex.reClm.analyticAt (f r)).comp (f := fun t : ℝ => f (t:ℂ))
    ((analyticAt_complex_to_real hf).comp (Complex.ofRealClm.analyticAt r))

/-- A complex local inverse is holomorphic near its base point.
Only the ordinary inverse function theorem and Cauchy's theorem are used. -/
theorem analytic_local_inverse {f f1 : ℂ → ℂ} {a : ℂ}
    (hf : ∀ z, HasStrictDerivAt f (f1 z) z) (hf1 : ContinuousAt f1 a) (ha : f1 a≠0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (f a) ∧
      (∀ᶠ z in 𝓝 a, g (f z)=z) := by
  let h := (hf a).hasStrictFDerivAt_equiv ha
  let e := h.toPartialHomeomorph f
  let g : ℂ → ℂ := e.symm
  have hleft : ∀ᶠ z in 𝓝 a, g (f z)=z := h.eventually_left_inverse
  have htarget : e.target ∈ 𝓝 (f a) := e.open_target.mem_nhds h.image_mem_toPartialHomeomorph_target
  have hnonzero : ∀ᶠ y in 𝓝 (f a), f1 (g y)≠0 :=
    h.localInverse_tendsto.eventually (hf1.eventually_ne ha)
  have hdiff : ∀ᶠ y in 𝓝 (f a), DifferentiableAt ℂ g y := by
    filter_upwards [htarget,hnonzero] with y hy hny
    have hgy : g y ∈ e.source := e.map_target hy
    have hlefty : ∀ᶠ z in 𝓝 (g y), g (f z)=z := e.eventually_left_inverse hgy
    have hder := (hf (g y)).to_local_left_inverse hny hlefty
    have hry : f (g y)=y := e.right_inv hy
    rw [hry] at hder
    exact hder.hasDerivAt.differentiableAt
  refine ⟨g,?_,hleft⟩
  exact DifferentiableOn.analyticAt (s := {y | DifferentiableAt ℂ g y})
    (fun _ hy => hy.differentiableWithinAt) hdiff

theorem analyticAt_cos (r : ℝ) : AnalyticAt ℝ Real.cos r := by
  simpa only [Complex.cos_ofReal_re] using
    analyticAt_real_restriction (Complex.differentiable_cos.analyticAt (r:ℂ))

theorem analyticAt_arcsin {r : ℝ} (hr : |r|<1) : AnalyticAt ℝ Real.arcsin r := by
  have hrlo : -1<r := (abs_lt.mp hr).1
  have hrhi : r<1 := (abs_lt.mp hr).2
  have hcos : Complex.cos ((arcsin r : ℝ):ℂ)≠0 := by
    rw [← Complex.ofReal_cos, Complex.ofReal_ne_zero]
    exact ne_of_gt (cos_pos_of_mem_Ioo
      ⟨neg_pi_div_two_lt_arcsin.mpr hrlo, arcsin_lt_pi_div_two.mpr hrhi⟩)
  obtain ⟨g,hg,hleft⟩ := analytic_local_inverse Complex.hasStrictDerivAt_sin
    Complex.continuous_cos.continuousAt hcos
  have hsin : Complex.sin ((arcsin r : ℝ):ℂ)=(r:ℂ) := by
    rw [← Complex.ofReal_sin, sin_arcsin hrlo.le hrhi.le]
  rw [hsin] at hg
  have hrestrict := analyticAt_real_restriction hg
  apply hrestrict.congr
  have hcont : Tendsto (fun t : ℝ => ((arcsin t : ℝ):ℂ)) (𝓝 r) (𝓝 ((arcsin r : ℝ):ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp continuous_arcsin.continuousAt.tendsto
  filter_upwards [hcont.eventually hleft, Ioo_mem_nhds hrlo hrhi] with t ht htr
  have hsint : Complex.sin ((arcsin t : ℝ):ℂ)=(t:ℂ) := by
    rw [← Complex.ofReal_sin, sin_arcsin htr.1.le htr.2.le]
  rw [hsint] at ht
  exact congrArg Complex.re ht

/-- The exact interior-analyticity primitive needed for sphere continuation. -/
theorem analyticAt_centeredKernel {r : ℝ} (hr : |r|<1) :
    AnalyticAt ℝ (fun t : ℝ => t*arcsin t+sqrt (1-t^2)) r := by
  have ha := analyticAt_arcsin hr
  have hc := (analyticAt_cos (arcsin r)).comp ha
  have h := ((analyticAt_id ℝ r).mul ha).add hc
  change AnalyticAt ℝ (fun t : ℝ => t*arcsin t+cos (arcsin t)) r at h
  simpa only [cos_arcsin] using h

end PaperLeanFormalization.KernelAnalytic

namespace PaperLeanFormalization.SphereContinuation

open Set Filter Metric FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- In dimension at least two, finitely many points do not obstruct real
analytic continuation. Continuity fills the exceptional points afterwards. -/
theorem zero_of_analytic_off_finite
    (hd : 1 < Module.rank ℝ E) (f : E → ℝ) (hf : Continuous f)
    (A : Set E) (hA : A.Finite)
    (ha : AnalyticOn ℝ f Aᶜ)
    {x : E} (hzero : f =ᶠ[𝓝 x] 0) : f = 0 := by
  letI : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).mp (zero_lt_one.trans hd)
  obtain ⟨U, hUsub, hUopen, hxU⟩ := _root_.mem_nhds_iff.mp hzero
  obtain ⟨y, hyU, hyA⟩ :=
    (hA.countable.dense_compl ℝ).inter_open_nonempty U hUopen ⟨x, hxU⟩
  have hyzero : f =ᶠ[𝓝 y] 0 :=
    Filter.mem_of_superset (hUopen.mem_nhds hyU) hUsub
  have hall : EqOn f 0 Aᶜ :=
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (hA.countable.isConnected_compl_of_one_lt_rank hd).isPreconnected hyA hyzero
  exact Continuous.ext_on (hA.countable.dense_compl ℝ) hf continuous_const hall

/-- The inverse stereographic chart is rational, so no trigonometric
analyticity theorem is required for the geometry. -/
theorem analytic_stereo_inverse (p : E) (hp : ‖p‖ = 1)
    (x : (ℝ ∙ p)ᗮ) :
    AnalyticAt ℝ (fun y : (ℝ ∙ p)ᗮ ↦ (stereoInvFun hp y : E)) x := by
  let V := (ℝ ∙ p)ᗮ
  have hid : AnalyticAt ℝ (fun y : V ↦ (y : E)) x :=
    V.subtypeL.analyticAt x
  have hsq : AnalyticAt ℝ (fun y : V ↦ ‖(y : E)‖ ^ 2) x := by
    have hb := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).analyticAt_bilinear
      ((x : E), (x : E))
    have hh : AnalyticAt ℝ (fun y : V ↦ (inner (y : E) (y : E) : ℝ)) x :=
      hb.comp₂ hid hid
    simpa only [real_inner_self_eq_norm_sq] using hh
  have hden : ‖(x : E)‖ ^ 2 + 4 ≠ 0 := by positivity
  have hratio := (hsq.add analyticAt_const).inv hden
  have hnum : AnalyticAt ℝ
      (fun y : V ↦ (4 : ℝ) • (y : E) + (‖(y : E)‖ ^ 2 - 4) • p) x :=
    (analyticAt_const.smul hid).add
      ((hsq.sub analyticAt_const).smul analyticAt_const)
  simpa only [stereoInvFun_apply] using hratio.smul hnum

/-- A sphere of ambient dimension at least three has a stereographic model
of dimension at least two. -/
theorem tangent_rank_gt_one (hd : 3 ≤ finrank ℝ E) (p : E) (hp : ‖p‖ = 1) :
    1 < Module.rank ℝ (ℝ ∙ p)ᗮ := by
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hdim := (ℝ ∙ p).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hp0] at hdim
  rw [← finrank_eq_rank]
  exact_mod_cast (show 1 < finrank ℝ (ℝ ∙ p)ᗮ by linarith only [hdim, hd])

/-- One stereographic chart suffices. Its finite punctures are removed by
Euclidean analytic continuation, and continuity fills both those punctures and
the chart's north pole. -/
theorem sphere_zero_of_chart_analytic
    (hd : 3 ≤ finrank ℝ E)
    (f : sphere (0 : E) 1 → ℝ) (hf : Continuous f)
    (A : Set (sphere (0 : E) 1)) (hA : A.Finite)
    (p u : sphere (0 : E) 1) (hup : u ≠ p)
    (ha : ∀ x : (ℝ ∙ (p : E))ᗮ,
      stereoInvFun (norm_eq_of_mem_sphere p) x ∉ A →
      AnalyticAt ℝ (f ∘ stereoInvFun (norm_eq_of_mem_sphere p)) x)
    (hzero : f =ᶠ[𝓝 u] 0) : f = 0 := by
  let hp : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  let g := stereoInvFun hp
  let B := g ⁻¹' A
  have hginj : Function.Injective g := by
    intro x y h
    have h' := congrArg (fun z : sphere (0 : E) 1 ↦ stereoToFun (p : E) (z : E)) h
    simpa only [g, stereo_right_inv] using h'
  have hB : B.Finite := Set.Finite.preimage (hginj.injOn _) hA
  let x₀ := stereoToFun (p : E) (u : E)
  have hgu : g x₀ = u :=
    stereo_left_inv hp (fun h ↦ hup (Subtype.ext h))
  have hzero' : (f ∘ g) =ᶠ[𝓝 x₀] 0 := by
    have ht := (continuous_stereoInvFun hp).tendsto x₀
    change Tendsto g (𝓝 x₀) (𝓝 (g x₀)) at ht
    rw [hgu] at ht
    exact hzero.comp_tendsto ht
  have hchart : f ∘ g = 0 :=
    zero_of_analytic_off_finite (tangent_rank_gt_one hd (p : E) hp)
      (f ∘ g) (hf.comp (continuous_stereoInvFun hp)) B hB
      (fun x hx ↦ ha x hx) hzero'
  have hoff : EqOn f 0 ({p}ᶜ : Set (sphere (0 : E) 1)) := by
    intro y hy
    have hg : g (stereoToFun (p : E) (y : E)) = y :=
      stereo_left_inv hp (fun h ↦ hy (Subtype.ext h))
    have := congrFun hchart (stereoToFun (p : E) (y : E))
    simpa only [Function.comp_apply, hg, Pi.zero_apply] using this
  have hrank : 1 < Module.rank ℝ E := by
    rw [← finrank_eq_rank]
    exact_mod_cast (show 1 < finrank ℝ E by linarith only [hd])
  letI : ConnectedSpace (sphere (0 : E) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hrank (0 : E) zero_le_one)
  letI : Nontrivial (sphere (0 : E) 1) := ⟨⟨u, p, hup⟩⟩
  exact Continuous.ext_on (dense_compl_singleton p) hf continuous_const hoff

/-- The only possible singular correlations of a unit atom occur at that
atom and its antipode. -/
theorem strict_correlation_of_not_atom (x a : E)
    (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hpos : x ≠ a) (hneg : x ≠ -a) :
    |(inner x a : ℝ)| < 1 := by
  have hle : |(inner x a : ℝ)| ≤ 1 := by
    simpa only [hx, ha, one_mul] using abs_real_inner_le_norm x a
  apply lt_of_le_of_ne hle
  intro heq
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heq with h | h
  · exact hpos ((inner_eq_one_iff_of_norm_one (𝕜 := ℝ) hx ha).mp h)
  · apply hneg
    apply (inner_eq_one_iff_of_norm_one (𝕜 := ℝ) hx (by simpa using ha)).mp
    simp only [inner_neg_right, h, neg_neg]

/-- Finite weighted regular kernels have the propagation property needed in
`stp:zm-propagation`, with arbitrary signs. The statement isolates precisely
the scalar assumptions and proves all sphere geometry locally. -/
theorem finite_kernel_zero_on_sphere_of_patch
    {N : ℕ} (hd : 3 ≤ finrank ℝ E)
    (K : ℝ → ℝ) (hK : Continuous K)
    (hKa : ∀ r : ℝ, |r| < 1 → AnalyticAt ℝ K r)
    (c : Fin N → ℝ) (a : Fin N → E) (ha : ∀ i, ‖a i‖ = 1)
    (u : E) (hu : ‖u‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (hpatch : ∀ z : E, dist z u < δ → ‖z‖ = 1 →
      (∑ i, c i * K (inner z (a i))) = 0) :
    ∀ y : E, ‖y‖ = 1 → (∑ i, c i * K (inner y (a i))) = 0 := by
  let f : sphere (0 : E) 1 → ℝ := fun z ↦ ∑ i, c i * K (inner (z : E) (a i))
  have hf : Continuous f := by
    apply continuous_finset_sum
    intro i _
    exact continuous_const.mul (hK.comp (continuous_subtype_val.inner continuous_const))
  let A : Set (sphere (0 : E) 1) :=
    Subtype.val ⁻¹' (range a ∪ range (fun i ↦ -a i))
  have hA : A.Finite :=
    Set.Finite.preimage (Subtype.val_injective.injOn _)
      ((Set.finite_range a).union (Set.finite_range (fun i ↦ -a i)))
  let u' : sphere (0 : E) 1 := ⟨u, by simpa only [mem_sphere_zero_iff_norm] using hu⟩
  let p : sphere (0 : E) 1 := -u'
  have hup : u' ≠ p := ne_neg_of_mem_unit_sphere ℝ u'
  have hchart : ∀ x : (ℝ ∙ (p : E))ᗮ,
      stereoInvFun (norm_eq_of_mem_sphere p) x ∉ A →
      AnalyticAt ℝ (f ∘ stereoInvFun (norm_eq_of_mem_sphere p)) x := by
    intro x hx
    let z := stereoInvFun (norm_eq_of_mem_sphere p) x
    apply Finset.analyticAt_sum
    intro i _
    apply analyticAt_const.mul
    have hregular : |(inner (z : E) (a i) : ℝ)| < 1 := by
      apply strict_correlation_of_not_atom (z : E) (a i)
        (norm_eq_of_mem_sphere z) (ha i)
      · intro h
        exact hx (Or.inl ⟨i, h.symm⟩)
      · intro h
        exact hx (Or.inr ⟨i, h.symm⟩)
    have hi : AnalyticAt ℝ
        (fun t : (ℝ ∙ (p : E))ᗮ ↦
          (inner (stereoInvFun (norm_eq_of_mem_sphere p) t : E) (a i) : ℝ)) x := by
      have hc := ((innerSL ℝ (a i)).analyticAt (z : E)).comp
        (f := fun t : (ℝ ∙ (p : E))ᗮ ↦
          (stereoInvFun (norm_eq_of_mem_sphere p) t : E)) (x := x)
        (analytic_stereo_inverse (p : E) (norm_eq_of_mem_sphere p) x)
      simpa only [innerSL_apply, real_inner_comm] using hc
    exact (hKa _ hregular).comp
      (f := fun t : (ℝ ∙ (p : E))ᗮ ↦
        (inner (stereoInvFun (norm_eq_of_mem_sphere p) t : E) (a i) : ℝ))
      (x := x) hi
  have hzero : f =ᶠ[𝓝 u'] 0 := by
    have hb := (continuous_subtype_val.tendsto u').eventually (ball_mem_nhds u hδ)
    filter_upwards [hb] with z hz
    exact hpatch (z : E) hz (norm_eq_of_mem_sphere z)
  have hall := sphere_zero_of_chart_analytic hd f hf A hA p u' hup hchart hzero
  intro y hy
  exact congrFun hall ⟨y, by simpa only [mem_sphere_zero_iff_norm] using hy⟩

/-- Student-minus-teacher form of the preceding theorem. No positivity,
stationarity, or local-minimum assumption enters the propagation step. -/
theorem finite_kernel_residual_zero_on_sphere_of_patch
    {n m : ℕ} (hd : 3 ≤ finrank ℝ E)
    (K : ℝ → ℝ) (hK : Continuous K)
    (hKa : ∀ r : ℝ, |r| < 1 → AnalyticAt ℝ K r)
    (c : Fin n → ℝ) (w : Fin n → E) (hw : ∀ i, ‖w i‖ = 1)
    (s : Fin m → ℝ) (v : Fin m → E) (hv : ∀ k, ‖v k‖ = 1)
    (u : E) (hu : ‖u‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (hpatch : ∀ z : E, dist z u < δ → ‖z‖ = 1 →
      (∑ i, c i * K (inner z (w i))) - (∑ k, s k * K (inner z (v k))) = 0) :
    ∀ y : E, ‖y‖ = 1 →
      (∑ i, c i * K (inner y (w i))) - (∑ k, s k * K (inner y (v k))) = 0 := by
  let a := Fin.append w v
  let b := Fin.append c (fun k ↦ -s k)
  have ha : ∀ i, ‖a i‖ = 1 := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) i
    · simpa only [a, Fin.append_left] using hw j
    · simpa only [a, Fin.append_right] using hv k
  have hsum (z : E) :
      (∑ i, b i * K (inner z (a i))) =
        (∑ i, c i * K (inner z (w i))) - (∑ k, s k * K (inner z (v k))) := by
    rw [Fin.sum_univ_add]
    simp only [a, b, Fin.append_left, Fin.append_right, neg_mul,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  have hall := finite_kernel_zero_on_sphere_of_patch hd K hK hKa b a ha u hu hδ
    (fun z hz hzu ↦ (hsum z).trans (hpatch z hz hzu))
  intro y hy
  rw [← hsum]
  exact hall y hy

/-- The explicit centered scalar kernel is continuous even at its atoms. -/
theorem continuous_centered_kernel :
    Continuous (fun r : ℝ ↦ r * Real.arcsin r + Real.sqrt (1 - r ^ 2)) := by
  exact (continuous_id.mul Real.continuous_arcsin).add
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))

/-- Adding the plain-ReLU affine correction preserves the scalar analytic
input. This is why the same higher-dimensional proof handles both models. -/
theorem analytic_kernel_add_linear (K : ℝ → ℝ) (a : ℝ)
    (hK : ∀ r : ℝ, |r| < 1 → AnalyticAt ℝ K r) :
    ∀ r : ℝ, |r| < 1 → AnalyticAt ℝ (fun t ↦ K t + a * t) r := by
  intro r hr
  exact (hK r hr).add (analyticAt_const.mul (analyticAt_id ℝ r))

end PaperLeanFormalization.SphereContinuation


namespace PaperLeanFormalization.PairKernelJet

/-- A scalar two-jet, including differentiability on a neighborhood so that
the product and chain rules can also be differentiated. -/
structure Jet (f : ℝ → ℝ) (x v a b : ℝ) : Prop where
  value : f x = v
  first : HasDerivAt f a x
  second : HasDerivAt (deriv f) b x
  nearby : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f t

namespace Jet

theorem congr {f g : ℝ → ℝ} {x v a b : ℝ} (h : Jet f x v a b)
    (heq : f = g) : Jet g x v a b := heq ▸ h

theorem germ {f g : ℝ → ℝ} {x v a b : ℝ} (h : Jet f x v a b)
    (heq : g =ᶠ[𝓝 x] f) : Jet g x v a b := by
  refine ⟨heq.eq_of_nhds.trans h.value, h.first.congr_of_eventuallyEq heq,
    h.second.congr_of_eventuallyEq heq.deriv, ?_⟩
  filter_upwards [h.nearby, heq.eventuallyEq_nhds] with t ht he
  exact he.differentiableAt_iff.mpr ht

theorem const (x c : ℝ) : Jet (fun _ : ℝ => c) x c 0 0 := by
  refine ⟨rfl, hasDerivAt_const x c, ?_, ?_⟩
  · simpa using hasDerivAt_const x (0 : ℝ)
  · exact eventually_of_forall fun _ => differentiableAt_const _

theorem id (x : ℝ) : Jet (fun t : ℝ => t) x x 1 0 := by
  refine ⟨rfl, hasDerivAt_id x, ?_, ?_⟩
  · simpa using hasDerivAt_const x (1 : ℝ)
  · exact eventually_of_forall fun _ => differentiableAt_id

theorem add {f g : ℝ → ℝ} {x v w a b A B : ℝ}
    (hf : Jet f x v a A) (hg : Jet g x w b B) :
    Jet (fun t => f t + g t) x (v+w) (a+b) (A+B) := by
  refine ⟨by rw [hf.value, hg.value], hf.first.add hg.first, ?_, ?_⟩
  · apply (hf.second.add hg.second).congr_of_eventuallyEq
    filter_upwards [hf.nearby, hg.nearby] with t ht hu
    exact deriv_add ht hu
  · filter_upwards [hf.nearby, hg.nearby] with t ht hu using ht.add hu

theorem mul {f g : ℝ → ℝ} {x v w a b A B : ℝ}
    (hf : Jet f x v a A) (hg : Jet g x w b B) :
    Jet (fun t => f t * g t) x (v*w) (a*w+v*b) (A*w+2*a*b+v*B) := by
  refine ⟨by rw [hf.value, hg.value], ?_, ?_, ?_⟩
  · simpa [hf.value, hg.value] using hf.first.mul hg.first
  · have h := (hf.second.mul hg.first).add (hf.first.mul hg.second)
    have heq : deriv (fun t => f t*g t) =ᶠ[𝓝 x]
        (fun t => deriv f t*g t+f t*deriv g t) := by
      filter_upwards [hf.nearby, hg.nearby] with t ht hu
      exact deriv_mul ht hu
    convert h.congr_of_eventuallyEq heq using 1
    rw [hf.value, hg.value, hf.first.deriv, hg.first.deriv]
    ring
  · filter_upwards [hf.nearby, hg.nearby] with t ht hu using ht.mul hu

theorem comp {f g : ℝ → ℝ} {x v w a b A B : ℝ}
    (hf : Jet f w v a A) (hg : Jet g x w b B) :
    Jet (fun t => f (g t)) x v (a*b) (A*b^2+a*B) := by
  have hfg : ∀ᶠ t in 𝓝 x, DifferentiableAt ℝ f (g t) := by
    have ht : Tendsto g (𝓝 x) (𝓝 w) := hg.value ▸ hg.first.continuousAt
    exact ht.eventually hf.nearby
  refine ⟨by rw [hg.value, hf.value], ?_, ?_, ?_⟩
  · exact (hg.value.symm ▸ hf.first).comp x hg.first
  · have h := (((hg.value.symm ▸ hf.second).comp x hg.first).mul hg.second)
    have heq : deriv (fun t => f (g t)) =ᶠ[𝓝 x]
        (fun t => deriv f (g t)*deriv g t) := by
      filter_upwards [hfg, hg.nearby] with t ht hu
      exact (ht.hasDerivAt.comp t hu.hasDerivAt).deriv
    convert h.congr_of_eventuallyEq heq using 1
    dsimp only [Function.comp_def]
    rw [hg.value, hf.first.deriv, hg.first.deriv]
    ring
  · filter_upwards [hfg, hg.nearby] with t ht hu using ht.comp t hu

theorem inv_one : Jet (fun t : ℝ => t⁻¹) 1 1 (-1) 2 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · simpa using hasDerivAt_inv (by norm_num : (1 : ℝ) ≠ 0)
  · rw [deriv_inv']
    convert ((hasDerivAt_pow 2 (1 : ℝ)).inv (by norm_num)).neg using 1; norm_num
  · filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)] with t ht
    exact (hasDerivAt_inv ht).differentiableAt

theorem sqrt_one : Jet Real.sqrt 1 1 (1/2) (-1/4) := by
  have hs := Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0)
  refine ⟨Real.sqrt_one, by simpa using hs, ?_, ?_⟩
  · have h := ((hs.const_mul 2).inv (by norm_num)).const_mul 1
    apply (show HasDerivAt (fun t => 1/(2*Real.sqrt t)) (-1/4) 1 by
      convert h using 1; norm_num [div_eq_mul_inv]).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)] with t ht
    exact (Real.hasDerivAt_sqrt ht).deriv
  · filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)] with t ht
    exact (Real.hasDerivAt_sqrt ht).differentiableAt

end Jet

theorem quadratic_jet (q₀ q₁ q₂ : ℝ) :
    Jet (fun t => q₀+q₁*t+q₂*t*t) 0 q₀ q₁ (2*q₂) := by
  convert ((Jet.const 0 q₀).add ((Jet.const 0 q₁).mul (Jet.id 0))).add
    (((Jet.const 0 q₂).mul (Jet.id 0)).mul (Jet.id 0)) using 1 <;> ring

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared norm identity used in the manuscript, before differentiating. -/
theorem norm_squared_path (x h : E) (hx : ‖x‖ = 1) (t : ℝ) :
    ‖x+t • h‖^2 = 1+2*(inner x h : ℝ)*t+‖h‖^2*t*t := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hx]
  rw [real_inner_comm h x]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The numerator of the correlation is an exact quadratic polynomial. -/
theorem inner_path (x y h k : E) (t : ℝ) :
    (inner (x+t • h) (y+t • k) : ℝ) =
      inner x y + (inner h y+inner x k)*t+inner h k*t*t := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

/-- `eq:norm-inner-path`, strengthened to arbitrary displacements and real
generator masses. The normal-field display is its immediate specialization. -/
theorem eq_norm_inner_path {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y h k : E) (hx : ‖x‖ = 1) (c s t : ℝ) :
    ‖c • (x+t • h)‖^2 = c^2*(1+2*(inner x h : ℝ)*t+‖h‖^2*t*t) ∧
    (inner (c • (x+t • h)) (s • (y+t • k)) : ℝ) =
      c*s*(inner x y+(inner h y+inner x k)*t+inner h k*t*t) := by
  constructor
  · rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_squared_path x h hx t]
  · rw [real_inner_smul_left, real_inner_smul_right, inner_path x y h k t]
    ring

/-- First and second derivatives of the actual norm path at a unit vector. -/
theorem norm_path_jet (x h : E) (hx : ‖x‖ = 1) :
    Jet (fun t => ‖x+t • h‖) 0 1 (inner x h)
      (‖h‖^2-(inner x h : ℝ)^2) := by

  have hs : Jet (fun t => ‖x+t • h‖^2) 0 1
      (2*(inner x h : ℝ)) (2*‖h‖^2) := by
    convert quadratic_jet 1 (2*(inner x h : ℝ)) (‖h‖^2) using 1
    funext t
    simpa only [one_smul, one_pow, one_mul] using
      (eq_norm_inner_path x x h h hx 1 1 t).1
  have ht := Jet.sqrt_one.comp hs
  convert ht using 1
  · funext t
    exact (Real.sqrt_sq (norm_nonneg (x+t • h))).symm
  · ring
  · ring

/-- Jets of the norm product and correlation, with all coefficients visible. -/
theorem eq_norm_correlation_rates (x y h k : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    let g := (inner x y : ℝ)
    let a := (inner x h : ℝ)
    let b := (inner y k : ℝ)
    let C := (inner h y+inner x k : ℝ)
    let T := ‖h‖^2+‖k‖^2-(a-b)^2
    Jet (fun t => ‖x+t • h‖*‖y+t • k‖) 0 1 (a+b) T ∧
    Jet (fun t => (inner (x+t • h) (y+t • k) : ℝ) /
        (‖x+t • h‖*‖y+t • k‖)) 0 g (C-g*(a+b))
      (2*inner h k-2*C*(a+b)+g*(2*(a+b)^2-T)) := by

  dsimp only
  have hD : Jet (fun t => ‖x+t • h‖*‖y+t • k‖) 0 1
      (inner x h+inner y k)
      (‖h‖^2+‖k‖^2-(inner x h-inner y k : ℝ)^2) := by
    convert (norm_path_jet x h hx).mul (norm_path_jet y k hy) using 1 <;> ring
  refine ⟨hD, ?_⟩
  have hN : Jet (fun t => (inner (x+t • h) (y+t • k) : ℝ)) 0
      (inner x y) (inner h y+inner x k) (2*inner h k) := by
    convert quadratic_jet (inner x y) (inner h y+inner x k) (inner h k) using 1
    funext t
    simpa only [one_smul, one_mul] using (eq_norm_inner_path x y h k hx 1 1 t).2
  convert hN.mul (Jet.inv_one.comp hD) using 1 <;> ring

end InnerProduct

abbrev centeredKernel (r : ℝ) : ℝ := r * arcsin r + sqrt (1 - r ^ 2)

private theorem kernel_derivative {r : ℝ} (_hm : r ≠ -1) (_hp : r ≠ 1) :
    HasDerivAt centeredKernel (Real.arcsin r) r :=
  KernelCalculus.hasDerivAt_centeredKernel r

theorem centered_kernel_jet (r : ℝ) (hr : |r| < 1) :
    Jet centeredKernel r (centeredKernel r) (Real.arcsin r)
      (Real.sqrt (1-r^2))⁻¹ := by
  have hm : r ≠ -1 := by intro h; simp [h] at hr
  have hp : r ≠ 1 := by intro h; simp [h] at hr
  have he : ∀ᶠ t in 𝓝 r, t ≠ -1 ∧ t ≠ 1 :=
    (eventually_ne_nhds hm).and (eventually_ne_nhds hp)
  refine ⟨rfl, kernel_derivative hm hp, ?_, ?_⟩
  · apply (show HasDerivAt Real.arcsin (Real.sqrt (1-r^2))⁻¹ r by
      simpa only [one_div] using Real.hasDerivAt_arcsin hm hp).congr_of_eventuallyEq
    filter_upwards [he] with t ht
    exact (kernel_derivative ht.1 ht.2).deriv
  · filter_upwards [he] with t ht
    exact (kernel_derivative ht.1 ht.2).differentiableAt

/-- `eq:pair-second-derivative`: the genuine product/chain rule, before the
norm and correlation coefficients are substituted. -/
theorem eq_pair_second_derivative (D rho : ℝ → ℝ) (t D₀ D₁ D₂ r r₁ r₂ : ℝ)
    (hD : Jet D t D₀ D₁ D₂) (hrho : Jet rho t r r₁ r₂) (hr : |r| < 1) :
    HasDerivAt (deriv (fun z => D z*centeredKernel (rho z)))
      (D₂*centeredKernel r+2*D₁*Real.arcsin r*r₁+
        D₀*(r₁^2/Real.sqrt (1-r^2))+D₀*Real.arcsin r*r₂) t := by
  convert (hD.mul ((centered_kernel_jet r hr).comp hrho)).second using 1
  simp only [div_eq_mul_inv]
  ring

/-- `eq:pair-closed-form`: actual curvature of the homogeneous pair kernel.
This consumes the preceding product/chain rule and the explicit path jets. -/
theorem eq_pair_closed_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y h k : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hg : |(inner x y : ℝ)| < 1) :
    HasDerivAt (deriv (fun t : ℝ => ‖x+t • h‖*‖y+t • k‖ *
        centeredKernel ((inner (x+t • h) (y+t • k) : ℝ)/
          (‖x+t • h‖*‖y+t • k‖))))
      (((inner h y+inner x k : ℝ)-inner x y*(inner x h+inner y k))^2 /
          Real.sqrt (1-(inner x y : ℝ)^2)+
        Real.sqrt (1-(inner x y : ℝ)^2)*
          (‖h‖^2+‖k‖^2-(inner x h-inner y k : ℝ)^2)+
        2*Real.arcsin (inner x y)*inner h k) 0 := by
  obtain ⟨hD, hR⟩ := eq_norm_correlation_rates x y h k hx hy
  convert eq_pair_second_derivative _ _ 0 1 _ _ _ _ _ hD hR hg using 1
  unfold centeredKernel
  ring

/-- The corresponding actual first derivative, in the coefficient form used
on the right hand side of the finite normal/shear trace. -/
theorem eq_pair_term_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y h k : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hg : |(inner x y : ℝ)| < 1) :
    HasDerivAt (fun t : ℝ => ‖x+t • h‖*‖y+t • k‖ *
        centeredKernel ((inner (x+t • h) (y+t • k) : ℝ)/
          (‖x+t • h‖*‖y+t • k‖)))
      (Real.sqrt (1-(inner x y : ℝ)^2)*(inner x h+inner y k)+
        Real.arcsin (inner x y)*(inner h y+inner x k)) 0 := by
  obtain ⟨hD, hR⟩ := eq_norm_correlation_rates x y h k hx hy
  convert (hD.mul ((centered_kernel_jet (inner x y) hg).comp hR)).first using 1
  unfold centeredKernel
  ring

/-- `eq:proportional-pair-quadratic`: a proportional pair contributes an
exact quadratic in its common vector, with the two nonnegative masses exposed.
The identity also holds when the common vector or either mass is zero. -/
theorem eq_proportional_pair_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : E) (a b eps : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (heps : |eps| = 1) :
    ‖a • X‖ * ‖b • (eps • X)‖ *
      centeredKernel ((inner (a • X) (b • (eps • X)) : ℝ) /
        (‖a • X‖ * ‖b • (eps • X)‖)) =
      (π / 2) * a * b * ‖X‖ ^ 2 := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hb0 : b = 0
  · simp [hb0]
  by_cases hX : X = 0
  · simp [hX]
  have hN : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have hk : centeredKernel eps = π / 2 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heps with h | h <;>
      simp [h, centeredKernel]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb,
    heps, one_mul, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hr : b * (eps * (a * ‖X‖ ^ 2)) / (a * ‖X‖ * (b * ‖X‖)) = eps := by
    field_simp [ha0, hb0, hN]
    ring
  rw [hr, hk]
  ring

private theorem homogeneous_pair_aligned {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : E) (eps : ℝ) (heps : |eps| = 1) :
    ‖X‖*‖eps • X‖*centeredKernel ((inner X (eps • X) : ℝ)/(‖X‖*‖eps • X‖)) =
      ‖X‖^2*centeredKernel eps := by
  have hk : centeredKernel eps = π / 2 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heps with h | h <;>
      simp [h, centeredKernel]
  simpa only [one_smul, mul_one, one_mul, hk, mul_comm] using
    eq_proportional_pair_quadratic X 1 1 eps (by norm_num) (by norm_num) heps

/-- At a collision the two paths move in proportion. Their correlation is
constant and the pair term is an exact quadratic, including times at which the
common vector vanishes. This avoids differentiating the singular inverse root. -/
theorem aligned_pair_jet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x h : E) (hx : ‖x‖ = 1) (eps : ℝ) (heps : |eps| = 1) :
    Jet (fun t : ℝ => ‖x+t • h‖*‖eps • x+t • (eps • h)‖ *
        centeredKernel ((inner (x+t • h) (eps • x+t • (eps • h)) : ℝ)/
          (‖x+t • h‖*‖eps • x+t • (eps • h)‖)))
      0 (centeredKernel eps) (2*inner x h*centeredKernel eps)
      (2*‖h‖^2*centeredKernel eps) := by
  have hn : Jet (fun t : ℝ => ‖x+t • h‖^2) 0 1
      (2*inner x h) (2*‖h‖^2) := by
    convert quadratic_jet 1 (2*(inner x h : ℝ)) (‖h‖^2) using 1
    funext t
    exact norm_squared_path x h hx t
  have heq : (fun t : ℝ => ‖x+t • h‖*‖eps • x+t • (eps • h)‖ *
        centeredKernel ((inner (x+t • h) (eps • x+t • (eps • h)) : ℝ)/
          (‖x+t • h‖*‖eps • x+t • (eps • h)‖))) =
      (fun t : ℝ => ‖x+t • h‖^2*centeredKernel eps) := by
    funext t
    have hvec : eps • x+t • (eps • h) = eps • (x+t • h) := by
      rw [smul_add, smul_comm t eps h]
    rw [hvec]
    exact homogeneous_pair_aligned (x+t • h) eps heps
  rw [heq]
  convert hn.mul (Jet.const 0 (centeredKernel eps)) using 1 <;> ring

/-- The endpoint version of `eq:pair-closed-form` under proportional motion.
The inverse-root and square-root terms are zero at this aligned pair, while
the remaining arcsine term is the actual second derivative. -/
theorem pair_closed_form_aligned {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x h : E) (hx : ‖x‖ = 1)
    (eps : ℝ) (heps : |eps| = 1) :
    HasDerivAt (deriv (fun t : ℝ => ‖x+t • h‖*‖eps • x+t • (eps • h)‖ *
        centeredKernel ((inner (x+t • h) (eps • x+t • (eps • h)) : ℝ)/
          (‖x+t • h‖*‖eps • x+t • (eps • h)‖))))
      (2*Real.arcsin (inner x (eps • x))*inner h (eps • h)) 0 := by
  have hs : eps^2 = 1 := by nlinarith only [sq_abs eps, congrArg (fun a : ℝ => a^2) heps]
  convert (aligned_pair_jet x h hx eps heps).second using 1
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, hx,
    one_pow, mul_one, centeredKernel, hs, sub_self, Real.sqrt_zero, add_zero]
  ring

/-- Radial motion also keeps the correlation constant. This includes an
aligned student--teacher pair with the teacher fixed (`beta = 0`), for which
the second derivative vanishes. No restriction on the base correlation is needed. -/
theorem ray_pair_jet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (alpha beta : ℝ) :
    Jet (fun t : ℝ => ‖x+t • (alpha • x)‖*‖y+t • (beta • y)‖ *
        centeredKernel ((inner (x+t • (alpha • x)) (y+t • (beta • y)) : ℝ)/
          (‖x+t • (alpha • x)‖*‖y+t • (beta • y)‖)))
      0 (centeredKernel (inner x y)) ((alpha+beta)*centeredKernel (inner x y))
      (2*alpha*beta*centeredKernel (inner x y)) := by
  have hpos (a : ℝ) : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1+a*t := by
    exact (show Continuous (fun t : ℝ => 1+a*t) from
      continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        (lt_mem_nhds (by norm_num))
  have heq : (fun t : ℝ => ‖x+t • (alpha • x)‖*‖y+t • (beta • y)‖ *
        centeredKernel ((inner (x+t • (alpha • x)) (y+t • (beta • y)) : ℝ)/
          (‖x+t • (alpha • x)‖*‖y+t • (beta • y)‖))) =ᶠ[𝓝 0]
      (fun t : ℝ => (1+(alpha+beta)*t+(alpha*beta)*t*t)*centeredKernel (inner x y)) := by
    filter_upwards [hpos alpha, hpos beta] with t ha hb
    have hscale (a : ℝ) (z : E) : z+t • (a • z) = (1+a*t) • z := by
      rw [add_smul, one_smul, smul_smul, mul_comm a t]
    rw [hscale alpha x, hscale beta y]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb,
      hx, hy, mul_one, real_inner_smul_left, real_inner_smul_right]
    have hr : (1+beta*t)*((1+alpha*t)*(inner x y : ℝ))/
        ((1+alpha*t)*(1+beta*t)) = inner x y := by
      field_simp [ne_of_gt ha, ne_of_gt hb]
      ring
    rw [hr]
    ring
  apply Jet.germ _ heq
  convert (quadratic_jet 1 (alpha+beta) (alpha*beta)).mul
    (Jet.const 0 (centeredKernel (inner x y))) using 1 <;> ring

end PaperLeanFormalization.PairKernelJet

namespace PaperLeanFormalization.NormalTrace

/-- First derivative of the homogeneous pair kernel at unit base vectors. -/
def pairFirst (P R a b C : ℝ) : ℝ := R * (a + b) + P * C

/-- Second derivative coefficient of the homogeneous pair kernel. Here
`a=⟪x,h⟫`, `b=⟪y,k⟫`, `u=‖h‖²`, `v=‖k‖²`,
`C=⟪h,y⟫+⟪x,k⟫`, and `E=⟪h,k⟫`. -/
def pairSecond (g P R D a b u v C E : ℝ) : ℝ :=
  D * (C - g * (a + b)) ^ 2 + R * (u + v - (a - b) ^ 2) + 2 * P * E

private theorem sum_quadratic {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (A B C : ℝ) :
    (∑ i, (A * x i ^ 2 + B * y i ^ 2 + C * (x i * y i))) =
      A * (∑ i, x i ^ 2) + B * (∑ i, y i ^ 2) + C * (∑ i, x i * y i) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem shear_axis_sum {ι : Type*} [Fintype ι]
    (X Y : ι → ℝ) (g P R D x y A B C : ℝ)
    (hX : ∑ i, X i ^ 2 = A) (hY : ∑ i, Y i ^ 2 = B)
    (hXY : ∑ i, X i * Y i = C) :
    (∑ i, pairSecond g P R D (X i*x) (Y i*y) (X i^2) (Y i^2)
      (X i*y+Y i*x) (X i*Y i)) =
      (D*(y-g*x)^2+R*(1-x^2))*A +
      (D*(x-g*y)^2+R*(1-y^2))*B +
      (2*D*(y-g*x)*(x-g*y)+2*R*x*y+2*P)*C := by
  calc
    _ = ∑ i, ((D*(y-g*x)^2+R*(1-x^2))*X i^2 +
        (D*(x-g*y)^2+R*(1-y^2))*Y i^2 +
        (2*D*(y-g*x)*(x-g*y)+2*R*x*y+2*P)*(X i*Y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold pairSecond
      ring
    _ = _ := by rw [sum_quadratic, hX, hY, hXY]

/-- The whole finite trace requires only the three Gram moments in the
subspace and in its orthogonal complement, and the scalar kernel ODE.
The slope `P` is unrestricted, so the same theorem covers the centered and
plain kernels. -/
theorem coordinate_pair_trace {r d : ℕ}
    (x y : Fin r → ℝ) (X Y : Fin d → ℝ) (g P R D A B C : ℝ)
    (hX : ∑ μ, X μ ^ 2 = A) (hY : ∑ μ, Y μ ^ 2 = B)
    (hXY : ∑ μ, X μ * Y μ = C)
    (hx : ∑ a, x a ^ 2 = 1-A) (hy : ∑ a, y a ^ 2 = 1-B)
    (hxy : ∑ a, x a * y a = g-C)
    (hkernel : D * (1-g^2) = R) :
    (∑ a, ∑ μ, pairSecond g P R D (X μ*x a) (Y μ*y a)
      (X μ^2) (Y μ^2) (X μ*y a+Y μ*x a) (X μ*Y μ)) +
      pairSecond g P R D A B A B (2*C) C =
      ((r : ℝ)+1) * pairFirst P R A B (2*C) := by
  let U := D*(A*g^2+B-2*C*g)-R*A
  let V := D*(A+B*g^2-2*C*g)-R*B
  let W := D*(-2*A*g-2*B*g+2*C*(1+g^2))+2*R*C
  let Z := R*(A+B)+2*P*C
  have hsum : (∑ a, ∑ μ, pairSecond g P R D (X μ*x a) (Y μ*y a)
      (X μ^2) (Y μ^2) (X μ*y a+Y μ*x a) (X μ*Y μ)) =
      U*(1-A)+V*(1-B)+W*(g-C)+(r : ℝ)*Z := by
    calc
      _ = ∑ a, (U*x a^2+V*y a^2+W*(x a*y a)+Z) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [shear_axis_sum X Y g P R D (x a) (y a) A B C hX hY hXY]
        dsimp [U, V, W, Z]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, sum_quadratic, hx, hy, hxy]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  dsimp [U, V, W, Z, pairFirst, pairSecond]
  linear_combination (A+B-2*A*B-2*C*g+2*C^2)*hkernel

/-- The normal part is explicitly the vector minus its finite orthogonal
projection onto the isometric image. -/
def normalPart {d r : ℕ}
    (J : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x - ∑ a, (inner (J (EuclideanSpace.basisFun (Fin r) ℝ a)) x : ℝ) •
    J (EuclideanSpace.basisFun (Fin r) ℝ a)

private theorem frame_gram {d r : ℕ}
    (J : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) :
    (∑ a, (inner (J (EuclideanSpace.basisFun (Fin r) ℝ a)) x : ℝ) *
      (inner (J (EuclideanSpace.basisFun (Fin r) ℝ a)) y : ℝ)) =
      inner x y - inner (normalPart J x) (normalPart J y) := by
  let e : Fin r → EuclideanSpace ℝ (Fin d) := fun a =>
    J (EuclideanSpace.basisFun (Fin r) ℝ a)
  have he : Orthonormal ℝ e :=
    (EuclideanSpace.basisFun (Fin r) ℝ).orthonormal.comp_linearIsometry J
  have horth (a : Fin r) : (inner (e a) (normalPart J y) : ℝ) = 0 := by
    change inner (e a) (y - ∑ b, (inner (e b) y : ℝ) • e b) = 0
    rw [inner_sub_right, he.inner_right_fintype, sub_self]
  have hxn : (inner (normalPart J x) (normalPart J y) : ℝ) =
      inner x (normalPart J y) := by
    change inner (x - ∑ a, (inner (e a) x : ℝ) • e a) (normalPart J y) = _
    simp only [inner_sub_left, sum_inner, real_inner_smul_left, horth, mul_zero,
      Finset.sum_const_zero, sub_zero]
  rw [hxn]
  change (∑ a, (inner (e a) x : ℝ) * inner (e a) y) =
    inner x y - inner x (y - ∑ a, (inner (e a) y : ℝ) • e a)
  simp only [inner_sub_right, inner_sum, real_inner_smul_right]
  rw [sub_sub_cancel]
  apply Finset.sum_congr rfl
  intro a _
  rw [real_inner_comm x (e a), mul_comm]

private theorem basis_gram {d : ℕ}
    (B : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    (∑ μ, (inner (B μ) x : ℝ) * inner (B μ) y) = inner x y := by
  simpa only [real_inner_comm x] using B.sum_inner_mul_inner x y

/-- The finite normal/shear trace for a completely arbitrary isometric
teacher subspace. Every coefficient of the trace is displayed in this type. -/
theorem isometry_pair_trace {d r : ℕ}
    (J : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (B : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (P R D : ℝ) (hkernel : D * (1-(inner x y : ℝ)^2) = R) :
    let g := (inner x y : ℝ)
    let X := fun μ => (inner (B μ) (normalPart J x) : ℝ)
    let Y := fun μ => (inner (B μ) (normalPart J y) : ℝ)
    let p := fun a => (inner (J (EuclideanSpace.basisFun (Fin r) ℝ a)) x : ℝ)
    let q := fun a => (inner (J (EuclideanSpace.basisFun (Fin r) ℝ a)) y : ℝ)
    let A := ‖normalPart J x‖^2
    let C := (inner (normalPart J x) (normalPart J y) : ℝ)
    let E := ‖normalPart J y‖^2
    (∑ a, ∑ μ, pairSecond g P R D (X μ*p a) (Y μ*q a)
      (X μ^2) (Y μ^2) (X μ*q a+Y μ*p a) (X μ*Y μ)) +
      pairSecond g P R D A E A E (2*C) C =
      ((r : ℝ)+1) * pairFirst P R A E (2*C) := by
  dsimp only
  apply coordinate_pair_trace
  · simpa only [sq, real_inner_self_eq_norm_mul_norm] using
      basis_gram B (normalPart J x) (normalPart J x)
  · simpa only [sq, real_inner_self_eq_norm_mul_norm] using
      basis_gram B (normalPart J y) (normalPart J y)
  · exact basis_gram B (normalPart J x) (normalPart J y)
  · simpa only [sq, real_inner_self_eq_norm_mul_norm, hx, one_mul] using
      frame_gram J x x
  · simpa only [sq, real_inner_self_eq_norm_mul_norm, hy, one_mul] using
      frame_gram J y y
  · exact frame_gram J x y
  · exact hkernel

theorem normalPart_image {d r : ℕ}
    (J : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin r)) : normalPart J (J z) = 0 := by
  have h := congrArg J ((EuclideanSpace.basisFun (Fin r) ℝ).sum_repr z)
  simp only [map_sum, map_smul, OrthonormalBasis.repr_apply_apply] at h
  unfold normalPart
  simp only [J.inner_map_map]
  rw [h, sub_self]

/-- Student--teacher trace: the teacher does not move because it lies in the
subspace. This is a corollary of the same pair identity, not a second proof. -/
theorem isometry_teacher_trace {d r : ℕ}
    (J : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (B : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hyJ : y ∈ Set.range J)
    (P R D : ℝ) (hkernel : D * (1-(inner x y : ℝ)^2) = R) :
    let g := (inner x y : ℝ)
    let X := fun μ => (inner (B μ) (normalPart J x) : ℝ)
    let p := fun a => (inner (J (EuclideanSpace.basisFun (Fin r) ℝ a)) x : ℝ)
    let q := fun a => (inner (J (EuclideanSpace.basisFun (Fin r) ℝ a)) y : ℝ)
    let A := ‖normalPart J x‖^2
    (∑ a, ∑ μ, pairSecond g P R D (X μ*p a) 0 (X μ^2) 0 (X μ*q a) 0) +
      pairSecond g P R D A 0 A 0 0 0 =
      ((r : ℝ)+1) * pairFirst P R A 0 0 := by
  obtain ⟨z, rfl⟩ := hyJ
  have h := isometry_pair_trace J B x (J z) hx hy P R D hkernel
  dsimp only at h ⊢
  simpa only [normalPart_image, inner_zero_right, norm_zero, zero_pow two_pos,
    zero_mul, mul_zero, add_zero] using h

/-- The inverse-square-root coefficient satisfies the required ODE even at
the endpoints under Lean's zero-inverse convention. Endpoint differentiability
of a composed path is still a separate question. -/
theorem inverse_sqrt_kernel_relation (g : ℝ) :
    (Real.sqrt (1-g^2))⁻¹ * (1-g^2) = Real.sqrt (1-g^2) := by
  simpa only [div_eq_mul_inv, mul_comm] using (Real.div_sqrt (x := 1-g^2))

/-- Finite weighted assembly of a trace identity. Applied to the disjoint
union of student pairs and student--teacher pairs, the weights are respectively
`c_i*c_j/(4π)` and `-2*c_i*s_k/(4π)`, exactly those in `KernelEnergy`. -/
theorem weighted_trace {ι κ : Type*} [Fintype ι] [Fintype κ]
    (weight : ι → ℝ) (Q : κ → ι → ℝ) (N F : ι → ℝ) (k : ℝ)
    (htrace : ∀ i, (∑ a, Q a i) + N i = k * F i) :
    (∑ a, ∑ i, weight i * Q a i) + (∑ i, weight i * N i) =
      k * ∑ i, weight i * F i := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i, weight i * ((∑ a, Q a i) + N i) :=
      Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, k * (weight i * F i) :=
      Finset.sum_congr rfl fun i _ => by rw [htrace]; ring
    _ = _ := by rw [← Finset.mul_sum]

end PaperLeanFormalization.NormalTrace

namespace PaperLeanFormalization.ConfinementTraceAssembly

open PairKernelJet NormalTrace

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

def normalMap {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d where
  toFun := normalPart J
  map_add' x y := by
    simp only [normalPart, inner_add_right, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    simp only [normalPart, inner_smul_right, RingHom.id_apply, smul_sub,
      Finset.smul_sum, smul_smul]

def frame {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d) (a : Fin r) : Vec d :=
  J (EuclideanSpace.basisFun (Fin r) ℝ a)

def shearMap {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d)
    (B : OrthonormalBasis (Fin d) ℝ (Vec d)) (a : Fin r) (mu : Fin d) :
    Vec d →ₗ[ℝ] Vec d where
  toFun x := (inner (B mu) (normalPart J x) : ℝ) • frame J a
  map_add' x y := by
    change (inner (B mu) (normalMap J (x+y)) : ℝ) • _ = _
    rw [map_add, inner_add_right, add_smul]
    rfl
  map_smul' c x := by
    change (inner (B mu) (normalMap J (c • x)) : ℝ) • _ = _
    rw [map_smul, real_inner_smul_right, mul_smul]
    rfl

theorem frame_orthonormal {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d) :
    Orthonormal ℝ (frame J) :=
  (EuclideanSpace.basisFun (Fin r) ℝ).orthonormal.comp_linearIsometry J

theorem frame_normal_inner {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d)
    (a : Fin r) (x : Vec d) : (inner (frame J a) (normalPart J x) : ℝ) = 0 := by
  change inner (frame J a) (x-∑ b, (inner (frame J b) x : ℝ) • frame J b) = 0
  rw [inner_sub_right, (frame_orthonormal J).inner_right_fintype, sub_self]

theorem normal_inner {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d) (x y : Vec d) :
    (inner x (normalPart J y) : ℝ) = inner (normalPart J x) (normalPart J y) := by
  change inner x (normalPart J y) =
    inner (x-∑ a, (inner (frame J a) x : ℝ) • frame J a) (normalPart J y)
  simp only [inner_sub_left, sum_inner, real_inner_smul_left,
    frame_normal_inner, mul_zero, Finset.sum_const_zero, sub_zero]

theorem normal_inner_left {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d) (x y : Vec d) :
    (inner (normalPart J x) y : ℝ) = inner (normalPart J x) (normalPart J y) := by
  rw [real_inner_comm, normal_inner, real_inner_comm (normalPart J y)]

def pairPath {d : ℕ} (x y : Vec d) (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) : ℝ :=
  ‖x+t • A x‖*‖y+t • A y‖ * centeredKernel
    ((inner (x+t • A x) (y+t • A y) : ℝ)/(‖x+t • A x‖*‖y+t • A y‖))

def pairSlope {d : ℕ} (x y : Vec d) (A : Vec d →ₗ[ℝ] Vec d) : ℝ :=
  pairFirst (arcsin (inner x y)) (sqrt (1-(inner x y : ℝ)^2))
    (inner x (A x)) (inner y (A y)) (inner (A x) y+inner x (A y))

def pairCurvature {d : ℕ} (x y : Vec d) (A : Vec d →ₗ[ℝ] Vec d) : ℝ :=
  pairSecond (inner x y) (arcsin (inner x y)) (sqrt (1-(inner x y : ℝ)^2))
    (sqrt (1-(inner x y : ℝ)^2))⁻¹ (inner x (A x)) (inner y (A y))
    (‖A x‖^2) (‖A y‖^2) (inner (A x) y+inner x (A y)) (inner (A x) (A y))

private theorem unit_alignment {d : ℕ} (x y : Vec d) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hg : |(inner x y : ℝ)| = 1) : ∃ eps : ℝ, |eps| = 1 ∧ y = eps • x := by
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hg with hp | hm
  · refine ⟨1, by norm_num, ?_⟩
    simpa using ((inner_eq_one_iff_of_norm_one hx hy).mp hp).symm
  · refine ⟨-1, by norm_num, ?_⟩
    have hneg : (inner (-x) y : ℝ) = 1 := by rw [inner_neg_left, hm]; norm_num
    simpa using ((inner_eq_one_iff_of_norm_one (by simpa using hx) hy).mp hneg).symm

/-- Interior and collision cases attach the closed coefficient to the actual
pair path. Since every displacement is the same linear map, collisions move
in proportion automatically. Thus no separation hypothesis is needed here. -/
theorem pair_path_jet {d : ℕ} (x y : Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Jet (pairPath x y A) 0 (centeredKernel (inner x y))
      (pairSlope x y A) (pairCurvature x y A) := by
  have hle : |(inner x y : ℝ)| ≤ 1 := by
    simpa only [hx, hy, one_mul] using abs_real_inner_le_norm x y
  rcases hle.lt_or_eq with hg | hg
  · obtain ⟨hD, hR⟩ := eq_norm_correlation_rates x y (A x) (A y) hx hy
    have hj := hD.mul ((centered_kernel_jet (inner x y) hg).comp hR)
    refine ⟨?_, ?_, ?_, hj.nearby⟩
    · simp [pairPath, hx, hy]
    · exact eq_pair_term_derivative x y (A x) (A y) hx hy hg
    · convert eq_pair_closed_form x y (A x) (A y) hx hy hg using 1
      unfold pairCurvature pairSecond
      simp only [div_eq_mul_inv]
      ring
  · obtain ⟨eps, heps, rfl⟩ := unit_alignment x y hx hy hg
    have hs : eps^2 = 1 := by
      nlinarith only [sq_abs eps, congrArg (fun a : ℝ => a^2) heps]
    have hj := aligned_pair_jet x (A x) hx eps heps
    have hgx : (inner x (eps • x) : ℝ) = eps := by
      simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
    unfold pairPath
    simp only [map_smul]
    convert hj using 1
    · rw [hgx]
    · unfold pairSlope pairFirst
      rw [hgx]
      simp only [map_smul, hgx, hs, sub_self, sqrt_zero, zero_mul, zero_add,
        real_inner_smul_left, real_inner_smul_right, centeredKernel, real_inner_comm (A x) x,
        real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
      ring
    · unfold pairCurvature pairSecond
      rw [hgx]
      simp only [map_smul, hgx, hs, sub_self, sqrt_zero, inv_zero, zero_mul, zero_add,
        real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, centeredKernel,
        hx, one_pow, mul_one]
      ring

theorem normal_pair_coefficients {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d) (x y : Vec d) :
    let g := (inner x y : ℝ)
    let X := ‖normalPart J x‖^2
    let Y := ‖normalPart J y‖^2
    let C := (inner (normalPart J x) (normalPart J y) : ℝ)
    pairSlope x y (normalMap J) = pairFirst (arcsin g) (sqrt (1-g^2)) X Y (2*C) ∧
    pairCurvature x y (normalMap J) =
      pairSecond g (arcsin g) (sqrt (1-g^2)) (sqrt (1-g^2))⁻¹ X Y X Y (2*C) C := by
  dsimp only
  have hxx := normal_inner J x x
  have hyy := normal_inner J y y
  rw [real_inner_self_eq_norm_sq] at hxx hyy
  simp only [pairSlope, pairCurvature, normalMap, LinearMap.coe_mk, AddHom.coe_mk,
    hxx, hyy, normal_inner J x y, normal_inner_left J x y, ← two_mul]
  trivial

theorem shear_pair_curvature {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d)
    (B : OrthonormalBasis (Fin d) ℝ (Vec d)) (a : Fin r) (mu : Fin d) (x y : Vec d) :
    let g := (inner x y : ℝ)
    let X := (inner (B mu) (normalPart J x) : ℝ)
    let Y := (inner (B mu) (normalPart J y) : ℝ)
    let p := (inner (frame J a) x : ℝ)
    let q := (inner (frame J a) y : ℝ)
    pairCurvature x y (shearMap J B a mu) =
      pairSecond g (arcsin g) (sqrt (1-g^2)) (sqrt (1-g^2))⁻¹
        (X*p) (Y*q) (X^2) (Y^2) (X*q+Y*p) (X*Y) := by
  have hn : ‖frame J a‖ = 1 := (frame_orthonormal J).1 a
  have hii : (inner (frame J a) (frame J a) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn, one_pow]
  simp only [pairCurvature, shearMap, LinearMap.coe_mk, AddHom.coe_mk,
    real_inner_smul_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hn, one_pow, mul_one, hii,
    real_inner_comm x (frame J a), real_inner_comm y (frame J a)]
  unfold pairSecond
  ring

/-- `eq:term-trace`, now for the actual first and second derivatives of one
homogeneous pair term. The closed form is consumed through `pair_path_jet`. -/
theorem eq_term_trace {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d)
    (B : OrthonormalBasis (Fin d) ℝ (Vec d)) (x y : Vec d)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (∑ a, ∑ mu, deriv (deriv (pairPath x y (shearMap J B a mu))) 0)+
        deriv (deriv (pairPath x y (normalMap J))) 0 =
      ((r : ℝ)+1)*deriv (pairPath x y (normalMap J)) 0 := by
  have hsecond (A : Vec d →ₗ[ℝ] Vec d) :
      deriv (deriv (pairPath x y A)) 0 = pairCurvature x y A :=
    (pair_path_jet x y A hx hy).second.deriv
  simp_rw [hsecond]
  rw [(pair_path_jet x y (normalMap J) hx hy).first.deriv]
  rw [(normal_pair_coefficients J x y).1, (normal_pair_coefficients J x y).2]
  simp_rw [shear_pair_curvature]
  exact isometry_pair_trace J B x y hx hy _ _ _
    (inverse_sqrt_kernel_relation (inner x y))

theorem sum_jets {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (x : ℝ) (v a b : ι → ℝ) (hj : ∀ i ∈ s, Jet (f i) x (v i) (a i) (b i)) :
    Jet (fun t => ∑ i in s, f i t) x (∑ i in s, v i) (∑ i in s, a i)
      (∑ i in s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Jet.const x 0
  | @insert i s hi ih =>
    have hsum := (hj i (Finset.mem_insert_self i s)).add
      (ih (fun j hmem => hj j (Finset.mem_insert_of_mem hmem)))
    simpa only [Finset.sum_insert hi] using hsum

/-- A finite sum of actual pair terms with unrestricted real weights. Student
pairs and signed student--teacher terms are instances of this one sum. -/
def weightedPairPath {d : ℕ} {ι : Type*} [Fintype ι] (weight : ι → ℝ)
    (x y : ι → Vec d) (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) : ℝ :=
  ∑ i, weight i*pairPath (x i) (y i) A t

theorem weighted_pair_jet {d : ℕ} {ι : Type*} [Fintype ι] (weight : ι → ℝ)
    (x y : ι → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) :
    Jet (weightedPairPath weight x y A) 0
      (∑ i, weight i*centeredKernel (inner (x i) (y i)))
      (∑ i, weight i*pairSlope (x i) (y i) A)
      (∑ i, weight i*pairCurvature (x i) (y i) A) := by
  apply sum_jets
  intro i _
  convert (Jet.const 0 (weight i)).mul (pair_path_jet (x i) (y i) A (hx i) (hy i))
    using 1 <;> ring

/-- `eq:global-trace`: finite summation of the actual term trace, not merely
an identity between formally chosen curvature coefficients. -/
theorem eq_global_trace {d r : ℕ} {ι : Type*} [Fintype ι]
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (weight : ι → ℝ) (x y : ι → Vec d)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) :
    (∑ a, ∑ mu, deriv (deriv (weightedPairPath weight x y (shearMap J B a mu))) 0)+
        deriv (deriv (weightedPairPath weight x y (normalMap J))) 0 =
      ((r : ℝ)+1)*deriv (weightedPairPath weight x y (normalMap J)) 0 := by
  have hsumsecond (A : Vec d →ₗ[ℝ] Vec d) :
      deriv (deriv (weightedPairPath weight x y A)) 0 =
        ∑ i, weight i*deriv (deriv (pairPath (x i) (y i) A)) 0 := by
    rw [(weighted_pair_jet weight x y A hx hy).second.deriv]
    simp_rw [(pair_path_jet _ _ A (hx _) (hy _)).second.deriv]
  have hsumfirst (A : Vec d →ₗ[ℝ] Vec d) :
      deriv (weightedPairPath weight x y A) 0 =
        ∑ i, weight i*deriv (pairPath (x i) (y i) A) 0 := by
    rw [(weighted_pair_jet weight x y A hx hy).first.deriv]
    simp_rw [(pair_path_jet _ _ A (hx _) (hy _)).first.deriv]
  simp_rw [hsumsecond, hsumfirst]
  have h := weighted_trace weight
    (fun (a : Fin r × Fin d) i => deriv (deriv (pairPath (x i) (y i)
      (shearMap J B a.1 a.2))) 0)
    (fun i => deriv (deriv (pairPath (x i) (y i) (normalMap J))) 0)
    (fun i => deriv (pairPath (x i) (y i) (normalMap J)) 0) ((r : ℝ)+1)
    (fun i => by simpa only [Fintype.sum_prod_type] using eq_term_trace J B (x i) (y i) (hx i) (hy i))
  simpa only [Fintype.sum_prod_type] using h

/-- Scalar minimality supplies nonnegative actual curvature. -/
theorem jet_second_nonneg {f : ℝ → ℝ} {v a b : ℝ}
    (hj : Jet f 0 v a b) (hmin : IsLocalMin f 0) : 0 ≤ b := by
  by_contra hb
  exact Preliminaries.negative_second_derivative_not_local_min hj.nearby
    hmin.deriv_eq_zero hj.second (lt_of_not_ge hb) hmin

/-- The nonnegative trace sum forces the normal curvature to vanish at a
local minimum. The assumptions here name actual scalar path local minima;
the polar pullback below supplies these from the parameter-space minimum. -/
theorem normal_curvature_zero_of_path_minima {d r : ℕ} {ι : Type*} [Fintype ι]
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (weight : ι → ℝ) (x y : ι → Vec d)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hN : IsLocalMin (weightedPairPath weight x y (normalMap J)) 0)
    (hS : ∀ a mu, IsLocalMin (weightedPairPath weight x y (shearMap J B a mu)) 0) :
    deriv (deriv (weightedPairPath weight x y (normalMap J))) 0 = 0 := by
  have hnonneg (A : Vec d →ₗ[ℝ] Vec d)
      (hmin : IsLocalMin (weightedPairPath weight x y A) 0) :
      0 ≤ deriv (deriv (weightedPairPath weight x y A)) 0 := by
    rw [(weighted_pair_jet weight x y A hx hy).second.deriv]
    exact jet_second_nonneg (weighted_pair_jet weight x y A hx hy) hmin
  have hn := hnonneg (normalMap J) hN
  have hs : 0 ≤ ∑ a, ∑ mu,
      deriv (deriv (weightedPairPath weight x y (shearMap J B a mu))) 0 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun mu _ => hnonneg _ (hS a mu)
  have ht := eq_global_trace J B weight x y hx hy
  rw [hN.deriv_eq_zero, mul_zero] at ht
  linarith only [ht, hn, hs]

abbrev Parameters (d n : ℕ) := (Fin n → ℝ) × (Fin n → Vec d)

/-- The mass absorbs the row norm; the direction is visibly normalized here. -/
def polarPath {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) : Parameters d n :=
  (fun i => c i*‖w i+t • A (w i)‖,
   fun i => ‖w i+t • A (w i)‖⁻¹ • (w i+t • A (w i)))

theorem polar_path_zero {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (hw : ∀ i, ‖w i‖ = 1) : polarPath c w A 0 = (c,w) := by
  simp [polarPath, hw]

/-- Pulling a constrained local minimum back to this curve is purely
topological. There is no global Hessian or ambient differentiability premise. -/
theorem local_minimum_polar_path {d n : ℕ} (L : Parameters d n → ℝ)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hw : ∀ i, ‖w i‖ = 1)
    (hmin : IsLocalMinOn L {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    IsLocalMin (fun t => L (polarPath c w A t)) 0 := by
  have hrow (i : Fin n) : Continuous (fun t : ℝ => w i+t • A (w i)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hn (i : Fin n) : ‖w i+(0 : ℝ) • A (w i)‖ ≠ 0 := by simp [hw]
  have hc : ContinuousAt (polarPath c w A) 0 := by
    apply ContinuousAt.prod
    · apply continuousAt_pi.mpr
      exact fun i => continuousAt_const.mul (hrow i).norm.continuousAt
    · apply continuousAt_pi.mpr
      exact fun i => ((hrow i).norm.continuousAt.inv₀ (hn i)).smul (hrow i).continuousAt
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, ‖w i+t • A (w i)‖ ≠ 0 := by
    apply eventually_all.mpr
    intro i
    exact (hrow i).norm.continuousAt.eventually_ne (hn i)
  have ht : Tendsto (polarPath c w A) (𝓝 0)
      (𝓝[{p : Parameters d n | ∀ i, ‖p.2 i‖ = 1}] (c,w)) := by
    apply tendsto_nhdsWithin_iff.mpr
    have hct : Tendsto (polarPath c w A) (𝓝 0) (𝓝 (polarPath c w A 0)) := hc
    refine ⟨by simpa only [polar_path_zero c w A hw] using hct, ?_⟩
    filter_upwards [he] with t ht
    intro i
    exact norm_smul_inv_norm (norm_ne_zero_iff.mp (ht i))
  show ∀ᶠ t in 𝓝 (0 : ℝ), L (polarPath c w A 0) ≤ L (polarPath c w A t)
  rw [polar_path_zero c w A hw]
  exact ht.eventually hmin

/-- The unnormalized variable part of the centered kernel loss. The Gaussian
population loss is a positive constant multiple plus a teacher constant. -/
def variableKernelLoss {d n m : ℕ} (s : Fin m → ℝ) (v : Fin m → Vec d)
    (p : Parameters d n) : ℝ :=
  (1/2)*(∑ i, ∑ j, p.1 i*p.1 j*centeredKernel (inner (p.2 i) (p.2 j)))-
    ∑ i, ∑ k, p.1 i*s k*centeredKernel (inner (p.2 i) (v k))

abbrev LossPairIndex (n m : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin m)

def lossPairWeight {n m : ℕ} (c : Fin n → ℝ) (s : Fin m → ℝ) : LossPairIndex n m → ℝ
  | .inl ij => c ij.1*c ij.2/2
  | .inr ik => -c ik.1*s ik.2

def lossPairLeft {d n m : ℕ} (w : Fin n → Vec d) : LossPairIndex n m → Vec d
  | .inl ij => w ij.1
  | .inr ik => w ik.1

def lossPairRight {d n m : ℕ} (w : Fin n → Vec d) (v : Fin m → Vec d) :
    LossPairIndex n m → Vec d
  | .inl ij => w ij.2
  | .inr ik => v ik.2

theorem normalized_inner {d : ℕ} (x y : Vec d) :
    (inner (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) : ℝ) = inner x y/(‖x‖*‖y‖) := by
  simp only [real_inner_smul_left, real_inner_smul_right, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Explicitly identify the finite pair sum with the real normalized loss
curve, including the negative student--teacher weights. -/
theorem variable_loss_path_eq {d n m : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hv : ∀ k, ‖v k‖ = 1) (hAv : ∀ k, A (v k) = 0) (t : ℝ) :
    weightedPairPath (lossPairWeight c s) (lossPairLeft w) (lossPairRight w v) A t =
      variableKernelLoss s v (polarPath c w A t) := by
  unfold weightedPairPath variableKernelLoss
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, lossPairWeight,
    lossPairLeft, lossPairRight, polarPath, Finset.mul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [normalized_inner]
    unfold pairPath
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    unfold pairPath
    simp only [hAv, smul_zero, add_zero, hv, mul_one, real_inner_smul_left]
    rw [div_eq_mul_inv, mul_comm (inner _ _ : ℝ) (‖w i+t • A (w i)‖⁻¹)]
    ring

theorem normal_map_teacher_zero {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d)
    (y : Vec d) (hy : y ∈ Set.range J) : normalMap J y = 0 := by
  obtain ⟨z, rfl⟩ := hy
  exact normalPart_image J z

theorem shear_map_teacher_zero {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d)
    (B : OrthonormalBasis (Fin d) ℝ (Vec d)) (a : Fin r) (mu : Fin d)
    (y : Vec d) (hy : y ∈ Set.range J) : shearMap J B a mu y = 0 := by
  obtain ⟨z, rfl⟩ := hy
  simp [shearMap, normalPart_image]

/-- Actual normal curvature vanishes at a constrained local minimum of the
finite centered loss. Teachers may have arbitrary signed masses, and no student
separation is required. All local path minima are obtained by polar pullback. -/
theorem centered_normal_curvature_zero {d r n m : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (variableKernelLoss s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    deriv (deriv (fun t => variableKernelLoss s v (polarPath c w (normalMap J) t))) 0 = 0 := by
  have hleft (i : LossPairIndex n m) : ‖lossPairLeft w i‖ = 1 := by
    cases i with | inl ij => exact hw ij.1 | inr ik => exact hw ik.1
  have hright (i : LossPairIndex n m) : ‖lossPairRight w v i‖ = 1 := by
    cases i with | inl ij => exact hw ij.2 | inr ik => exact hv ik.2
  have hpath (A : Vec d →ₗ[ℝ] Vec d) (hAv : ∀ k, A (v k) = 0) :
      weightedPairPath (lossPairWeight c s) (lossPairLeft w) (lossPairRight w v) A =
        (fun t => variableKernelLoss s v (polarPath c w A t)) := by
    funext t
    exact variable_loss_path_eq c w s v A hv hAv t
  have hn := normal_curvature_zero_of_path_minima J B (lossPairWeight c s)
    (lossPairLeft w) (lossPairRight w v) hleft hright
    (by rw [hpath _ (fun k => normal_map_teacher_zero J (v k) (hvJ k))]
        exact local_minimum_polar_path _ c w _ hw hmin)
    (fun a mu => by
      rw [hpath _ (fun k => shear_map_teacher_zero J B a mu (v k) (hvJ k))]
      exact local_minimum_polar_path _ c w _ hw hmin)
  rwa [hpath _ (fun k => normal_map_teacher_zero J (v k) (hvJ k))] at hn

end PaperLeanFormalization.ConfinementTraceAssembly

namespace PaperLeanFormalization.AmplitudeNormalVariation

open PairKernelJet NormalTrace ConfinementTraceAssembly

def amplitudeCurve (S T : ℝ → ℝ) (alpha beta t : ℝ) : ℝ :=
  (1+alpha*t)^2/2*S (beta*t)-(1+alpha*t)*T (beta*t)

def amplitudeSurface (S T : ℝ → ℝ) (a t : ℝ) : ℝ :=
  (1+a)^2/2*S t-(1+a)*T t

theorem amplitude_surface_mixed_derivative {S T : ℝ → ℝ} {S₁ T₁ : ℝ}
    (hS : HasDerivAt S S₁ 0) (hT : HasDerivAt T T₁ 0) :
    HasDerivAt (fun a => deriv (amplitudeSurface S T a) 0) (S₁-T₁) 0 := by
  have heq : (fun a => deriv (amplitudeSurface S T a) 0) =
      (fun a : ℝ => (1+a)^2/2*S₁-(1+a)*T₁) := by
    funext a
    exact ((hS.const_mul ((1+a)^2/2)).sub (hT.const_mul (1+a))).deriv
  rw [heq]
  have ha := (hasDerivAt_id (0 : ℝ)).const_add 1
  convert (((ha.pow 2).div_const 2).mul_const S₁).sub (ha.mul_const T₁) using 1
  simp only [id_eq]
  ring

/-- `eq:mixed-second-moment`: after normal stationarity the actual mixed
derivative is half the student's self-energy derivative. -/
theorem eq_mixed_second_moment {S T : ℝ → ℝ} {S₁ T₁ : ℝ}
    (hS : HasDerivAt S S₁ 0) (hT : HasDerivAt T T₁ 0) (hstat : S₁/2-T₁ = 0) :
    HasDerivAt (fun a => deriv (amplitudeSurface S T a) 0) (S₁/2) 0 := by
  convert amplitude_surface_mixed_derivative hS hT using 1
  linarith only [hstat]

/-- Differentiate the exact amplitude/normal identity using the already
proved normal-path jets. The mixed coefficient is `S' - T'`. -/
theorem amplitude_curve_jet {S T : ℝ → ℝ} {S₀ S₁ S₂ T₀ T₁ T₂ : ℝ}
    (hS : Jet S 0 S₀ S₁ S₂) (hT : Jet T 0 T₀ T₁ T₂) (alpha beta : ℝ) :
    Jet (amplitudeCurve S T alpha beta) 0 (S₀/2-T₀)
      (alpha*(S₀-T₀)+beta*(S₁/2-T₁))
      (alpha^2*S₀+2*alpha*beta*(S₁-T₁)+beta^2*(S₂/2-T₂)) := by
  have hb : Jet (fun t : ℝ => beta*t) 0 0 beta 0 := by
    convert (Jet.const 0 beta).mul (Jet.id 0) using 1 <;> ring
  have ha : Jet (fun t : ℝ => 1+alpha*t) 0 1 alpha 0 := by
    convert (Jet.const 0 1).add ((Jet.const 0 alpha).mul (Jet.id 0)) using 1 <;> ring
  have hs := (((Jet.const 0 (1/2)).mul (ha.mul ha)).mul (hS.comp hb))
  have ht := ((Jet.const 0 (-1)).mul ha).mul (hT.comp hb)
  convert hs.add ht using 1
  · funext t
    unfold amplitudeCurve
    ring
  all_goals ring

/-- A null normal mode of a positive-semidefinite two-variable quadratic
form has zero mixed coefficient; this is the scalar PSD-radical argument. -/
theorem psd_null_mixed (A C : ℝ)
    (hpsd : ∀ a b : ℝ, 0 ≤ a^2*A+2*a*b*C) : C = 0 := by
  have h := hpsd (2*C) (-(A+1))
  nlinarith only [h, sq_nonneg C]

/-- Normal stationarity and null normal curvature remove the teacher from
the mixed term. Hence the student's self-energy derivative must vanish. -/
theorem self_energy_derivative_zero {S T : ℝ → ℝ} {S₀ S₁ S₂ T₀ T₁ T₂ : ℝ}
    (hS : Jet S 0 S₀ S₁ S₂) (hT : Jet T 0 T₀ T₁ T₂)
    (hmin : ∀ a b : ℝ, IsLocalMin (amplitudeCurve S T a b) 0)
    (hnull : deriv (deriv (amplitudeCurve S T 0 1)) 0 = 0) : S₁ = 0 := by
  have hn := amplitude_curve_jet hS hT 0 1
  have hstat : S₁/2-T₁ = 0 := by
    simpa using (hmin 0 1).hasDerivAt_eq_zero hn.first
  have hsecond : S₂/2-T₂ = 0 := by
    simpa only [hn.second.deriv, zero_pow two_pos, zero_mul, zero_add, one_pow,
      one_mul, mul_zero] using hnull
  have hpsd (a b : ℝ) : 0 ≤ a^2*S₀+2*a*b*(S₁-T₁) := by
    have h := jet_second_nonneg (amplitude_curve_jet hS hT a b) (hmin a b)
    simpa only [hsecond, mul_zero, add_zero] using h
  have hC := psd_null_mixed S₀ (S₁-T₁) hpsd
  have hid := (eq_mixed_second_moment hS.first hT.first hstat).unique
    (amplitude_surface_mixed_derivative hS.first hT.first)
  rw [hC] at hid
  linarith only [hid]

def studentPairEnergy {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, c i*c j*pairPath (w i) (w j) A t

def teacherPairEnergy {d n m : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) : ℝ :=
  ∑ i, ∑ k, c i*s k*pairPath (w i) (v k) A t

theorem student_energy_jet {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (hw : ∀ i, ‖w i‖ = 1) :
    Jet (studentPairEnergy c w A) 0
      (∑ i, ∑ j, c i*c j*centeredKernel (inner (w i) (w j)))
      (∑ i, ∑ j, c i*c j*pairSlope (w i) (w j) A)
      (∑ i, ∑ j, c i*c j*pairCurvature (w i) (w j) A) := by
  convert weighted_pair_jet (fun ij : Fin n × Fin n => c ij.1*c ij.2)
    (fun ij => w ij.1) (fun ij => w ij.2) A (fun ij => hw ij.1) (fun ij => hw ij.2) using 1
  · funext t
    simp only [weightedPairPath, studentPairEnergy, Fintype.sum_prod_type]
  all_goals simp only [Fintype.sum_prod_type]

theorem teacher_energy_jet {d n m : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    Jet (teacherPairEnergy c w s v A) 0
      (∑ i, ∑ k, c i*s k*centeredKernel (inner (w i) (v k)))
      (∑ i, ∑ k, c i*s k*pairSlope (w i) (v k) A)
      (∑ i, ∑ k, c i*s k*pairCurvature (w i) (v k) A) := by
  convert weighted_pair_jet (fun ik : Fin n × Fin m => c ik.1*s ik.2)
    (fun ik => w ik.1) (fun ik => v ik.2) A (fun ik => hw ik.1) (fun ik => hv ik.2) using 1
  · funext t
    simp only [weightedPairPath, teacherPairEnergy, Fintype.sum_prod_type]
  all_goals simp only [Fintype.sum_prod_type]

theorem student_energy_eq_polar {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) :
    studentPairEnergy c w A t = ∑ i, ∑ j,
      (polarPath c w A t).1 i*(polarPath c w A t).1 j*
        centeredKernel (inner ((polarPath c w A t).2 i) ((polarPath c w A t).2 j)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [polarPath, normalized_inner, pairPath]
  ring

theorem teacher_energy_eq_polar {d n m : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hv : ∀ k, ‖v k‖ = 1) (hAv : ∀ k, A (v k) = 0) (t : ℝ) :
    teacherPairEnergy c w s v A t = ∑ i, ∑ k,
      (polarPath c w A t).1 i*s k*centeredKernel (inner ((polarPath c w A t).2 i) (v k)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [pairPath, polarPath, hAv, smul_zero, add_zero, hv, mul_one,
    real_inner_smul_left]
  rw [div_eq_mul_inv, mul_comm (inner _ _ : ℝ) (‖w i+t • A (w i)‖⁻¹)]
  ring

def massScale {d n : ℕ} (a : ℝ) (p : Parameters d n) : Parameters d n :=
  (fun i => a*p.1 i, p.2)

theorem loss_mass_scale {d n m : ℕ} (s : Fin m → ℝ) (v : Fin m → Vec d)
    (a : ℝ) (p : Parameters d n) :
    variableKernelLoss s v (massScale a p) =
      (a^2/2)*(∑ i, ∑ j, p.1 i*p.1 j*centeredKernel (inner (p.2 i) (p.2 j)))-
        a*(∑ i, ∑ k, p.1 i*s k*centeredKernel (inner (p.2 i) (v k))) := by
  simp only [variableKernelLoss, massScale, Finset.mul_sum]
  congr 1
  all_goals
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

def amplitudeParameterPath {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (alpha beta t : ℝ) : Parameters d n :=
  massScale (1+alpha*t) (polarPath c w A (beta*t))

/-- The two-parameter dependence is an exact
quadratic polynomial in the global amplitude. No differentiation under a
Gaussian integral is required for the mixed derivative. -/
theorem amplitude_loss_identity {d n m : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hv : ∀ k, ‖v k‖ = 1) (hAv : ∀ k, A (v k) = 0) (alpha beta t : ℝ) :
    variableKernelLoss s v (amplitudeParameterPath c w A alpha beta t) =
      amplitudeCurve (studentPairEnergy c w A) (teacherPairEnergy c w s v A) alpha beta t := by
  unfold amplitudeParameterPath amplitudeCurve
  rw [loss_mass_scale, student_energy_eq_polar, teacher_energy_eq_polar c w s v A hv hAv]

theorem local_minimum_amplitude_parameter_path {d n : ℕ} (L : Parameters d n → ℝ)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hw : ∀ i, ‖w i‖ = 1)
    (hmin : IsLocalMinOn L {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) (alpha beta : ℝ) :
    IsLocalMin (fun t => L (amplitudeParameterPath c w A alpha beta t)) 0 := by
  have hrow (i : Fin n) : Continuous (fun t : ℝ => w i+(beta*t) • A (w i)) :=
    continuous_const.add ((continuous_const.mul continuous_id).smul continuous_const)
  have hn (i : Fin n) : ‖w i+(beta*(0 : ℝ)) • A (w i)‖ ≠ 0 := by simp [hw]
  have hzero : amplitudeParameterPath c w A alpha beta 0 = (c,w) := by
    simp [amplitudeParameterPath, massScale, polarPath, hw]
  have hc : ContinuousAt (amplitudeParameterPath c w A alpha beta) 0 := by
    apply ContinuousAt.prod
    · apply continuousAt_pi.mpr
      exact fun i => (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).mul
        (continuousAt_const.mul (hrow i).norm.continuousAt)
    · apply continuousAt_pi.mpr
      exact fun i => ((hrow i).norm.continuousAt.inv₀ (hn i)).smul (hrow i).continuousAt
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, ‖w i+(beta*t) • A (w i)‖ ≠ 0 := by
    apply eventually_all.mpr
    intro i
    exact (hrow i).norm.continuousAt.eventually_ne (hn i)
  have ht : Tendsto (amplitudeParameterPath c w A alpha beta) (𝓝 0)
      (𝓝[{p : Parameters d n | ∀ i, ‖p.2 i‖ = 1}] (c,w)) := by
    apply tendsto_nhdsWithin_iff.mpr
    have hct : Tendsto (amplitudeParameterPath c w A alpha beta) (𝓝 0)
        (𝓝 (amplitudeParameterPath c w A alpha beta 0)) := hc
    refine ⟨by simpa only [hzero] using hct, ?_⟩
    filter_upwards [he] with t ht
    intro i
    exact norm_smul_inv_norm (norm_ne_zero_iff.mp (ht i))
  show ∀ᶠ t in 𝓝 (0 : ℝ),
    L (amplitudeParameterPath c w A alpha beta 0) ≤ L (amplitudeParameterPath c w A alpha beta t)
  rw [hzero]
  exact ht.eventually hmin

/-- The mixed-term conclusion at the actual centered loss, obtained from
the fresh trace and the amplitude identity. -/
theorem centered_self_energy_derivative_zero {d r n m : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (variableKernelLoss s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    deriv (studentPairEnergy c w (normalMap J)) 0 = 0 := by
  have hAv (k : Fin m) : normalMap J (v k) = 0 := normal_map_teacher_zero J (v k) (hvJ k)
  have heq (a b : ℝ) :
      (fun t => variableKernelLoss s v (amplitudeParameterPath c w (normalMap J) a b t)) =
        amplitudeCurve (studentPairEnergy c w (normalMap J))
          (teacherPairEnergy c w s v (normalMap J)) a b := by
    funext t
    exact amplitude_loss_identity c w s v (normalMap J) hv hAv a b t
  have hcurv := centered_normal_curvature_zero J B c w s v hw hv hvJ hmin
  have hN : deriv (deriv (amplitudeCurve (studentPairEnergy c w (normalMap J))
      (teacherPairEnergy c w s v (normalMap J)) 0 1)) 0 = 0 := by
    rw [← heq 0 1]
    simpa only [amplitudeParameterPath, zero_mul, add_zero, one_mul, massScale] using hcurv
  have hS := student_energy_jet c w (normalMap J) hw
  rw [hS.first.deriv]
  exact self_energy_derivative_zero hS (teacher_energy_jet c w s v (normalMap J) hw hv)
    (fun a b => by
      rw [← heq a b]
      exact local_minimum_amplitude_parameter_path _ c w _ hw hmin a b) hN

/-- The finite mixed energy displayed in `eq:mixed-term-formula`. -/
def mixedEnergy {d r n : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) : ℝ :=
  (∑ i, c i*‖normalPart J (w i)‖^2*
    ∑ j, c j*sqrt (1-(inner (w i) (w j) : ℝ)^2))+
  ∑ i, ∑ j, c i*c j*(inner (normalPart J (w i)) (normalPart J (w j)) : ℝ)*
    arcsin (inner (w i) (w j))

/-- `eq:second-moment-derivative`: differentiate each genuine pair path,
then use symmetry to combine the two radial contributions. -/
theorem eq_second_moment_derivative {d r n : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) :
    deriv (studentPairEnergy c w (normalMap J)) 0 = 2*mixedEnergy J c w := by
  let R := fun i j => sqrt (1-(inner (w i) (w j) : ℝ)^2)
  let N := fun i => ‖normalPart J (w i)‖^2
  let Z := fun i j =>
    (inner (normalPart J (w i)) (normalPart J (w j)) : ℝ)*arcsin (inner (w i) (w j))
  have hswap : (∑ i, ∑ j, c i*c j*R i j*N j) =
      ∑ i, ∑ j, c i*c j*R i j*N i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [R]
    rw [real_inner_comm (w j) (w i)]
    ring
  rw [(student_energy_jet c w (normalMap J) hw).first.deriv]
  have hexp : (∑ i, ∑ j, c i*c j*pairSlope (w i) (w j) (normalMap J)) =
      (∑ i, ∑ j, c i*c j*R i j*N i)+
      (∑ i, ∑ j, c i*c j*R i j*N j)+2*(∑ i, ∑ j, c i*c j*Z i j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(normal_pair_coefficients J (w i) (w j)).1]
    dsimp [pairFirst, R, N, Z]
    ring
  rw [hexp, hswap]
  have hrad : (∑ i, ∑ j, c i*c j*R i j*N i) =
      ∑ i, c i*‖normalPart J (w i)‖^2*∑ j, c j*sqrt (1-(inner (w i) (w j) : ℝ)^2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [R, N]
    ring
  rw [hrad]
  unfold mixedEnergy
  dsimp [Z]
  simp only [mul_assoc]
  ring

/-- The actual two-parameter loss has the mixed derivative from
`eq:mixed-second-moment`. The teacher disappears by normal stationarity. -/
theorem actual_mixed_derivative_eq_half_self_derivative {d r n m : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (variableKernelLoss s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    deriv (fun a => deriv (fun t => variableKernelLoss s v
      (massScale (1+a) (polarPath c w (normalMap J) t))) 0) 0 =
      deriv (studentPairEnergy c w (normalMap J)) 0/2 := by
  let S := studentPairEnergy c w (normalMap J)
  let T := teacherPairEnergy c w s v (normalMap J)
  have hAv (k : Fin m) : normalMap J (v k) = 0 := normal_map_teacher_zero J (v k) (hvJ k)
  have heq (a : ℝ) : (fun t => variableKernelLoss s v
      (massScale (1+a) (polarPath c w (normalMap J) t))) = amplitudeSurface S T a := by
    funext t
    unfold amplitudeSurface
    dsimp only [S, T]
    rw [loss_mass_scale, student_energy_eq_polar,
      teacher_energy_eq_polar c w s v (normalMap J) hv hAv]
  have hnormal : IsLocalMin (amplitudeSurface S T 0) 0 := by
    rw [← heq 0]
    simpa only [add_zero, massScale, one_mul] using
      local_minimum_polar_path (variableKernelLoss s v) c w (normalMap J) hw hmin
  have hS := student_energy_jet c w (normalMap J) hw
  have hT := teacher_energy_jet c w s v (normalMap J) hw hv
  have hstat :
      (∑ i, ∑ j, c i*c j*pairSlope (w i) (w j) (normalMap J))/2-
      (∑ i, ∑ k, c i*s k*pairSlope (w i) (v k) (normalMap J)) = 0 := by
    apply hnormal.hasDerivAt_eq_zero
    convert (hS.first.div_const 2).sub hT.first using 1
    funext t
    dsimp only [amplitudeSurface, S, T]
    ring
  have hmixed := eq_mixed_second_moment hS.first hT.first hstat
  have hf : (fun a => deriv (fun t => variableKernelLoss s v
      (massScale (1+a) (polarPath c w (normalMap J) t))) 0) =
      (fun a => deriv (amplitudeSurface S T a) 0) := by
    funext a
    rw [heq a]
  rw [hf, hS.first.deriv]
  exact hmixed.deriv

/-- `eq:mixed-term-formula`: the actual amplitude/normal mixed derivative
equals the displayed finite mixed energy. This is the kernel normalization
`2π ℒ`, so no extra Gaussian normalization factor occurs on the right. -/
theorem eq_mixed_term_formula {d r n m : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (variableKernelLoss s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    deriv (fun a => deriv (fun t => variableKernelLoss s v
      (massScale (1+a) (polarPath c w (normalMap J) t))) 0) 0 = mixedEnergy J c w := by
  rw [actual_mixed_derivative_eq_half_self_derivative J c w s v hw hv hvJ hmin,
    eq_second_moment_derivative J c w hw]
  ring

/-- The finite mixed energy vanishes at the actual centered local minimum.
Combining this with its fresh strict positivity yields confinement. -/
theorem centered_mixed_energy_zero {d r n m : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (variableKernelLoss s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    mixedEnergy J c w = 0 := by

  have hactual : deriv (fun a => deriv (fun t => variableKernelLoss s v
      (massScale (1+a) (polarPath c w (normalMap J) t))) 0) 0 = 0 := by
    rw [actual_mixed_derivative_eq_half_self_derivative J c w s v hw hv hvJ hmin,
      centered_self_energy_derivative_zero J B c w s v hw hv hvJ hmin]
    norm_num
  exact (eq_mixed_term_formula J c w s v hw hv hvJ hmin).symm.trans hactual

end PaperLeanFormalization.AmplitudeNormalVariation

namespace PaperLeanFormalization.PlainConfinementVariation

open PairKernelJet NormalTrace ConfinementTraceAssembly AmplitudeNormalVariation

def moment {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d) : Vec d :=
  ∑ i, c i • w i

/-- `lambda = π/2` is the plain ReLU kernel. This definition exposes the
entire extra first-moment polynomial, including the signed teacher moment. -/
def plainVariableLoss {d n m : ℕ} (lambda : ℝ) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (p : Parameters d n) : ℝ :=
  variableKernelLoss s v p + lambda/2*‖moment p.1 p.2‖^2-
    lambda*(inner (moment p.1 p.2) (moment s v) : ℝ)

theorem moment_inner {d n m : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) :
    (inner (moment c w) (moment s v) : ℝ) = ∑ i, ∑ k, c i*s k*inner (w i) (v k) := by
  simp only [moment, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem kernel_offset_sum {ι : Type*} [Fintype ι]
    (lambda : ℝ) (weight rho : ι → ℝ) :
    (∑ i, weight i*(centeredKernel (rho i)+lambda*rho i)) =
      (∑ i, weight i*centeredKernel (rho i))+lambda*∑ i, weight i*rho i := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The first-moment polynomial is exactly the variable loss for the scalar
kernel `K(rho) + lambda*rho`, not a surrogate objective. -/
theorem plain_loss_kernel_form {d n m : ℕ} (lambda : ℝ) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (p : Parameters d n) :
    plainVariableLoss lambda s v p =
      (1/2)*(∑ i, ∑ j, p.1 i*p.1 j*(centeredKernel (inner (p.2 i) (p.2 j))+
        lambda*inner (p.2 i) (p.2 j)))-
      ∑ i, ∑ k, p.1 i*s k*(centeredKernel (inner (p.2 i) (v k))+lambda*inner (p.2 i) (v k)) := by
  have hss := kernel_offset_sum lambda (fun ij : Fin n × Fin n => p.1 ij.1*p.1 ij.2)
    (fun ij => (inner (p.2 ij.1) (p.2 ij.2) : ℝ))
  have hst := kernel_offset_sum lambda (fun ik : Fin n × Fin m => p.1 ik.1*s ik.2)
    (fun ik => (inner (p.2 ik.1) (v ik.2) : ℝ))
  simp only [Fintype.sum_prod_type] at hss hst
  unfold plainVariableLoss variableKernelLoss
  rw [← real_inner_self_eq_norm_sq (moment p.1 p.2), moment_inner, moment_inner, hss, hst]
  ring

theorem moment_mass_scale {d n : ℕ} (a : ℝ) (p : Parameters d n) :
    moment (massScale a p).1 (massScale a p).2 = a • moment p.1 p.2 := by
  simp only [moment, massScale, Finset.smul_sum, mul_smul]

theorem moment_polar_path {d n : ℕ} (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) :
    moment (polarPath c w A t).1 (polarPath c w A t).2 =
      moment c w+t • A (moment c w) := by
  have hn (x : Vec d) : ‖x‖ • (‖x‖⁻¹ • x) = x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [smul_smul, mul_inv_cancel (norm_ne_zero_iff.mpr hx), one_smul]
  change (∑ i, (c i*‖w i+t • A (w i)‖) •
    (‖w i+t • A (w i)‖⁻¹ • (w i+t • A (w i)))) = _
  calc
    _ = ∑ i, c i • (w i+t • A (w i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_smul, hn]
    _ = _ := by
      simp only [moment, smul_add, Finset.sum_add_distrib,
        map_sum, map_smul, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_comm]

theorem moment_teacher_map_zero {d m : ℕ} (s : Fin m → ℝ) (v : Fin m → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (hAv : ∀ k, A (v k) = 0) : A (moment s v) = 0 := by
  simp only [moment, map_sum, map_smul, hAv, smul_zero, Finset.sum_const_zero]

theorem norm_square_affine_jet {d : ℕ} (x h : Vec d) :
    Jet (fun t : ℝ => ‖x+t • h‖^2) 0 (‖x‖^2) (2*inner x h) (2*‖h‖^2) := by
  have heq : (fun t : ℝ => ‖x+t • h‖^2) =
      (fun t : ℝ => ‖x‖^2+(2*inner x h)*t+‖h‖^2*t*t) := by
    funext t
    rw [← real_inner_self_eq_norm_sq, inner_path]
    simp only [real_inner_self_eq_norm_sq, real_inner_comm h x]
    ring
  rw [heq]
  exact quadratic_jet _ _ _

theorem inner_affine_jet {d : ℕ} (x h y : Vec d) :
    Jet (fun t : ℝ => (inner (x+t • h) y : ℝ)) 0 (inner x y) (inner h y) 0 := by
  convert quadratic_jet (inner x y) (inner h y) 0 using 1
  · funext t
    simp only [inner_add_left, real_inner_smul_left]
    ring
  · ring

def correctionPath {d : ℕ} (lambda : ℝ) (M T : Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (t : ℝ) : ℝ := lambda/2*‖M+t • A M‖^2-lambda*(inner (M+t • A M) T : ℝ)

theorem correction_path_jet {d : ℕ} (lambda : ℝ) (M T : Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) :
    Jet (correctionPath lambda M T A) 0 (lambda/2*‖M‖^2-lambda*inner M T)
      (lambda*(inner M (A M)-inner (A M) T)) (lambda*‖A M‖^2) := by
  convert ((Jet.const 0 (lambda/2)).mul (norm_square_affine_jet M (A M))).add
    ((Jet.const 0 (-lambda)).mul (inner_affine_jet M (A M) T)) using 1
  · funext t
    unfold correctionPath
    ring
  all_goals ring

theorem shear_norm_trace {d r : ℕ} (J : Vec r →ₗᵢ[ℝ] Vec d)
    (B : OrthonormalBasis (Fin d) ℝ (Vec d)) (M : Vec d) :
    (∑ a, ∑ mu, ‖shearMap J B a mu M‖^2) = (r : ℝ)*‖normalMap J M‖^2 := by
  have haxis (a : Fin r) : (∑ mu, ‖shearMap J B a mu M‖^2) = ‖normalMap J M‖^2 := by
    have hB := B.sum_inner_mul_inner (normalPart J M) (normalPart J M)
    simp only [← pow_two, real_inner_self_eq_norm_sq] at hB
    change (∑ mu, ‖shearMap J B a mu M‖^2) = ‖normalPart J M‖^2
    rw [← hB]
    apply Finset.sum_congr rfl
    intro mu _
    simp only [shearMap, LinearMap.coe_mk, AddHom.coe_mk, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, (frame_orthonormal J).1 a, one_pow, mul_one]
    rw [real_inner_comm]
    ring
  simp only [haxis, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `eq:plain-correction-trace`: the normal first and second derivatives,
the fixed-normal additive amplitude mixed derivative, and the shear trace of
the plain quadratic correction. The teacher-only constant has no derivatives.
The displayed manuscript normalization is `lambda = π / 2`. -/
theorem eq_plain_correction_trace {d r : ℕ} (lambda : ℝ)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (M T : Vec d) (hNT : normalMap J T = 0) :
    deriv (correctionPath lambda M T (normalMap J)) 0 = lambda * ‖normalMap J M‖^2 ∧
    deriv (deriv (correctionPath lambda M T (normalMap J))) 0 =
      lambda * ‖normalMap J M‖^2 ∧
    HasDerivAt (fun a : ℝ => deriv (fun t : ℝ =>
      lambda/2 * ‖(1+a) • M + t • normalMap J M‖^2 -
        lambda * (inner ((1+a) • M + t • normalMap J M) T : ℝ)) 0)
      (lambda * ‖normalMap J M‖^2) 0 ∧
    (∑ a, ∑ mu, deriv (deriv (correctionPath lambda M T (shearMap J B a mu))) 0) =
      lambda * ∑ a : Fin r, ∑ mu : Fin d, (inner (B mu) (normalMap J M) : ℝ)^2 ∧
    (lambda * ∑ a : Fin r, ∑ mu : Fin d, (inner (B mu) (normalMap J M) : ℝ)^2) =
      lambda * (r : ℝ) * ‖normalMap J M‖^2 := by
  have hMM : (inner M (normalMap J M) : ℝ) = ‖normalMap J M‖^2 := by
    change inner M (normalPart J M) = ‖normalMap J M‖^2
    rw [normal_inner, real_inner_self_eq_norm_sq]
    rfl
  have hMT : (inner (normalMap J M) T : ℝ) = 0 := by
    change inner (normalPart J M) T = 0
    rw [normal_inner_left]
    change inner (normalPart J M) (normalMap J T) = 0
    rw [hNT, inner_zero_right]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [(correction_path_jet lambda M T (normalMap J)).first.deriv, hMM, hMT, sub_zero]
  · exact (correction_path_jet lambda M T (normalMap J)).second.deriv
  · have heq : (fun a : ℝ => deriv (fun t : ℝ =>
        lambda/2 * ‖(1+a) • M + t • normalMap J M‖^2 -
          lambda * (inner ((1+a) • M + t • normalMap J M) T : ℝ)) 0) =
        (fun a : ℝ => lambda * ‖normalMap J M‖^2 * (1+a)) := by
      funext a
      have hn := (norm_square_affine_jet ((1+a) • M) (normalMap J M)).first
      have hi := (inner_affine_jet ((1+a) • M) (normalMap J M) T).first
      rw [((hn.const_mul (lambda/2)).sub (hi.const_mul lambda)).deriv]
      simp only [real_inner_smul_left, hMM, hMT]
      ring
    rw [heq]
    convert ((hasDerivAt_id (0 : ℝ)).const_add 1).const_mul
      (lambda * ‖normalMap J M‖^2) using 1
    ring
  · simp_rw [(correction_path_jet lambda M T _).second.deriv]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro mu _
    simp only [shearMap, LinearMap.coe_mk, AddHom.coe_mk, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, (frame_orthonormal J).1 a, one_pow, mul_one]
    rfl
  · have hB := B.sum_inner_mul_inner (normalMap J M) (normalMap J M)
    have hB' : (∑ mu : Fin d, (inner (B mu) (normalMap J M) : ℝ)^2) =
        ‖normalMap J M‖^2 := by
      rw [← real_inner_self_eq_norm_sq, ← hB]
      apply Finset.sum_congr rfl
      intro mu _
      rw [real_inner_comm (normalMap J M) (B mu)]
      ring
    simp_rw [hB']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem correction_trace {d r : ℕ} (lambda : ℝ)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (M T : Vec d) (hNT : normalMap J T = 0) :
    (∑ a, ∑ mu, lambda*‖shearMap J B a mu M‖^2)+lambda*‖normalMap J M‖^2 =
      ((r : ℝ)+1)*(lambda*(inner M (normalMap J M)-inner (normalMap J M) T)) := by
  obtain ⟨hfirst, _, _, hshear, hsum⟩ := eq_plain_correction_trace lambda J B M T hNT
  simp_rw [(correction_path_jet lambda M T _).second.deriv] at hshear
  rw [(correction_path_jet lambda M T _).first.deriv] at hfirst
  rw [hshear, hsum, hfirst]
  ring

def plainPath {d n m : ℕ} (lambda : ℝ) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) : ℝ :=
  plainVariableLoss lambda s v (polarPath c w A t)

theorem plain_path_eq {d n m : ℕ} (lambda : ℝ) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hv : ∀ k, ‖v k‖ = 1) (hAv : ∀ k, A (v k) = 0) (t : ℝ) :
    plainPath lambda c w s v A t =
      weightedPairPath (lossPairWeight c s) (lossPairLeft w) (lossPairRight w v) A t+
        correctionPath lambda (moment c w) (moment s v) A t := by
  rw [variable_loss_path_eq c w s v A hv hAv]
  unfold plainPath plainVariableLoss correctionPath
  rw [moment_polar_path]
  ring

theorem plain_path_jet {d n m : ℕ} (lambda : ℝ) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hAv : ∀ k, A (v k) = 0) :
    Jet (plainPath lambda c w s v A) 0
      ((∑ i, lossPairWeight c s i*centeredKernel (inner (lossPairLeft w i) (lossPairRight w v i)))+
        (lambda/2*‖moment c w‖^2-lambda*inner (moment c w) (moment s v)))
      ((∑ i, lossPairWeight c s i*pairSlope (lossPairLeft w i) (lossPairRight w v i) A)+
        lambda*(inner (moment c w) (A (moment c w))-inner (A (moment c w)) (moment s v)))
      ((∑ i, lossPairWeight c s i*pairCurvature (lossPairLeft w i) (lossPairRight w v i) A)+
        lambda*‖A (moment c w)‖^2) := by
  have hleft (i : LossPairIndex n m) : ‖lossPairLeft w i‖ = 1 := by
    cases i with | inl ij => exact hw ij.1 | inr ik => exact hw ik.1
  have hright (i : LossPairIndex n m) : ‖lossPairRight w v i‖ = 1 := by
    cases i with | inl ij => exact hw ij.2 | inr ik => exact hv ik.2
  apply Jet.congr ((weighted_pair_jet (lossPairWeight c s) (lossPairLeft w)
    (lossPairRight w v) A hleft hright).add (correction_path_jet lambda (moment c w) (moment s v) A))
  funext t
  exact (plain_path_eq lambda c w s v A hv hAv t).symm

/-- The plain trace is the centered trace plus the first-moment polynomial
trace. It concerns actual derivatives of the plain loss curve. -/
theorem plain_global_trace {d r n m : ℕ} (lambda : ℝ)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J) :
    (∑ a, ∑ mu, deriv (deriv (plainPath lambda c w s v (shearMap J B a mu))) 0)+
        deriv (deriv (plainPath lambda c w s v (normalMap J))) 0 =
      ((r : ℝ)+1)*deriv (plainPath lambda c w s v (normalMap J)) 0 := by
  have hN (k : Fin m) := normal_map_teacher_zero J (v k) (hvJ k)
  have hS (a : Fin r) (mu : Fin d) (k : Fin m) := shear_map_teacher_zero J B a mu (v k) (hvJ k)
  have hleft (i : LossPairIndex n m) : ‖lossPairLeft w i‖ = 1 := by
    cases i with | inl ij => exact hw ij.1 | inr ik => exact hw ik.1
  have hright (i : LossPairIndex n m) : ‖lossPairRight w v i‖ = 1 := by
    cases i with | inl ij => exact hw ij.2 | inr ik => exact hv ik.2
  have hc := eq_global_trace J B (lossPairWeight c s) (lossPairLeft w) (lossPairRight w v)
    hleft hright
  have hsecond (A : Vec d →ₗ[ℝ] Vec d) :=
    (weighted_pair_jet (lossPairWeight c s) (lossPairLeft w) (lossPairRight w v) A hleft hright).second.deriv
  have hfirst (A : Vec d →ₗ[ℝ] Vec d) :=
    (weighted_pair_jet (lossPairWeight c s) (lossPairLeft w) (lossPairRight w v) A hleft hright).first.deriv
  simp_rw [hsecond, hfirst] at hc
  have hcorr := correction_trace lambda J B (moment c w) (moment s v)
    (moment_teacher_map_zero s v (normalMap J) hN)
  rw [(plain_path_jet lambda c w s v (normalMap J) hw hv hN).second.deriv,
    (plain_path_jet lambda c w s v (normalMap J) hw hv hN).first.deriv]
  have hs (a : Fin r) (mu : Fin d) :=
    (plain_path_jet lambda c w s v (shearMap J B a mu) hw hv (hS a mu)).second.deriv
  simp_rw [hs]
  simp only [Finset.sum_add_distrib]
  linear_combination hc+hcorr

theorem plain_normal_curvature_zero {d r n m : ℕ} (lambda : ℝ)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (plainVariableLoss lambda s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    deriv (deriv (plainPath lambda c w s v (normalMap J))) 0 = 0 := by
  have hlocal (A : Vec d →ₗ[ℝ] Vec d) : IsLocalMin (plainPath lambda c w s v A) 0 :=
    local_minimum_polar_path _ c w A hw hmin
  have hnonneg (A : Vec d →ₗ[ℝ] Vec d) (hAv : ∀ k, A (v k) = 0) :
      0 ≤ deriv (deriv (plainPath lambda c w s v A)) 0 := by
    rw [(plain_path_jet lambda c w s v A hw hv hAv).second.deriv]
    exact jet_second_nonneg (plain_path_jet lambda c w s v A hw hv hAv) (hlocal A)
  have hn := hnonneg (normalMap J) (fun k => normal_map_teacher_zero J (v k) (hvJ k))
  have hs : 0 ≤ ∑ a, ∑ mu, deriv (deriv (plainPath lambda c w s v (shearMap J B a mu))) 0 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun mu _ =>
      hnonneg _ (fun k => shear_map_teacher_zero J B a mu (v k) (hvJ k))
  have ht := plain_global_trace lambda J B c w s v hw hv hvJ
  rw [(hlocal (normalMap J)).deriv_eq_zero, mul_zero] at ht
  linarith only [ht, hn, hs]

def plainStudentEnergy {d n : ℕ} (lambda : ℝ) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) : ℝ :=
  studentPairEnergy c w A t+lambda*‖moment c w+t • A (moment c w)‖^2

def plainTeacherEnergy {d n m : ℕ} (lambda : ℝ) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) : ℝ :=
  teacherPairEnergy c w s v A t+lambda*(inner (moment c w+t • A (moment c w)) (moment s v) : ℝ)

theorem plain_student_energy_jet {d n : ℕ} (lambda : ℝ) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (hw : ∀ i, ‖w i‖ = 1) :
    Jet (plainStudentEnergy lambda c w A) 0
      ((∑ i, ∑ j, c i*c j*centeredKernel (inner (w i) (w j)))+lambda*‖moment c w‖^2)
      ((∑ i, ∑ j, c i*c j*pairSlope (w i) (w j) A)+2*lambda*inner (moment c w) (A (moment c w)))
      ((∑ i, ∑ j, c i*c j*pairCurvature (w i) (w j) A)+2*lambda*‖A (moment c w)‖^2) := by
  convert (student_energy_jet c w A hw).add
    ((Jet.const 0 lambda).mul (norm_square_affine_jet (moment c w) (A (moment c w))))
    using 1 <;> ring

theorem plain_teacher_energy_jet {d n m : ℕ} (lambda : ℝ) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    Jet (plainTeacherEnergy lambda c w s v A) 0
      ((∑ i, ∑ k, c i*s k*centeredKernel (inner (w i) (v k)))+lambda*inner (moment c w) (moment s v))
      ((∑ i, ∑ k, c i*s k*pairSlope (w i) (v k) A)+lambda*inner (A (moment c w)) (moment s v))
      (∑ i, ∑ k, c i*s k*pairCurvature (w i) (v k) A) := by
  convert (teacher_energy_jet c w s v A hw hv).add
    ((Jet.const 0 lambda).mul (inner_affine_jet (moment c w) (A (moment c w)) (moment s v)))
    using 1 <;> ring

theorem plain_amplitude_identity {d n m : ℕ} (lambda : ℝ)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) (hv : ∀ k, ‖v k‖ = 1) (hAv : ∀ k, A (v k) = 0)
    (alpha beta t : ℝ) :
    plainVariableLoss lambda s v (amplitudeParameterPath c w A alpha beta t) =
      amplitudeCurve (plainStudentEnergy lambda c w A) (plainTeacherEnergy lambda c w s v A)
        alpha beta t := by
  unfold plainVariableLoss
  rw [amplitude_loss_identity c w s v A hv hAv alpha beta t]
  unfold amplitudeParameterPath
  rw [moment_mass_scale, moment_polar_path]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left]
  unfold amplitudeCurve plainStudentEnergy plainTeacherEnergy
  ring

theorem plain_self_energy_derivative_zero {d r n m : ℕ} (lambda : ℝ)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (plainVariableLoss lambda s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    deriv (plainStudentEnergy lambda c w (normalMap J)) 0 = 0 := by
  have hAv (k : Fin m) : normalMap J (v k) = 0 := normal_map_teacher_zero J (v k) (hvJ k)
  have heq (a b : ℝ) :
      (fun t => plainVariableLoss lambda s v (amplitudeParameterPath c w (normalMap J) a b t)) =
        amplitudeCurve (plainStudentEnergy lambda c w (normalMap J))
          (plainTeacherEnergy lambda c w s v (normalMap J)) a b := by
    funext t
    exact plain_amplitude_identity lambda c w s v (normalMap J) hv hAv a b t
  have hcurv := plain_normal_curvature_zero lambda J B c w s v hw hv hvJ hmin
  have hN : deriv (deriv (amplitudeCurve (plainStudentEnergy lambda c w (normalMap J))
      (plainTeacherEnergy lambda c w s v (normalMap J)) 0 1)) 0 = 0 := by
    rw [← heq 0 1]
    simpa only [plainPath, amplitudeParameterPath, zero_mul, add_zero, one_mul, massScale] using hcurv
  have hS := plain_student_energy_jet lambda c w (normalMap J) hw
  rw [hS.first.deriv]
  exact self_energy_derivative_zero hS (plain_teacher_energy_jet lambda c w s v (normalMap J) hw hv)
    (fun a b => by
      rw [← heq a b]
      exact local_minimum_amplitude_parameter_path _ c w _ hw hmin a b) hN

theorem offset_mixed_energy_zero {d r n m : ℕ} (lambda : ℝ)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (plainVariableLoss lambda s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    mixedEnergy J c w+lambda*‖∑ i, c i • normalPart J (w i)‖^2 = 0 := by
  have hz := plain_self_energy_derivative_zero lambda J B c w s v hw hv hvJ hmin
  rw [(plain_student_energy_jet lambda c w (normalMap J) hw).first.deriv,
    ← (student_energy_jet c w (normalMap J) hw).first.deriv,
    eq_second_moment_derivative J c w hw] at hz
  -- The preceding amplitude argument uses stationarity of the total loss.
  -- Identify its remaining plain correction through the fixed-normal mixed
  -- derivative, rather than recomputing the orthogonal-projection inner product.
  have hNT : normalMap J (moment s v) = 0 := by
    simp only [moment, map_sum, SMulHomClass.map_smul]
    apply Finset.sum_eq_zero
    intro k _
    rw [normal_map_teacher_zero J (v k) (hvJ k), smul_zero]
  obtain ⟨_, _, hMixed, _, _⟩ :=
    eq_plain_correction_trace lambda J B (moment c w) (moment s v) hNT
  have hRaw : HasDerivAt (fun a : ℝ => deriv (fun t : ℝ =>
      lambda/2 * ‖(1+a) • moment c w + t • normalMap J (moment c w)‖^2 -
        lambda * (inner ((1+a) • moment c w + t • normalMap J (moment c w))
          (moment s v) : ℝ)) 0)
      (lambda * inner (moment c w) (normalMap J (moment c w))) 0 := by
    have heq : (fun a : ℝ => deriv (fun t : ℝ =>
        lambda/2 * ‖(1+a) • moment c w + t • normalMap J (moment c w)‖^2 -
          lambda * (inner ((1+a) • moment c w + t • normalMap J (moment c w))
            (moment s v) : ℝ)) 0) =
        (fun a : ℝ =>
          lambda * inner (moment c w) (normalMap J (moment c w)) * (1+a) -
            lambda * inner (normalMap J (moment c w)) (moment s v)) := by
      funext a
      have hn := (norm_square_affine_jet ((1+a) • moment c w)
        (normalMap J (moment c w))).first
      have hi := (inner_affine_jet ((1+a) • moment c w)
        (normalMap J (moment c w)) (moment s v)).first
      rw [((hn.const_mul (lambda/2)).sub (hi.const_mul lambda)).deriv]
      simp only [real_inner_smul_left]
      ring
    rw [heq]
    convert ((((hasDerivAt_id (0 : ℝ)).const_add 1).const_mul
      (lambda * inner (moment c w) (normalMap J (moment c w)))).sub_const
        (lambda * inner (normalMap J (moment c w)) (moment s v))) using 1
    ring
  have hMM := hRaw.unique hMixed
  rw [mul_assoc 2 lambda, hMM] at hz
  have hNM : normalMap J (moment c w) = ∑ i, c i • normalPart J (w i) := by
    simp only [moment, map_sum, SMulHomClass.map_smul]
    rfl
  rw [hNM] at hz
  linarith only [hz]

/-- For plain ReLU, the extra mixed energy is precisely the nonnegative
`(π/2)` times the squared normal first moment from the manuscript. -/
theorem plain_mixed_energy_zero {d r n m : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (plainVariableLoss (π/2) s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    mixedEnergy J c w+(π/2)*‖∑ i, c i • normalPart J (w i)‖^2 = 0 :=
  offset_mixed_energy_zero (π/2) J B c w s v hw hv hvJ hmin


end PaperLeanFormalization.PlainConfinementVariation

namespace PaperLeanFormalization.FinitePlane

open FiniteDimensional

/-- Extend an orthonormal basis of the given small subspace, then retain the
first two basis vectors. This works uniformly for subspace dimensions zero,
one, and two. -/
theorem exists_isometricPlane_containing_rankLeTwo_submodule {d : ℕ}
    (hd : 2 ≤ d) (S : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hr : finrank ℝ S ≤ 2) :
    ∃ J : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      ∀ x ∈ S, x ∈ Set.range J := by
  classical
  let r := finrank ℝ S
  let bs := stdOrthonormalBasis ℝ S
  let s : Set (Fin d) := {i | i.val < r}
  let v : Fin d → EuclideanSpace ℝ (Fin d) :=
    fun i => if hi : i.val < r then (bs ⟨i.val, hi⟩ : EuclideanSpace ℝ (Fin d)) else 0
  let e : s → Fin r := fun i => ⟨i.val.val, i.property⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (Fin.val : Fin r → ℕ) hij
  have hv : Orthonormal ℝ (s.restrict v) := by
    have h := (bs.orthonormal.comp_linearIsometry S.subtypeₗᵢ).comp e he
    convert h using 1
    funext i
    change (if hi : i.val.val < r then
      (bs ⟨i.val.val, hi⟩ : EuclideanSpace ℝ (Fin d)) else 0) = (bs (e i) : EuclideanSpace ℝ (Fin d))
    rw [dif_pos (show i.val.val < r from i.property)]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : finrank ℝ (EuclideanSpace ℝ (Fin d)) = Fintype.card (Fin d))
  let b₂ := EuclideanSpace.basisFun (Fin 2) ℝ
  let f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    b₂.toBasis.constr ℝ (fun i => b (Fin.castLE hd i))
  have hcast : Function.Injective (Fin.castLE hd) := by
    intro i j hij
    exact Fin.ext (congrArg (Fin.val : Fin d → ℕ) hij)
  have hf : Orthonormal ℝ (f ∘ b₂.toBasis) := by
    have h := b.orthonormal.comp (Fin.castLE hd) hcast
    convert h using 1
    funext i
    exact b₂.toBasis.constr_basis ℝ _ i
  let J := f.isometryOfOrthonormal (v := b₂.toBasis) b₂.orthonormal hf
  have hJ (i : Fin 2) : J (b₂ i) = b (Fin.castLE hd i) :=
    b₂.toBasis.constr_basis ℝ _ i
  have hmem (i : Fin r) : (bs i : EuclideanSpace ℝ (Fin d)) ∈ LinearMap.range J.toLinearMap := by
    refine ⟨b₂ (Fin.castLE hr i), ?_⟩
    change J (b₂ (Fin.castLE hr i)) = _
    have hprefix : Fin.castLE hd (Fin.castLE hr i) ∈ s := i.isLt
    rw [hJ, hb _ hprefix]
    simp only [v, Fin.coe_castLE, dif_pos i.isLt]
  refine ⟨J, fun x hx => ?_⟩
  have hs : (∑ i : Fin r, bs.repr ⟨x, hx⟩ i • (bs i : EuclideanSpace ℝ (Fin d))) ∈
      LinearMap.range J.toLinearMap :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hmem i))
  have heq := congrArg (fun y : S => (y : EuclideanSpace ℝ (Fin d)))
    (bs.sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at heq
  rw [heq] at hs
  exact hs

/-- The usual cosine--sine parametrization covers the entire unit circle. -/
theorem exists_angle_of_norm_eq_one {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ = 1) :
    ∃ θ : ℝ, (![Real.cos θ, Real.sin θ] : EuclideanSpace ℝ (Fin 2)) = w := by
  let z : ℂ := ⟨w 0, w 1⟩
  have hunit : w 0 ^ 2 + w 1 ^ 2 = 1 := by
    have h := real_inner_self_eq_norm_sq w
    rw [PiLp.inner_apply, Fin.sum_univ_two, hw] at h
    change w 0*w 0+w 1*w 1=(1:ℝ)^2 at h
    nlinarith only [h]
  have hz : Complex.abs z = 1 := by
    have hh : Complex.abs z ^ 2 = 1 := by
      rw [Complex.sq_abs]
      change w 0*w 0+w 1*w 1=1
      nlinarith only [hunit]
    nlinarith only [hh, Complex.abs.nonneg z]
  refine ⟨Complex.arg z, ?_⟩
  funext i
  fin_cases i
  · change Real.cos (Complex.arg z) = w 0
    simpa only [hz, one_mul] using Complex.abs_mul_cos_arg z
  · change Real.sin (Complex.arg z) = w 1
    simpa only [hz, one_mul] using Complex.abs_mul_sin_arg z

theorem continuous_circle :
    Continuous (fun θ : ℝ => (![Real.cos θ, Real.sin θ] : EuclideanSpace ℝ (Fin 2))) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Real.continuous_cos
  · exact Real.continuous_sin

end PaperLeanFormalization.FinitePlane


namespace PaperLeanFormalization.SecondMomentPair

open MeasureTheory PairKernelJet ConfinementTraceAssembly AmplitudeNormalVariation

theorem norm_normalize {d : ℕ} (w : Vec d) : ‖w‖ • (‖w‖⁻¹ • w) = w := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [smul_smul, mul_inv_cancel (norm_ne_zero_iff.mpr hw), one_smul]

theorem centered_feature_normalize {d : ℕ} (w x : Vec d) :
    |(inner w x : ℝ)|/2 = ‖w‖*(|(inner (‖w‖⁻¹ • w) x : ℝ)|/2) := by
  have h : (inner w x : ℝ) = ‖w‖*inner (‖w‖⁻¹ • w) x := by
    rw [← real_inner_smul_left, norm_normalize]
  rw [h, abs_mul, abs_of_nonneg (norm_nonneg w)]
  ring

/-- The two-feature moment for arbitrary raw rows. Vanishing rows are
handled explicitly, so normalization has no hidden nonzero hypothesis. -/
theorem raw_centered_pair_moment {d : ℕ} (hd : 2 ≤ d) (w v : Vec d) :
    (∫ x : Vec d, (|(inner w x : ℝ)|/2)*(|(inner v x : ℝ)|/2)*stdGaussianDensity x) =
      (1/(2*π))*(‖w‖*‖v‖*centeredKernel ((inner w v : ℝ)/(‖w‖*‖v‖))) := by
  by_cases hw : w = 0
  · simp [hw]
  by_cases hv : v = 0
  · simp [hv]
  let u := ‖w‖⁻¹ • w
  let z := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hw
  have hz : ‖z‖ = 1 := norm_smul_inv_norm hv
  have hscale : (∫ x : Vec d,
      (|(inner w x : ℝ)|/2)*(|(inner v x : ℝ)|/2)*stdGaussianDensity x) =
      (‖w‖*‖v‖)*(∫ x : Vec d, (|(inner u x : ℝ)|/2)*(|(inner z x : ℝ)|/2)*stdGaussianDensity x) := by
    rw [← integral_mul_left]
    congr 1
    funext x
    rw [centered_feature_normalize w x, centered_feature_normalize v x]
    dsimp only [u, z]
    ring
  rw [hscale, Preliminaries.centered_feature_pair_moment hd u z hu hz]
  change (‖w‖*‖v‖)*((1/(2*π))*centeredKernel (inner u z)) = _
  dsimp only [u, z]
  rw [normalized_inner]
  ring

/-- `eq:second-moment-pair`: literal Gaussian expectation of the squared
centered network. Arbitrary signed weights and zero raw generators are allowed.
Taking every weight equal to one gives the generator display in the paper. -/
theorem eq_second_moment_pair {d : ℕ} {ι : Type*} [Fintype ι] (hd : 2 ≤ d)
    (c : ι → ℝ) (V : ι → Vec d) :
    (2*π)*(∫ x : Vec d,
      (∑ i, c i*(|(inner (V i) x : ℝ)|/2))^2*stdGaussianDensity x) =
      ∑ i, ∑ j, c i*c j*‖V i‖*‖V j‖*
        centeredKernel ((inner (V i) (V j) : ℝ)/(‖V i‖*‖V j‖)) := by
  have h := Preliminaries.weighted_square_integral volume
    (fun (w x : Vec d) => |(inner w x : ℝ)|/2) stdGaussianDensity c V
    (fun w v => ‖w‖*‖v‖*centeredKernel ((inner w v : ℝ)/(‖w‖*‖v‖))) (1/(2*π))
    (fun i j => Preliminaries.centered_feature_pair_integrable hd (V i) (V j))
    (fun i j => raw_centered_pair_moment hd (V i) (V j))
  rw [h]
  have hcancel : (2*π)*(1/(2*π)) = 1 := by field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hcancel, one_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem unit_second_moment_pair {d : ℕ} {ι : Type*} [Fintype ι] (hd : 2 ≤ d)
    (c : ι → ℝ) (w : ι → Vec d) (hw : ∀ i, ‖w i‖ = 1) :
    (2*π)*(∫ x : Vec d,
      (∑ i, c i*(|(inner (w i) x : ℝ)|/2))^2*stdGaussianDensity x) =
      ∑ i, ∑ j, c i*c j*centeredKernel (inner (w i) (w j)) := by
  simpa only [hw, mul_one, one_mul, div_one] using eq_second_moment_pair hd c w

/-- The expectation-level adapter for a generator path. The rows at time
`t` need not be unit or nonzero; the raw pair theorem includes both cases. -/
theorem second_moment_on_linear_path {d n : ℕ} (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) :
    (2*π)*(∫ x : Vec d,
      (∑ i, c i*(|(inner (w i+t • A (w i)) x : ℝ)|/2))^2*stdGaussianDensity x) =
      studentPairEnergy c w A t := by
  rw [eq_second_moment_pair hd c (fun i => w i+t • A (w i))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold pairPath
  ring

theorem second_moment_on_linear_path_unscaled {d n : ℕ} (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) :
    (∫ x : Vec d,
      (∑ i, c i*(|(inner (w i+t • A (w i)) x : ℝ)|/2))^2*stdGaussianDensity x) =
      (1/(2*π))*studentPairEnergy c w A t := by
  have h := second_moment_on_linear_path hd c w A t
  rw [← h]
  field_simp [Real.pi_ne_zero]
  ring

/-- The literal centered loss expansion consumes the displayed second-moment
equation on one signed family: student units followed by negative teacher
units. This is the natural probabilistic consumer of `eq_second_moment_pair`. -/
theorem centered_loss_eq_variable_kernel {d n m : ℕ} (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    PaperLeanFormalization.Definitions.CenteredLoss c w s v =
      (1/(2*π))*(variableKernelLoss s v (c,w)-variableKernelLoss s v (s,v)) := by
  let a : Fin n ⊕ Fin m → ℝ := Sum.elim c (fun k => -s k)
  let z : Fin n ⊕ Fin m → Vec d := Sum.elim w v
  have hz (i : Fin n ⊕ Fin m) : ‖z i‖ = 1 := by
    cases i with | inl i => exact hw i | inr k => exact hv k
  have h := unit_second_moment_pair hd a z hz
  have hcross : (∑ k, ∑ i, s k*c i*centeredKernel (inner (v k) (w i))) =
      ∑ i, ∑ k, c i*s k*centeredKernel (inner (w i) (v k)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm (v k) (w i)]
    ring
  simp only [a, z, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, Finset.sum_add_distrib,
    ← sub_eq_add_neg, Finset.sum_sub_distrib] at h
  rw [hcross] at h
  unfold PaperLeanFormalization.Definitions.CenteredLoss variableKernelLoss
  have algebra (I U C T : ℝ) (hm : 2*π*I = U-C-(C-T)) :
      (1/2)*I = (1/(2*π))*((1/2)*U-C-((1/2)*T-T)) := by
    field_simp [Real.pi_ne_zero]
    nlinarith only [hm]
  exact algebra _ _ _ _ h

end PaperLeanFormalization.SecondMomentPair

/-!
## Normal stretching

Positivity of the mixed energy without the closed-form expansion: the student
second moment along the normal stretching `w ↦ w + t·q` is convex in `t`, and
it is strictly larger for the actual generators than for their projections
onto the teacher span (by convexity of the feature and the reflection across
the span), so its derivative at the actual generators is positive.
-/

namespace PaperLeanFormalization.NormalStretching

open PaperLeanFormalization MeasureTheory Filter Set
open scoped Topology
open NormalTrace ConfinementTraceAssembly AmplitudeNormalVariation SecondMomentPair
open PlainConfinementVariation PairKernelJet

variable {d r n : ℕ}

/-- The reflection across the teacher span is self-adjoint. -/
theorem reflect_inner (J : Vec r →ₗᵢ[ℝ] Vec d) (u z : Vec d) :
    (inner u (z - (2:ℝ) • normalPart J z) : ℝ) =
      inner (u - (2:ℝ) • normalPart J u) z := by
  have h1 := normal_inner J u z
  have h2 := normal_inner_left J u z
  rw [inner_sub_right, inner_sub_left, real_inner_smul_right, real_inner_smul_left, h1, h2]

/-- The reflection across the teacher span preserves inner products. -/
theorem reflect_inner_reflect (J : Vec r →ₗᵢ[ℝ] Vec d) (u v : Vec d) :
    (inner (u - (2:ℝ) • normalPart J u) (v - (2:ℝ) • normalPart J v) : ℝ) = inner u v := by
  have h1 := normal_inner J u v
  have h2 := normal_inner_left J u v
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [h1, h2, normal_inner]
  ring

theorem reflect_norm (J : Vec r →ₗᵢ[ℝ] Vec d) (u : Vec d) :
    ‖u - (2:ℝ) • normalPart J u‖ = ‖u‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner (u), reflect_inner_reflect]

/-- The student square along any direction family is Gaussian integrable. -/
theorem student_square_integrable (hd : 2 ≤ d) (c : Fin n → ℝ) (u : Fin n → Vec d) :
    Integrable (fun x : Vec d =>
      (∑ j, c j * (|(inner (u j) x : ℝ)| / 2)) ^ 2 * stdGaussianDensity x) := by
  have h := Skip.centered_residual_square_integrable hd c u
    (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : Vec d))
  simpa using h

theorem density_pos (x : Vec d) : 0 < stdGaussianDensity x := by
  unfold stdGaussianDensity; positivity

/-- Pointwise convexity of the squared student along the stretching. -/
theorem stretch_pointwise (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (z : Vec d) :
    (∑ j, c j * (|(inner (w j + (a * x + b * y) • A (w j)) z : ℝ)| / 2)) ^ 2 *
        stdGaussianDensity z ≤
      a * ((∑ j, c j * (|(inner (w j + x • A (w j)) z : ℝ)| / 2)) ^ 2 * stdGaussianDensity z) +
      b * ((∑ j, c j * (|(inner (w j + y • A (w j)) z : ℝ)| / 2)) ^ 2 * stdGaussianDensity z) := by
  set hx := ∑ j, c j * (|(inner (w j + x • A (w j)) z : ℝ)| / 2) with hhx
  set hy := ∑ j, c j * (|(inner (w j + y • A (w j)) z : ℝ)| / 2) with hhy
  set ht := ∑ j, c j * (|(inner (w j + (a * x + b * y) • A (w j)) z : ℝ)| / 2) with hht
  have ht0 : 0 ≤ ht := Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (by positivity)
  have hle : ht ≤ a * hx + b * hy := by
    rw [hht, hhx, hhy, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hlin : (inner (w j + (a * x + b * y) • A (w j)) z : ℝ) =
        a * inner (w j + x • A (w j)) z + b * inner (w j + y • A (w j)) z := by
      simp only [inner_add_left, real_inner_smul_left]
      have hb' : b = 1 - a := by linarith
      subst hb'
      ring
    rw [hlin]
    have habs : |a * inner (w j + x • A (w j)) z + b * inner (w j + y • A (w j)) z| ≤
        a * |(inner (w j + x • A (w j)) z : ℝ)| + b * |(inner (w j + y • A (w j)) z : ℝ)| := by
      calc _ ≤ |a * inner (w j + x • A (w j)) z| + |b * inner (w j + y • A (w j)) z| := abs_add _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
    nlinarith [hc j, habs]
  have hsq : ht ^ 2 ≤ a * hx ^ 2 + b * hy ^ 2 := by
    have h1 : ht ^ 2 ≤ (a * hx + b * hy) ^ 2 := pow_le_pow_left ht0 hle 2
    have h2 : (a * hx + b * hy) ^ 2 ≤ a * hx ^ 2 + b * hy ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (hx - hy))]
    exact h1.trans h2
  have hρ := (density_pos z).le
  calc ht ^ 2 * stdGaussianDensity z ≤ (a * hx ^ 2 + b * hy ^ 2) * stdGaussianDensity z :=
        mul_le_mul_of_nonneg_right hsq hρ
    _ = _ := by ring

/-- The stretched student second moment is a convex function of the stretching. -/
theorem studentPairEnergy_convex (hd : 2 ≤ d) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (w : Fin n → Vec d) (A : Vec d →ₗ[ℝ] Vec d) :
    ConvexOn ℝ Set.univ (studentPairEnergy c w A) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hint : ∀ t : ℝ, Integrable (fun z : Vec d =>
      (∑ j, c j * (|(inner (w j + t • A (w j)) z : ℝ)| / 2)) ^ 2 * stdGaussianDensity z) :=
    fun t => student_square_integrable hd c (fun j => w j + t • A (w j))
  rw [← second_moment_on_linear_path hd c w A (a * x + b * y),
    ← second_moment_on_linear_path hd c w A x, ← second_moment_on_linear_path hd c w A y]
  have hsum : a * ((2 * π) * ∫ z : Vec d,
        (∑ j, c j * (|(inner (w j + x • A (w j)) z : ℝ)| / 2)) ^ 2 * stdGaussianDensity z) +
      b * ((2 * π) * ∫ z : Vec d,
        (∑ j, c j * (|(inner (w j + y • A (w j)) z : ℝ)| / 2)) ^ 2 * stdGaussianDensity z) =
      (2 * π) * ∫ z : Vec d,
        (a * ((∑ j, c j * (|(inner (w j + x • A (w j)) z : ℝ)| / 2)) ^ 2 * stdGaussianDensity z) +
         b * ((∑ j, c j * (|(inner (w j + y • A (w j)) z : ℝ)| / 2)) ^ 2 * stdGaussianDensity z)) := by
    rw [integral_add ((hint x).const_mul a) ((hint y).const_mul b), integral_mul_left,
      integral_mul_left]
    ring
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (hint _) (((hint x).const_mul a).add ((hint y).const_mul b))
  intro z
  exact stretch_pointwise c hc w A ha hb hab z

/-- Elementary: the average of `|u|` and `|u - 2v|` dominates `|u - v|`. -/
theorem abs_midpoint (u v : ℝ) : |u - v| ≤ (|u| + |u - 2 * v|) / 2 := by
  have := abs_add u (u - 2 * v)
  rw [show u + (u - 2 * v) = 2 * (u - v) by ring, abs_mul, abs_two] at this
  linarith

theorem abs_midpoint_strict {u v : ℝ} (h : |u - v| < |v|) :
    |u - v| < (|u| + |u - 2 * v|) / 2 := by
  rcases abs_cases v with ⟨hv, _⟩ | ⟨hv, _⟩ <;> rcases abs_cases (u - v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases u with ⟨h2, _⟩ | ⟨h2, _⟩ <;> rcases abs_cases (u - 2 * v) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
    linarith

/-- Reflecting the normal components does not change the student second moment. -/
theorem second_moment_reflect (hd : 2 ≤ d) (J : Vec r →ₗᵢ[ℝ] Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) :
    (∫ x : Vec d, (∑ j, c j * (|(inner (w j - (2:ℝ) • normalPart J (w j)) x : ℝ)| / 2)) ^ 2 *
        stdGaussianDensity x) =
      ∫ x : Vec d, (∑ j, c j * (|(inner (w j) x : ℝ)| / 2)) ^ 2 * stdGaussianDensity x := by
  have h1 := eq_second_moment_pair hd c (fun j => w j - (2:ℝ) • normalPart J (w j))
  have h2 := eq_second_moment_pair hd c w
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hπ
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [reflect_norm, reflect_norm, reflect_inner_reflect]

/-- Normal stretching lemma: the second moment of the student is strictly
smaller for the projected generators than for the actual ones, as soon as an
active generator has a normal component. -/
theorem second_moment_projected_lt (hd : 2 ≤ d) (J : Vec r →ₗᵢ[ℝ] Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (hc : ∀ i, 0 ≤ c i)
    (i : Fin n) (hci : 0 < c i) (hQi : normalPart J (w i) ≠ 0) :
    (∫ x : Vec d, (∑ j, c j * (|(inner (w j + (-1:ℝ) • normalMap J (w j)) x : ℝ)| / 2)) ^ 2 *
        stdGaussianDensity x) <
      ∫ x : Vec d, (∑ j, c j * (|(inner (w j + (0:ℝ) • normalMap J (w j)) x : ℝ)| / 2)) ^ 2 *
        stdGaussianDensity x := by
  classical
  -- the three students: projected, actual, reflected
  set hP : Vec d → ℝ := fun x => ∑ j, c j * (|(inner (w j + (-1:ℝ) • normalMap J (w j)) x : ℝ)| / 2)
  set hA : Vec d → ℝ := fun x => ∑ j, c j * (|(inner (w j + (0:ℝ) • normalMap J (w j)) x : ℝ)| / 2)
    with hAdef
  set hB : Vec d → ℝ := fun x => ∑ j, c j * (|(inner (w j - (2:ℝ) • normalPart J (w j)) x : ℝ)| / 2)
    with hBdef
  show ∫ x, hP x ^ 2 * stdGaussianDensity x < ∫ x, hA x ^ 2 * stdGaussianDensity x
  have hnormal : ∀ j x, (inner (normalMap J (w j)) x : ℝ) = inner (normalPart J (w j)) x :=
    fun j x => rfl
  -- the three inner products in terms of u = ⟨w_j, x⟩ and v = ⟨q_j, x⟩
  have eP : ∀ j x, (inner (w j + (-1:ℝ) • normalMap J (w j)) x : ℝ) =
      inner (w j) x - inner (normalPart J (w j)) x := by
    intro j x; rw [inner_add_left, real_inner_smul_left, hnormal]; ring
  have eA : ∀ j x, (inner (w j + (0:ℝ) • normalMap J (w j)) x : ℝ) = inner (w j) x := by
    intro j x; rw [zero_smul, add_zero]
  have eB : ∀ j x, (inner (w j - (2:ℝ) • normalPart J (w j)) x : ℝ) =
      inner (w j) x - 2 * inner (normalPart J (w j)) x := by
    intro j x; rw [inner_sub_left, real_inner_smul_left]
  have hmid : ∀ x, (hA x + hB x) / 2 =
      ∑ j, (c j * (|(inner (w j) x : ℝ)| / 2) +
        c j * (|(inner (w j) x : ℝ) - 2 * inner (normalPart J (w j)) x| / 2)) / 2 := by
    intro x
    simp only [hAdef, hBdef, eA, eB]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hterm : ∀ j x, c j * (|(inner (w j + (-1:ℝ) • normalMap J (w j)) x : ℝ)| / 2) ≤
      (c j * (|(inner (w j) x : ℝ)| / 2) +
        c j * (|(inner (w j) x : ℝ) - 2 * inner (normalPart J (w j)) x| / 2)) / 2 := by
    intro j x
    rw [eP]
    have := abs_midpoint (inner (w j) x) (inner (normalPart J (w j)) x)
    nlinarith [hc j, this]
  have hPle : ∀ x, hP x ≤ (hA x + hB x) / 2 := by
    intro x
    rw [hmid]
    exact Finset.sum_le_sum fun j _ => hterm j x
  have hP0 : ∀ x, 0 ≤ hP x := fun x => Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (by positivity)
  -- the pointwise gap
  set D : Vec d → ℝ := fun x => ((hA x ^ 2 + hB x ^ 2) / 2 - hP x ^ 2) * stdGaussianDensity x
    with hDdef
  have hDnonneg : ∀ x, 0 ≤ D x := by
    intro x
    apply mul_nonneg _ (density_pos x).le
    have h1 : hP x ^ 2 ≤ ((hA x + hB x) / 2) ^ 2 := pow_le_pow_left (hP0 x) (hPle x) 2
    nlinarith [sq_nonneg (hA x - hB x)]
  -- strict on an open set around the normal component of `w i`
  set U : Set (Vec d) := {x | |(inner (w i) x : ℝ) - inner (normalPart J (w i)) x| <
    |(inner (normalPart J (w i)) x : ℝ)|}
  have hUopen : IsOpen U := by
    apply isOpen_lt
    · exact ((continuous_const.inner continuous_id).sub (continuous_const.inner continuous_id)).abs
    · exact (continuous_const.inner continuous_id).abs
  have hUne : U.Nonempty := by
    refine ⟨normalPart J (w i), ?_⟩
    show |(inner (w i) (normalPart J (w i)) : ℝ) - inner (normalPart J (w i)) (normalPart J (w i))| <
      |(inner (normalPart J (w i)) (normalPart J (w i)) : ℝ)|
    rw [normal_inner, sub_self, abs_zero, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
    exact pow_pos (norm_pos_iff.mpr hQi) 2
  have hDpos : ∀ x ∈ U, 0 < D x := by
    intro x hx
    apply mul_pos _ (density_pos x)
    have hstrict : hP x < (hA x + hB x) / 2 := by
      rw [hmid]
      refine Finset.sum_lt_sum (fun j _ => hterm j x) ⟨i, Finset.mem_univ i, ?_⟩
      rw [eP]
      have := abs_midpoint_strict hx
      nlinarith [hci, this]
    have h1 : hP x ^ 2 < ((hA x + hB x) / 2) ^ 2 := pow_lt_pow_left hstrict (hP0 x) two_ne_zero
    nlinarith [sq_nonneg (hA x - hB x)]
  -- integrability, in the abbreviated forms
  have hintP : Integrable (fun x => hP x ^ 2 * stdGaussianDensity x) :=
    student_square_integrable hd c (fun j => w j + (-1:ℝ) • normalMap J (w j))
  have hintA : Integrable (fun x => hA x ^ 2 * stdGaussianDensity x) :=
    student_square_integrable hd c (fun j => w j + (0:ℝ) • normalMap J (w j))
  have hintB : Integrable (fun x => hB x ^ 2 * stdGaussianDensity x) :=
    student_square_integrable hd c (fun j => w j - (2:ℝ) • normalPart J (w j))
  have hintAB : Integrable (fun x => (hA x ^ 2 * stdGaussianDensity x +
      hB x ^ 2 * stdGaussianDensity x) / 2) := (hintA.add hintB).div_const 2
  have hDeq : ∀ x, D x = (hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x) / 2 -
      hP x ^ 2 * stdGaussianDensity x := by
    intro x; simp only [hDdef]; ring
  have hintD : Integrable D := by
    have : D = fun x => (hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x) / 2 -
        hP x ^ 2 * stdGaussianDensity x := funext hDeq
    rw [this]
    exact hintAB.sub hintP
  -- positivity of the integral of the gap
  have hpos : 0 < ∫ x, D x := by
    rw [integral_pos_iff_support_of_nonneg_ae (eventually_of_forall hDnonneg) hintD]
    apply lt_of_lt_of_le (hUopen.measure_pos volume hUne)
    apply measure_mono
    intro x hx
    exact (hDpos x hx).ne'
  have hsplit : ∫ x, D x = ((∫ x, hA x ^ 2 * stdGaussianDensity x) +
      ∫ x, hB x ^ 2 * stdGaussianDensity x) / 2 - ∫ x, hP x ^ 2 * stdGaussianDensity x := by
    calc ∫ x, D x = ∫ x, ((hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x) / 2 -
          hP x ^ 2 * stdGaussianDensity x) := integral_congr_ae (eventually_of_forall hDeq)
      _ = (∫ x, (hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x) / 2) -
          ∫ x, hP x ^ 2 * stdGaussianDensity x := integral_sub hintAB hintP
      _ = (∫ x, (hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x)) / 2 -
          ∫ x, hP x ^ 2 * stdGaussianDensity x := by rw [integral_div]
      _ = _ := by rw [integral_add hintA hintB]
  have hrefl : ∫ x, hB x ^ 2 * stdGaussianDensity x = ∫ x, hA x ^ 2 * stdGaussianDensity x := by
    have h := second_moment_reflect hd J c w
    simp only [hBdef, hAdef, eA]
    exact h
  have key : 0 < ((∫ x, hA x ^ 2 * stdGaussianDensity x) +
      ∫ x, hB x ^ 2 * stdGaussianDensity x) / 2 - ∫ x, hP x ^ 2 * stdGaussianDensity x :=
    hsplit ▸ hpos
  rw [hrefl] at key
  linarith

/-- Positivity of the mixed energy from the normal-stretching lemma: the
second moment along the stretching is convex, so its derivative at the actual
generators dominates the increase from the projected generators. -/
theorem mixedEnergy_pos_of_active_normal (hd : 2 ≤ d)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hc : ∀ i, 0 ≤ c i)
    (i : Fin n) (hci : 0 < c i) (hQi : normalPart J (w i) ≠ 0) :
    0 < mixedEnergy J c w := by
  have hjet := student_energy_jet c w (normalMap J) hw
  have hD : HasDerivAt (studentPairEnergy c w (normalMap J)) (2 * mixedEnergy J c w) 0 := by
    have := hjet.first.differentiableAt.hasDerivAt
    rwa [eq_second_moment_derivative J c w hw] at this
  have hconv := studentPairEnergy_convex hd c hc w (normalMap J)
  -- secant bound: g 0 - g (-1) ≤ g' 0
  have hsecant : studentPairEnergy c w (normalMap J) 0 - studentPairEnergy c w (normalMap J) (-1) ≤
      2 * mixedEnergy J c w := by
    have hlim : Tendsto (slope (studentPairEnergy c w (normalMap J)) 0) (𝓝[<] 0)
        (𝓝 (2 * mixedEnergy J c w)) :=
      (hasDerivAt_iff_tendsto_slope.mp hD).mono_left
        (nhdsWithin_mono 0 (fun y (hy : y ∈ Set.Iio 0) => ne_of_lt hy))
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsWithin_Iio (show (0:ℝ) ∈ Set.Ioc (-1) 0 from ⟨by norm_num, le_refl 0⟩)]
      with y hy
    have h := hconv.secant_mono (Set.mem_univ 0) (Set.mem_univ (-1)) (Set.mem_univ y)
      (by norm_num) (ne_of_lt hy.2) hy.1.le
    rw [slope_def_field]
    have hL : (studentPairEnergy c w (normalMap J) (-1) - studentPairEnergy c w (normalMap J) 0) /
        (-1 - 0) = studentPairEnergy c w (normalMap J) 0 - studentPairEnergy c w (normalMap J) (-1) := by
      ring
    rw [hL] at h
    exact h
  -- strict increase from the projected generators
  have hgap : studentPairEnergy c w (normalMap J) (-1) < studentPairEnergy c w (normalMap J) 0 := by
    rw [← second_moment_on_linear_path hd c w (normalMap J) (-1),
      ← second_moment_on_linear_path hd c w (normalMap J) 0]
    exact mul_lt_mul_of_pos_left (second_moment_projected_lt hd J c w hc i hci hQi) (by positivity)
  linarith

/-! ### The plain ReLU feature -/

/-- Positive homogeneity of the ReLU feature under normalization. -/
theorem plain_feature_normalize (w x : Vec d) :
    max 0 (inner w x : ℝ) = ‖w‖ * max 0 (inner (‖w‖⁻¹ • w) x : ℝ) := by
  have h : (inner w x : ℝ) = ‖w‖ * inner (‖w‖⁻¹ • w) x := by
    rw [← real_inner_smul_left, norm_normalize]
  rw [h]
  rcases le_or_lt 0 (inner (‖w‖⁻¹ • w) x : ℝ) with hnn | hneg
  · rw [max_eq_right hnn, max_eq_right (mul_nonneg (norm_nonneg w) hnn)]
  · rw [max_eq_left hneg.le,
      max_eq_left (mul_nonpos_iff.mpr (Or.inl ⟨norm_nonneg w, hneg.le⟩)), mul_zero]

/-- The plain two-feature moment for arbitrary raw rows. -/
theorem raw_plain_pair_moment (hd : 2 ≤ d) (w v : Vec d) :
    (∫ x : Vec d, max 0 (inner w x : ℝ) * max 0 (inner v x : ℝ) * stdGaussianDensity x) =
      (1 / (2 * π)) * (‖w‖ * ‖v‖ * centeredKernel ((inner w v : ℝ) / (‖w‖ * ‖v‖)) +
        (π / 2) * inner w v) := by
  by_cases hw : w = 0
  · simp [hw]
  by_cases hv : v = 0
  · simp [hv]
  let u := ‖w‖⁻¹ • w
  let z := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hw
  have hz : ‖z‖ = 1 := norm_smul_inv_norm hv
  have hscale : (∫ x : Vec d, max 0 (inner w x : ℝ) * max 0 (inner v x : ℝ) *
      stdGaussianDensity x) = (‖w‖ * ‖v‖) *
      (∫ x : Vec d, max 0 (inner u x : ℝ) * max 0 (inner z x : ℝ) * stdGaussianDensity x) := by
    rw [← integral_mul_left]
    congr 1
    funext x
    rw [plain_feature_normalize w x, plain_feature_normalize v x]
    dsimp only [u, z]
    ring
  rw [hscale, Preliminaries.plain_feature_pair_moment hd u z hu hz]
  dsimp only [u, z]
  rw [normalized_inner]
  unfold centeredKernel
  have hne : ‖w‖ * ‖v‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hw) (norm_ne_zero_iff.mpr hv)
  field_simp
  ring

/-- The literal Gaussian expectation of the squared plain student. -/
theorem plain_second_moment_pair {ι : Type*} [Fintype ι] (hd : 2 ≤ d)
    (c : ι → ℝ) (V : ι → Vec d) :
    (2 * π) * (∫ x : Vec d, (∑ i, c i * max 0 (inner (V i) x : ℝ)) ^ 2 * stdGaussianDensity x) =
      ∑ i, ∑ j, c i * c j * (‖V i‖ * ‖V j‖ * centeredKernel ((inner (V i) (V j) : ℝ) /
        (‖V i‖ * ‖V j‖)) + (π / 2) * inner (V i) (V j)) := by
  have h := Preliminaries.weighted_square_integral volume
    (fun (w x : Vec d) => max 0 (inner w x : ℝ)) stdGaussianDensity c V
    (fun w v => ‖w‖ * ‖v‖ * centeredKernel ((inner w v : ℝ) / (‖w‖ * ‖v‖)) + (π / 2) * inner w v)
    (1 / (2 * π))
    (fun i j => Preliminaries.gaussian_plain_pair_integrable hd (V i) (V j))
    (fun i j => raw_plain_pair_moment hd (V i) (V j))
  rw [h]
  have hcancel : (2 * π) * (1 / (2 * π)) = 1 := by field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hcancel, one_mul]

/-- The plain student second moment along a generator path is the plain
student energy with the ReLU weight `π/2`. -/
theorem plain_second_moment_on_linear_path (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (A : Vec d →ₗ[ℝ] Vec d) (t : ℝ) :
    (2 * π) * (∫ x : Vec d,
      (∑ i, c i * max 0 (inner (w i + t • A (w i)) x : ℝ)) ^ 2 * stdGaussianDensity x) =
      plainStudentEnergy (π / 2) c w A t := by
  rw [plain_second_moment_pair hd c (fun i => w i + t • A (w i))]
  unfold plainStudentEnergy studentPairEnergy
  have hM : moment c w + t • A (moment c w) = ∑ i, c i • (w i + t • A (w i)) := by
    simp only [moment, map_sum, LinearMap.map_smul, Finset.smul_sum, smul_add,
      Finset.sum_add_distrib, smul_smul, mul_comm t]
  have hsq : ‖∑ i, c i • (w i + t • A (w i))‖ ^ 2 =
      ∑ i, ∑ j, c i * c j * inner (w i + t • A (w i)) (w j + t • A (w j)) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hM, hsq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold pairPath
  ring

theorem plain_student_square_integrable (hd : 2 ≤ d) (c : Fin n → ℝ) (u : Fin n → Vec d) :
    Integrable (fun x : Vec d =>
      (∑ j, c j * max 0 (inner (u j) x : ℝ)) ^ 2 * stdGaussianDensity x) := by
  have hpair (i j : Fin n) : Integrable (fun x : Vec d =>
      (c i * max 0 (inner (u i) x : ℝ)) * (c j * max 0 (inner (u j) x : ℝ)) *
        stdGaussianDensity x) := by
    convert (Preliminaries.gaussian_plain_pair_integrable hd (u i) (u j)).const_mul (c i * c j)
      using 1
    funext x
    ring
  exact Skip.finite_square_integrable volume (fun i x => c i * max 0 (inner (u i) x : ℝ))
    stdGaussianDensity hpair

theorem max_zero_eq_half (s : ℝ) : max 0 s = (s + |s|) / 2 := by
  rcases le_or_lt 0 s with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h.le, abs_of_neg h]; ring

theorem relu_convex_comb {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b) :
    max 0 (a * u + b * v) ≤ a * max 0 u + b * max 0 v := by
  rw [max_zero_eq_half, max_zero_eq_half, max_zero_eq_half]
  have := abs_add (a * u) (b * v)
  rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb] at this
  linarith

theorem relu_midpoint (u v : ℝ) : max 0 (u - v) ≤ (max 0 u + max 0 (u - 2 * v)) / 2 := by
  rw [max_zero_eq_half, max_zero_eq_half, max_zero_eq_half]
  linarith [abs_midpoint u v]

theorem relu_midpoint_strict {u v : ℝ} (h : |u - v| < |v|) :
    max 0 (u - v) < (max 0 u + max 0 (u - 2 * v)) / 2 := by
  rw [max_zero_eq_half, max_zero_eq_half, max_zero_eq_half]
  linarith [abs_midpoint_strict h]

/-- Pointwise convexity of the squared plain student along the stretching. -/
theorem plain_stretch_pointwise (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (w : Fin n → Vec d)
    (A : Vec d →ₗ[ℝ] Vec d) {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (z : Vec d) :
    (∑ j, c j * max 0 (inner (w j + (a * x + b * y) • A (w j)) z : ℝ)) ^ 2 *
        stdGaussianDensity z ≤
      a * ((∑ j, c j * max 0 (inner (w j + x • A (w j)) z : ℝ)) ^ 2 * stdGaussianDensity z) +
      b * ((∑ j, c j * max 0 (inner (w j + y • A (w j)) z : ℝ)) ^ 2 * stdGaussianDensity z) := by
  set hx := ∑ j, c j * max 0 (inner (w j + x • A (w j)) z : ℝ) with hhx
  set hy := ∑ j, c j * max 0 (inner (w j + y • A (w j)) z : ℝ) with hhy
  set ht := ∑ j, c j * max 0 (inner (w j + (a * x + b * y) • A (w j)) z : ℝ) with hht
  have ht0 : 0 ≤ ht := Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (le_max_left _ _)
  have hle : ht ≤ a * hx + b * hy := by
    rw [hht, hhx, hhy, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hlin : (inner (w j + (a * x + b * y) • A (w j)) z : ℝ) =
        a * inner (w j + x • A (w j)) z + b * inner (w j + y • A (w j)) z := by
      simp only [inner_add_left, real_inner_smul_left]
      have hb' : b = 1 - a := by linarith
      subst hb'
      ring
    rw [hlin]
    have := relu_convex_comb (u := (inner (w j + x • A (w j)) z : ℝ))
      (v := (inner (w j + y • A (w j)) z : ℝ)) ha hb
    nlinarith [hc j, this]
  have hsq : ht ^ 2 ≤ a * hx ^ 2 + b * hy ^ 2 := by
    have h1 : ht ^ 2 ≤ (a * hx + b * hy) ^ 2 := pow_le_pow_left ht0 hle 2
    have h2 : (a * hx + b * hy) ^ 2 ≤ a * hx ^ 2 + b * hy ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (hx - hy))]
    exact h1.trans h2
  have hρ := (density_pos z).le
  calc ht ^ 2 * stdGaussianDensity z ≤ (a * hx ^ 2 + b * hy ^ 2) * stdGaussianDensity z :=
        mul_le_mul_of_nonneg_right hsq hρ
    _ = _ := by ring

theorem plainStudentEnergy_convex (hd : 2 ≤ d) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (w : Fin n → Vec d) (A : Vec d →ₗ[ℝ] Vec d) :
    ConvexOn ℝ Set.univ (plainStudentEnergy (π / 2) c w A) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hint : ∀ t : ℝ, Integrable (fun z : Vec d =>
      (∑ j, c j * max 0 (inner (w j + t • A (w j)) z : ℝ)) ^ 2 * stdGaussianDensity z) :=
    fun t => plain_student_square_integrable hd c (fun j => w j + t • A (w j))
  rw [← plain_second_moment_on_linear_path hd c w A (a * x + b * y),
    ← plain_second_moment_on_linear_path hd c w A x, ← plain_second_moment_on_linear_path hd c w A y]
  have hsum : a * ((2 * π) * ∫ z : Vec d,
        (∑ j, c j * max 0 (inner (w j + x • A (w j)) z : ℝ)) ^ 2 * stdGaussianDensity z) +
      b * ((2 * π) * ∫ z : Vec d,
        (∑ j, c j * max 0 (inner (w j + y • A (w j)) z : ℝ)) ^ 2 * stdGaussianDensity z) =
      (2 * π) * ∫ z : Vec d,
        (a * ((∑ j, c j * max 0 (inner (w j + x • A (w j)) z : ℝ)) ^ 2 * stdGaussianDensity z) +
         b * ((∑ j, c j * max 0 (inner (w j + y • A (w j)) z : ℝ)) ^ 2 * stdGaussianDensity z)) := by
    rw [integral_add ((hint x).const_mul a) ((hint y).const_mul b), integral_mul_left,
      integral_mul_left]
    ring
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (hint _) (((hint x).const_mul a).add ((hint y).const_mul b))
  intro z
  exact plain_stretch_pointwise c hc w A ha hb hab z

theorem plain_second_moment_reflect (hd : 2 ≤ d) (J : Vec r →ₗᵢ[ℝ] Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) :
    (∫ x : Vec d, (∑ j, c j * max 0 (inner (w j - (2:ℝ) • normalPart J (w j)) x : ℝ)) ^ 2 *
        stdGaussianDensity x) =
      ∫ x : Vec d, (∑ j, c j * max 0 (inner (w j) x : ℝ)) ^ 2 * stdGaussianDensity x := by
  have h1 := plain_second_moment_pair hd c (fun j => w j - (2:ℝ) • normalPart J (w j))
  have h2 := plain_second_moment_pair hd c w
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hπ
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [reflect_norm, reflect_norm, reflect_inner_reflect]

/-- Normal stretching lemma for the plain ReLU student. -/
theorem plain_second_moment_projected_lt (hd : 2 ≤ d) (J : Vec r →ₗᵢ[ℝ] Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (hc : ∀ i, 0 ≤ c i)
    (i : Fin n) (hci : 0 < c i) (hQi : normalPart J (w i) ≠ 0) :
    (∫ x : Vec d, (∑ j, c j * max 0 (inner (w j + (-1:ℝ) • normalMap J (w j)) x : ℝ)) ^ 2 *
        stdGaussianDensity x) <
      ∫ x : Vec d, (∑ j, c j * max 0 (inner (w j + (0:ℝ) • normalMap J (w j)) x : ℝ)) ^ 2 *
        stdGaussianDensity x := by
  classical
  set hP : Vec d → ℝ := fun x => ∑ j, c j * max 0 (inner (w j + (-1:ℝ) • normalMap J (w j)) x : ℝ)
  set hA : Vec d → ℝ := fun x => ∑ j, c j * max 0 (inner (w j + (0:ℝ) • normalMap J (w j)) x : ℝ)
    with hAdef
  set hB : Vec d → ℝ := fun x => ∑ j, c j * max 0 (inner (w j - (2:ℝ) • normalPart J (w j)) x : ℝ)
    with hBdef
  show ∫ x, hP x ^ 2 * stdGaussianDensity x < ∫ x, hA x ^ 2 * stdGaussianDensity x
  have hnormal : ∀ j x, (inner (normalMap J (w j)) x : ℝ) = inner (normalPart J (w j)) x :=
    fun j x => rfl
  have eP : ∀ j x, (inner (w j + (-1:ℝ) • normalMap J (w j)) x : ℝ) =
      inner (w j) x - inner (normalPart J (w j)) x := by
    intro j x; rw [inner_add_left, real_inner_smul_left, hnormal]; ring
  have eA : ∀ j x, (inner (w j + (0:ℝ) • normalMap J (w j)) x : ℝ) = inner (w j) x := by
    intro j x; rw [zero_smul, add_zero]
  have eB : ∀ j x, (inner (w j - (2:ℝ) • normalPart J (w j)) x : ℝ) =
      inner (w j) x - 2 * inner (normalPart J (w j)) x := by
    intro j x; rw [inner_sub_left, real_inner_smul_left]
  have hmid : ∀ x, (hA x + hB x) / 2 =
      ∑ j, (c j * max 0 (inner (w j) x : ℝ) +
        c j * max 0 ((inner (w j) x : ℝ) - 2 * inner (normalPart J (w j)) x)) / 2 := by
    intro x
    simp only [hAdef, hBdef, eA, eB]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hterm : ∀ j x, c j * max 0 (inner (w j + (-1:ℝ) • normalMap J (w j)) x : ℝ) ≤
      (c j * max 0 (inner (w j) x : ℝ) +
        c j * max 0 ((inner (w j) x : ℝ) - 2 * inner (normalPart J (w j)) x)) / 2 := by
    intro j x
    rw [eP]
    have := relu_midpoint (inner (w j) x) (inner (normalPart J (w j)) x)
    nlinarith [hc j, this]
  have hPle : ∀ x, hP x ≤ (hA x + hB x) / 2 := by
    intro x
    rw [hmid]
    exact Finset.sum_le_sum fun j _ => hterm j x
  have hP0 : ∀ x, 0 ≤ hP x :=
    fun x => Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (le_max_left _ _)
  set D : Vec d → ℝ := fun x => ((hA x ^ 2 + hB x ^ 2) / 2 - hP x ^ 2) * stdGaussianDensity x
    with hDdef
  have hDnonneg : ∀ x, 0 ≤ D x := by
    intro x
    apply mul_nonneg _ (density_pos x).le
    have h1 : hP x ^ 2 ≤ ((hA x + hB x) / 2) ^ 2 := pow_le_pow_left (hP0 x) (hPle x) 2
    nlinarith [sq_nonneg (hA x - hB x)]
  set U : Set (Vec d) := {x | |(inner (w i) x : ℝ) - inner (normalPart J (w i)) x| <
    |(inner (normalPart J (w i)) x : ℝ)|}
  have hUopen : IsOpen U := by
    apply isOpen_lt
    · exact ((continuous_const.inner continuous_id).sub (continuous_const.inner continuous_id)).abs
    · exact (continuous_const.inner continuous_id).abs
  have hUne : U.Nonempty := by
    refine ⟨normalPart J (w i), ?_⟩
    show |(inner (w i) (normalPart J (w i)) : ℝ) - inner (normalPart J (w i)) (normalPart J (w i))| <
      |(inner (normalPart J (w i)) (normalPart J (w i)) : ℝ)|
    rw [normal_inner, sub_self, abs_zero, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
    exact pow_pos (norm_pos_iff.mpr hQi) 2
  have hDpos : ∀ x ∈ U, 0 < D x := by
    intro x hx
    apply mul_pos _ (density_pos x)
    have hstrict : hP x < (hA x + hB x) / 2 := by
      rw [hmid]
      refine Finset.sum_lt_sum (fun j _ => hterm j x) ⟨i, Finset.mem_univ i, ?_⟩
      rw [eP]
      have := relu_midpoint_strict hx
      nlinarith [hci, this]
    have h1 : hP x ^ 2 < ((hA x + hB x) / 2) ^ 2 := pow_lt_pow_left hstrict (hP0 x) two_ne_zero
    nlinarith [sq_nonneg (hA x - hB x)]
  have hintP : Integrable (fun x => hP x ^ 2 * stdGaussianDensity x) :=
    plain_student_square_integrable hd c (fun j => w j + (-1:ℝ) • normalMap J (w j))
  have hintA : Integrable (fun x => hA x ^ 2 * stdGaussianDensity x) :=
    plain_student_square_integrable hd c (fun j => w j + (0:ℝ) • normalMap J (w j))
  have hintB : Integrable (fun x => hB x ^ 2 * stdGaussianDensity x) :=
    plain_student_square_integrable hd c (fun j => w j - (2:ℝ) • normalPart J (w j))
  have hintAB : Integrable (fun x => (hA x ^ 2 * stdGaussianDensity x +
      hB x ^ 2 * stdGaussianDensity x) / 2) := (hintA.add hintB).div_const 2
  have hDeq : ∀ x, D x = (hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x) / 2 -
      hP x ^ 2 * stdGaussianDensity x := by
    intro x; simp only [hDdef]; ring
  have hintD : Integrable D := by
    have : D = fun x => (hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x) / 2 -
        hP x ^ 2 * stdGaussianDensity x := funext hDeq
    rw [this]
    exact hintAB.sub hintP
  have hpos : 0 < ∫ x, D x := by
    rw [integral_pos_iff_support_of_nonneg_ae (eventually_of_forall hDnonneg) hintD]
    apply lt_of_lt_of_le (hUopen.measure_pos volume hUne)
    apply measure_mono
    intro x hx
    exact (hDpos x hx).ne'
  have hsplit : ∫ x, D x = ((∫ x, hA x ^ 2 * stdGaussianDensity x) +
      ∫ x, hB x ^ 2 * stdGaussianDensity x) / 2 - ∫ x, hP x ^ 2 * stdGaussianDensity x := by
    calc ∫ x, D x = ∫ x, ((hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x) / 2 -
          hP x ^ 2 * stdGaussianDensity x) := integral_congr_ae (eventually_of_forall hDeq)
      _ = (∫ x, (hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x) / 2) -
          ∫ x, hP x ^ 2 * stdGaussianDensity x := integral_sub hintAB hintP
      _ = (∫ x, (hA x ^ 2 * stdGaussianDensity x + hB x ^ 2 * stdGaussianDensity x)) / 2 -
          ∫ x, hP x ^ 2 * stdGaussianDensity x := by rw [integral_div]
      _ = _ := by rw [integral_add hintA hintB]
  have hrefl : ∫ x, hB x ^ 2 * stdGaussianDensity x = ∫ x, hA x ^ 2 * stdGaussianDensity x := by
    have h := plain_second_moment_reflect hd J c w
    simp only [hBdef, hAdef, eA]
    exact h
  have key : 0 < ((∫ x, hA x ^ 2 * stdGaussianDensity x) +
      ∫ x, hB x ^ 2 * stdGaussianDensity x) / 2 - ∫ x, hP x ^ 2 * stdGaussianDensity x :=
    hsplit ▸ hpos
  rw [hrefl] at key
  linarith

/-- Positivity of the plain mixed energy, the centered one plus the
first-moment correction, by the same stretching argument for the ReLU feature. -/
theorem plain_mixed_energy_pos (hd : 2 ≤ d)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hc : ∀ i, 0 ≤ c i)
    (i : Fin n) (hci : 0 < c i) (hQi : normalPart J (w i) ≠ 0) :
    0 < mixedEnergy J c w + (π / 2) * ‖∑ i, c i • normalPart J (w i)‖ ^ 2 := by
  have hjetP := plain_student_energy_jet (π / 2) c w (normalMap J) hw
  have hjetC := student_energy_jet c w (normalMap J) hw
  have hslope : (∑ i, ∑ j, c i * c j * pairSlope (w i) (w j) (normalMap J)) =
      2 * mixedEnergy J c w := by
    rw [← eq_second_moment_derivative J c w hw]
    exact hjetC.first.deriv.symm
  have hAM : normalPart J (moment c w) = ∑ i, c i • normalPart J (w i) := by
    have : normalMap J (moment c w) = ∑ i, c i • normalMap J (w i) := by
      simp only [moment, map_sum, LinearMap.map_smul]
    exact this
  have hMAM : (inner (moment c w) (normalMap J (moment c w)) : ℝ) =
      ‖∑ i, c i • normalPart J (w i)‖ ^ 2 := by
    change (inner (moment c w) (normalPart J (moment c w)) : ℝ) = _
    rw [normal_inner, real_inner_self_eq_norm_sq, hAM]
  have hD : HasDerivAt (plainStudentEnergy (π / 2) c w (normalMap J))
      (2 * (mixedEnergy J c w + (π / 2) * ‖∑ i, c i • normalPart J (w i)‖ ^ 2)) 0 := by
    have h := hjetP.first
    rw [hslope, hMAM] at h
    convert h using 1
    ring
  have hconv := plainStudentEnergy_convex hd c hc w (normalMap J)
  have hsecant : plainStudentEnergy (π / 2) c w (normalMap J) 0 -
      plainStudentEnergy (π / 2) c w (normalMap J) (-1) ≤
      2 * (mixedEnergy J c w + (π / 2) * ‖∑ i, c i • normalPart J (w i)‖ ^ 2) := by
    have hlim : Tendsto (slope (plainStudentEnergy (π / 2) c w (normalMap J)) 0) (𝓝[<] 0)
        (𝓝 (2 * (mixedEnergy J c w + (π / 2) * ‖∑ i, c i • normalPart J (w i)‖ ^ 2))) :=
      (hasDerivAt_iff_tendsto_slope.mp hD).mono_left
        (nhdsWithin_mono 0 (fun y (hy : y ∈ Set.Iio 0) => ne_of_lt hy))
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsWithin_Iio (show (0:ℝ) ∈ Set.Ioc (-1) 0 from ⟨by norm_num, le_refl 0⟩)]
      with y hy
    have h := hconv.secant_mono (Set.mem_univ 0) (Set.mem_univ (-1)) (Set.mem_univ y)
      (by norm_num) (ne_of_lt hy.2) hy.1.le
    rw [slope_def_field]
    have hL : (plainStudentEnergy (π / 2) c w (normalMap J) (-1) -
        plainStudentEnergy (π / 2) c w (normalMap J) 0) / (-1 - 0) =
        plainStudentEnergy (π / 2) c w (normalMap J) 0 -
          plainStudentEnergy (π / 2) c w (normalMap J) (-1) := by
      ring
    rw [hL] at h
    exact h
  have hgap : plainStudentEnergy (π / 2) c w (normalMap J) (-1) <
      plainStudentEnergy (π / 2) c w (normalMap J) 0 := by
    rw [← plain_second_moment_on_linear_path hd c w (normalMap J) (-1),
      ← plain_second_moment_on_linear_path hd c w (normalMap J) 0]
    exact mul_lt_mul_of_pos_left (plain_second_moment_projected_lt hd J c w hc i hci hQi)
      (by positivity)
  linarith

end PaperLeanFormalization.NormalStretching

namespace PaperLeanFormalization.FirstDerivativeExpectation

open MeasureTheory
open PaperLeanFormalization.Definitions
open PaperLeanFormalization.Preliminaries

def net {d n : ℕ} (c : Fin n → ℝ) (V : Fin n → Vec d) (x : Vec d) : ℝ :=
  ∑ i, c i * (|(inner (V i) x : ℝ)| / 2)

def variation {d n : ℕ} (c : Fin n → ℝ) (V Z : Fin n → Vec d) (x : Vec d) : ℝ :=
  ∑ i, c i * (Real.sign (inner (V i) x) / 2) * (inner (Z i) x : ℝ)

def size {d n : ℕ} (c : Fin n → ℝ) (V : Fin n → Vec d) : ℝ :=
  ∑ i, |c i| * ‖V i‖

theorem size_nonneg {d n : ℕ} (c : Fin n → ℝ) (V : Fin n → Vec d) :
    0 ≤ size c V := Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)

private theorem abs_affine_derivative (a b t : ℝ) (h : a + t * b ≠ 0 ∨ b = 0) :
    HasDerivAt (fun r : ℝ => |a + r * b|) (Real.sign (a + t * b) * b) t := by
  rcases h with h | rfl
  · have hd : HasDerivAt (fun r : ℝ => a + r * b) b t := by
      simpa only [one_mul] using ((hasDerivAt_id t).mul_const b).const_add a
    rcases lt_or_gt_of_ne h with hn | hp
    · have heq : (fun r : ℝ => |a + r * b|) =ᶠ[𝓝 t] (fun r => -(a + r * b)) := by
        filter_upwards [hd.continuousAt.eventually (gt_mem_nhds hn)] with r hr
        exact abs_of_neg hr
      simpa only [Real.sign_of_neg hn, neg_one_mul] using
        hd.neg.congr_of_eventuallyEq heq
    · have heq : (fun r : ℝ => |a + r * b|) =ᶠ[𝓝 t] (fun r => a + r * b) := by
        filter_upwards [hd.continuousAt.eventually (lt_mem_nhds hp)] with r hr
        exact abs_of_pos hr
      simpa only [Real.sign_of_pos hp, one_mul] using hd.congr_of_eventuallyEq heq
  · simpa only [mul_zero, add_zero] using hasDerivAt_const t |a|

/-- `eq:student-first-derivative`, with the kink qualification made explicit.
The manuscript's generator network is the specialization `c i = 1`.
A row with zero displacement also has this derivative at a kink. -/
theorem eq_student_first_derivative {d n : ℕ} (c : Fin n → ℝ)
    (V Z : Fin n → Vec d) (x : Vec d) (t : ℝ)
    (h : ∀ i, (inner (V i + t • Z i) x : ℝ) ≠ 0 ∨ (inner (Z i) x : ℝ) = 0) :
    HasDerivAt (fun r => net c (fun i => V i + r • Z i) x)
      (variation c (fun i => V i + t • Z i) Z x) t := by
  have hi (i : Fin n) := (abs_affine_derivative (inner (V i) x) (inner (Z i) x) t
    (by simpa only [inner_add_left, real_inner_smul_left] using h i)).div_const 2 |>.const_mul (c i)
  convert HasDerivAt.sum (u := (Finset.univ : Finset (Fin n))) (fun i _ => hi i) using 1
  · funext r
    simp only [net, inner_add_left, real_inner_smul_left]
  · unfold variation
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_add_left, real_inner_smul_left]
    ring

/-- The exceptional hyperplane of any nonzero row has Lebesgue measure zero. -/
theorem ae_inner_ne_zero {d : ℕ} (V : Vec d) (hV : V ≠ 0) :
    ∀ᵐ x : Vec d, (inner V x : ℝ) ≠ 0 := by
  let L : Vec d →ₗ[ℝ] ℝ := (innerSL ℝ V).toLinearMap
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro hk
    have hm : V ∈ LinearMap.ker L := by rw [hk]; trivial
    have hz : (inner V V : ℝ) = 0 := hm
    exact hV (inner_self_eq_zero.mp hz)
  have H := Measure.addHaar_submodule volume (LinearMap.ker L) hker
  rw [ae_iff]
  simpa only [not_not] using H

theorem ae_student_first_derivative {d n : ℕ} (c : Fin n → ℝ)
    (V Z : Fin n → Vec d) (h : ∀ i, V i ≠ 0 ∨ Z i = 0) :
    ∀ᵐ x : Vec d, HasDerivAt (fun t : ℝ => net c (fun i => V i + t • Z i) x)
      (variation c V Z x) 0 := by
  have H (i : Fin n) : ∀ᵐ x : Vec d, (inner (V i) x : ℝ) ≠ 0 ∨
      (inner (Z i) x : ℝ) = 0 := by
    rcases h i with hi | hi
    · exact (ae_inner_ne_zero (V i) hi).mono fun _ hx => Or.inl hx
    · exact eventually_of_forall fun _ => Or.inr (by rw [hi, inner_zero_left])
  filter_upwards [eventually_all.mpr H] with x hx
  simpa only [variation, zero_smul, add_zero] using eq_student_first_derivative c V Z x 0
    (by simpa only [zero_smul, add_zero] using hx)

theorem continuous_net {d n : ℕ} (c : Fin n → ℝ) (V : Fin n → Vec d) :
    Continuous (net c V) := by
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul (((continuous_const.inner continuous_id).abs).div_const 2)

theorem net_bound {d n : ℕ} (c : Fin n → ℝ) (V : Fin n → Vec d) (x : Vec d) :
    |net c V x| ≤ size c V * ‖x‖ := by
  calc
    _ ≤ ∑ i, |c i * (|(inner (V i) x : ℝ)| / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|c i| * ‖V i‖) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_div, abs_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have H := abs_real_inner_le_norm (V i) x
      nlinarith [mul_nonneg (abs_nonneg (c i)) (abs_nonneg (inner (V i) x : ℝ)),
        mul_le_mul_of_nonneg_left H (abs_nonneg (c i))]
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem net_path_lipschitz {d n : ℕ} (c : Fin n → ℝ) (V Z : Fin n → Vec d)
    (x : Vec d) (t r : ℝ) :
    |net c (fun i => V i + t • Z i) x - net c (fun i => V i + r • Z i) x| ≤
      (size c Z * ‖x‖) * |t - r| := by
  unfold net
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |c i * (|inner (V i + t • Z i) x| / 2) -
      c i * (|inner (V i + r • Z i) x| / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|c i| * ‖Z i‖ * ‖x‖) * |t - r| := by
      apply Finset.sum_le_sum
      intro i _
      have H := abs_abs_sub_abs_le_abs_sub
        (inner (V i + t • Z i) x : ℝ) (inner (V i + r • Z i) x)
      have heq : (inner (V i + t • Z i) x : ℝ) - inner (V i + r • Z i) x =
          (t - r) * inner (Z i) x := by
        simp only [inner_add_left, real_inner_smul_left]
        ring
      rw [heq, abs_mul] at H
      have Hinner := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (Z i) x)
        (abs_nonneg (t - r))
      rw [← mul_sub, ← sub_div, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have Hc := mul_le_mul_of_nonneg_left (H.trans Hinner) (abs_nonneg (c i))
      have hp := mul_nonneg (abs_nonneg (c i))
        (abs_nonneg (|(inner (V i + t • Z i) x : ℝ)| - |inner (V i + r • Z i) x|))
      nlinarith only [Hc, hp]
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

private theorem measurable_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const)

theorem measurable_variation {d n : ℕ} (c : Fin n → ℝ) (V Z : Fin n → Vec d) :
    Measurable (variation c V Z) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.mul ((measurable_sign.comp
    (continuous_const.inner continuous_id).measurable).div_const 2)).mul
      (continuous_const.inner continuous_id).measurable

private theorem square_density_lipschitz (f : ℝ → ℝ) (M B D : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Metric.ball (0 : ℝ) 1, |f t| ≤ M)
    (hl : ∀ t r, |f t - f r| ≤ B * |t - r|) :
    LipschitzOnWith (Real.nnabs (M * B * D))
      (fun t => (1 / 2 : ℝ) * f t ^ 2 * D) (Metric.ball (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht r hr
  rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs,
    abs_of_nonneg (mul_nonneg (mul_nonneg hM hB) hD)]
  have hsum : |f t + f r| ≤ 2 * M :=
    (abs_add _ _).trans (by linarith only [hb t ht, hb r hr])
  have hp := mul_le_mul hsum (hl t r) (abs_nonneg (f t - f r))
    (mul_nonneg (by norm_num) hM)
  have hpD := mul_le_mul_of_nonneg_right hp hD
  have heq : (1 / 2 : ℝ) * f t ^ 2 * D - (1 / 2 : ℝ) * f r ^ 2 * D =
      (1 / 2 : ℝ) * ((f t + f r) * (f t - f r)) * D := by ring
  rw [heq, abs_mul, abs_mul, abs_mul, abs_of_nonneg hD]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith only [hpD]

/-- `eq:loss-first-derivative`, for the literal Gaussian square loss.
The domination is a constant times `‖x‖²` times the Gaussian density. Thus
zero rows are allowed exactly when they have zero displacement, and neither
pairwise noncollision nor positive masses is required. -/
theorem eq_loss_first_derivative {d n m : ℕ} (hd : 2 ≤ d)
    (c : Fin n → ℝ) (V Z : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hrow : ∀ i, V i ≠ 0 ∨ Z i = 0) :
    HasDerivAt (fun t : ℝ => CenteredLoss c (fun i => V i + t • Z i) s v)
      (∫ x : Vec d, (net c V x - net s v x) * variation c V Z x * stdGaussianDensity x) 0 := by
  let R : ℝ → Vec d → ℝ := fun t x => net c (fun i => V i + t • Z i) x - net s v x
  let M := size c Z + size c V + size s v
  let B := size c Z
  have hM : 0 ≤ M := add_nonneg (add_nonneg (size_nonneg c Z) (size_nonneg c V)) (size_nonneg s v)
  have hB : 0 ≤ B := size_nonneg c Z
  have hdens : Continuous (fun x : Vec d => stdGaussianDensity x) := by
    unfold stdGaussianDensity
    exact continuous_const.mul
      (continuous_exp.comp (((continuous_norm.pow 2).neg).div_const 2))
  have hdens0 (x : Vec d) : 0 ≤ stdGaussianDensity x := by
    unfold stdGaussianDensity
    positivity
  have hR (t : ℝ) : Continuous (R t) := (continuous_net c _).sub (continuous_net s v)
  have hb0 (x : Vec d) : |R 0 x| ≤ (size c V + size s v) * ‖x‖ := by
    change |net c (fun i => V i + (0 : ℝ) • Z i) x - net s v x| ≤ _
    simp only [zero_smul, add_zero]
    exact (abs_sub _ _).trans (by nlinarith only [net_bound c V x, net_bound s v x])
  have hl (x : Vec d) (t r : ℝ) : |R t x - R r x| ≤ B * ‖x‖ * |t - r| := by
    simpa only [R, sub_sub_sub_cancel_right] using net_path_lipschitz c V Z x t r
  have hb (x : Vec d) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) : |R t x| ≤ M * ‖x‖ := by
    have ht' : |t| ≤ 1 := (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht : |t| < 1).le
    have H := (abs_sub_le (R t x) (R 0 x) 0)
    rw [sub_zero, sub_zero] at H
    have Hlip := hl x t 0
    rw [sub_zero] at Hlip
    have Hbound := mul_le_mul_of_nonneg_left ht' (mul_nonneg hB (norm_nonneg x))
    dsimp only [M, B] at *
    nlinarith only [H, Hlip, hb0 x, Hbound]
  have hbase : Integrable (fun x : Vec d => (1 / 2 : ℝ) * R 0 x ^ 2 * stdGaussianDensity x) := by
    convert (gaussian_growth_square_integrable hd (hR 0) hb0).const_mul (1 / 2 : ℝ) using 1
    ext x
    ring
  have hbound : Integrable (fun x : Vec d => (M * ‖x‖) * (B * ‖x‖) * stdGaussianDensity x) := by
    convert (gaussian_norm_square_integrable hd).const_mul (M * B) using 1
    ext x
    ring
  have hmeas : AEStronglyMeasurable (fun x : Vec d =>
      R 0 x * variation c V Z x * stdGaussianDensity x) volume :=
    (((hR 0).measurable.mul (measurable_variation c V Z)).mul hdens.measurable).aestronglyMeasurable
  have H := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume)
    (x₀ := (0 : ℝ)) (ε := 1) (by norm_num)
    (F := fun t x => (1 / 2 : ℝ) * R t x ^ 2 * stdGaussianDensity x)
    (F' := fun x => R 0 x * variation c V Z x * stdGaussianDensity x)
    (eventually_of_forall fun t =>
      ((continuous_const.mul ((hR t).pow 2)).mul hdens).aestronglyMeasurable)
    hbase hmeas
    (eventually_of_forall fun x => square_density_lipschitz (fun t => R t x)
      (M * ‖x‖) (B * ‖x‖) (stdGaussianDensity x)
      (mul_nonneg hM (norm_nonneg x)) (mul_nonneg hB (norm_nonneg x)) (hdens0 x)
      (hb x) (hl x)) hbound
    (by
      filter_upwards [ae_student_first_derivative c V Z hrow] with x hx
      convert (((hx.sub_const (net s v x)).pow 2).const_mul (1 / 2 : ℝ)).mul_const
        (stdGaussianDensity x) using 1
      simp only [R, zero_smul, add_zero, pow_one]
      ring)
  have heq : (fun t : ℝ => CenteredLoss c (fun i => V i + t • Z i) s v) =
      (fun t => ∫ x : Vec d, (1 / 2 : ℝ) * R t x ^ 2 * stdGaussianDensity x) := by
    funext t
    unfold CenteredLoss
    rw [← integral_mul_left]
    congr 1
    ext x
    dsimp only [R, net]
    ring
  rw [heq]
  simpa only [R, zero_smul, add_zero] using H.2

end PaperLeanFormalization.FirstDerivativeExpectation

namespace PaperLeanFormalization.FirstDerivativeExpectation

open MeasureTheory
open PaperLeanFormalization.Definitions
open PairKernelJet NormalTrace AmplitudeNormalVariation
open ConfinementTraceAssembly hiding Vec Parameters

/-- The actual Gaussian first variation agrees with the first component of
the fresh finite pair jet, by uniqueness of the derivative of one literal
self-loss. Both expectation displays are necessary inputs to this comparison. -/
theorem first_expectation_eq_pair_derivative {d n : ℕ} (hd : 2 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (A : Vec d →ₗ[ℝ] Vec d)
    (hw : ∀ i, ‖w i‖ = 1) :
    (∫ x : Vec d, net c w x * variation c w (fun i => A (w i)) x * stdGaussianDensity x) =
      (1 / (4 * π)) * deriv (studentPairEnergy c w A) 0 := by
  let s : Fin 0 → ℝ := fun _ => 0
  let v : Fin 0 → Vec d := fun _ => 0
  have hrow (i : Fin n) : w i ≠ 0 ∨ A (w i) = 0 := by
    apply Or.inl
    intro hi
    have H := hw i
    rw [hi, norm_zero] at H
    norm_num at H
  have H := eq_loss_first_derivative hd c w (fun i => A (w i)) s v hrow
  have heq : (fun t : ℝ => CenteredLoss c (fun i => w i + t • A (w i)) s v) =
      fun t => (1 / (4 * π)) * studentPairEnergy c w A t := by
    funext t
    unfold CenteredLoss
    simp only [Fin.sum_univ_zero, sub_zero]
    rw [SecondMomentPair.second_moment_on_linear_path_unscaled hd c w A t]
    ring
  rw [heq] at H
  simp only [net, Fin.sum_univ_zero, sub_zero] at H
  have HK := (student_energy_jet c w A hw).first.const_mul (1 / (4 * π))
  rw [(student_energy_jet c w A hw).first.deriv]
  exact H.unique HK

/-- The amplitude/normal mixed derivative is the displayed actual Gaussian
expectation. The normal stationarity used here is precisely the reason the
teacher contribution disappears in the manuscript. -/
theorem actual_mixed_eq_gaussian_expectation {d r n m : ℕ} (hd : 2 ≤ d)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (variableKernelLoss s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    deriv (fun a => deriv (fun t => variableKernelLoss s v
      (massScale (1+a) (polarPath c w (normalMap J) t))) 0) 0 =
      (2 * π) * (∫ x : Vec d, net c w x *
        variation c w (fun i => normalMap J (w i)) x * stdGaussianDensity x) := by
  rw [actual_mixed_derivative_eq_half_self_derivative J c w s v hw hv hvJ hmin,
    first_expectation_eq_pair_derivative hd c w (normalMap J) hw]
  field_simp [Real.pi_ne_zero]
  ring

/-- The trace/PSD conclusion forces the literal mixed expectation to vanish;
its evaluated pair moment then forces the mixed energy to vanish. -/
theorem centered_mixed_energy_zero_from_expectation {d r n m : ℕ} (hd : 2 ≤ d)
    (J : Vec r →ₗᵢ[ℝ] Vec d) (B : OrthonormalBasis (Fin d) ℝ (Vec d))
    (c : Fin n → ℝ) (w : Fin n → Vec d) (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (hvJ : ∀ k, v k ∈ Set.range J)
    (hmin : IsLocalMinOn (variableKernelLoss s v) {p | ∀ i, ‖p.2 i‖ = 1} (c,w)) :
    mixedEnergy J c w = 0 := by
  have hexpectation : (2 * π) * (∫ x : Vec d, net c w x *
      variation c w (fun i => normalMap J (w i)) x * stdGaussianDensity x) = 0 := by
    rw [first_expectation_eq_pair_derivative hd c w (normalMap J) hw,
      centered_self_energy_derivative_zero J B c w s v hw hv hvJ hmin,
      mul_zero, mul_zero]
  have hactual := (actual_mixed_eq_gaussian_expectation hd J c w s v hw hv hvJ hmin).trans hexpectation
  exact (eq_mixed_term_formula J c w s v hw hv hvJ hmin).symm.trans hactual

end PaperLeanFormalization.FirstDerivativeExpectation

namespace PaperLeanFormalization.Geometry


open PaperLeanFormalization

open PaperLeanFormalization

/-- Every unit planar vector has a literal angle representative. -/
theorem exists_angle {x : Definitions.Vec 2} (hx : ‖x‖ = 1) :
    ∃ t : ℝ, Definitions.Angle t = x :=
  FinitePlane.exists_angle_of_norm_eq_one hx

/-- The displayed centered kernel has period `π`: cosine and arcsine both
change sign, while the squared cosine in the square root does not. -/
theorem centered_planar_kernel_periodic : Function.Periodic Planar.kernel Real.pi := by
  intro x
  simp only [Planar.kernel, Real.cos_add_pi, Real.arcsin_neg, neg_mul_neg, neg_sq]

/-- Independent integer changes of angle representatives leave each kernel
entry unchanged. -/
theorem centered_planar_kernel_integer_shifts (x y : ℝ) (k l : ℤ) :
    Planar.kernel ((x + (k : ℝ) * Real.pi) - (y + (l : ℝ) * Real.pi)) =
      Planar.kernel (x - y) := by
  have hgap : (x + (k : ℝ) * Real.pi) - (y + (l : ℝ) * Real.pi) =
      (x - y) + ((k - l : ℤ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [hgap]
  exact (centered_planar_kernel_periodic.int_mul (k - l)) (x - y)

/-- The finite variable-loss formula is invariant under all independent
integer-`π` changes of student and teacher representatives. -/
theorem variable_loss_integer_shifts {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (k : Fin n → ℤ) (l : Fin m → ℤ) :
    Planar.variableLoss s (fun a ↦ beta a + (l a : ℝ) * Real.pi)
      (c, fun i ↦ theta i + (k i : ℝ) * Real.pi) =
        Planar.variableLoss s beta (c, theta) := by
  simp only [Planar.variableLoss, centered_planar_kernel_integer_shifts]

/-- Local minima transport along a continuous angle translation. The
modulo operation itself need not be continuous at interval endpoints. -/
theorem local_min_of_integer_angle_shifts {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (k : Fin n → ℤ) (l : Fin m → ℤ)
    (hmin : IsLocalMin
      (Planar.variableLoss s (fun a ↦ beta a + (l a : ℝ) * Real.pi))
      (c, fun i ↦ theta i + (k i : ℝ) * Real.pi)) :
    IsLocalMin (Planar.variableLoss s beta) (c, theta) := by
  let translate : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun p ↦ (p.1, fun i ↦ p.2 i + (k i : ℝ) * Real.pi)
  have hcont : Continuous translate := by
    apply Continuous.prod_mk continuous_fst
    exact continuous_pi fun i ↦ ((continuous_apply i).comp continuous_snd).add continuous_const
  have hh := hmin.comp_continuous (g := translate) (b := (c, theta))
    hcont.continuousAt
  convert hh using 1
  funext p
  exact (variable_loss_integer_shifts p.1 p.2 s beta k l).symm

/-- Canonical unoriented line angle in the half-open interval `[0,π)`. -/
def canonicalPlanarAngle (x : ℝ) : ℝ := toIcoMod Real.pi_pos 0 x

theorem canonical_planar_angle_range (x : ℝ) :
    0 ≤ canonicalPlanarAngle x ∧ canonicalPlanarAngle x < Real.pi :=
  toIcoMod_mem_Ico' Real.pi_pos x

/-- The original angle differs from its canonical representative by an
integer multiple of `π`. -/
theorem canonical_planar_angle_decomposition (x : ℝ) :
    canonicalPlanarAngle x + ((toIcoDiv Real.pi_pos 0 x : ℤ) : ℝ) * Real.pi = x := by
  simpa only [canonicalPlanarAngle, zsmul_eq_mul] using
    toIcoMod_add_toIcoDiv_zsmul Real.pi_pos 0 x

theorem variable_loss_canonical_angles {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    Planar.variableLoss s (fun a ↦ canonicalPlanarAngle (beta a))
      (c, fun i ↦ canonicalPlanarAngle (theta i)) =
        Planar.variableLoss s beta (c, theta) := by
  have h := variable_loss_integer_shifts c
    (fun i ↦ canonicalPlanarAngle (theta i)) s
    (fun a ↦ canonicalPlanarAngle (beta a))
    (fun i ↦ toIcoDiv Real.pi_pos 0 (theta i))
    (fun a ↦ toIcoDiv Real.pi_pos 0 (beta a))
  simp_rw [canonical_planar_angle_decomposition] at h
  exact h.symm

/-- Normalize both angle families while transporting the full signed-mass
local minimum, with masses unchanged. -/
theorem local_min_canonical_angles {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hmin : IsLocalMin (Planar.variableLoss s beta) (c, theta)) :
    IsLocalMin (Planar.variableLoss s (fun a ↦ canonicalPlanarAngle (beta a)))
      (c, fun i ↦ canonicalPlanarAngle (theta i)) := by
  apply local_min_of_integer_angle_shifts c
    (fun i ↦ canonicalPlanarAngle (theta i)) s
    (fun a ↦ canonicalPlanarAngle (beta a))
    (fun i ↦ toIcoDiv Real.pi_pos 0 (theta i))
    (fun a ↦ toIcoDiv Real.pi_pos 0 (beta a))
  simp_rw [canonical_planar_angle_decomposition]
  exact hmin

/-- The canonical-angle data needed by the planar counting argument,
including preservation of the teacher's self-fit loss value. -/
theorem exists_canonical_angles_local_min {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hmin : IsLocalMin (Planar.variableLoss s beta) (c, theta)) :
    ∃ theta' : Fin n → ℝ, ∃ beta' : Fin m → ℝ,
      (∀ i, 0 ≤ theta' i ∧ theta' i < Real.pi) ∧
      (∀ a, 0 ≤ beta' a ∧ beta' a < Real.pi) ∧
      IsLocalMin (Planar.variableLoss s beta') (c, theta') ∧
      Planar.variableLoss s beta' (c, theta') = Planar.variableLoss s beta (c, theta) ∧
      Planar.variableLoss s beta' (s, beta') = Planar.variableLoss s beta (s, beta) := by
  refine ⟨(fun i ↦ canonicalPlanarAngle (theta i)),
    (fun a ↦ canonicalPlanarAngle (beta a)),
    (fun i ↦ canonical_planar_angle_range (theta i)),
    (fun a ↦ canonical_planar_angle_range (beta a)),
    local_min_canonical_angles c theta s beta hmin,
    variable_loss_canonical_angles c theta s beta,
    variable_loss_canonical_angles s beta s beta⟩

theorem kernel_sub_canonical_angle (x a : ℝ) :
    Planar.kernel (x - canonicalPlanarAngle a) = Planar.kernel (x - a) := by
  have h := centered_planar_kernel_integer_shifts x (canonicalPlanarAngle a)
    0 (toIcoDiv Real.pi_pos 0 a)
  simpa only [Int.cast_zero, zero_mul, add_zero, canonical_planar_angle_decomposition]
    using h.symm

theorem residual_canonical_angles {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    Planar.residual c (fun i ↦ canonicalPlanarAngle (theta i))
      s (fun k ↦ canonicalPlanarAngle (beta k)) x = Planar.residual c theta s beta x := by
  simp only [Planar.residual, kernel_sub_canonical_angle]

theorem variable_loss_common_angle_translation {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (t : ℝ) :
    Planar.variableLoss s (fun k ↦ beta k - t) (c, fun i ↦ theta i - t) =
      Planar.variableLoss s beta (c, theta) := by
  simp only [Planar.variableLoss, sub_sub_sub_cancel_right]

theorem local_min_common_angle_translation {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (t : ℝ)
    (hmin : IsLocalMin (Planar.variableLoss s beta) (c, theta)) :
    IsLocalMin (Planar.variableLoss s (fun k ↦ beta k - t))
      (c, fun i ↦ theta i - t) := by
  let translate : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun p ↦ (p.1, fun i ↦ p.2 i + t)
  have hcont : Continuous translate :=
    continuous_fst.prod_mk (continuous_pi fun i ↦
      ((continuous_apply i).comp continuous_snd).add continuous_const)
  have hmin' : IsLocalMin (Planar.variableLoss s beta)
      (translate (c, fun i ↦ theta i - t)) := by
    simpa only [translate, sub_add_cancel] using hmin
  have h := hmin'.comp_continuous (g := translate)
    (b := (c, fun i ↦ theta i - t)) hcont.continuousAt
  convert h using 1
  funext p
  have heq := variable_loss_common_angle_translation p.1
    (fun i ↦ p.2 i + t) s beta t
  simpa only [add_sub_cancel, translate, Function.comp_apply] using heq

theorem residual_common_angle_translation {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (t x : ℝ) :
    Planar.residual c (fun i ↦ theta i - t) s (fun k ↦ beta k - t) x =
      Planar.residual c theta s beta (t + x) := by
  unfold Planar.residual
  simp only [show ∀ a : ℝ, x - (a-t) = t+x-a by intro a; ring]

/-- The only use of nonnegative teacher masses in the planar propagation
argument: a positive net mass is carried by an actual positive student. -/
theorem positive_net_weight_has_positive_student {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (hs : ∀ k, 0 ≤ s k)
    (y : ℝ) (hy : 0 < Planar.netWeight c theta s beta y) :
    ∃ i, theta i = y ∧ 0 < c i := by
  classical
  by_contra hnone
  have hstudent : (∑ i in Finset.univ.filter (fun i => theta i = y), c i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact le_of_not_gt (fun hp => hnone ⟨i, (Finset.mem_filter.mp hi).2, hp⟩)
  have hteacher : 0 ≤ ∑ k in Finset.univ.filter (fun k => beta k = y), s k :=
    Finset.sum_nonneg fun k _ => hs k
  unfold Planar.netWeight at hy
  linarith only [hy, hstudent, hteacher]

/-- Shifting every angle by `t` and reducing modulo `π` transports the residual's
derivative: at `x` it is the derivative of the original residual at `t + x`. -/
theorem deriv_residual_shift_canonical {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (t x : ℝ) :
    deriv (Planar.residual c (fun i ↦ canonicalPlanarAngle (theta i - t))
      s (fun k ↦ canonicalPlanarAngle (beta k - t))) x =
      deriv (Planar.residual c theta s beta) (t + x) := by
  have hshift : Planar.residual c (fun i ↦ canonicalPlanarAngle (theta i - t))
      s (fun k ↦ canonicalPlanarAngle (beta k - t)) =
      Planar.residual c theta s beta ∘ HAdd.hAdd t := by
    funext y
    exact (residual_canonical_angles c (fun i ↦ theta i - t) s (fun k ↦ beta k - t) y).trans
      (residual_common_angle_translation c theta s beta t y)
  rw [hshift]
  have h := (Planar.hasDerivAt_residual c theta s beta (t + x)).comp x
    ((hasDerivAt_id x).const_add t)
  rw [h.deriv, (Planar.hasDerivAt_residual c theta s beta (t + x)).deriv, mul_one]

/-- The derivative of the residual is `π`-periodic, as the residual is. -/
theorem deriv_residual_add_pi {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (x : ℝ) :
    deriv (Planar.residual c theta s beta) (x + π) =
      deriv (Planar.residual c theta s beta) x := by
  have hfun : Planar.residual c theta s beta =
      Planar.residual c theta s beta ∘ (fun y ↦ id y + π) := by
    funext y
    exact (Planar.residual_periodic c theta s beta y).symm
  have h := (Planar.hasDerivAt_residual c theta s beta (x + π)).comp x
    ((hasDerivAt_id x).add_const π)
  conv_rhs => rw [hfun]
  rw [h.deriv, (Planar.hasDerivAt_residual c theta s beta (x + π)).deriv, mul_one]

/-- The zero arc excludes positive net lines. With every positive net line a
double zero, the gap occupancy behind `lem:line-count` puts a negative line in
the gap of the last positive line; that gap also contains the zero arc, and
the gap lemma `lem:gap-sign` makes the residual negative there. The
nonnegative-teacher condition is used only to identify a positive student on
every positive net line. -/
theorem zero_arc_no_positive_line {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (hs : ∀ k, 0 ≤ s k)
    {ε xstar : ℝ} (hε : 0 < ε) (hxπ : xstar < π)
    (htheta : ∀ i, ε ≤ theta i ∧ theta i < xstar)
    (hbeta : ∀ k, ε ≤ beta k ∧ beta k < xstar)
    (hstart : ∀ x, 0 < x → x < ε → Planar.residual c theta s beta x = 0)
    (hcrit : fderiv ℝ (Planar.variableLoss s beta) (c, theta) = 0) :
    Planar.positiveLines c theta s beta = ∅ := by
  classical
  have hθ : ∀ i, 0 ≤ theta i ∧ theta i < π :=
    fun i ↦ ⟨hε.le.trans (htheta i).1, (htheta i).2.trans hxπ⟩
  have hβ : ∀ k, 0 ≤ beta k ∧ beta k < π :=
    fun k ↦ ⟨hε.le.trans (hbeta k).1, (hbeta k).2.trans hxπ⟩
  have hlines : ∀ x ∈ Finset.univ.image theta ∪ Finset.univ.image beta,
      ε ≤ x ∧ x < xstar := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact htheta i
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
      exact hbeta k
  have hzeros : ∀ x ∈ Planar.positiveLines c theta s beta,
      Planar.residual c theta s beta x = 0 ∧
        deriv (Planar.residual c theta s beta) x = 0 := by
    intro x hx
    have hpos : 0 < Planar.netWeight c theta s beta x := (Finset.mem_filter.mp hx).2
    obtain ⟨i, hi, hci⟩ :=
      positive_net_weight_has_positive_student c theta s beta hs x hpos
    have h := Planar.critical_point_double_zero hcrit i (ne_of_gt hci)
    rwa [hi] at h
  have hhalf : Planar.residual c theta s beta (ε / 2) = 0 :=
    hstart (ε / 2) (half_pos hε) (half_lt_self hε)
  by_contra hne
  have hnonempty : (Planar.positiveLines c theta s beta).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨r, hcard⟩ : ∃ r, (Planar.positiveLines c theta s beta).card = r + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr hnonempty)).symm⟩
  have hd := Planar.signed_sorted_positive_data c theta s beta hcard hzeros
  have hrange := Planar.signed_sorted_ranges c theta s beta hcard hθ hβ
  have heq := Planar.residual_eq_signed_sorted c theta s beta hcard
  dsimp only at hd hrange
  set a := (Planar.positiveLines c theta s beta).orderEmbOfFin hcard
  set b := (Planar.negativeLines c theta s beta).orderEmbOfFin rfl
  set u : Fin (r + 1) → ℝ := fun i ↦ Planar.netWeight c theta s beta (a i)
  set v := fun k ↦ -Planar.netWeight c theta s beta (b k)
  obtain ⟨gap, hgap, hsurj, -⟩ := Planar.ordered_count_of_double_zeros u a v b
    a.strictMono hrange.1 hrange.2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2
  obtain ⟨k, hk⟩ := hsurj (Fin.last r)
  have hkgap := (hgap k (Fin.last r)).mp hk
  have hright : Planar.Gaps.rightEndpoint a (Fin.last r) = a 0 + π := by
    simp [Planar.Gaps.rightEndpoint]
  rw [hright] at hkgap
  set t := a (Fin.last r)
  have hamem : ∀ i, a i ∈ Finset.univ.image theta ∪ Finset.univ.image beta :=
    fun i ↦ (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem _ hcard i)).1
  have ha0 : ε ≤ a 0 := (hlines _ (hamem 0)).1
  have htπ : t < π := (hlines _ (hamem (Fin.last r))).2.trans hxπ
  have ht0 : 0 ≤ t := (hrange.1 (Fin.last r)).1
  have ha0t : a 0 ≤ t := a.strictMono.monotone (Fin.zero_le _)
  have hl0 : 0 < a 0 + π - t := by linarith
  have hlπ : a 0 + π - t ≤ π := by linarith
  have hcanon : ∀ x, 0 ≤ x → x < π →
      canonicalPlanarAngle (x - t) = Planar.Gaps.relativeAngle t x := by
    intro x hx0 hxπ'
    unfold canonicalPlanarAngle Planar.Gaps.relativeAngle
    rw [toIcoMod_eq_iff]
    split_ifs
    · refine ⟨⟨by linarith, by linarith⟩, -1, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_one]
      ring
    · refine ⟨⟨by linarith, by linarith⟩, 0, ?_⟩
      simp
  set a' := fun i ↦ canonicalPlanarAngle (a i - t)
  set b' := fun k ↦ canonicalPlanarAngle (b k - t)
  have hshift : ∀ x, Planar.residual u a' v b' x = Planar.residual u a v b (t + x) :=
    fun x ↦ (residual_canonical_angles u (fun i ↦ a i - t) v (fun k ↦ b k - t) x).trans
      (residual_common_angle_translation u a v b t x)
  have hshiftD : ∀ x, deriv (Planar.residual u a' v b') x =
      deriv (Planar.residual u a v b) (t + x) :=
    fun x ↦ deriv_residual_shift_canonical u a v b t x
  have htorque : ∀ x, BeamGapKernel.residualTorque u a' v b' x =
      deriv (Planar.residual u a' v b') x :=
    fun x ↦ ((Planar.hasDerivAt_residual u a' v b' x).deriv).symm
  have hderivA : ∀ i, deriv (Planar.residual u a v b) (a i) = 0 :=
    fun i ↦ (Planar.hasDerivAt_residual u a v b (a i)).deriv.trans (hd.2.2.2.2 i)
  have hz0 : Planar.residual u a' v b' 0 = 0 := by
    rw [hshift, add_zero]
    exact hd.2.2.2.1 (Fin.last r)
  have ht0' : BeamGapKernel.residualTorque u a' v b' 0 = 0 := by
    rw [htorque, hshiftD, add_zero]
    exact hderivA (Fin.last r)
  have hzl : Planar.residual u a' v b' (a 0 + π - t) = 0 := by
    rw [hshift, show t + (a 0 + π - t) = a 0 + π by ring, Planar.residual_periodic]
    exact hd.2.2.2.1 0
  have htl : BeamGapKernel.residualTorque u a' v b' (a 0 + π - t) = 0 := by
    rw [htorque, hshiftD, show t + (a 0 + π - t) = a 0 + π by ring,
      deriv_residual_add_pi]
    exact hderivA 0
  have ha'range : ∀ i, 0 ≤ a' i ∧ a' i ≤ π :=
    fun i ↦ ⟨(canonical_planar_angle_range _).1, (canonical_planar_angle_range _).2.le⟩
  have hb'range : ∀ k, 0 ≤ b' k ∧ b' k ≤ π :=
    fun k ↦ ⟨(canonical_planar_angle_range _).1, (canonical_planar_angle_range _).2.le⟩
  have ha'gap : ∀ i, a' i = 0 ∨ a 0 + π - t ≤ a' i := by
    intro i
    show canonicalPlanarAngle (a i - t) = 0 ∨ a 0 + π - t ≤ canonicalPlanarAngle (a i - t)
    rw [hcanon (a i) (hrange.1 i).1 (hrange.1 i).2]
    unfold Planar.Gaps.relativeAngle
    by_cases hi : i = Fin.last r
    · left
      have hit : a i = t := by rw [hi]
      rw [hit, if_neg (lt_irrefl _), sub_self]
    · right
      have hlt : a i < t := a.strictMono (lt_of_le_of_ne (Fin.le_last i) hi)
      rw [if_pos hlt]
      linarith [a.strictMono.monotone (Fin.zero_le i)]
  have hgapsign := Planar.gap_sign_of_clean_config u a' v b' hl0 hlπ ha'range ha'gap
    hb'range hd.2.1 hz0 ht0' hzl htl
  dsimp only at hgapsign
  have hT : (Finset.univ.filter (fun k ↦ 0 < b' k ∧ b' k < a 0 + π - t)).Nonempty := by
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    show 0 < canonicalPlanarAngle (b k - t) ∧ canonicalPlanarAngle (b k - t) < a 0 + π - t
    rw [hcanon (b k) (hrange.2 k).1 (hrange.2 k).2]
    exact hkgap
  have hneg := (hgapsign.2 hT).1 (π - t + ε / 2) (by linarith) (by linarith)
  have hzero' : Planar.residual u a' v b' (π - t + ε / 2) = 0 := by
    rw [hshift, show t + (π - t + ε / 2) = ε / 2 + π by ring, Planar.residual_periodic,
      ← heq]
    exact hhalf
  linarith

/-- Without positive net lines the residual is a nonpositive combination of
positive kernels, so it vanishes on the zero arc only if no negative net line
exists either; then it vanishes identically. -/
theorem zero_arc_residual_zero_of_no_positive_line {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hstart : ∀ x, 0 < x → x < ε → Planar.residual c theta s beta x = 0)
    (hP : Planar.positiveLines c theta s beta = ∅) :
    ∀ x, Planar.residual c theta s beta x = 0 := by
  classical
  have hhalf : Planar.residual c theta s beta (ε / 2) = 0 :=
    hstart (ε / 2) (half_pos hε) (half_lt_self hε)
  have hkernel : ∀ x, 0 < Planar.kernel x := Planar.Gaps.centered_kernel_pos
  have hnonpos : ∀ x ∈ Finset.univ.image theta ∪ Finset.univ.image beta,
      Planar.netWeight c theta s beta x ≤ 0 := by
    intro x hx
    by_contra hlt
    push_neg at hlt
    have hmem : x ∈ Planar.positiveLines c theta s beta := Finset.mem_filter.mpr ⟨hx, hlt⟩
    rw [hP] at hmem
    exact Finset.not_mem_empty x hmem
  have hN : Planar.negativeLines c theta s beta = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hy' := Finset.mem_filter.mp hy
    have hlt : Planar.residual c theta s beta (ε / 2) < 0 := by
      rw [Planar.residual_eq_sum_netWeight, ← Finset.add_sum_erase _ _ hy'.1]
      apply add_neg_of_neg_of_nonpos
      · exact mul_neg_of_neg_of_pos hy'.2 (hkernel _)
      · apply Finset.sum_nonpos
        intro z hz
        exact mul_nonpos_iff.mpr
          (Or.inr ⟨hnonpos z (Finset.mem_of_mem_erase hz), (hkernel _).le⟩)
    linarith
  intro x
  rw [Planar.residual_eq_sum_netWeight]
  apply Finset.sum_eq_zero
  intro y hy
  rcases (hnonpos y hy).lt_or_eq with hlt | h0
  · exfalso
    have hmem : y ∈ Planar.negativeLines c theta s beta := Finset.mem_filter.mpr ⟨hy, hlt⟩
    rw [hN] at hmem
    exact Finset.not_mem_empty y hmem
  · rw [h0, zero_mul]

/-- Propagation of a zero arc around the circle by the gap Green function
(`lem:gap-sign`): the two lemmas above in sequence. -/
theorem canonical_zero_arc_residual_zero {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (hs : ∀ k, 0 ≤ s k)
    {ε xstar : ℝ} (hε : 0 < ε) (hxπ : xstar < π)
    (htheta : ∀ i, ε ≤ theta i ∧ theta i < xstar)
    (hbeta : ∀ k, ε ≤ beta k ∧ beta k < xstar)
    (hstart : ∀ x, 0 < x → x < ε → Planar.residual c theta s beta x = 0)
    (hcrit : fderiv ℝ (Planar.variableLoss s beta) (c, theta) = 0) :
    ∀ x, Planar.residual c theta s beta x = 0 :=
  zero_arc_residual_zero_of_no_positive_line c theta s beta hε hstart
    (zero_arc_no_positive_line c theta s beta hs hε hxπ htheta hbeta hstart hcrit)


/-- A finite family strictly inside `(0,π)` has a common positive margin
from both ends; the extra positive number can prescribe an arbitrary cap. -/
theorem finite_angles_have_margin {N : ℕ}
    (a : Fin N → ℝ) (ha : ∀ i, 0 < a i ∧ a i < π)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ∧ ∀ i, ε < a i ∧ a i < π - ε := by
  have hnear : ∀ᶠ ε : ℝ in 𝓝 0,
      ε < r ∧ ∀ i, ε < a i ∧ ε < π - a i := by
    apply Filter.Eventually.and (eventually_lt_nhds hr)
    rw [Filter.eventually_all]
    intro i
    exact (eventually_lt_nhds (ha i).1).and
      (eventually_lt_nhds (sub_pos.mpr (ha i).2))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hsmall : dist (δ/2) (0:ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith only [hδ]
  obtain ⟨hcap, hall⟩ := hball hsmall
  refine ⟨δ/2, half_pos hδ, hcap, fun i ↦ ⟨(hall i).1, ?_⟩⟩
  linarith only [(hall i).2]

/-- Inside every open arc one can choose a cut not congruent modulo `π`
to any of the finitely many atom angles. -/
theorem exists_nonatom_cut {N : ℕ} (a : Fin N → ℝ)
    (α : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, |t - α| < η / 2 ∧ ∀ i, 0 < canonicalPlanarAngle (a i - t) := by
  let bad : Set ℝ := range (fun p : Fin N × ℤ ↦ a p.1 - (p.2 : ℝ) * π)
  have hbad : bad.Countable := Set.countable_range _
  obtain ⟨t, ht, havoid⟩ := (hbad.dense_compl ℝ).inter_open_nonempty
    (Ioo (α-η/2) (α+η/2)) isOpen_Ioo
    (show (Ioo (α-η/2) (α+η/2)).Nonempty from ⟨α, by
      constructor <;> linarith only [hη]⟩)
  refine ⟨t, abs_lt.mpr ⟨by linarith only [ht.1], by linarith only [ht.2]⟩, ?_⟩
  intro i
  have hne : canonicalPlanarAngle (a i - t) ≠ 0 := by
    intro hzero
    apply havoid
    refine ⟨(i, toIcoDiv Real.pi_pos 0 (a i-t)), ?_⟩
    have h := canonical_planar_angle_decomposition (a i - t)
    rw [hzero, zero_add] at h
    dsimp
    linarith only [h]
  exact lt_of_le_of_ne (canonical_planar_angle_range (a i-t)).1 hne.symm

/-- Arbitrary open zero arcs propagate around the full projective circle.
The finite-atom cut is chosen inside the given arc, after which the fresh
causal proof applies. Only the teacher masses must be nonnegative. -/
theorem planar_residual_zero_of_open_zero_arc {n m : ℕ}
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) (hs : ∀ k, 0 ≤ s k)
    (hmin : IsLocalMin (Planar.variableLoss s beta) (c, theta))
    (α : ℝ) {η : ℝ} (hη : 0 < η)
    (hzero : ∀ x : ℝ, |x - α| < η → Planar.residual c theta s beta x = 0) :
    ∀ x : ℝ, Planar.residual c theta s beta x = 0 := by
  let a := Fin.append theta beta
  obtain ⟨t, ht, hcut⟩ := exists_nonatom_cut a α hη
  let theta' := fun i ↦ canonicalPlanarAngle (theta i - t)
  let beta' := fun k ↦ canonicalPlanarAngle (beta k - t)
  let a' := fun i ↦ canonicalPlanarAngle (a i - t)
  have harange : ∀ i, 0 < a' i ∧ a' i < π :=
    fun i ↦ ⟨hcut i, (canonical_planar_angle_range (a i-t)).2⟩
  obtain ⟨ε, hε, hεcap, hmargin⟩ := finite_angles_have_margin a' harange
    (lt_min (show 0 < η/4 by positivity) (show 0 < π/4 by positivity))
  have hεη : ε < η / 4 := hεcap.trans_le (min_le_left _ _)
  have htheta' : ∀ i, ε ≤ theta' i ∧ theta' i < π - ε := by
    intro i
    have h := hmargin (Fin.castAdd m i)
    simp only [a', a, Fin.append_left] at h
    exact ⟨h.1.le, h.2⟩
  have hbeta' : ∀ k, ε ≤ beta' k ∧ beta' k < π - ε := by
    intro k
    have h := hmargin (Fin.natAdd n k)
    simp only [a', a, Fin.append_right] at h
    exact ⟨h.1.le, h.2⟩
  have htransport (x : ℝ) :
      Planar.residual c theta' s beta' x = Planar.residual c theta s beta (t+x) := by
    exact (residual_canonical_angles c (fun i ↦ theta i-t) s
      (fun k ↦ beta k-t) x).trans
      (residual_common_angle_translation c theta s beta t x)
  have hnear (x : ℝ) (hx : |x| < η/2) : Planar.residual c theta' s beta' x = 0 := by
    rw [htransport]
    apply hzero
    calc
      |t+x-α| = |(t-α)+x| := by congr 1; ring
      _ ≤ |t-α| + |x| := abs_add _ _
      _ < η := by linarith only [ht, hx]
  have hstart : ∀ x : ℝ, 0 < x → x < ε → Planar.residual c theta' s beta' x = 0 := by
    intro x hx hxe
    apply hnear
    rw [abs_of_pos hx]
    linarith only [hxe, hεη, hη]
  have hmin' : IsLocalMin (Planar.variableLoss s beta') (c, theta') :=
    local_min_canonical_angles c (fun i ↦ theta i-t) s (fun k ↦ beta k-t)
      (local_min_common_angle_translation c theta s beta t hmin)
  have hall := canonical_zero_arc_residual_zero c theta' s beta' hs hε
    (show π-ε < π by linarith only [hε]) htheta' hbeta' hstart hmin'.fderiv_eq_zero
  intro x
  have h := (htransport (x-t)).symm.trans (hall (x-t))
  simpa only [show t+(x-t)=x by ring] using h

section DimensionOne

open Definitions MeasureTheory

/-- A unit direction on the line has the same centered feature as either
orientation of the unique coordinate axis. -/
theorem centered_feature_dimension_one
    (w x : Vec 1) (hw : ‖w‖ = 1) : |⟪w, x⟫_ℝ| = |x 0| := by
  have hwabs : |w 0| = 1 := by
    simpa only [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs,
      sq_abs, Real.sqrt_sq_eq_abs] using hw
  rw [PiLp.inner_apply, Fin.sum_univ_one]
  simp only [IsROrC.inner_apply, starRingEnd_apply, star_trivial,
    abs_mul, hwabs, one_mul]

/-- The value of this scalar integral is unnecessary for dimension-one
benignity; the proof works even if the scalar were zero. -/
def dimensionOneLossCoefficient : ℝ :=
  (1 / 2 : ℝ) * ∫ x : Vec 1, (|x 0| / 2) ^ 2 * stdGaussianDensity x

/-- The literal population loss depends only on the discrepancy of total
masses in dimension one. No kernel or normalization bridge is involved. -/
theorem centered_loss_dimension_one_formula {n m : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Vec 1)
    (s : Fin m → ℝ) (v : Fin m → Vec 1)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    CenteredLoss c w s v = dimensionOneLossCoefficient *
      ((∑ i, c i) - ∑ k, s k) ^ 2 := by
  have hintegrand (x : Vec 1) :
      ((∑ i, c i * (|⟪w i, x⟫_ℝ| / 2)) -
        ∑ k, s k * (|⟪v k, x⟫_ℝ| / 2)) ^ 2 * stdGaussianDensity x =
      ((∑ i, c i) - ∑ k, s k) ^ 2 *
        ((|x 0| / 2) ^ 2 * stdGaussianDensity x) := by
    simp_rw [centered_feature_dimension_one _ x (hw _),
      centered_feature_dimension_one _ x (hv _), ← Finset.sum_mul]
    ring
  unfold CenteredLoss
  simp_rw [hintegrand]
  rw [MeasureTheory.integral_mul_left]
  unfold dimensionOneLossCoefficient
  ring

/-- Updating one mass by `t` increases the total mass by exactly `t`. -/
theorem sum_mass_update_add {n : ℕ} (c : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (∑ j, Function.update c i (c i + t) j) = (∑ j, c j) + t := by
  classical
  have hpoint (j : Fin n) : Function.update c i (c i + t) j =
      c j + if j = i then t else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [Function.update_same, if_true]
    · simp only [Function.update_noteq hji, if_neg hji, add_zero]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp

/-- Every constrained local minimum on the one-dimensional unit cylinder
with at least one student has zero literal centered population loss.
Mass differentiation suffices; neither zero mass nor teacher signs are needed. -/
theorem centered_local_min_dimension_one_zero {n m : ℕ}
    (c : Fin n → ℝ) (w : Fin n → Vec 1)
    (s : Fin m → ℝ) (v : Fin m → Vec 1)
    (hw : ∀ j, ‖w j‖ = 1) (hv : ∀ k, ‖v k‖ = 1) (i : Fin n)
    (hmin : IsLocalMinOn
      (fun p : Parameters 1 n ↦ CenteredLoss p.1 p.2 s v)
      {p | ∀ j, ‖p.2 j‖ = 1} (c, w)) :
    CenteredLoss c w s v = 0 := by
  classical
  let D : ℝ := (∑ j, c j) - ∑ k, s k
  let lift : ℝ → Parameters 1 n := fun t ↦ (Function.update c i (c i + t), w)
  have hbase : lift 0 = (c, w) := by
    simp only [lift, add_zero, Function.update_eq_self]
  have hcont : Continuous lift := by
    dsimp only [lift]
    apply Continuous.prod_mk
    · exact continuous_const.update i (continuous_const.add continuous_id)
    · exact continuous_const
  have hminLift : IsLocalMinOn
      (fun p : Parameters 1 n ↦ CenteredLoss p.1 p.2 s v)
      {p | ∀ j, ‖p.2 j‖ = 1} (lift 0) := by
    rw [hbase]
    exact hmin
  have hminScalar : IsLocalMin
      (fun t : ℝ ↦ dimensionOneLossCoefficient * (D + t) ^ 2) 0 := by
    have hh := (hminLift.comp_continuousOn
      (s := Set.univ) (fun t _ ↦ hw) hcont.continuousOn (Set.mem_univ 0)).isLocalMin
        Filter.univ_mem
    convert hh using 1
    funext t
    dsimp only [Function.comp_apply, lift]
    rw [centered_loss_dimension_one_formula _ w s v hw hv, sum_mass_update_add]
    ring
  have hderiv : HasDerivAt
      (fun t : ℝ ↦ dimensionOneLossCoefficient * (D + t) ^ 2)
      (2 * dimensionOneLossCoefficient * D) 0 := by
    have hh := (((hasDerivAt_id (0 : ℝ)).const_add D).pow 2).const_mul
      dimensionOneLossCoefficient
    convert hh using 1; norm_num; ring
  have hstationary := hminScalar.hasDerivAt_eq_zero hderiv
  rw [centered_loss_dimension_one_formula c w s v hw hv]
  change dimensionOneLossCoefficient * D ^ 2 = 0
  calc
    dimensionOneLossCoefficient * D ^ 2 =
        (2 * dimensionOneLossCoefficient * D) * (D / 2) := by ring
    _ = 0 := by rw [hstationary, zero_mul]

end DimensionOne

theorem width_one_kernel_zero : Planar.kernel 0 = π/2 := by
  simp [Planar.kernel]

/-- The complete width-one variable loss, directly in the scalar kernel. -/
theorem width_one_variable_loss (c theta s beta : Fin 1 → ℝ) :
    Planar.variableLoss s beta (c, theta) =
      c 0^2 * π/4 - c 0 * s 0 * Planar.kernel (theta 0-beta 0) := by
  simp only [Planar.variableLoss, Fin.sum_univ_one, sub_self, width_one_kernel_zero]
  ring

/-- `eq:width-one-centered-loss`: the actual Gaussian half-square loss,
with its teacher constant and normalization explicit. -/
theorem eq_width_one_centered_loss (c theta s beta : Fin 1 → ℝ) :
    Definitions.CenteredLoss c (fun i => Definitions.Angle (theta i))
      s (fun k => Definitions.Angle (beta k)) =
      (c 0 ^ 2 + s 0 ^ 2) / 8 -
        c 0 * s 0 / (2 * π) * Planar.kernel (theta 0 - beta 0) := by
  rw [Planar.GaussianSurface.centeredLoss_eq_variableLoss,
    width_one_variable_loss, width_one_variable_loss, sub_self, width_one_kernel_zero]
  field_simp [pi_ne_zero]
  ring

theorem width_one_kernel_at_sin_zero {x : ℝ} (hx : sin x = 0) :
    Planar.kernel x = π/2 := by
  have hcos : cos x = 1 ∨ cos x = -1 := by
    have h := sin_sq_add_cos_sq x
    rw [hx] at h
    have hp : (cos x-1)*(cos x+1) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hp with hp | hp
    · left; linarith only [hp]
    · right; linarith only [hp]
  rcases hcos with hcos | hcos <;> simp [Planar.kernel, hcos]

private theorem width_one_angle_derivative (c s beta t : ℝ) :
    HasDerivAt (fun x => c^2*π/4-c*s*Planar.kernel (x-beta))
      (c*s*(sin (t-beta)*arcsin (cos (t-beta)))) t := by
  have hK : HasDerivAt Planar.kernel
      (-sin (t-beta)*arcsin (cos (t-beta))) (t-beta) :=
    KernelCalculus.hasDerivAt_angularKernel (t-beta)
  have h := (((hK.comp t ((hasDerivAt_id t).sub_const beta)).const_mul
    (c*s)).const_sub (c^2*π/4))
  convert h using 1
  ring

/-- The fresh angular second derivative equals `-c*s` at perpendicularity. -/
theorem width_one_perpendicular_not_local_min {c s theta beta : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hcos : cos (theta-beta) = 0) :
    ¬ IsLocalMin (fun t => c^2*π/4-c*s*Planar.kernel (t-beta)) theta := by
  let g : ℝ → ℝ := fun t => c^2*π/4-c*s*Planar.kernel (t-beta)
  have hd (t) : HasDerivAt g (c*s*(sin (t-beta)*arcsin (cos (t-beta)))) t :=
    width_one_angle_derivative c s beta t
  have hderiv : deriv g = fun t => c*s*(sin (t-beta)*arcsin (cos (t-beta))) :=
    funext fun t => (hd t).deriv
  have habs : |sin (theta-beta)| = 1 := by
    have h := sin_sq_add_cos_sq (theta-beta)
    rw [hcos] at h
    have hsq : sin (theta-beta)^2 = 1 := by nlinarith only [h]
    have hroot := congrArg Real.sqrt hsq
    simpa only [sqrt_sq_eq_abs, sqrt_one] using hroot
  have hK : KernelCalculus.angularKernel (theta-beta) = 1 := by
    simp [KernelCalculus.angularKernel, KernelCalculus.centeredKernel, hcos]
  have hsecond : HasDerivAt (deriv g) (-(c*s)) theta := by
    rw [hderiv]
    have h := (((KernelCalculus.hasDerivAt_angularKernel_first (theta-beta)).comp theta
      ((hasDerivAt_id theta).sub_const beta)).neg.const_mul (c*s))
    rw [habs, hK] at h
    convert h using 1
    · funext t
      simp only [Function.comp_apply, id_eq]
      ring
    · ring
  apply Preliminaries.negative_second_derivative_not_local_min
    (eventually_of_forall fun t => (hd t).differentiableAt) _ hsecond
    (neg_neg_of_pos (mul_pos hc hs))
  rw [hderiv]
  simp [hcos]

private theorem width_one_scalar_local_min (c theta s beta : Fin 1 → ℝ)
    (hmin : IsLocalMin (Planar.variableLoss s beta) (c, theta)) :
    IsLocalMin (fun p : ℝ × ℝ => p.1^2*π/4-p.1*s 0*Planar.kernel (p.2-beta 0))
      (c 0, theta 0) := by
  let lift : ℝ × ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
    fun p => (fun _ => p.1, fun _ => p.2)
  have hcont : Continuous lift := (continuous_pi fun _ => continuous_fst).prod_mk
    (continuous_pi fun _ => continuous_snd)
  have hbase : lift (c 0, theta 0) = (c, theta) := by
    apply Prod.ext <;> funext i
    · exact congrArg c (Subsingleton.elim 0 i)
    · exact congrArg theta (Subsingleton.elim 0 i)
  have hminLift : IsLocalMin (Planar.variableLoss s beta) (lift (c 0, theta 0)) := by
    rwa [hbase]
  convert hminLift.comp_continuous hcont.continuousAt using 1
  funext p
  exact (width_one_variable_loss (fun _ => p.1) (fun _ => p.2) s beta).symm

/-- Width-one benignity uses only the explicit mass/angle scalar restrictions,
the fresh C1 kernel formula, and its fresh C2 perpendicular curvature. -/
theorem width_one_positive_local_min_exact_fit (c theta s beta : Fin 1 → ℝ)
    (hc : 0 < c 0) (hs : 0 < s 0)
    (hmin : IsLocalMin (Planar.variableLoss s beta) (c, theta)) :
    Planar.variableLoss s beta (c, theta) = Planar.variableLoss s beta (s, beta) := by
  have hscalar := width_one_scalar_local_min c theta s beta hmin
  have hmassMin : IsLocalMin
      (fun r : ℝ => r^2*π/4-r*s 0*Planar.kernel (theta 0-beta 0)) (c 0) :=
    hscalar.comp_continuous (g := fun r : ℝ => (r, theta 0)) (b := c 0)
      ((continuous_id.prod_mk continuous_const : Continuous (fun r : ℝ => (r, theta 0))).continuousAt)
  have hmassDeriv : HasDerivAt
      (fun r : ℝ => r^2*π/4-r*s 0*Planar.kernel (theta 0-beta 0))
      (c 0*π/2-s 0*Planar.kernel (theta 0-beta 0)) (c 0) := by
    convert ((((hasDerivAt_id (c 0)).pow 2).mul_const π).div_const 4).sub
      (((hasDerivAt_id (c 0)).mul_const (s 0)).mul_const
        (Planar.kernel (theta 0-beta 0))) using 1
    simp only [id_eq]
    ring
  have hmass := hmassMin.hasDerivAt_eq_zero hmassDeriv
  have hangle : IsLocalMin
      (fun t : ℝ => c 0^2*π/4-c 0*s 0*Planar.kernel (t-beta 0)) (theta 0) :=
    hscalar.comp_continuous (g := fun t : ℝ => (c 0, t)) (b := theta 0)
      ((continuous_const.prod_mk continuous_id : Continuous (fun t : ℝ => (c 0, t))).continuousAt)
  have htorque : sin (theta 0-beta 0)*arcsin (cos (theta 0-beta 0)) = 0 :=
    (mul_eq_zero.mp (hangle.hasDerivAt_eq_zero
      (width_one_angle_derivative (c 0) (s 0) (beta 0) (theta 0)))).resolve_left
        (ne_of_gt (mul_pos hc hs))
  have hsin : sin (theta 0-beta 0) = 0 := by
    rcases mul_eq_zero.mp htorque with hsin | harcsin
    · exact hsin
    · exact False.elim (width_one_perpendicular_not_local_min hc hs
        (arcsin_eq_zero_iff.mp harcsin) hangle)
  have hpeak := width_one_kernel_at_sin_zero hsin
  rw [hpeak] at hmass
  have hcs : c 0 = s 0 := by
    have heq : c 0*(π/2) = s 0*(π/2) := by nlinarith only [hmass]
    exact mul_right_cancel₀ (half_pos pi_pos).ne' heq
  have hzero : Definitions.CenteredLoss c (fun i => Definitions.Angle (theta i))
      s (fun k => Definitions.Angle (beta k)) = 0 := by
    rw [eq_width_one_centered_loss, hpeak, hcs]
    field_simp [pi_ne_zero]
    ring
  rw [Planar.GaussianSurface.centeredLoss_eq_variableLoss] at hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left
    (one_div_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero)))

/-- With no teacher, the explicit positive mass derivative rules out a
positive-width-one local minimum. -/
theorem width_one_positive_no_teacher (c theta : Fin 1 → ℝ) (s beta : Fin 0 → ℝ)
    (hc : 0 < c 0) : ¬ IsLocalMin (Planar.variableLoss s beta) (c, theta) := by
  intro hmin
  let lift : ℝ → (Fin 1 → ℝ) × (Fin 1 → ℝ) := fun t => (fun _ => t, theta)
  have hcont : Continuous lift := (continuous_pi fun _ => continuous_id).prod_mk continuous_const
  have hbase : lift (c 0) = (c, theta) := by
    apply Prod.ext
    · funext i; exact congrArg c (Subsingleton.elim 0 i)
    · rfl
  have hminLift : IsLocalMin (Planar.variableLoss s beta) (lift (c 0)) := by rwa [hbase]
  have hscalar : IsLocalMin (fun r : ℝ => r^2*π/4) (c 0) := by
    convert hminLift.comp_continuous hcont.continuousAt using 1
    funext r
    simp only [Function.comp_apply, lift, Planar.variableLoss, Fin.sum_univ_one,
      Fin.sum_univ_zero, sub_zero, sub_self, width_one_kernel_zero]
    ring
  have hd : HasDerivAt (fun r : ℝ => r^2*π/4) (c 0*π/2) (c 0) := by
    convert (((hasDerivAt_id (c 0)).pow 2).mul_const π).div_const 4 using 1
    simp only [id_eq]
    ring
  exact (div_pos (mul_pos hc pi_pos) (by norm_num : (0 : ℝ) < 2)).ne'
    (hscalar.hasDerivAt_eq_zero hd)
variable {d r n m : ℕ}

/-- Literal loss versus its finite variable quadratic: the teacher constant
and the positive normalization are exposed rather than buried in a predicate. -/
theorem literal_loss_eq_scaled_variable_kernel
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    Definitions.Loss q c w s v = (1 / (2 * π)) *
      (massNetLossKernel (Definitions.Kernel q) c w s v -
        massNetLossKernel (Definitions.Kernel q) s v s v) := by
  cases q with
  | centered => exact SecondMomentPair.centered_loss_eq_variable_kernel hd c w s v hw hv
  | plainRelu =>
    rw [Preliminaries.loss_eq_kernelEnergy hd .plainRelu c w s v hw hv]
    unfold Preliminaries.KernelEnergy massNetLossKernel
    field_simp [Real.pi_ne_zero]
    ring

/-- A positive scaling and a fixed additive teacher constant preserve exactly
the ordinary signed-mass/sphere local-minimum topology. -/
theorem literal_local_minimum_iff_variable_kernel
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1) :
    IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦ Definitions.Loss q p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w) ↔
    IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦ massNetLossKernel (Definitions.Kernel q) p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w) := by
  have hscale : (0 : ℝ) < 1 / (2 * π) := by positivity
  constructor
  · intro hmin
    filter_upwards [hmin, self_mem_nhdsWithin] with p hp hunit
    rw [literal_loss_eq_scaled_variable_kernel hd q c w s v hw hv,
      literal_loss_eq_scaled_variable_kernel hd q p.1 p.2 s v hunit hv] at hp
    exact (sub_le_sub_iff_right _).mp ((mul_le_mul_left hscale).mp hp)
  · intro hmin
    filter_upwards [hmin, self_mem_nhdsWithin] with p hp hunit
    rw [literal_loss_eq_scaled_variable_kernel hd q c w s v hw hv,
      literal_loss_eq_scaled_variable_kernel hd q p.1 p.2 s v hunit hv]
    exact (mul_le_mul_left hscale).mpr ((sub_le_sub_iff_right _).mpr hp)

/-- The common final step: pair the zero residual with all finitely many
student and teacher atoms in the literal normalized loss identity. -/
theorem eq_zero_mass_pairing
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (hall : ∀ x : Definitions.Vec d, ‖x‖ = 1 → Definitions.Residual q c w s v x = 0) :
    Definitions.Loss q c w s v = 0 := by
  rw [Preliminaries.eq_residual_loss hd q c w s v hw hv]
  have hstudent : (∑ i, c i * Definitions.Residual q c w s v (w i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hall (w i) (hw i), mul_zero]
  have hteacher : (∑ k, s k * Definitions.Residual q c w s v (v k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hall (v k) (hv k), mul_zero]
  rw [hstudent, hteacher, sub_self, mul_zero]

open NormalTrace ConfinementTraceAssembly AmplitudeNormalVariation

/-- The explicit finite projection has zero normal component exactly on its
isometric carrier. This also works when that carrier is zero-dimensional. -/
theorem normal_part_eq_zero_iff_mem_range {d r : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (x : Vec d) :
    normalPart J x = 0 ↔ x ∈ Set.range J := by
  constructor
  · intro hx
    refine ⟨∑ a, (inner (J (EuclideanSpace.basisFun (Fin r) ℝ a)) x : ℝ) •
      EuclideanSpace.basisFun (Fin r) ℝ a, ?_⟩
    rw [map_sum]
    simp only [map_smul]
    exact (sub_eq_zero.mp hx).symm
  · rintro ⟨y, rfl⟩
    exact normalPart_image J y

/-- Confining just the positive-mass directions is enough: a zero mass has
zero weighted generator, so no neuron deletion or collision merging is needed. -/
theorem weighted_generators_in_range_of_positive_directions {d r n : ℕ}
    (J : Vec r →ₗᵢ[ℝ] Vec d) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (hc : ∀ i, 0 ≤ c i)
    (hdir : ∀ i, 0 < c i → w i ∈ Set.range J) :
    ∀ i, c i • w i ∈ Set.range J := by
  intro i
  by_cases hci : c i = 0
  · exact ⟨0, by simp [hci]⟩
  · obtain ⟨y, hy⟩ := hdir i (lt_of_le_of_ne (hc i) (Ne.symm hci))
    exact ⟨c i • y, by rw [map_smul, hy]⟩

/-- Realize a finite-dimensional subspace as an orthonormal image, without
requiring linear independence or a positive rank for the teacher. -/
theorem generators_in_subspace_of_isometric_ranges {d n m : ℕ}
    (S : Submodule ℝ (Vec d)) (v : Fin m → Vec d)
    (c : Fin n → ℝ) (w : Fin n → Vec d) (hvS : ∀ k, v k ∈ S)
    (hconf : ∀ (J : Vec (FiniteDimensional.finrank ℝ S) →ₗᵢ[ℝ] Vec d),
      (∀ k, v k ∈ Set.range J) → ∀ i, c i • w i ∈ Set.range J) :
    ∀ i, c i • w i ∈ S := by
  let b := stdOrthonormalBasis ℝ S
  let J : Vec (FiniteDimensional.finrank ℝ S) →ₗᵢ[ℝ] Vec d :=
    S.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  have hvJ : ∀ k, v k ∈ Set.range J := by
    intro k
    let vk : S := ⟨v k, hvS k⟩
    exact ⟨b.repr vk, congrArg Subtype.val (b.repr.symm_apply_apply vk)⟩
  intro i
  obtain ⟨y, hy⟩ := hconf J hvJ i
  rw [← hy]
  exact (b.repr.symm y).property

/-- The direct confinement endgame permits zero masses and collisions. For
either feature the mixed curvature vanishes at a local minimum, while the
normal-stretching lemma makes it positive as soon as an active generator has
a normal component; zero weighted generators are handled without deleting
neurons. -/
theorem nonnegative_confinement_in_range
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model)
    (J : Vec r →ₗᵢ[ℝ] Vec d)
    {c : Fin n → ℝ} {w : Fin n → Vec d}
    {s : Fin m → ℝ} {v : Fin m → Vec d}
    (hvJ : ∀ k, v k ∈ Set.range J)
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1) (hc : ∀ i, 0 ≤ c i)
    (hmin : IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦
        massNetLossKernel (Definitions.Kernel q) p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w)) :
    (∀ i, 0 < c i → w i ∈ Set.range J) ∧
      (∀ i, c i • w i ∈ Set.range J) := by
  have hdir : ∀ i, 0 < c i → w i ∈ Set.range J := by
    intro i hci
    apply (normal_part_eq_zero_iff_mem_range J (w i)).mp
    by_contra hQi
    let B := EuclideanSpace.basisFun (Fin d) ℝ
    cases q with
    | centered =>
        have hzero := FirstDerivativeExpectation.centered_mixed_energy_zero_from_expectation
          hd J B c w s v hw hv hvJ hmin
        have hpos := NormalStretching.mixedEnergy_pos_of_active_normal hd J c w hw hc i hci hQi
        linarith
    | plainRelu =>
        have heq : PlainConfinementVariation.plainVariableLoss (π/2) s v =
            (fun p : Definitions.Parameters d n ↦
              massNetLossKernel (Definitions.Kernel .plainRelu) p.1 p.2 s v) := by
          funext p
          exact PlainConfinementVariation.plain_loss_kernel_form (π/2) s v p
        rw [← heq] at hmin
        have hzero := PlainConfinementVariation.plain_mixed_energy_zero J B c w s v hw hv hvJ hmin
        have hpos := NormalStretching.plain_mixed_energy_pos hd J c w hw hc i hci hQi
        linarith
  exact ⟨hdir, weighted_generators_in_range_of_positive_directions J c w hc hdir⟩

/-- Positive masses permit forgetting the weights in the common confinement
statement. This is the interface used by the planar angle reduction below. -/
theorem centered_positive_confinement_in_range
    (hd : 2 ≤ d) (J : Vec r →ₗᵢ[ℝ] Vec d)
    {c : Fin n → ℝ} {w : Fin n → Vec d}
    {s : Fin m → ℝ} {v : Fin m → Vec d}
    (hvJ : ∀ k, v k ∈ Set.range J)
    (hv : Definitions.UnitDirections v) (hw : Definitions.UnitDirections w)
    (hc : ∀ i, 0 < c i) (hmin : IsMassNetLocalMin s v c w) :
    ∀ i, w i ∈ Set.range J := by
  exact fun i ↦ (nonnegative_confinement_in_range hd .centered J hvJ hv hw
    (fun j ↦ (hc j).le) hmin).1 i (hc i)

/-- Local proof of the manuscript's common centered/plain confinement
statement: literal Gaussian loss → finite trace → null normal variation →
zero mixed term → positive active energy → teacher span. -/
theorem prop_teacher_span_confinement
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model)
    {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1) (hc : ∀ i, 0 ≤ c i)
    (hmin : IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦ Definitions.Loss q p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w)) :
    ∀ i, c i • w i ∈ Submodule.span ℝ (Set.range v) := by
  have hkernel := (literal_local_minimum_iff_variable_kernel hd q c w s v hw hv).mp hmin
  exact generators_in_subspace_of_isometric_ranges
    (Submodule.span ℝ (Set.range v)) v c w
    (fun k ↦ Submodule.subset_span (Set.mem_range_self k))
    (fun J hvJ ↦ (nonnegative_confinement_in_range hd q J hvJ hv hw hc hkernel).2)

end PaperLeanFormalization.Geometry



/-!
# The zero-mass propositions: patch, continuation, pairing

The zero-mass argument begins by moving the direction of the dead neuron
without changing the represented function. Stationarity in its mass then
makes the residual vanish on a spherical patch. Propagation alone depends on
dimension: a two-point scalar calculation, the planar causal formula, or
analytic continuation in one stereographic chart. All three arguments are
developed in this file.
-/

noncomputable section

open Real Set Filter Metric
open scoped BigOperators Topology RealInnerProductSpace

namespace PaperLeanFormalization.Geometry

open PaperLeanFormalization PaperLeanFormalization

variable {d n m : ℕ}

/-- The restriction of the ambient residual to the circle is the planar potential. -/
theorem centered_residual_on_circle
    (c theta : Fin n → ℝ) (beta s : Fin m → ℝ) (gamma : ℝ) :
    massResidualField c (fun j ↦ Definitions.Angle (theta j)) s
        (fun k ↦ Definitions.Angle (beta k)) (Definitions.Angle gamma) =
      residualPotential c beta s theta gamma := by
  unfold massResidualField massTeacherPotential residualPotential phiCos
  congr 1
  · exact Finset.sum_congr rfl fun j _ ↦ by rw [Preliminaries.angle_inner]
  · exact Finset.sum_congr rfl fun k _ ↦ by rw [Preliminaries.angle_inner]

/-- The one-dimensional unit sphere consists of a vector and its antipode. -/
theorem unit_direction_dimension_one_eq_or_neg
    (x u : EuclideanSpace ℝ (Fin 1)) (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) :
    x = u ∨ x = -u := by
  have habs (z : EuclideanSpace ℝ (Fin 1)) : ‖z‖ = |z 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs,
      sq_abs, Real.sqrt_sq_eq_abs]
  have hcoordinates : |x 0| = |u 0| := by rw [← habs, ← habs, hx, hu]
  rcases abs_eq_abs.mp hcoordinates with h | h
  · left
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h
  · right
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h

/-- Centered residual evenness is immediate from the displayed kernel sums. -/
theorem centered_residual_antipodal {d n m : ℕ}
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    PaperLeanFormalization.massResidualField c w s v (-x) = PaperLeanFormalization.massResidualField c w s v x := by
  simp only [PaperLeanFormalization.massResidualField, PaperLeanFormalization.massTeacherPotential,
    inner_neg_left, orthantPhi, Real.arcsin_neg, neg_sq, neg_mul_neg]

/-- The dimension-one continuation step needs one zero and antipodal evenness. -/
theorem centered_residual_dimension_one_from_seed {n m : ℕ}
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin 1))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin 1))
    (u : EuclideanSpace ℝ (Fin 1)) (hu : ‖u‖ = 1)
    (hzero : PaperLeanFormalization.massResidualField c w s v u = 0) :
    ∀ x : EuclideanSpace ℝ (Fin 1), ‖x‖ = 1 →
      PaperLeanFormalization.massResidualField c w s v x = 0 := by
  intro x hx
  rcases unit_direction_dimension_one_eq_or_neg x u hx hu with rfl | rfl
  · exact hzero
  · rw [centered_residual_antipodal]
    exact hzero


/-- In dimension one a single zero determines the residual on both sphere points. -/
theorem centered_patch_dimension_one
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin 1))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin 1))
    (u : EuclideanSpace ℝ (Fin 1)) (hu : ‖u‖ = 1)
    (hzero : massResidualField c w s v u = 0) :
    ∀ x : EuclideanSpace ℝ (Fin 1), ‖x‖ = 1 →
      massResidualField c w s v x = 0 := by
  exact centered_residual_dimension_one_from_seed c w s v u hu hzero

/-- The ambient kernel objective in an isometric angle chart is exactly the
local planar finite-sum objective, before restoring the teacher constant. -/
theorem kernel_loss_in_isometric_angle_chart
    (J : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    massNetLossKernel (Definitions.Kernel .centered) c
      (fun i ↦ J (Definitions.Angle (theta i))) s
      (fun k ↦ J (Definitions.Angle (beta k))) =
        Planar.variableLoss s beta (c, theta) := by
  unfold massNetLossKernel Planar.variableLoss
  simp_rw [J.inner_map_map, Preliminaries.angle_inner]
  rfl

/-- The complete literal Gaussian loss in the angle chart. This explicitly
records both the `1/(2π)` factor and the additive teacher constant. -/
theorem centered_loss_in_isometric_angle_chart
    (hd : 2 ≤ d)
    (J : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ) :
    Definitions.CenteredLoss c (fun i ↦ J (Definitions.Angle (theta i))) s
      (fun k ↦ J (Definitions.Angle (beta k))) =
        (1 / (2 * π)) * (Planar.variableLoss s beta (c, theta) -
          Planar.variableLoss s beta (s, beta)) := by
  change Definitions.Loss .centered _ _ _ _ = _
  rw [literal_loss_eq_scaled_variable_kernel hd .centered]
  · rw [kernel_loss_in_isometric_angle_chart, kernel_loss_in_isometric_angle_chart]
  · intro i
    rw [J.norm_map, Preliminaries.angle_unit]
  · intro k
    rw [J.norm_map, Preliminaries.angle_unit]

/-- Angular perturbations form a continuous subfamily of all ambient sphere
perturbations. Restriction of local minimality is therefore immediate. -/
theorem ambient_local_minimum_restricts_to_angles
    (J : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (hmin : IsMassNetLocalMin s (fun k ↦ J (Definitions.Angle (beta k))) c
      (fun i ↦ J (Definitions.Angle (theta i)))) :
    IsLocalMin (Planar.variableLoss s beta) (c, theta) := by
  let chart : ((Fin n → ℝ) × (Fin n → ℝ)) → Definitions.Parameters d n :=
    fun p ↦ (p.1, fun i ↦ J (Definitions.Angle (p.2 i)))
  have hcont : Continuous chart := continuous_fst.prod_mk
    (continuous_pi fun i ↦ J.continuous.comp
      (FinitePlane.continuous_circle.comp ((continuous_apply i).comp continuous_snd)))
  have hmaps : ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
      chart p ∈ {z : Definitions.Parameters d n | ∀ i, ‖z.2 i‖ = 1} := by
    intro p i
    change ‖J (Definitions.Angle (p.2 i))‖ = 1
    rw [J.norm_map, Preliminaries.angle_unit]
  have htend : Tendsto chart (𝓝 (c, theta))
      (𝓝[{z : Definitions.Parameters d n | ∀ i, ‖z.2 i‖ = 1}]
        (chart (c, theta))) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hcont.continuousAt.tendsto, Filter.eventually_of_forall hmaps⟩
  have hev := htend.eventually hmin
  exact hev.mono fun p hp ↦ by
    change massNetLossKernel (Definitions.Kernel .centered) c (fun i ↦ J (Definitions.Angle (theta i))) s
        (fun k ↦ J (Definitions.Angle (beta k))) ≤
      massNetLossKernel (Definitions.Kernel .centered) p.1 (fun i ↦ J (Definitions.Angle (p.2 i))) s
        (fun k ↦ J (Definitions.Angle (beta k))) at hp
    simpa only [kernel_loss_in_isometric_angle_chart] using hp

/-- The planar case turns the patch into an open angle interval. Teacher
nonnegativity is needed precisely by the zero-arc rigidity theorem. -/
theorem centered_patch_dimension_two
    {s : Fin m → ℝ} {v : Fin m → EuclideanSpace ℝ (Fin 2)}
    {c : Fin n → ℝ} {w : Fin n → EuclideanSpace ℝ (Fin 2)}
    (hs : ∀ k, 0 ≤ s k) (hv : Definitions.UnitDirections v) (hw : Definitions.UnitDirections w)
    (hmin : IsMassNetLocalMin s v c w)
    {u : EuclideanSpace ℝ (Fin 2)} (hu : ‖u‖ = 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hpatch : ∀ x, dist x u < δ → ‖x‖ = 1 →
      massResidualField c w s v x = 0) :
    ∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ = 1 →
      massResidualField c w s v x = 0 := by
  classical
  choose beta hbeta using fun k => exists_angle (hv k)
  choose theta htheta using fun j => exists_angle (hw j)
  choose alpha halpha using exists_angle hu
  have hvfun : (fun k ↦ Definitions.Angle (beta k)) = v := funext hbeta
  have hwfun : (fun j ↦ Definitions.Angle (theta j)) = w := funext htheta
  have hminPlanar : IsLocalMin (Planar.variableLoss s beta) (c, theta) := by
    apply ambient_local_minimum_restricts_to_angles (LinearIsometry.id : Definitions.Vec 2 →ₗᵢ[ℝ] Definitions.Vec 2)
    change IsMassNetLocalMin s (fun k ↦ Definitions.Angle (beta k)) c (fun j ↦ Definitions.Angle (theta j))
    rw [hvfun, hwfun]
    exact hmin
  have hnear : {gamma : ℝ | dist (Definitions.Angle gamma) u < δ} ∈ 𝓝 alpha := by
    rw [← halpha]
    exact FinitePlane.continuous_circle.continuousAt
      (Metric.ball_mem_nhds (Definitions.Angle alpha) hδ)
  rw [Metric.mem_nhds_iff] at hnear
  obtain ⟨eta, heta, hnear⟩ := hnear
  have hflat : ∀ gamma, |gamma - alpha| < eta →
      Planar.residual c theta s beta gamma = 0 := by
    intro gamma hgamma
    change residualPotential c beta s theta gamma = 0
    rw [← centered_residual_on_circle c theta beta s gamma, hvfun, hwfun]
    exact hpatch (Definitions.Angle gamma)
      (hnear (by simpa only [Real.dist_eq] using hgamma)) (Preliminaries.angle_unit gamma)
  have hresidual := planar_residual_zero_of_open_zero_arc c theta s beta hs
    hminPlanar alpha heta hflat
  intro x hx
  obtain ⟨gamma, rfl⟩ := exists_angle hx
  rw [← hvfun, ← hwfun, centered_residual_on_circle]
  exact hresidual gamma

/-- In dimension at least three, continuation in one stereographic chart
propagates a zero patch without sign restrictions on either family. -/
theorem centered_patch_dimension_ge_three
    (hd : 3 ≤ d)
    (c : Fin n → ℝ) (w : Fin n → EuclideanSpace ℝ (Fin d))
    (s : Fin m → ℝ) (v : Fin m → EuclideanSpace ℝ (Fin d))
    (hw : Definitions.UnitDirections w) (hv : Definitions.UnitDirections v)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hpatch : ∀ x, dist x u < δ → ‖x‖ = 1 →
      massResidualField c w s v x = 0) :
    ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 →
      massResidualField c w s v x = 0 := by
  exact SphereContinuation.finite_kernel_residual_zero_on_sphere_of_patch
    (by simpa using hd) orthantPhi SphereContinuation.continuous_centered_kernel
    (fun r hr ↦ KernelAnalytic.analyticAt_centeredKernel hr)
    c w hw s v hv u hu hδ hpatch

/-- The three dimension cases are deliberately visible in the local proof. -/
theorem stp_zm_propagation
    (hd : 1 ≤ d)
    {s : Fin m → ℝ} {v : Fin m → EuclideanSpace ℝ (Fin d)}
    {c : Fin n → ℝ} {w : Fin n → EuclideanSpace ℝ (Fin d)}
    (hs₂ : d = 2 → ∀ k, 0 ≤ s k) (hv : Definitions.UnitDirections v)
    (hw : Definitions.UnitDirections w) (hmin : IsMassNetLocalMin s v c w)
    {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hpatch : ∀ x, dist x u < δ → ‖x‖ = 1 →
      massResidualField c w s v x = 0) :
    ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 →
      massResidualField c w s v x = 0 := by
  by_cases hd1 : d = 1
  · subst d
    exact centered_patch_dimension_one c w s v u hu
      (hpatch u (by simpa using hδ) hu)
  by_cases hd2 : d = 2
  · subst d
    exact centered_patch_dimension_two (hs₂ rfl) hv hw hmin hu hδ hpatch
  exact centered_patch_dimension_ge_three (by omega (config := {})) c w s v hw hv u hu hδ hpatch


section Revival

open Definitions Preliminaries

/-- Reviving a zero-mass slot adds exactly one weighted feature to a finite sum. -/
theorem weighted_sum_revival {V : Type*} {n : ℕ}
    (c : Fin n → ℝ) (w : Fin n → V) (f : V → ℝ)
    (i : Fin n) (hci : c i = 0) (t : ℝ) (u : V) :
    (∑ j, Function.update c i t j * f (Function.update w i u j)) =
      (∑ j, c j * f (w j)) + t * f u := by
  classical
  have hpoint (j : Fin n) :
      Function.update c i t j * f (Function.update w i u j) =
        c j * f (w j) + if j = i then t * f u else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [Function.update_same, hci, zero_mul, zero_add, if_true]
    · simp only [Function.update_noteq hji, if_neg hji, add_zero]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp

/-- The revived quadratic has its original value, two equal cross terms,
and the revived feature's self-interaction. -/
theorem symmetric_double_sum_revival {V : Type*} {n : ℕ}
    (B : V → V → ℝ) (hB : ∀ x y, B x y = B y x)
    (c : Fin n → ℝ) (w : Fin n → V)
    (i : Fin n) (hci : c i = 0) (t : ℝ) (u : V) :
    (∑ a, ∑ b, Function.update c i t a * Function.update c i t b *
      B (Function.update w i u a) (Function.update w i u b)) =
    (∑ a, ∑ b, c a * c b * B (w a) (w b)) +
      2 * t * (∑ b, c b * B u (w b)) + t ^ 2 * B u u := by
  have hrow (x : V) :
      (∑ b, Function.update c i t b * B x (Function.update w i u b)) =
        (∑ b, c b * B x (w b)) + t * B x u :=
    weighted_sum_revival c w (B x) i hci t u
  have hcross : (∑ a, c a * (t * B (w a) u)) = t * ∑ a, c a * B u (w a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [hB (w a) u]
    ring
  have hbase : (∑ a, c a * (∑ b, c b * B (w a) (w b))) =
      ∑ a, ∑ b, c a * c b * B (w a) (w b) := by
    simp only [Finset.mul_sum, mul_assoc]
  calc
    _ = ∑ a, Function.update c i t a *
        (∑ b, Function.update c i t b * B (Function.update w i u a)
          (Function.update w i u b)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = (∑ a, c a * (∑ b, Function.update c i t b * B (w a)
          (Function.update w i u b))) +
        t * (∑ b, Function.update c i t b * B u (Function.update w i u b)) :=
      weighted_sum_revival c w
        (fun x ↦ ∑ b, Function.update c i t b * B x (Function.update w i u b)) i hci t u
    _ = (∑ a, c a * ((∑ b, c b * B (w a) (w b)) + t * B (w a) u)) +
        t * ((∑ b, c b * B u (w b)) + t * B u u) := by simp only [hrow]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hbase, hcross]
      ring

/-- The quadratic coefficient depends only on the choice of activation. -/
def revivalQuadraticCoefficient : PaperLeanFormalization.Model → ℝ
  | .centered => 1 / 8
  | .plainRelu => 1 / 4

/-- Exact finite-kernel version of `eq:revival-signed`, for both models. -/
theorem kernel_energy_revival_signed {d n m : ℕ}
    (q : PaperLeanFormalization.Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d) (i : Fin n) (hci : c i = 0)
    (t : ℝ) (u : Vec d) (hu : ‖u‖ = 1) :
    KernelEnergy q (Function.update c i t) (Function.update w i u) s v -
      KernelEnergy q c w s v =
        t / (2 * Real.pi) * Residual q c w s v u +
          revivalQuadraticCoefficient q * t ^ 2 := by
  have hSS := symmetric_double_sum_revival (fun x y : Vec d ↦ Kernel q (inner x y))
    (fun x y ↦ congrArg (Kernel q) (real_inner_comm y x)) c w i hci t u
  have hST := weighted_sum_revival c w
    (fun x ↦ ∑ k, s k * Kernel q (inner x (v k))) i hci t u
  have hSTsum :
      (∑ a, ∑ k, Function.update c i t a * s k *
        Kernel q (inner (Function.update w i u a) (v k))) =
      (∑ a, ∑ k, c a * s k * Kernel q (inner (w a) (v k))) +
        t * ∑ k, s k * Kernel q (inner u (v k)) := by
    simpa only [Finset.mul_sum, mul_assoc] using hST
  have hdiag : Kernel q (inner u u) = 4 * Real.pi * revivalQuadraticCoefficient q := by
    rw [real_inner_self_eq_norm_sq, hu]
    cases q <;> norm_num [Kernel, revivalQuadraticCoefficient, Real.arcsin_one] <;> ring
  unfold KernelEnergy
  rw [hSS]
  rw [hSTsum, hdiag]
  unfold Residual
  field_simp [Real.pi_ne_zero]
  ring

/-- The literal-loss revival identity under its named finite-kernel
representation. Integration supplies `loss_eq_kernelEnergy` for this premise. -/
theorem eq_revival_signed {d n m : ℕ}
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ j, ‖w j‖ = 1)
    (hv : ∀ k, ‖v k‖ = 1)
    (i : Fin n) (hci : c i = 0) (t : ℝ) (u : Vec d) (hu : ‖u‖ = 1) :
    Loss q (Function.update c i t) (Function.update w i u) s v - Loss q c w s v =
      t / (2 * Real.pi) * Residual q c w s v u + revivalQuadraticCoefficient q * t ^ 2 := by
  classical
  have hunit : ∀ j, ‖Function.update w i u j‖ = 1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_same] using hu
    · simpa only [Function.update_noteq hji] using hw j
  rw [Preliminaries.loss_eq_kernelEnergy hd q _ _ s v hunit hv,
    Preliminaries.loss_eq_kernelEnergy hd q c w s v hw hv]
  exact kernel_energy_revival_signed q c w s v i hci t u hu

/-- The derivative used in `stp:zm-revival` is obtained from the exact
quadratic identity, so the displayed equation participates in the proof. -/
theorem hasDerivAt_revival {d n m : ℕ}
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model) (c : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ j, ‖w j‖ = 1)
    (hv : ∀ k, ‖v k‖ = 1)
    (i : Fin n) (hci : c i = 0) (u : Vec d) (hu : ‖u‖ = 1) :
    HasDerivAt (fun t ↦ Loss q (Function.update c i t) (Function.update w i u) s v)
      ((1 / (2 * Real.pi)) * Residual q c w s v u) 0 := by
  have hfun : (fun t ↦ Loss q (Function.update c i t) (Function.update w i u) s v) =
      fun t ↦ Loss q c w s v + t / (2 * Real.pi) * Residual q c w s v u +
        revivalQuadraticCoefficient q * t ^ 2 := by
    funext t
    have h := eq_revival_signed hd q c w s v hw hv
      i hci t u hu
    linarith only [h]
  rw [hfun]
  have hlinear := (((hasDerivAt_id (0 : ℝ)).div_const (2 * Real.pi)).mul_const
    (Residual q c w s v u)).const_add (Loss q c w s v)
  have hquadratic := ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul
    (revivalQuadraticCoefficient q)
  convert hlinear.add hquadratic using 1; norm_num

end Revival

/-- A flat zero-mass fibre turns a constrained local minimum into mass
stationarity at every nearby direction. This one elementary product-neighborhood
argument serves both features and keeps the zero-patch mechanism local. -/
theorem zero_patch_of_flat_slot
    (L : Definitions.Parameters d n → ℝ) (R : Definitions.Vec d → ℝ)
    {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    (hw : ∀ j, ‖w j‖ = 1) {i : Fin n} (hci : c i = 0)
    (hflat : ∀ x, ‖x‖ = 1 → L (Function.update c i 0, Function.update w i x) = L (c, w))
    (hderiv : ∀ x, ‖x‖ = 1 → HasDerivAt
      (fun t ↦ L (Function.update c i t, Function.update w i x)) (R x) 0)
    (hmin : IsLocalMinOn L {p | ∀ j, ‖p.2 j‖ = 1} (c, w)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, dist x (w i) < δ → ‖x‖ = 1 → R x = 0 := by
  classical
  let park : ℝ × Definitions.Vec d → Definitions.Parameters d n :=
    fun p ↦ (Function.update c i p.1, Function.update w i p.2)
  have hcont : Continuous park := by
    exact ((continuous_const : Continuous (fun _ : ℝ × Definitions.Vec d ↦ c)).update
      i continuous_fst).prod_mk
        ((continuous_const : Continuous (fun _ : ℝ × Definitions.Vec d ↦ w)).update
          i continuous_snd)
  have hbase : park (0, w i) = (c, w) := by
    dsimp [park]
    rw [← hci, Function.update_eq_self, Function.update_eq_self]
  have hmaps : Set.MapsTo park
      {p : ℝ × Definitions.Vec d | ‖p.2‖ = 1}
      {p : Definitions.Parameters d n | ∀ j, ‖p.2 j‖ = 1} := by
    intro p hp j
    change ‖Function.update w i p.2 j‖ = 1
    by_cases hji : j = i
    · rw [hji, Function.update_same]
      exact hp
    · rw [Function.update_noteq hji]
      exact hw j
  have htend := (hcont.continuousWithinAt
    (s := {p : ℝ × Definitions.Vec d | ‖p.2‖ = 1})
    (x := (0, w i))).tendsto_nhdsWithin hmaps
  rw [hbase] at htend
  have hev := htend.eventually hmin
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hnear⟩ := hev
  refine ⟨δ, hδ, fun x hx hxu ↦ ?_⟩
  apply IsLocalMin.hasDerivAt_eq_zero (f := fun t ↦
    L (Function.update c i t, Function.update w i x)) (a := 0) _ (hderiv x hxu)
  show ∀ᶠ t in 𝓝 (0 : ℝ),
    L (Function.update c i 0, Function.update w i x) ≤
      L (Function.update c i t, Function.update w i x)
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun t ht ↦ ?_⟩
  rw [hflat x hxu]
  have hpair : dist ((t, x) : ℝ × Definitions.Vec d) (0, w i) < δ := by
    rw [Prod.dist_eq]
    exact max_lt ht hx
  exact hnear hpair hxu


/-- `stp:zm-revival`: the named exact quadratic yields a zero residual patch.
The only topological step is the flat-fibre neighborhood argument above. -/
theorem stp_zm_revival
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model)
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ j, ‖w j‖ = 1)
    {i : Fin n} (hci : c i = 0)
    (hmin : IsLocalMinOn (fun p : Definitions.Parameters d n ↦
      Definitions.Loss q p.1 p.2 s v) {p | ∀ j, ‖p.2 j‖ = 1} (c, w)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, dist x (w i) < δ → ‖x‖ = 1 →
      Definitions.Residual q c w s v x = 0 := by
  have hflat (x : Definitions.Vec d) (hx : ‖x‖ = 1) :
      Definitions.Loss q (Function.update c i 0) (Function.update w i x) s v =
        Definitions.Loss q c w s v := by
    have h := eq_revival_signed hd q c w s v hw hv i hci 0 x hx
    simpa only [zero_div, zero_mul, zero_pow two_pos, mul_zero, add_zero,
      sub_eq_zero] using h
  obtain ⟨δ, hδ, hpatch⟩ := zero_patch_of_flat_slot
    (fun p : Definitions.Parameters d n ↦ Definitions.Loss q p.1 p.2 s v)
    (fun x ↦ (1 / (2 * π)) * Definitions.Residual q c w s v x) hw hci hflat
    (fun x hx ↦ hasDerivAt_revival hd q c w s v hw hv i hci x hx) hmin
  refine ⟨δ, hδ, fun x hx hunit ↦ ?_⟩
  exact (mul_eq_zero.mp (hpatch x hx hunit)).resolve_left
    (one_div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))

/-- `stp:zm-pairing`: consume the normalized zero-residual identity. -/
theorem stp_zm_pairing
    (hd : 2 ≤ d) (q : PaperLeanFormalization.Model)
    (c : Fin n → ℝ) (w : Fin n → Definitions.Vec d)
    (s : Fin m → ℝ) (v : Fin m → Definitions.Vec d)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (hall : ∀ x : Definitions.Vec d, ‖x‖ = 1 →
      Definitions.Residual q c w s v x = 0) :
    Definitions.Loss q c w s v = 0 :=
  eq_zero_mass_pairing hd q c w s v hw hv hall

/-- Local proof of `prop:zero_mass_exact_fit`, with the shared literal loss. -/
theorem prop_zero_mass_exact_fit
    (hd : 1 ≤ d)
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    (hs₂ : d = 2 → ∀ k, 0 ≤ s k)
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    {i : Fin n} (hci : c i = 0)
    (hmin : IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦ Definitions.CenteredLoss p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w)) :
    Definitions.CenteredLoss c w s v = 0 := by
  by_cases hd1 : d = 1
  · subst d
    exact centered_local_min_dimension_one_zero c w s v hw hv i hmin
  · have hd2 : 2 ≤ d := by omega (config := {})
    have hmass : IsMassNetLocalMin s v c w :=
      (literal_local_minimum_iff_variable_kernel hd2 .centered c w s v hw hv).mp hmin
    obtain ⟨δ, hδ, hpatch⟩ := stp_zm_revival hd2 .centered hv hw hci hmin
    have hall := stp_zm_propagation hd hs₂ hv hw hmass (hw i) hδ hpatch
    exact stp_zm_pairing hd2 .centered c w s v hw hv hall

/-- For plain ReLU the continuation runs on the sphere with finitely many signed
student/teacher directions removed. This explicitly constructs its chart seed. -/
theorem plain_zero_patch_propagates
    {q : ℕ} (hq : 2 ≤ q)
    {s : Fin m → ℝ} {v : Fin m → EuclideanSpace ℝ (Fin (q + 1))}
    {c : Fin n → ℝ} {w : Fin n → EuclideanSpace ℝ (Fin (q + 1))}
    (hv : Definitions.UnitDirections v) (hw : Definitions.UnitDirections w)
    {i : Fin n} {δ : ℝ} (hδ : 0 < δ)
    (hvanish : ∀ x, dist x (w i) < δ → ‖x‖ = 1 →
      Definitions.Residual .plainRelu c w s v x = 0) :
    ∀ x : EuclideanSpace ℝ (Fin (q + 1)), ‖x‖ = 1 →
      Definitions.Residual .plainRelu c w s v x = 0 := by
  exact SphereContinuation.finite_kernel_residual_zero_on_sphere_of_patch
    (by simpa using (show 3 ≤ q + 1 by omega (config := {}))) reluPhi
    (SphereContinuation.continuous_centered_kernel.add (continuous_const.mul continuous_id))
    (SphereContinuation.analytic_kernel_add_linear orthantPhi (π / 2)
      (fun _ hr ↦ KernelAnalytic.analyticAt_centeredKernel hr))
    c w hw s v hv (w i) (hw i) hδ hvanish

/-- Local proof of `prop:nc-dead-student`, for all ambient dimensions at least three. -/
theorem prop_nc_dead_student
    (hd : 3 ≤ d)
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    {i : Fin n} (hci : c i = 0)
    (hmin : IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦ Definitions.PlainLoss p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w)) :
    Definitions.PlainLoss c w s v = 0 := by
  obtain ⟨δ, hδ, hpatch⟩ := stp_zm_revival (by omega (config := {})) .plainRelu hv hw hci hmin
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, d = q + 1 := ⟨d - 1, by omega (config := {})⟩
  have hall := plain_zero_patch_propagates (by omega (config := {}) : 2 ≤ q) hv hw hδ hpatch
  exact stp_zm_pairing (by omega (config := {})) .plainRelu c w s v hw hv hall


/-- Once a positive local minimum is confined, every teacher and student has
an angle in a common isometric plane. No lower bound on the span rank is used. -/
theorem positive_coplanar_local_minimum_angle_reduction
    (hd : 2 ≤ d)
    {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1) (hc : ∀ i, 0 < c i)
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hmin : IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦ Definitions.CenteredLoss p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w)) :
    ∃ (theta : Fin n → ℝ) (beta : Fin m → ℝ),
      IsLocalMin (Planar.variableLoss s beta) (c, theta) ∧
      Definitions.CenteredLoss c w s v =
        (1 / (2 * π)) * (Planar.variableLoss s beta (c, theta) -
          Planar.variableLoss s beta (s, beta)) := by
  classical
  have hmass : IsMassNetLocalMin s v c w := by
    exact (literal_local_minimum_iff_variable_kernel hd .centered c w s v hw hv).mp hmin
  obtain ⟨J, hJ⟩ := FinitePlane.exists_isometricPlane_containing_rankLeTwo_submodule hd
    (Submodule.span ℝ (Set.range v)) hplane
  have hvJ : ∀ k, v k ∈ Set.range J :=
    fun k ↦ hJ (v k) (Submodule.subset_span (Set.mem_range_self k))
  have hwJ := centered_positive_confinement_in_range hd J hvJ hv hw hc hmass
  choose v₀ hv₀ using hvJ
  choose w₀ hw₀ using hwJ
  have hv₀norm : ∀ k, ‖v₀ k‖ = 1 := fun k ↦ by
    rw [← J.norm_map (v₀ k), hv₀ k, hv k]
  have hw₀norm : ∀ i, ‖w₀ i‖ = 1 := fun i ↦ by
    rw [← J.norm_map (w₀ i), hw₀ i, hw i]
  choose beta hbeta using fun k ↦ exists_angle (hv₀norm k)
  choose theta htheta using fun i ↦ exists_angle (hw₀norm i)
  have hvfun : (fun k ↦ J (Definitions.Angle (beta k))) = v := by
    funext k
    rw [hbeta k, hv₀ k]
  have hwfun : (fun i ↦ J (Definitions.Angle (theta i))) = w := by
    funext i
    rw [htheta i, hw₀ i]
  refine ⟨theta, beta, ?_, ?_⟩
  · apply ambient_local_minimum_restricts_to_angles J
    rw [hvfun, hwfun]
    exact hmass
  · rw [← hvfun, ← hwfun]
    exact centered_loss_in_isometric_angle_chart hd J c theta s beta


/-- Width zero, width one, and arbitrary angle representatives are reduced
locally to the canonical multi-student planar obligation. -/
theorem positive_planar_exact_fit_of_canonical_ge_two
    (hplanar : ∀ {N M : ℕ} (c theta : Fin N → ℝ) (s beta : Fin M → ℝ),
      2 ≤ N → M ≤ N → (∀ i, 0 < c i) → (∀ k, 0 < s k) →
      (∀ i, 0 ≤ theta i ∧ theta i < π) →
      (∀ k, 0 ≤ beta k ∧ beta k < π) →
      IsLocalMin (Planar.variableLoss s beta) (c, theta) →
      Planar.variableLoss s beta (c, theta) = Planar.variableLoss s beta (s, beta))
    (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hmn : m ≤ n) (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (hmin : IsLocalMin (Planar.variableLoss s beta) (c, theta)) :
    Planar.variableLoss s beta (c, theta) = Planar.variableLoss s beta (s, beta) := by
  by_cases hn0 : n = 0
  · subst n
    have hm0 : m = 0 := by omega (config := {})
    subst m
    simp only [Planar.variableLoss, Fin.sum_univ_zero]
  by_cases hn1 : n = 1
  · subst n
    by_cases hm0 : m = 0
    · subst m
      exact False.elim (width_one_positive_no_teacher c theta s beta (hc 0) hmin)
    have hm1 : m = 1 := by omega (config := {})
    subst m
    exact width_one_positive_local_min_exact_fit c theta s beta (hc 0) (hs 0) hmin
  obtain ⟨theta', beta', htheta', hbeta', hmin', hvalue, hself⟩ :=
    exists_canonical_angles_local_min c theta s beta hmin
  rw [← hvalue, ← hself]
  exact hplanar c theta' s beta' (by omega (config := {})) hmn hc hs htheta' hbeta' hmin'

/-- The final ambient assembly, with the precise planar obligation stated
explicitly while its local support/interlacing/beam proof is developed. -/
theorem centered_benign_of_planar_exact_fit
    (hplanar : ∀ {N M : ℕ} (c theta : Fin N → ℝ) (s beta : Fin M → ℝ),
      M ≤ N → (∀ i, 0 < c i) → (∀ k, 0 < s k) →
      IsLocalMin (Planar.variableLoss s beta) (c, theta) →
      Planar.variableLoss s beta (c, theta) = Planar.variableLoss s beta (s, beta))
    (hd : 2 ≤ d) (hmn : m ≤ n)
    {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hc : ∀ i, 0 ≤ c i) (hs : ∀ k, 0 < s k)
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hmin : IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦ Definitions.CenteredLoss p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w)) :
    Definitions.CenteredLoss c w s v = 0 := by
  classical
  by_cases hpos : ∀ i, 0 < c i
  · obtain ⟨theta, beta, hminAngle, hloss⟩ :=
      positive_coplanar_local_minimum_angle_reduction hd hv hw hpos hplane hmin
    rw [hloss, hplanar c theta s beta hmn hpos hs hminAngle, sub_self, mul_zero]
  · obtain ⟨i, hi⟩ := Classical.not_forall.mp hpos
    exact prop_zero_mass_exact_fit (by omega (config := {})) (fun _ k ↦ (hs k).le) hv hw
      (le_antisymm (le_of_not_gt hi) (hc i)) hmin


/-- The normalized literal planar loss is differentiable because its complete
finite-kernel expression is differentiable. -/
theorem differentiable_literal_planar_loss {n m : ℕ} (s beta : Fin m → ℝ) :
    Differentiable ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      Definitions.CenteredLoss p.1 (fun i ↦ Definitions.Angle (p.2 i))
        s (fun k ↦ Definitions.Angle (beta k))) := by
  have h := ((Planar.differentiable_variableLoss (n := n) s beta).sub_const
    (Planar.variableLoss s beta (s, beta))).const_mul (1 / (2 * π) : ℝ)
  convert h using 1
  funext p
  exact Planar.GaussianSurface.centeredLoss_eq_variableLoss p.1 p.2 s beta

/-- A strict negative *total* second derivative still gives a genuine escape:
being nonzero first certifies that `deriv f` really is differentiable. -/
theorem negative_total_second_derivative_contradicts_local_min
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L : P → ℝ) (hL : Differentiable ℝ L)
    (gamma : ℝ → P) (hgamma : Differentiable ℝ gamma)
    (hnegative : deriv (deriv (L ∘ gamma)) 0 < 0) :
    ¬ IsLocalMin L (gamma 0) := by
  intro hmin
  have hline : IsLocalMin (L ∘ gamma) 0 :=
    hmin.comp_continuous (g := gamma) (b := 0) hgamma.continuous.continuousAt
  have hdiff : ∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ (L ∘ gamma) t :=
    Filter.eventually_of_forall (hL.comp hgamma)
  have hsecond : HasDerivAt (deriv (L ∘ gamma))
      (deriv (deriv (L ∘ gamma)) 0) 0 :=
    (differentiableAt_of_deriv_ne_zero (ne_of_lt hnegative)).hasDerivAt
  exact Preliminaries.negative_second_derivative_not_local_min hdiff
    hline.deriv_eq_zero hsecond hnegative hline

/-- The only deferred theorem input is exactly the shared normalized
`prop:beam-descent` statement. All support, counting, topology, and normalization
steps below are the fresh local proofs. -/
theorem canonical_positive_planar_exact_fit_of_beam_descent
    (beam : ∀ {N : ℕ} (c theta s beta : Fin N → ℝ),
      2 ≤ N → (∀ i, 0 < c i) → (∀ k, 0 < s k) →
      (∀ i, 0 ≤ theta i ∧ theta i < π) →
      (∀ k, 0 ≤ beta k ∧ beta k < π) →
      Function.Injective theta → Function.Injective beta →
      (∀ i k, theta i ≠ beta k) →
      fderiv ℝ (fun p : (Fin N → ℝ) × (Fin N → ℝ) ↦
        Definitions.CenteredLoss p.1 (fun i ↦ Definitions.Angle (p.2 i))
          s (fun k ↦ Definitions.Angle (beta k))) (c, theta) = 0 →
      ∃ dc dtheta : Fin N → ℝ,
        deriv (deriv (fun t : ℝ ↦ Definitions.CenteredLoss (fun i ↦ c i + t * dc i)
          (fun i ↦ Definitions.Angle (theta i + t * dtheta i))
          s (fun k ↦ Definitions.Angle (beta k)))) 0 < 0)
    {n m : ℕ} (c theta : Fin n → ℝ) (s beta : Fin m → ℝ)
    (hn : 2 ≤ n) (hmn : m ≤ n) (hc : ∀ i, 0 < c i) (hs : ∀ k, 0 < s k)
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hmin : IsLocalMin (Planar.variableLoss s beta) (c, theta)) :
    Planar.variableLoss s beta (c, theta) = Planar.variableLoss s beta (s, beta) := by
  classical
  by_cases hempty : Planar.positiveLines c theta s beta = ∅
  · let i : Fin n := ⟨0, by omega (config := {})⟩
    exact Planar.variableLoss_eq_exact_fit_of_residual_zero c theta s beta
      (Planar.empty_positive_support_residual_zero c theta s beta hempty
        (theta i) (Planar.mass_stationarity hmin.fderiv_eq_zero i))
  · obtain ⟨hnm, hinj, hbinj, hsep, _hinterlaces⟩ :=
      Planar.clean_structure_of_nonempty_positive_lines hmn htheta hbeta hc hs hmin
        (Finset.nonempty_iff_ne_empty.mpr hempty)
    subst m
    have hminLiteral := (Planar.GaussianSurface.centeredLoss_isLocalMin_iff c theta s beta).mpr hmin
    obtain ⟨dc, dtheta, hnegative⟩ := beam c theta s beta hn hc hs htheta hbeta
      hinj hbinj hsep hminLiteral.fderiv_eq_zero
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun p ↦
      Definitions.CenteredLoss p.1 (fun i ↦ Definitions.Angle (p.2 i))
        s (fun k ↦ Definitions.Angle (beta k))
    let gamma : ℝ → (Fin n → ℝ) × (Fin n → ℝ) :=
      fun t ↦ ((fun i ↦ c i + t * dc i), (fun i ↦ theta i + t * dtheta i))
    have hgamma : Differentiable ℝ gamma := by
      apply Differentiable.prod
      · exact differentiable_pi.mpr fun i ↦
          (differentiable_const (c i)).add (differentiable_id.mul_const (dc i))
      · exact differentiable_pi.mpr fun i ↦
          (differentiable_const (theta i)).add (differentiable_id.mul_const (dtheta i))
    have hbase : gamma 0 = (c, theta) := by simp only [gamma, zero_mul, add_zero]
    have hnot := negative_total_second_derivative_contradicts_local_min L
      (differentiable_literal_planar_loss s beta) gamma hgamma hnegative
    rw [hbase] at hnot
    exact False.elim (hnot hminLiteral)

/-- Exact `lem:S-is-small`, proved without beam descent. The inactive-slot
case uses local flatness, the zero-arc cut and the causal propagation proof. -/
theorem lem_S_is_small {n m : ℕ} (hmn : m ≤ n)
    {c theta : Fin n → ℝ} {s beta : Fin m → ℝ}
    (htheta : ∀ i, 0 ≤ theta i ∧ theta i < π)
    (hbeta : ∀ k, 0 ≤ beta k ∧ beta k < π)
    (hc : ∀ i, 0 ≤ c i) (hs : ∀ k, 0 < s k)
    (hmin : IsLocalMin (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
      Definitions.CenteredLoss p.1 (fun i ↦ Definitions.Angle (p.2 i))
        s (fun k ↦ Definitions.Angle (beta k))) (c, theta))
    (hsmall : (Definitions.PositiveLines c theta s beta).card ≤ 1) :
    Definitions.CenteredLoss c (fun i ↦ Definitions.Angle (theta i))
      s (fun k ↦ Definitions.Angle (beta k)) = 0 := by
  classical
  have hfinite := (Planar.GaussianSurface.centeredLoss_isLocalMin_iff c theta s beta).mp hmin
  have hfit : Planar.variableLoss s beta (c, theta) =
      Planar.variableLoss s beta (s, beta) := by
    by_cases hpos : ∀ i, 0 < c i
    · by_cases hn0 : n = 0
      · subst n
        have hm0 : m = 0 := by omega (config := {})
        subst m
        simp only [Planar.variableLoss, Fin.sum_univ_zero]
      by_cases hn1 : n = 1
      · subst n
        by_cases hm0 : m = 0
        · subst m
          exact False.elim (width_one_positive_no_teacher c theta s beta (hpos 0) hfinite)
        have hm1 : m = 1 := by omega (config := {})
        subst m
        exact width_one_positive_local_min_exact_fit c theta s beta (hpos 0) (hs 0) hfinite
      exact Planar.variableLoss_eq_exact_fit_of_residual_zero c theta s beta
        (Planar.small_positive_support_residual_zero_of_two_students
          (by omega (config := {})) htheta hbeta hpos (fun k ↦ (hs k).le) hfinite hsmall)
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hpos
      have hci : c i = 0 := le_antisymm (le_of_not_gt hi) (hc i)
      obtain ⟨ε, hε, harc⟩ :=
        Planar.ZeroSlot.zero_mass_slot_residual_zero_arc c theta s beta i hci hfinite
      exact Planar.variableLoss_eq_exact_fit_of_residual_zero c theta s beta
        (planar_residual_zero_of_open_zero_arc c theta s beta (fun k ↦ (hs k).le)
          hfinite (theta i) hε harc)
  rw [Planar.GaussianSurface.centeredLoss_eq_variableLoss, hfit, sub_self, mul_zero]

theorem centered_benign {d n m : ℕ}
    (hd : 2 ≤ d) (hmn : m ≤ n)
    {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hc : ∀ i, 0 ≤ c i) (hs : ∀ k, 0 < s k)
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hmin : IsLocalMinOn
      (fun p : Definitions.Parameters d n ↦ Definitions.CenteredLoss p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w)) :
    Definitions.CenteredLoss c w s v = 0 := by
  apply centered_benign_of_planar_exact_fit
    (fun c theta s beta hmn hc hs hmin ↦
      positive_planar_exact_fit_of_canonical_ge_two
        (canonical_positive_planar_exact_fit_of_beam_descent
          Planar.GaussianSurface.prop_beam_descent)
        c theta s beta hmn hc hs hmin)
    hd hmn hv hw hc hs hplane hmin

/-- `thm:headline`: the learned skip reduces every local minimum to the centered theorem. -/
theorem thm_headline {d n m : ℕ} (hd : 2 ≤ d) (hmn : m ≤ n)
    {b bStar : Definitions.Vec d} {c : Fin n → ℝ} {w : Fin n → Definitions.Vec d}
    {s : Fin m → ℝ} {v : Fin m → Definitions.Vec d}
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hc : ∀ i, 0 ≤ c i) (hs : ∀ k, 0 < s k)
    (hmin : IsLocalMinOn
      (fun p : Definitions.Vec d × Definitions.Parameters d n ↦
        Definitions.SkipLoss p.1 p.2.1 p.2.2 bStar s v)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (b, (c, w))) :
    Definitions.SkipLoss b c w bStar s v = 0 := by
  obtain ⟨hb, hcenter⟩ := (Skip.skip_local_minimum_iff hd b c w bStar s v hw).mp hmin
  rw [Skip.eq_skip_connection hd,
    centered_benign hd hmn hv hw hc hs hplane hcenter, hb, sub_self, norm_zero]
  norm_num

section PositiveDimension

open Definitions MeasureTheory

/-- A pointwise centered fit with the current directions supplies a straight
path to a skip fit. Along this path the whole residual is scaled by `1 - t`. -/
theorem skip_local_min_zero_of_centered_fit {d n m : ℕ}
    (b bStar : Vec d) (c cFit : Fin n → ℝ) (w : Fin n → Vec d)
    (s : Fin m → ℝ) (v : Fin m → Vec d)
    (hw : ∀ i, ‖w i‖ = 1)
    (hfit : ∀ x, (∑ i, cFit i * (|⟪w i, x⟫_ℝ| / 2)) =
      ∑ k, s k * (|⟪v k, x⟫_ℝ| / 2))
    (hmin : IsLocalMinOn
      (fun p : Vec d × Parameters d n ↦ SkipLoss p.1 p.2.1 p.2.2 bStar s v)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (b, (c, w))) :
    SkipLoss b c w bStar s v = 0 := by
  let masses : ℝ → Fin n → ℝ := fun t i ↦ (1 - t) * c i + t * cFit i
  let lift : ℝ → Vec d × Parameters d n := fun t ↦
    (MatchingSkip bStar s v (masses t) w +
      (1 - t) • (b - MatchingSkip bStar s v c w), (masses t, w))
  have hcontMass : Continuous masses := by
    exact continuous_pi fun i ↦
      ((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)
  have hcont : Continuous lift :=
    (((Skip.matching_skip_continuous bStar s v).comp
      (hcontMass.prod_mk continuous_const)).add
        ((continuous_const.sub continuous_id).smul continuous_const)).prod_mk
      (hcontMass.prod_mk continuous_const)
  have hbase : lift 0 = (b, (c, w)) := by simp [lift, masses]
  have hloss (t : ℝ) : SkipLoss (lift t).1 (lift t).2.1 (lift t).2.2 bStar s v =
      (1 - t) ^ 2 * SkipLoss b c w bStar s v := by
    have hres (x : Vec d) :
        (⟪(lift t).1, x⟫_ℝ + ∑ i, (masses t) i * max 0 ⟪w i, x⟫_ℝ -
          (⟪bStar, x⟫_ℝ + ∑ k, s k * max 0 ⟪v k, x⟫_ℝ)) =
        (1 - t) * (⟪b, x⟫_ℝ + ∑ i, c i * max 0 ⟪w i, x⟫_ℝ -
          (⟪bStar, x⟫_ℝ + ∑ k, s k * max 0 ⟪v k, x⟫_ℝ)) := by
      rw [Skip.residual_even_odd, Skip.residual_even_odd]
      dsimp only [lift]
      rw [add_sub_cancel', real_inner_smul_left]
      simp only [masses, add_mul, mul_assoc, Finset.sum_add_distrib,
        ← Finset.mul_sum, hfit x]
      ring
    have hfun : (fun x : Vec d ↦
        (⟪(lift t).1, x⟫_ℝ + ∑ i, (masses t) i * max 0 ⟪w i, x⟫_ℝ -
          (⟪bStar, x⟫_ℝ + ∑ k, s k * max 0 ⟪v k, x⟫_ℝ)) ^ 2 *
          stdGaussianDensity x) = fun x ↦ (1 - t) ^ 2 *
        ((⟪b, x⟫_ℝ + ∑ i, c i * max 0 ⟪w i, x⟫_ℝ -
          (⟪bStar, x⟫_ℝ + ∑ k, s k * max 0 ⟪v k, x⟫_ℝ)) ^ 2 *
          stdGaussianDensity x) := by
      funext x
      rw [hres]
      ring
    change SkipLoss (lift t).1 (masses t) w bStar s v = _
    unfold SkipLoss
    rw [hfun, integral_mul_left]
    ring
  have hminLift : IsLocalMin
      (fun t : ℝ ↦ (1 - t) ^ 2 * SkipLoss b c w bStar s v) 0 := by
    have hmin' : IsLocalMinOn
        (fun p : Vec d × Parameters d n ↦ SkipLoss p.1 p.2.1 p.2.2 bStar s v)
        {p | ∀ i, ‖p.2.2 i‖ = 1} (lift 0) := by rw [hbase]; exact hmin
    have hh := (hmin'.comp_continuousOn
      (s := Set.univ) (fun _ _ ↦ hw) hcont.continuousOn (Set.mem_univ 0)).isLocalMin
        Filter.univ_mem
    convert hh using 1
    funext t
    exact (hloss t).symm
  have hderiv := (((hasDerivAt_id (0 : ℝ)).const_sub 1).pow 2).mul_const
    (SkipLoss b c w bStar s v)
  have hz := hminLift.hasDerivAt_eq_zero hderiv
  norm_num at hz
  linarith only [hz]

/-- On the line, any total teacher mass can be represented with the fixed
student directions, provided an empty student has an empty teacher. -/
theorem skip_local_min_dimension_one_zero {n m : ℕ} (hmn : m ≤ n)
    (b bStar : Vec 1) (c : Fin n → ℝ) (w : Fin n → Vec 1)
    (s : Fin m → ℝ) (v : Fin m → Vec 1)
    (hw : ∀ i, ‖w i‖ = 1) (hv : ∀ k, ‖v k‖ = 1)
    (hmin : IsLocalMinOn
      (fun p : Vec 1 × Parameters 1 n ↦ SkipLoss p.1 p.2.1 p.2.2 bStar s v)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (b, (c, w))) :
    SkipLoss b c w bStar s v = 0 := by
  classical
  obtain ⟨cFit, hsum⟩ : ∃ cFit : Fin n → ℝ, (∑ i, cFit i) = ∑ k, s k := by
    by_cases hn : n = 0
    · have hm : m = 0 := by omega (config := {})
      subst n; subst m
      exact ⟨c, by simp⟩
    · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      refine ⟨Function.update (fun _ ↦ 0) i (∑ k, s k), ?_⟩
      simpa using sum_mass_update_add (fun _ : Fin n ↦ (0 : ℝ)) i (∑ k, s k)
  apply skip_local_min_zero_of_centered_fit b bStar c cFit w s v hw _ hmin
  intro x
  simp_rw [centered_feature_dimension_one _ x (hw _),
    centered_feature_dimension_one _ x (hv _), ← Finset.sum_mul, hsum]

/-- The original higher-dimensional theorem and the scalar mass argument cover
every positive ambient dimension. -/
theorem centered_benign_pos_dimension {d n m : ℕ}
    (hd : 1 ≤ d) (hmn : m ≤ n)
    {c : Fin n → ℝ} {w : Fin n → Vec d}
    {s : Fin m → ℝ} {v : Fin m → Vec d}
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hc : ∀ i, 0 ≤ c i) (hs : ∀ k, 0 < s k)
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hmin : IsLocalMinOn
      (fun p : Parameters d n ↦ CenteredLoss p.1 p.2 s v)
      {p | ∀ i, ‖p.2 i‖ = 1} (c, w)) : CenteredLoss c w s v = 0 := by
  by_cases hd1 : d = 1
  · subst d
    by_cases hn : n = 0
    · have hm : m = 0 := by omega (config := {})
      subst n; subst m
      simp [CenteredLoss]
    · exact centered_local_min_dimension_one_zero c w s v hw hv
        ⟨0, Nat.pos_of_ne_zero hn⟩ hmin
  · exact centered_benign (by omega (config := {})) hmn hv hw hc hs hplane hmin

theorem skip_benign_pos_dimension {d n m : ℕ} (hd : 1 ≤ d) (hmn : m ≤ n)
    {b bStar : Vec d} {c : Fin n → ℝ} {w : Fin n → Vec d}
    {s : Fin m → ℝ} {v : Fin m → Vec d}
    (hplane : FiniteDimensional.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 2)
    (hv : ∀ k, ‖v k‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hc : ∀ i, 0 ≤ c i) (hs : ∀ k, 0 < s k)
    (hmin : IsLocalMinOn
      (fun p : Vec d × Parameters d n ↦ SkipLoss p.1 p.2.1 p.2.2 bStar s v)
      {p | ∀ i, ‖p.2.2 i‖ = 1} (b, (c, w))) : SkipLoss b c w bStar s v = 0 := by
  by_cases hd1 : d = 1
  · subst d
    exact skip_local_min_dimension_one_zero hmn b bStar c w s v hw hv hmin
  · exact thm_headline (by omega (config := {})) hmn hplane hv hw hc hs hmin

end PositiveDimension

end PaperLeanFormalization.Geometry
