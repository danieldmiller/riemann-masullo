module

public import RiemannMasullo.Ch13_ZerosHecke.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec6
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec5
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic

/-! # From the trace formula to GRH

Masullo, §1.4, pp. 27–31, repeated in §§1.8.4–1.8.5. The introductory trace
identity recurs as Theorem 12.5.1.1. The centered version is `traceFormula`.
The page 28 display uses an uncentered zero window. Its literal form is
`Printed.introTrace_globalTrace` in the companion file. The passage from the
trace identity to the zero-free region requires limits of the trace terms.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "D𝔽" => BruhatCompactSupport C𝔽
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "q(" v ")" => ((v : V).asIdeal.absNorm : ℝ)
local notation "N(" g ")" => (((ideleClassNorm F) (g : C𝔽)).val : ℝ)
local notation "right(" a ")" => (Complex.re ⁻¹' Ioi (a : ℝ))
local notation "τVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "finiteL(" χ ")" => (finiteHeckeL_exists_continuation (F := F) χ).choose
local notation "zeroOrder(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "windowZeros(" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder(χ, s) ∧ |s.re - 1 / 2| < (a : ℝ)}

-- TODO(paper-gap): The “Finish!” footnotes on p. 27 belong to §§1.3.3–1.3.4.
-- The deduction here inherits the unfinished kernel comparisons in those subsections.
-- The centered window in §1.8.4, p. 53, agrees with the shift in §1.4.3.

section CharacterTrace

/-- Paper: §1.4.1, p. 28. A radial profile gives a test of norm-one weight
conjugate to the character by multiplication by that conjugate on the idele classes.
Deviation: The conjugate is required by the stated weight and by the zero Mellin
pairing. The product in the prose of §§1.4.2–1.4.3 uses the character itself. -/
def introTraceTest (χ : U𝔽) (h : ℝ → ℂ) (g : C𝔽) : ℂ :=
  (star (χ g : ℂ)) * h (N(g))

/-- Paper: §1.4.1, p. 28. Right translation by a norm-one class multiplies the
test by the conjugate character value on that class. -/
theorem introTraceTest_mul_normOne (χ : U𝔽) (h : ℝ → ℂ)
    (g : C𝔽) (u : (ideleClassNorm F).ker) :
    introTraceTest χ h (g * u.val) = star (χ u.val : ℂ) * introTraceTest χ h g := by
  have hu : ideleClassNorm F u.val = 1 := u.property
  simp only [introTraceTest, map_mul, hu, mul_one, Circle.coe_mul, star_mul]
  ac_rfl

/-- Paper: §1.4.1, p. 28. Mathlib's Mellin moment of the radial profile uses the
positive norm coordinate with Haar density `dt/t`. -/
def introTraceMellin (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin h s

/-- Paper: §1.4.1, p. 28. In the selected isotype the global Mellin integral
exists and is the radial moment times the norm-one Tamagawa volume. -/
theorem introTraceTest_mellin (χ : U𝔽) (h : ℝ → ℂ) (φ : D𝔽)
    (_hφ : ∀ g, φ.val g = introTraceTest χ h g) (s : ℂ) :
    let f := fun g : C𝔽 ↦ φ.val g * ideleClassNormTwist χ s g
    Integrable f (ideleClassTamagawaMeasure F) ∧
      (∫ g, f g ∂ideleClassTamagawaMeasure F) = τVolume * introTraceMellin h s := by sorry

local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "archIntegrand(" χ ", " h ", " w ")" =>
  (fun u : (w : InfinitePlace F).Completionˣ ↦
    introTraceTest χ h (archClass(w) u) * (Real.sqrt (‖u.val‖ ^ InfinitePlace.mult w) : ℂ) /
      ((‖1 - u.val‖ ^ InfinitePlace.mult w : ℝ) : ℂ))

open Classical in
/-- Paper: §1.4.1, p. 28. The archimedean term is the ordinary local integral
on tests vanishing at norm one.
Deviation: As in the corrected `traceFormula`, the denominator uses the normalized
local absolute value of `1 - u`, and the weight is the square root of the
normalized norm of `u`. The displayed real denominator uses the positive sign
even for the negative branch. The displayed complex denominator is unsquared. -/
def introTraceArchimedean (χ : U𝔽) (h : ℝ → ℂ) (w : InfinitePlace F) : ℂ :=
  (if w.IsReal then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) *
    ∫ u, archIntegrand(χ, h, w) u ∂infiniteLocalMultiplicativeTamagawaMeasure F w

/-- Paper: §1.4.1, p. 28. At a real place this integral is the local
Connes–Weil term of a compactly supported Bruhat test vanishing at norm one. -/
theorem introTraceArchimedean_eq_realPrincipalValue (χ : U𝔽) (h : ℝ → ℂ)
    (_hh : h 1 = 0) (w : InfinitePlace F) (_hw : w.IsReal)
    (φ : BruhatCompactSupport w.Completionˣ)
    (_hφ : ∀ u, φ.val u = introTraceTest χ h (archClass(w) u)) :
    Integrable archIntegrand(χ, h, w) (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
      introTraceArchimedean χ h w = infiniteConnesWeilPrincipalValue w φ := by sorry

open Classical in
/-- Paper: §1.4.1, p. 28. The finite term at a place is a sum over the positive
and negative prime-power shells.
Deviation: Averaging over local integer units annihilates ramified characters.
At unramified places the uniformizer value uses the library's Euler convention. -/
def introTracePrimePower (χ : U𝔽) (h : ℝ → ℂ) (v : V) (k : ℕ) : ℂ :=
  let c := ideleClassNormTwist χ 0
  let m := k + 1
  if c.IsUnramifiedAt v then
    (Real.log q(v) : ℂ) *
      (c.localValue v ^ m * h (q(v) ^ m) + star (c.localValue v) ^ m * h ((q(v) ^ m)⁻¹)) /
      (q(v) : ℂ) ^ ((m : ℂ) / 2)
  else 0

/-- Paper: §1.4.1, p. 28. The two shells of exponent one for the trivial
character have coefficient `log(q)/sqrt(q)`. -/
theorem introTracePrimePower_one_first (h : ℝ → ℂ) (v : V) :
    introTracePrimePower (1 : U𝔽) h v 0 =
      (Real.log q(v) : ℂ) * (h q(v) + h (q(v)⁻¹)) / (q(v) : ℂ) ^ (1 / 2 : ℂ) := by
  classical
  have htriv : ideleClassNormTwist (1 : U𝔽) 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hunit (u : (v.adicCompletion F)ˣ) :
      (1 : HeckeCharacter (𝓞 F) F).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hur : (1 : HeckeCharacter (𝓞 F) F).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
      hunit (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv : (1 : HeckeCharacter (𝓞 F) F).localValue v = 1 := hunit u
  simp [introTracePrimePower, htriv, hur, hv]

/-- Paper: §1.4.1, p. 28. The spectral side sums the full zero orders in the
selected character and the open window centered at one half. -/
def introTraceSpectralSum (χ : U𝔽) (h : ℝ → ℂ) (a : ℝ) : ℂ :=
  ∑' ρ : windowZeros(χ, a), (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2)

/-- Paper: §1.4.1, p. 28. A window containing exactly one zero gives its
multiplicity times the radial Mellin moment at that zero's shifted parameter. -/
theorem introTraceSpectralSum_eq_single (χ : U𝔽) (h : ℝ → ℂ) (a : ℝ) (ρ : ℂ)
    (_hρ : 0 < zeroOrder(χ, ρ) ∧ |ρ.re - 1 / 2| < a)
    (_honly : ∀ w : windowZeros(χ, a), w.val = ρ) :
    introTraceSpectralSum χ h a =
      (zeroOrder(χ, ρ) : ℂ) * introTraceMellin h (ρ - 1 / 2) := by
  let w : windowZeros(χ, a) := ⟨ρ, _hρ⟩
  unfold introTraceSpectralSum
  exact tsum_eq_single w fun v hv ↦ (hv (Subtype.ext (_honly v))).elim

open Classical in
/-- Paper: §1.4.1, p. 28. In a single isotype, the local terms equal the
polar moments minus the zero sum. The polar moments occur in the trivial isotype.
Deviation: The character is represented by its extension trivial on the chosen
norm section. The window is centered as in §1.8.4. The identity specializes
the corrected `traceFormula`, using normalized local kernels and unit averages.
The common Tamagawa volume cancels against the Mellin disintegration factor.
The arbitrary window still depends on `traceFormula_exteriorZeros`. -/
theorem introTrace_characterTrace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (h : ℝ → ℂ) (_hh : h 1 = 0) (φ : D𝔽)
    (_hφ : ∀ g, φ.val g = introTraceTest χ h g) (a : ℝ) (_ha : 0 < a) :
    (∀ w : InfinitePlace F,
      Integrable archIntegrand(χ, h, w) (infiniteLocalMultiplicativeTamagawaMeasure F w)) ∧
    Summable (fun p : V × ℕ ↦ introTracePrimePower χ h p.1 p.2) ∧
    HasSum (fun ρ : windowZeros(χ, a) ↦
      (zeroOrder(χ, ρ.val) : ℂ) * introTraceMellin h (ρ.val - 1 / 2))
      ((if χ = 1 then introTraceMellin h (1 / 2) + introTraceMellin h (-1 / 2) else 0) -
        (∑ w : InfinitePlace F, introTraceArchimedean χ h w) -
        ∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2) := by sorry

end CharacterTrace

section Tests

/-- Paper: §1.4.2, p. 28. The radial power is zero below one, one half at
one, and the inverse complex power above one.
Deviation: The radial profile is extended by zero to the nonpositive real axis
for additive convolution. -/
def introTracePower (z : ℂ) (t : ℝ) : ℂ :=
  if 1 < t then (t : ℂ) ^ (-z) else if t = 1 then 1 / 2 else 0

/-- Paper: §1.4.2, p. 28. On the positive side at parameter two the profile
has value one quarter at two and value one half at the jump. -/
theorem introTracePower_two :
    introTracePower 2 2 = 1 / 4 ∧ introTracePower 2 1 = 1 / 2 := by
  refine ⟨?_, by simp [introTracePower]⟩
  simp only [introTracePower, show (1 : ℝ) < 2 by norm_num, ↓reduceIte, Complex.cpow_neg]
  norm_num

/-- Paper: §1.4.2, p. 28. The radial power is smooth on the two real
intervals separated by its jump at one. -/
theorem introTracePower_contDiffOn (z : ℂ) :
    ContDiffOn ℝ ⊤ (introTracePower z) ({1}ᶜ : Set ℝ) := by
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  rcases lt_or_gt_of_ne (show x ≠ 1 from hx) with h | h
  · have : introTracePower z =ᶠ[nhds x] fun _ ↦ 0 := by
      filter_upwards [eventually_lt_nhds h] with t ht
      simp [introTracePower, ht.not_gt, ht.ne]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have : introTracePower z =ᶠ[nhds x]
        fun t : ℝ ↦ Complex.exp ((Real.log t : ℂ) * (-z)) := by
      filter_upwards [eventually_gt_nhds h] with t ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
      simp only [introTracePower, ht, ↓reduceIte, Complex.cpow_def_of_ne_zero ht0,
        Complex.ofReal_log (by linarith : (0 : ℝ) ≤ t)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ this
    have hlog : ContDiffAt ℝ ⊤ Real.log x := Real.contDiffAt_log.2 (by linarith)
    exact Complex.contDiff_exp.contDiffAt.comp x
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog).mul contDiffAt_const)

/-- Paper: §1.4.2, p. 28. The limiting power depends holomorphically
on the complex parameter at each fixed radial coordinate. -/
theorem introTracePower_differentiable (t : ℝ) :
    Differentiable ℂ (fun z ↦ introTracePower z t) := by
  by_cases ht : 1 < t
  · simp only [introTracePower, ite_eq_left ht]
    exact differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (by linarith)))
  · simp only [introTracePower, ite_eq_right ht]
    exact differentiable_const _

/-- Paper: §1.4.2, pp. 28–29. The cutoffs increase pointwise to the indicator
of `(1, ∞)` and the mollifiers have nonnegative unit mass and shrinking support.
Deviation: The paper leaves the mollifier and convolution unspecified. This
uses ordinary additive convolution in the coordinate `t` with Lebesgue measure
and encodes the cofinal approximation by sequences. -/
def IsIntroTraceApproximation (h ρ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, ContDiff ℝ ⊤ (h n) ∧ HasCompactSupport (h n) ∧
    tsupport (h n) ⊆ Ioi 1 ∧ ∀ t, h n t ∈ Icc 0 1) ∧
  Monotone h ∧ (∀ t > 1, Tendsto (fun n ↦ h n t) atTop (𝓝 1)) ∧
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ n, 0 < ε n ∧ ContDiff ℝ ⊤ (ρ n) ∧ (∀ t, 0 ≤ ρ n t) ∧
      tsupport (ρ n) ⊆ Icc (-ε n) (ε n) ∧ (∫ t, ρ n t) = 1

/-- Paper: §1.4.2, pp. 28–29. Smooth bump cutoffs and ordinary mollifiers
give an approximation sequence with the stated support and convergence. -/
theorem exists_introTraceApproximation :
    ∃ h ρ, IsIntroTraceApproximation h ρ := by sorry

/-- Paper: §1.4.2, p. 28. The approximant is the cutoff times the mollified
radial power in the norm coordinate. -/
def introTraceApprox (h ρ : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (h t : ℂ) * ∫ u : ℝ, (ρ u : ℂ) * introTracePower z (t - u)

/-- Paper: §1.4.2, pp. 28–29. The approximants are supported strictly
above norm one and agree with the limiting power at each fixed norm other
than one in the limit.
Deviation: The support statement uses topological support, so each individual
cutoff vanishes in an open neighborhood of one. -/
theorem introTraceApprox_support (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    tsupport (introTraceApprox (h n) (ρ n) z) ⊆ Ioi 1 := by sorry

/-- Paper: §1.4.2, p. 29. Every fixed positive norm other than one has
the printed pointwise limit. -/
theorem introTraceApprox_tendsto (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (z : ℂ) (t : ℝ) (_ht : 0 < t) (_ht₁ : t ≠ 1) :
    Tendsto (fun n ↦ introTraceApprox (h n) (ρ n) z t) atTop (𝓝 (introTracePower z t)) := by sorry

/-- Paper: §1.4.2, pp. 28–29. At any fixed norm, the mollified cutoff
depends holomorphically on the complex parameter. -/
theorem introTraceApprox_differentiable (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (t : ℝ) :
    Differentiable ℂ (fun z ↦ introTraceApprox (h n) (ρ n) z t) := by
  obtain ⟨-, -, -, ε, -, hε⟩ := _hA
  obtain ⟨-, hρc, -, hρs, -⟩ := hε n
  have hρint : Integrable (ρ n) := hρc.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hρs)
  have hρm : Measurable fun u ↦ (ρ n u : ℂ) :=
    Complex.measurable_ofReal.comp hρc.continuous.measurable
  have hPm : ∀ z : ℂ, Measurable (introTracePower z) := fun z ↦
    Measurable.ite measurableSet_Ioi (by fun_prop)
      (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
  have hu : ∀ u, ρ n u ≠ 0 → t - u ≤ t + ε n := fun u hu ↦ by
    have := hρs (subset_tsupport _ hu)
    linarith [this.1]
  intro z₀
  set K : ℝ := |z₀.re| + 1
  set C : ℝ := |Real.log (t + ε n)| * |t + ε n| ^ K
  set M : ℝ := max 1 (|t + ε n| ^ K)
  have hpow : ∀ u, ∀ z ∈ Metric.ball z₀ 1, ρ n u ≠ 0 → 1 < t - u →
      (t - u) ^ (-z.re) ≤ |t + ε n| ^ K := by
    intro u z hz hρ h1
    have hz' : |z.re - z₀.re| < 1 :=
      (Complex.abs_re_le_norm (z - z₀)).trans_lt (by simpa [dist_eq_norm] using hz)
    calc (t - u) ^ (-z.re) ≤ (t - u) ^ K := Real.rpow_le_rpow_of_exponent_le h1.le
          (by linarith [(abs_lt.1 hz').1, neg_abs_le z₀.re])
      _ ≤ |t + ε n| ^ K := Real.rpow_le_rpow (by linarith)
          ((hu u hρ).trans (le_abs_self _)) (by positivity)
  have hF_int : Integrable (fun u ↦ (ρ n u : ℂ) * introTracePower z₀ (t - u)) := by
    refine Integrable.mono' (hρint.norm.mul_const M)
      (hρm.mul ((hPm z₀).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Eventually.of_forall fun u ↦ ?_)
    by_cases hρ : ρ n u = 0
    · simp [hρ]
    rw [norm_mul, Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold introTracePower
    split_ifs with h1 h2
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
      exact (hpow u z₀ (Metric.mem_ball_self one_pos) hρ h1).trans (le_max_right _ _)
    · exact le_trans (by norm_num) (le_max_left _ _)
    · simpa using (zero_le_one.trans (le_max_left _ _) : (0 : ℝ) ≤ M)
  have hF'_meas : AEStronglyMeasurable (fun u : ℝ ↦ (ρ n u : ℂ) *
      if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z₀) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
      else 0) volume :=
    (hρm.mul (Measurable.ite (measurableSet_lt measurable_const
      (measurable_const.sub measurable_id)) (by fun_prop) measurable_const)).aestronglyMeasurable
  have h_bound : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1, ‖(ρ n u : ℂ) *
      (if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
        else 0)‖ ≤ ‖ρ n u‖ * C := by
    refine Eventually.of_forall fun u z hz ↦ ?_
    rw [norm_mul, Complex.norm_real]
    by_cases hρ : ρ n u = 0
    · simp [hρ]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    split_ifs with h1
    · have hc : 0 < t - u := by linarith
      rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos hc, Complex.neg_re, ← Complex.ofReal_log hc.le,
        Complex.norm_real, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul ?_ (hpow u z hz hρ h1) (by positivity) (abs_nonneg _)
      rw [abs_of_nonneg (Real.log_nonneg h1.le)]
      exact (Real.log_le_log hc (hu u hρ)).trans (le_abs_self _)
    · simp only [norm_zero]
      positivity
  have h_diff : ∀ᵐ u ∂volume, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) ((ρ n u : ℂ) *
        (if 1 < t - u then ((t - u : ℝ) : ℂ) ^ (-z) * Complex.log ((t - u : ℝ) : ℂ) * (-1)
          else 0)) z := by
    refine Eventually.of_forall fun u z _ ↦ ?_
    split_ifs with h1
    · have hfun : (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) =
          fun z ↦ (ρ n u : ℂ) * ((t - u : ℝ) : ℂ) ^ (-z) := by
        funext z
        simp [introTracePower, h1]
      rw [hfun]
      exact ((hasDerivAt_neg z).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.2 (by linarith)))).const_mul _
    · have hfun : (fun z ↦ (ρ n u : ℂ) * introTracePower z (t - u)) =
          fun _ ↦ (ρ n u : ℂ) * introTracePower 0 (t - u) := by
        funext z
        simp [introTracePower, h1]
      rw [hfun]
      exact (hasDerivAt_const z _).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z ↦ (hρm.mul
      ((hPm z).comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    hF_int hF'_meas h_bound (hρint.norm.mul_const C) h_diff
  exact (differentiableAt_const _).mul key.2.differentiableAt

/-- Paper: §1.4.2, pp. 28–29. After twisting by the conjugate character
the approximant is a compactly supported Bruhat test on the idele classes. -/
theorem introTraceApprox_exists_bruhat (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    ∃ φ : D𝔽, ∀ g, φ.val g = introTraceTest χ (introTraceApprox (h n) (ρ n) z) g := by sorry

/-- Paper: §1.4.2, pp. 28–29. The twisted approximant satisfies the second
standing hypothesis of the trace identity, vanishing at every norm-one class. -/
theorem introTraceApprox_zero_on_normOne (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) :
    ∀ g : (ideleClassNorm F).ker,
      introTraceTest χ (introTraceApprox (h n) (ρ n) z) g.val = 0 := by
  intro g
  have hzero : introTraceApprox (h n) (ρ n) z 1 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun ht ↦ lt_irrefl (1 : ℝ) (introTraceApprox_support h ρ _hA n z ht)
  have hg : ideleClassNorm F g.val = 1 := g.property
  simp [introTraceTest, hg, hzero]

/-- Paper: §§1.4.2–1.4.3, pp. 28–29. For a fixed Mellin exponent `s`,
the approximant moments converge locally uniformly on `Re z > Re s`
to the Mellin integral of the limiting radial power. -/
theorem introTraceApprox_mellin_tendsto (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (s : ℂ) :
    TendstoLocallyUniformlyOn
      (fun n z ↦ introTraceMellin (introTraceApprox (h n) (ρ n) z) s)
      (fun z ↦ introTraceMellin (introTracePower z) s) atTop right(s.re) := by sorry

/-- Paper: §§1.4.2, 1.4.5, pp. 28–29. The Mellin transform of the limiting
radial power exists on the convergence half-plane and equals `1 / (z - s)`. -/
theorem introTracePower_mellin (z s : ℂ) (_hs : s.re < z.re) :
    IntegrableOn (fun t : ℝ ↦ introTracePower z t * (t : ℂ) ^ (s - 1)) (Ioi 0) ∧
      introTraceMellin (introTracePower z) s = 1 / (z - s) := by sorry

end Tests

section Limits

local notation "approx(" h ", " ρ ", " n ", " z ")" => introTraceApprox (h n) (ρ n) z
local notation "archSum(" χ ", " h ")" =>
  (∑ w : InfinitePlace F, introTraceArchimedean χ h w)
local notation "primeSum(" χ ", " h ")" =>
  (∑' p : V × ℕ, introTracePrimePower χ h p.1 p.2)

/-- With the radial cutoff fixed, Fubini combines the local integral and the
mollification into a single weighted Mellin integral. -/
private theorem introTraceApprox_archimedean_differentiable_integral
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ] (A : X → ℂ) (t : X → ℝ)
    (ρ : ℝ → ℝ) (hA : Measurable A) (ht : Measurable t) (hρ : Measurable ρ)
    (hAi : Integrable A μ) (hρi : Integrable ρ) (B ε : ℝ)
    (hB : ∀ x, A x ≠ 0 → t x ≤ B) (hε : ∀ u, ρ u ≠ 0 → -ε ≤ u) :
    Differentiable ℂ (fun z ↦ ∫ x, A x * ∫ u, (ρ u : ℂ) *
      introTracePower z (t x - u) ∂volume ∂μ) := by
  let r (p : X × ℝ) := max 1 (t p.1 - p.2)
  let f (p : X × ℝ) := A p.1 * (ρ p.2 : ℂ) * introTracePower 0 (t p.1 - p.2)
  have hr : Measurable r := measurable_const.max (ht.comp measurable_fst |>.sub measurable_snd)
  have hr1 (p : X × ℝ) : 1 ≤ r p := le_max_left _ _
  have hrp (p : X × ℝ) : 0 < r p := zero_lt_one.trans_le (hr1 p)
  have hf : Measurable f := by
    have hp : Measurable (introTracePower 0) := by
      unfold introTracePower
      exact Measurable.ite measurableSet_Ioi (by fun_prop)
        (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
    exact ((hA.comp measurable_fst).mul ((hρ.comp measurable_snd).complex_ofReal)).mul
      (hp.comp ((ht.comp measurable_fst).sub measurable_snd))
  have hI (z : ℂ) : Integrable (fun p ↦ f p * (r p : ℂ) ^ z) (μ.prod volume) := by
    let C := max 1 (B + ε) ^ |z.re|
    have hdom := (hAi.norm.mul_prod hρi.norm).mul_const C
    refine hdom.mono' (hf.mul (hr.complex_ofReal.pow_const _)).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ ?_)
    by_cases ha : A p.1 = 0
    · simp [f, ha]
    by_cases hρ0 : ρ p.2 = 0
    · simp [f, hρ0]
    have hrle : r p ≤ max 1 (B + ε) := by
      exact max_le_max le_rfl (by linarith [hB _ ha, hε _ hρ0])
    have hpow : r p ^ z.re ≤ C :=
      (Real.rpow_le_rpow_of_exponent_le (hr1 p) (le_abs_self _)).trans
        (Real.rpow_le_rpow (hrp p).le hrle (abs_nonneg _))
    have hp : ‖introTracePower 0 (t p.1 - p.2)‖ ≤ 1 := by
      unfold introTracePower
      split_ifs <;> norm_num [norm_div]
    simp only [f, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (hrp p)]
    calc
      _ ≤ (‖A p.1‖ * ‖ρ p.2‖ * 1) * C := by gcongr
      _ = _ := by simp
  have han := analyticOnNhd_integral_mul_cpow_of_integrable (μ.prod volume)
    f r hr hrp isOpen_univ (fun z _ ↦ hI z)
  have hd : Differentiable ℂ (fun z : ℂ ↦ ∫ p, f p * (r p : ℂ) ^ z ∂μ.prod volume) :=
    fun z ↦ (han z (mem_univ _)).differentiableAt
  convert hd.comp differentiable_neg using 1
  ext1 z
  change _ = ∫ p, f p * (r p : ℂ) ^ (-z) ∂μ.prod volume
  rw [integral_prod _ (hI (-z))]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun u ↦ ?_
  have hp (a : ℝ) : introTracePower z a =
      introTracePower 0 a * ((max 1 a : ℝ) : ℂ) ^ (-z) := by
    by_cases ha : 1 < a
    · simp [introTracePower, ha, max_eq_right ha.le]
    · simp [introTracePower, ha, max_eq_left (le_of_not_gt ha)]
  simp only [f, r, hp (t x - u), mul_assoc]

/-- Paper: §1.4.3, p. 29. Each fixed-cutoff archimedean integral is entire
in the parameter.
Deviation: The archimedean kernels use the corrected trace formula. -/
theorem introTraceApprox_archimedean_differentiable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (w : InfinitePlace F) :
    Differentiable ℂ (fun z ↦ introTraceArchimedean χ approx(h, ρ, n, z) w) := by
  classical
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology w.Completionˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : LocallyCompactSpace w.Completionˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
  let : μ.IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let localClass := IdeleClassGroup.ofCompletion (𝓞 F) F w
  let t (u : w.Completionˣ) : ℝ := ‖u.val‖ ^ w.mult
  have ht : Continuous t := (continuous_norm.comp Units.continuous_val).pow _
  have ht_norm (u : w.Completionˣ) :
      N(IdeleClassGroup.ofCompletion (𝓞 F) F w u) = t u := by
    rw [ideleClassNorm_ofCompletion, Units.val_pow_eq_pow_val, NNReal.coe_pow]
    rfl
  obtain ⟨hh, -, -, ε, -, hε⟩ := _hA
  obtain ⟨hhc, hhK, hhS, -⟩ := hh n
  obtain ⟨-, hρc, -, hρS, -⟩ := hε n
  obtain ⟨B, hB⟩ := hhK.bddAbove
  let K := t ⁻¹' tsupport (h n)
  have hK_closed : IsClosed K := (isClosed_tsupport _).preimage ht
  have hK_norm (u : w.Completionˣ) (hu : u ∈ K) : 1 < t u := hhS hu
  have hK : IsCompact K := by
    let S : Set w.Completion := (fun u : w.Completion ↦ ‖u‖ ^ w.mult) ⁻¹' tsupport (h n)
    have hS1 {u : w.Completion} (hu : u ∈ S) : 1 < ‖u‖ ^ w.mult := hhS hu
    have hScompact : IsCompact S := by
      have he := InfinitePlace.Completion.isometry_extensionEmbedding w
      have hball : IsCompact (Metric.closedBall (0 : w.Completion) B) := by
        simpa only [← he.preimage_closedBall] using he.isClosedEmbedding.isCompact_preimage
          (isCompact_closedBall (InfinitePlace.Completion.extensionEmbedding w 0) B)
      refine hball.of_isClosed_subset ((isClosed_tsupport _).preimage (continuous_norm.pow _)) ?_
      intro u hu
      rw [mem_closedBall_zero_iff]
      have hnorm : 1 ≤ ‖u‖ := by
        by_contra! h
        exact (not_lt_of_ge (pow_le_one₀ (norm_nonneg _) h.le)) (hS1 hu)
      exact (le_self_pow₀ hnorm w.mult_ne_zero).trans (hB hu)
    refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' hScompact ?_
    intro u hu
    have hne : u ≠ 0 := by
      intro hzero
      have h := hS1 hu
      rw [hzero, norm_zero, zero_pow w.mult_ne_zero] at h
      exact (not_lt_of_ge zero_le_one) h
    exact ⟨Units.mk0 u hne, rfl⟩
  let a (u : w.Completionˣ) : ℂ :=
    star (χ (localClass u) : ℂ) * (h n (t u) : ℂ) *
      (Real.sqrt (t u) : ℂ) / ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)
  have hzero (u : w.Completionˣ) (hu : u ∉ K) : a u = 0 := by
    have hh0 : h n (t u) = 0 := image_eq_zero_of_notMem_tsupport hu
    simp [a, hh0]
  have hχ : Continuous (fun u : w.Completionˣ ↦ (χ (localClass u) : ℂ)) :=
    continuous_subtype_val.comp (χ.continuous.comp (continuous_ideleClass_ofCompletion F w))
  have hden : Continuous (fun u : w.Completionˣ ↦ ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_norm.comp (continuous_const.sub Units.continuous_val)).pow _)
  have ha : Measurable a :=
    ((hχ.star.measurable.mul ((hhc.continuous.comp ht).measurable.complex_ofReal)).mul
      ((Real.continuous_sqrt.comp ht).measurable.complex_ofReal)).div hden.measurable
  have hai : Integrable a μ := by
    have hac : ContinuousOn a K := by
      apply ContinuousOn.div
      · exact ((hχ.star.mul (Complex.continuous_ofReal.comp (hhc.continuous.comp ht))).mul
          (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp ht))).continuousOn
      · exact hden.continuousOn
      · intro u hu
        apply Complex.ofReal_ne_zero.mpr
        apply pow_ne_zero
        rw [norm_ne_zero_iff, sub_ne_zero]
        intro he
        have hone : t u = 1 := by simp [t, ← he]
        exact (ne_of_gt (hK_norm u hu)) hone
    refine ((hac.integrableOn_compact hK).integrable_indicator hK_closed.measurableSet).congr ?_
    refine ae_of_all _ fun u ↦ ?_
    by_cases hu : u ∈ K
    · exact indicator_of_mem hu _
    · rw [indicator_of_notMem hu, hzero u hu]
  have hρi : Integrable (ρ n) := hρc.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hρS)
  have hd := introTraceApprox_archimedean_differentiable_integral μ a t (ρ n)
    ha ht.measurable hρc.continuous.measurable hai hρi B (ε n)
    (fun u hu ↦ hB (show u ∈ K from not_not.mp (mt (hzero u) hu)))
    (fun x hx ↦ (hρS (subset_tsupport _ hx)).1)
  unfold introTraceArchimedean
  refine (differentiable_const _).mul ?_
  convert hd using 1
  ext1 z
  apply integral_congr_ae
  refine ae_of_all _ fun u ↦ ?_
  simp only [introTraceTest, introTraceApprox, ht_norm, a, t]
  ring

/-- Paper: §1.4.3, p. 29. For the trivial rational character at parameter two,
the real-place term goes to positive infinity as the cutoffs are removed.
Deviation: This replaces the printed uniform bound. It also applies to the
corrected trace formula, since the positive real branch has the same kernel. -/
theorem introTraceApprox_rat_archimedean_tendsto_atTop (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (∑ w : InfinitePlace ℚ,
      introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) w).re) atTop atTop := by sorry

/-- Paper: §1.4.3, p. 29. A common subsequence of the two archimedean sums
has holomorphic limits on the interior of the compact set if the stated
uniform bounds hold.
Deviation: The bounds are hypotheses of the Montel implication. The real-place
bound fails for the rational trivial character. -/
theorem introTrace_montel_of_bounded (K : Set ℂ) (_hK : IsCompact K)
    (A B : ℕ → ℂ → ℂ) (_hA : ∀ n, DifferentiableOn ℂ (A n) (interior K))
    (_hB : ∀ n, DifferentiableOn ℂ (B n) (interior K))
    (_hbound : ∃ C : ℝ, 0 < C ∧ ∀ n z, z ∈ K → ‖A n z‖ ≤ C ∧ ‖B n z‖ ≤ C) :
    ∃ (k : ℕ → ℕ) (L₁ L₂ : ℂ → ℂ), StrictMono k ∧
      TendstoLocallyUniformlyOn (A ∘ k) L₁ atTop (interior K) ∧
      TendstoLocallyUniformlyOn (B ∘ k) L₂ atTop (interior K) ∧
      AnalyticOnNhd ℂ L₁ (interior K) ∧ AnalyticOnNhd ℂ L₂ (interior K) := by sorry

-- TODO(paper-gap): Pointwise convergence of the individual Mellin terms
-- leaves the infinite zero sum uncontrolled. At the trivial rational character and
-- a window containing the full divisor the zero sum itself diverges at z = 2.

/-- Paper: §1.4.3, p. 29. At each fixed cutoff the zero sum converges at every
parameter. This gives the totalized spectral sum its intended value in every chart. -/
theorem introTraceApprox_spectral_summable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (a : ℝ) (_ha : 0 < a) (z : ℂ) :
    Summable (fun r : windowZeros(χ, a) ↦
      (zeroOrder(χ, r.val) : ℂ) * introTraceMellin approx(h, ρ, n, z) (r.val - 1 / 2)) := by sorry

/-- Paper: §1.4.3, p. 29. Each fixed-cutoff zero sum is entire in the
test parameter.
Deviation: The sum uses full zero orders and the corrected centered window.
Passing to a holomorphic limit needs a further estimate on the zero sum. -/
theorem introTraceApprox_spectral_differentiable (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (a : ℝ) (_ha : 0 < a) :
    Differentiable ℂ (fun z ↦ introTraceSpectralSum χ approx(h, ρ, n, z) a) := by sorry

/-- Paper: §1.4.3, p. 29. For the trivial rational character, the zero
sum in the window of half-width one has real part tending to minus infinity
at parameter two.
Deviation: This replaces the claimed separate holomorphic spectral limit.
The full explicit formula suffices for this window because it contains all zeros. -/
theorem introTraceApprox_rat_spectral_tendsto_atBot (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1).re)
      atTop atBot := by sorry

/-- Paper: §1.4.4, p. 29. The negative prime-power norms lie below one,
where every cutoff test vanishes. -/
theorem introTraceApprox_primePower_inv_zero (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) (n : ℕ) (z : ℂ) (v : V) (m : ℕ) (_hm : 0 < m) :
    approx(h, ρ, n, z) ((q(v) ^ m)⁻¹) = 0 := by
  have hq : 1 ≤ q(v) := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hle : (q(v) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hq)
  apply image_eq_zero_of_notMem_tsupport
  exact fun ht ↦ hle.not_gt (introTraceApprox_support h ρ _hA n z ht)

/-- Paper: §1.4.4, p. 29. The finite terms converge locally uniformly to
the negative logarithmic derivative of the finite Hecke L-function.
Deviation: The sign is negative by differentiation of the Euler product,
as in `finiteHeckeL_logDeriv_hasSum_ideals`. The same argument works on
`Re z > 1/2`, the absolute-convergence region for `s = z + 1/2`.
The local coefficients include the unit averaging in the corrected trace formula. -/
theorem introTraceApprox_primeSum_tendsto (χ : U𝔽) (h ρ : ℕ → ℝ → ℝ)
    (_hA : IsIntroTraceApproximation h ρ) :
    TendstoLocallyUniformlyOn (fun n z ↦ primeSum(χ, approx(h, ρ, n, z)))
      (fun z ↦ -logDeriv finiteL(χ) (z + 1 / 2)) atTop right(1 / 2) := by sorry

open Classical in
/-- Paper: §1.4.5, pp. 29–30. If the archimedean and zero terms together
converge on the common half-plane to the restriction of a holomorphic
function on the right of the window, that function extends the regularized
shifted logarithmic derivative.
Deviation: The two polar moments are added to the logarithmic derivative
because the finite sum tends to its negative. The character is normalized
on the norm section so the poles have the printed coordinates. The corrected
trace formula gives the identity at each cutoff with the centered zero window
and normalized local terms. Neither separate Montel limit in the sketch
supplies the hypothesis on the combined terms. -/
theorem introTrace_logDeriv_extension_of_limit (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (a : ℝ) (_ha : 0 < a) (h ρ : ℕ → ℝ → ℝ) (_hA : IsIntroTraceApproximation h ρ)
    (H : ℂ → ℂ) (_hH : AnalyticOnNhd ℂ H right(a))
    (_hlim : TendstoLocallyUniformlyOn
      (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a)
      H atTop right(max a 1)) :
    EqOn H (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
      if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1) := by sorry

-- TODO(paper-gap): The reference to §5.1 on p. 29 (also p. 55) supplies no
-- continuation argument. The corrected cutoff identity does not itself bound
-- the separate terms or provide the holomorphic limit of their sum.

/-- Paper: §1.4.5, pp. 29–30. In each normalized chart a holomorphic function
on the right of the window agrees on the common half-plane with the limit of
the combined archimedean and spectral terms for a cofinal family of tests.
Gap: The separate limits on p. 29 diverge for the trivial rational character.
The paper gives no extension of the combined value across the overlap.
Deviation: Only the restriction of the extension to the overlap must be a
cutoff limit. One cofinal family for each chart and width suffices. -/
theorem introTrace_combined_limit_extension (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (_hχ : ∀ t, χ (τ t) = 1)
    (a : ℝ) (_ha : 0 < a) :
    ∃ (h ρ : ℕ → ℝ → ℝ) (H : ℂ → ℂ), IsIntroTraceApproximation h ρ ∧
      AnalyticOnNhd ℂ H right(a) ∧ TendstoLocallyUniformlyOn
        (fun n z ↦ archSum(χ, approx(h, ρ, n, z)) + introTraceSpectralSum χ approx(h, ρ, n, z) a)
        H atTop right(max a 1) := by sorry

open Classical in
/-- Paper: §1.4.5, p. 30. Continuation from every positive half-width gives
holomorphy of the shifted logarithmic derivative throughout the right half-plane
except for the possible shifted pole in the trivial character.
Deviation: The regularizing term has the sign dictated by the corrected Euler
sum. Meromorphic continuation on the overlap is used before concluding
holomorphy of the pointwise logarithmic derivative away from the pole. -/
theorem introTrace_logDeriv_analytic_of_extensions (χ : U𝔽)
    (_h : ∀ a : ℝ, 0 < a → ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧
      EqOn H (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2) +
        if χ = 1 then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) right(max a 1)) :
    AnalyticOnNhd ℂ (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2))
      {z : ℂ | 0 < z.re ∧ (χ ≠ 1 ∨ z ≠ 1 / 2)} := by sorry

/-- Paper: §1.4.5, p. 30. A holomorphic shifted logarithmic derivative
excludes finite Hecke zeros to the right of one half. The exceptional point
for the trivial character is a pole of the finite L-function. -/
theorem introTrace_finiteL_no_right_zeros (χ : U𝔽)
    (_h : AnalyticOnNhd ℂ (fun z ↦ logDeriv finiteL(χ) (z + 1 / 2))
      {z : ℂ | 0 < z.re ∧ (χ ≠ 1 ∨ z ≠ 1 / 2)}) (s : ℂ) (_hs : 1 / 2 < s.re) :
    meromorphicOrderAt finiteL(χ) s ≤ 0 := by sorry

/-- Paper: §1.4.5, p. 30. Right-hand nonvanishing for the finite continuations
in the section-normalized characters implies right-hand nonvanishing for every
completed continuation. Imaginary norm twists translate the exponent, and the
gamma factors are regular and nonzero in the positive half-plane. -/
theorem introTrace_completedL_no_right_zeros (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F))
    (_h : ∀ (ψ : U𝔽), (∀ t, ψ (τ t) = 1) →
      ∀ s : ℂ, 1 / 2 < s.re → meromorphicOrderAt finiteL(ψ) s ≤ 0)
    (χ : U𝔽) (s : ℂ) (_hs : 1 / 2 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by sorry

/-- Paper: §1.4.5, p. 30. The completed functional equation reflects the
zero-free region for the inverse character to the left of one half for the
original character. -/
theorem introTrace_completedL_no_left_zeros (χ : U𝔽)
    (_h : ∀ s : ℂ, 1 / 2 < s.re → meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) s ≤ 0)
    (s : ℂ) (_hs : s.re < 1 / 2) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s ≤ 0 := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation χ
    (continuedCompletedHeckeL χ) (continuedCompletedHeckeL χ⁻¹)
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    (continuedCompletedHeckeL_spec χ⁻¹).1 (continuedCompletedHeckeL_spec χ⁻¹).2
  let r (z : ℂ) := 1 - z
  have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
  have e : continuedCompletedHeckeL χ⁻¹ ∘ r = fun z ↦ ε z * continuedCompletedHeckeL χ z :=
    funext he
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
    (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [e] at ho
  change meromorphicOrderAt (ε * continuedCompletedHeckeL χ) s = _ at ho
  rw [meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at ho
  exact ho.trans_le (_h (r s) (by change 1 / 2 < 1 - s.re; linarith))

end Limits

-- TODO(paper-gap): In §1.4.6, p. 30, continuity in the Bruhat test topology alone
-- cannot extend the identity from tests supported away from norm one. In the radial
-- log coordinate, first-derivative evaluation at zero annihilates every such test
-- but takes value one on x times a bump equal to one near zero. A bound in a weaker
-- topology, or control of the distributions supported at norm one, is needed.
-- Under GRH the full zero set of idelicExplicitFormula lies in every centered
-- open window of positive width, for all compactly supported Bruhat tests.
-- Section 1.4.2 fixes the profile as t^(-z) with midpoint value at t = 1.
-- For a convolution square the value at the identity is the squared L² norm.

section Boundary

local notation "outside(" χ ", " S ")" =>
  toMeromorphicNFOn (fun s ↦ reciprocalPartialHeckeEulerProduct χ S s * finiteL(χ) s) univ
local notation "outsideMass(" S ")" =>
  (∏ᶠ v : {v : V // v ∉ S},
    (((finiteLocalMultiplicativeTamagawaMeasure F v.val)
      (v.val.adicCompletionIntegers F).units).toReal : ℂ))

/-- Paper: §1.4.7, p. 30. Extension by the integer tests outside `S`
multiplies the local Mellin transform by the outside Euler product and
the product of the outside local integer-unit masses.
Section 1.1.4 (p. 12) defines the local character for χ unramified outside S.
Deviation: For the finite S in §1.4.7 retain the outside unit masses. If S contains
the different as on p. 25, their product is one. This is the meromorphic comparison in
`weilIdentity_unramifiedOutside_meromorphic`, with the normalized outside
Euler product of §6.3. The masses depend on the Haar convention. -/
theorem introTrace_transition_mellin (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    (fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s))
      =ᶠ[codiscrete ℂ] (fun s ↦
        outsideMass(S) * sLocalIdelicZFunction f (twist s) * heckeEulerProductOutside S χ hχ s) :=
  by
  let L := finiteL(χ)
  obtain ⟨hL, hs⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hraw := weilIdentity_unramifiedOutside_meromorphic (F := F) S f χ hχ L hL
    (fun z hz ↦ hs ⟨z, hz⟩)
  have hm : MeromorphicOn (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) univ :=
    fun z hz ↦ ((strongCoprimalityJetMatrix_det_ne_zero_euler χ S).1 z).meromorphicAt.mul
      (hL hz).meromorphicAt
  have he : (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z)
      =ᶠ[codiscrete ℂ] heckeEulerProductOutside S χ hχ := by
    rw [heckeEulerProductOutside_eq_finite S χ hχ L hL hs]
    simpa only [Filter.codiscrete] using toMeromorphicNFOn_eqOn_codiscrete hm
  filter_upwards [hraw, he] with z htrans heuler
  rw [htrans, ← heuler]
  simp only [reciprocalPartialHeckeEulerProduct, mul_assoc]

-- On theta classes this is the representative formula for sLocalThetaToGlobal_mk,
-- globalThetaMellin_mk and sLocalThetaMellin_mk from §§5.1–5.2.

/-- Paper: §1.4.7, pp. 30–31. The finite Hecke L-function has no zero on
the line of real part one.
Deviation: Meromorphic order allows the pole of a pure norm character on
this line. A normal-form point value at a pole would be zero in Lean. -/
theorem introTrace_finiteL_no_zeros_one_line (χ : U𝔽) (t : ℝ) :
    meromorphicOrderAt finiteL(χ) ⟨1, t⟩ ≤ 0 := by
  obtain ⟨A, hA, h⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, hzero⟩ := h F χ
  have hlog : 0 ≤ Real.log (B * (|t| + 3)) := Real.log_nonneg (by
    have hBt : 0 ≤ B * |t| := mul_nonneg (by linarith) (abs_nonneg t)
    nlinarith)
  apply hzero _ (finiteHeckeL_exists_continuation χ).choose_spec.1
    (finiteHeckeL_exists_continuation χ).choose_spec.2
  change 1 - A / ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|t| + 3))) ≤ 1
  exact sub_le_self _ (div_nonneg hA.le (mul_nonneg (by positivity) hlog))

/-- Paper: §1.4.7, pp. 30–31. The outside Euler product has no zero on the
line of real part one, so its reciprocal is holomorphic there.
Deviation: Multiplying by inverse local Euler factors creates no zeros
on this line. The reciprocal at a pole is interpreted in normal form. -/
theorem introTrace_outside_inv_analytic_one_line (χ : U𝔽) (S : Finset V) (t : ℝ) :
    AnalyticAt ℂ (fun s ↦ (outside(χ, S) s)⁻¹) ⟨1, t⟩ := by
  let L := finiteL(χ)
  let z : ℂ := ⟨1, t⟩
  obtain ⟨ha, hn⟩ := strongCoprimalityJetMatrix_det_ne_zero_euler χ S
  have hm : MeromorphicOn (fun w ↦ reciprocalPartialHeckeEulerProduct χ S w * L w) univ :=
    fun w hw ↦ (ha w).meromorphicAt.mul ((finiteHeckeL_exists_continuation χ).choose_spec.1 hw).meromorphicAt
  have hnf := meromorphicNFOn_toMeromorphicNFOn (fun w ↦ reciprocalPartialHeckeEulerProduct χ S w * L w) univ
  apply (hnf (mem_univ z)).inv.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_inv, meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z)]
  change 0 ≤ -meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ S * L) z
  rw [meromorphicOrderAt_mul_of_ne_zero (ha z) (hn z (by norm_num [z]))]
  have hle : meromorphicOrderAt L z ≤ 0 := introTrace_finiteL_no_zeros_one_line χ t
  cases he : meromorphicOrderAt L z with
  | top => simp [he] at hle
  | coe k =>
    rw [he] at hle
    have hk : k ≤ 0 := by exact_mod_cast hle
    exact_mod_cast neg_nonneg.mpr hk

/-- Paper: §1.4.7, p. 31. Multiplication by the reciprocal of the outside
Euler product undoes the transition multiplier as a meromorphic identity.
Deviation: The reciprocal includes the measure normalization. Cancellation
holds on punctured neighborhoods, including at poles on the boundary. -/
theorem introTrace_transition_mellin_inv (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (t : ℝ) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    (fun s ↦ (outsideMass(S) * heckeEulerProductOutside S χ hχ s)⁻¹ *
      globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s))
      =ᶠ[𝓝[≠] (⟨1, t⟩ : ℂ)] (fun s ↦ sLocalIdelicZFunction f (twist s)) := by sorry

/-- Paper: §1.4.7, p. 31. The continued product recovers the local Mellin value
on the boundary after normalization at its removable singularities.
Deviation: At a pole of the outside factor the two separate normal-form point
values give zero when multiplied. The product is normalized as a whole. -/
theorem introTrace_transition_mellin_inv_boundaryValue (S : Finset V) (χ : U𝔽)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (t : ℝ) :
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    toMeromorphicNFOn (fun s ↦ (outsideMass(S) * heckeEulerProductOutside S χ hχ s)⁻¹ *
      globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)) univ ⟨1, t⟩ =
        sLocalIdelicZFunction f (twist ⟨1, t⟩) := by sorry

-- The first and third growth inputs on p. 31 are already stated as
-- finiteHeckeL_continuation_isBigO_rpow and finiteHeckeL_inv_isBigO_oneLine.

/-- Paper: §1.4.7, p. 31. On both tails there are horizontal edges of
growing contour boxes on which the reciprocal finite L-function is regular,
nonzero, and polynomially bounded uniformly along the edge.
Deviation: The real parts range over the fixed width of the boxes in the
preceding sentence. The polynomial bounds concern large absolute heights. -/
theorem introTrace_finiteL_inv_horizontal_growth (χ : U𝔽) (a b : ℝ) (_hab : a < b) :
    ∃ (T : ℤ → ℝ) (C : ℝ) (m : ℕ), 0 < C ∧ Tendsto T atTop atTop ∧ Tendsto T atBot atBot ∧
      ∀ k : ℤ, ∀ σ ∈ Icc a b,
        meromorphicOrderAt finiteL(χ) ⟨σ, T k⟩ = 0 ∧
          ‖(finiteL(χ) ⟨σ, T k⟩)⁻¹‖ ≤ C * (1 + |T k|) ^ m := by sorry

end Boundary

-- Section 1.4.8, p. 31. The full multiplicity in the open strip and the capped
-- edge multiplicity are spectralStripMultiplicity_interior and
-- spectralStripMultiplicity_boundary. The strict test for jet k is 2*k + 1 < s,
-- by lt_spectralBoundaryMultiplicity and scalarIntervalSobolev_eval_boundary_iff.
-- TODO(paper-gap): §§1.4.8–1.4.9, p. 31. Continuity of the surviving evaluations
-- does not compare the fixed geometric distribution across widths. The missing
-- orbital comparison is recorded by traceFormula_exteriorZeros in Chapter 12.

/-- Paper: §1.4.5, p. 30. For every number field and every unitary character
of its idele class group, a zero of the continued completed Hecke L-function
in the open critical strip has real part one half. The paper gives no
numbered statement for this claim. Theorem 13.3.1.2 is a title. The deduction
below depends on the missing extension in §1.4.5.
Deviation: Positive meromorphic order expresses a zero of the continuation
and distinguishes zeros from poles. -/
theorem heckeL_zero_re_eq_half (χ : U𝔽) (s : ℂ) (_hs₀ : 0 < s.re) (_hs₁ : s.re < 1)
    (_hzero : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s) :
    s.re = 1 / 2 := by
  classical
  let q : (AdeleRing (𝓞 F) F)ˣ →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  have hr (ψ : U𝔽) (w : ℂ) (hw : 1 / 2 < w.re) :
      meromorphicOrderAt (continuedCompletedHeckeL ψ) w ≤ 0 := by
    refine introTrace_completedL_no_right_zeros τ hτ ?_ ψ w hw
    intro η hη
    refine introTrace_finiteL_no_right_zeros η (introTrace_logDeriv_analytic_of_extensions η ?_)
    intro a ha
    obtain ⟨h, ρ, H, hA, hH, hlim⟩ := introTrace_combined_limit_extension τ hτ η hη a ha
    exact ⟨H, hH, introTrace_logDeriv_extension_of_limit τ hτ η hη a ha h ρ hA H hH hlim⟩
  apply le_antisymm
  · exact le_of_not_gt fun h ↦ _hzero.not_ge (hr χ s h)
  · exact le_of_not_gt fun h ↦ _hzero.not_ge
      (introTrace_completedL_no_left_zeros χ (hr χ⁻¹) s h)

end RiemannMasullo
