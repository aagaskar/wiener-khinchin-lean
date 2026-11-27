module

public import WienerKhinchinLean.FourierCorrelation

import WienerKhinchinLean.CharacteristicFunction

/-!
# The Wiener–Khinchin theorem

A continuous-time wide-sense stationary process with continuous autocorrelation has
a unique finite spectral measure representing its autocorrelation.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexInnerProductSpace FourierTransform Topology

/-- The uncentered autocorrelation between the process values at times `t` and `s`. -/
noncomputable def autocorrelation {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ → Ω → ℂ) (P : Measure Ω) (t s : ℝ) : ℂ :=
  ∫ ω, X t ω * conj (X s ω) ∂P

/-- Wide-sense stationarity means square-integrability at every time, a constant mean,
and an autocorrelation that depends only on the time difference `t - s`. -/
structure IsWideSenseStationary {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ → Ω → ℂ) (P : Measure Ω) : Prop where
  square_integrable_at_all_t : ∀ t, MemLp (X t) 2 P
  has_constant_mean : ∀ t, (∫ ω, X t ω ∂P) = ∫ ω, X 0 ω ∂P
  autocorrelation_depends_only_on_lag : ∀ t s,
    autocorrelation X P t s = autocorrelation X P (t - s) 0

/-- The lag autocorrelation of a wide-sense stationary process, using time zero as reference. -/
noncomputable def IsWideSenseStationary.autocorrelation {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ → Ω → ℂ} {P : Measure Ω} (_hX : IsWideSenseStationary X P) (τ : ℝ) : ℂ :=
  _root_.autocorrelation X P τ 0

namespace IsWideSenseStationary

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℂ} {P : Measure Ω}

/-- The autocorrelation quadratic form equals the integral of the squared magnitude of the
corresponding finite linear combination of process values. I.e., if we define
 \(Y=\sum_j c_jX(t_j)\), then
\[
\sum_{j,k} c_j\,\overline{c_k}\,r(t_j-t_k)
= \mathbb E_P[|Y|^2].
\]
-/
theorem autocorrelation_quadratic_form_eq_integral_normSq (hX : IsWideSenseStationary X P)
    {ι : Type*} (indices : Finset ι) (t : ι → ℝ) (c : ι → ℂ) :
    ∑ j ∈ indices, ∑ k ∈ indices, c j * conj (c k) * hX.autocorrelation (t j - t k) =
      ((∫ ω, Complex.normSq (∑ j ∈ indices, c j * X (t j) ω) ∂P : ℝ) : ℂ) := by
  have hInt (j k : ι) :
      Integrable (fun ω ↦ (c j * X (t j) ω) * conj (c k * X (t k) ω)) P :=
    ((hX.square_integrable_at_all_t (t j)).const_mul (c j)).integrable_mul
      ((hX.square_integrable_at_all_t (t k)).const_mul (c k)).star
  rw [← integral_complex_ofReal]
  simp_rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  rw [integral_finsetSum indices (fun j _ ↦ integrable_finsetSum indices (fun k _ ↦ hInt j k))]
  have hSum (j : ι) :
      (∫ ω, ∑ k ∈ indices, (c j * X (t j) ω) * conj (c k * X (t k) ω) ∂P) =
        ∑ k ∈ indices, ∫ ω, (c j * X (t j) ω) * conj (c k * X (t k) ω) ∂P :=
    integral_finsetSum indices (fun k _ ↦ hInt j k)
  simp_rw [hSum]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  change c j * conj (c k) * _root_.autocorrelation X P (t j - t k) 0 = _
  rw [← hX.autocorrelation_depends_only_on_lag (t j) (t k)]
  unfold _root_.autocorrelation
  rw [← integral_const_mul]
  congr 1
  funext ω
  rw [map_mul]
  ring

/-- The lag autocorrelation is positive definite. -/
theorem autocorrelation_positive_definite (hX : IsWideSenseStationary X P)
    {ι : Type*} (indices : Finset ι) (t : ι → ℝ) (c : ι → ℂ) :
    0 ≤ (∑ j ∈ indices, ∑ k ∈ indices,
      c j * conj (c k) * hX.autocorrelation (t j - t k)).re := by
  rw [hX.autocorrelation_quadratic_form_eq_integral_normSq indices t c, Complex.ofReal_re]
  exact integral_nonneg fun ω ↦ Complex.normSq_nonneg _

end IsWideSenseStationary

section ObservationWindow

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℂ} {P : Measure Ω}

/-- `processAtTime hX t` views the random variable `X t` as an element of
`Lp ℂ 2 P`, using the square-integrability proof from `hX`. -/
private noncomputable def processAtTime (hX : IsWideSenseStationary X P) (t : ℝ) : Lp ℂ 2 P :=
  (hX.square_integrable_at_all_t t).toLp (X t)

/-- \(\mathbb E_P[\overline{X(s)}X(t)]\) equals the autocorrelation
at lag `t - s`. -/
private theorem inner_product_eq_autocorrelation (hX : IsWideSenseStationary X P) (t s : ℝ) :
    ⟪processAtTime hX s, processAtTime hX t⟫ = hX.autocorrelation (t - s) := by
  change ⟪processAtTime hX s, processAtTime hX t⟫ = autocorrelation X P (t - s) 0
  rw [← hX.autocorrelation_depends_only_on_lag t s, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hX.square_integrable_at_all_t s).coeFn_toLp,
    (hX.square_integrable_at_all_t t).coeFn_toLp] with ω hs ht
  change ⟪processAtTime hX s ω, processAtTime hX t ω⟫ = _
  change processAtTime hX s ω = _ at hs
  change processAtTime hX t ω = _ at ht
  rw [hs, ht, RCLike.inner_apply]

private theorem norm_sq_eq_autocorrelation_zero (hX : IsWideSenseStationary X P) (t : ℝ) :
    ‖processAtTime hX t‖ ^ 2 = (hX.autocorrelation 0).re := by
  have hInner := inner_product_eq_autocorrelation hX t t
  rw [sub_self, inner_self_eq_norm_sq_to_K] at hInner
  change (↑‖processAtTime hX t‖ : ℂ) ^ 2 = _ at hInner
  rw [← Complex.ofReal_pow] at hInner
  simpa only [Complex.ofReal_re] using congrArg Complex.re hInner

private theorem continuous_processAtTime (hX : IsWideSenseStationary X P)
    (hR : Continuous hX.autocorrelation) :
    Continuous (processAtTime hX) := by
  refine continuous_iff_continuousAt.mpr fun s ↦ tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  -- The autocorrelation controls the L² distance between two process values.
  have hSq (t : ℝ) : ‖processAtTime hX t - processAtTime hX s‖ ^ 2 =
      2 * ((hX.autocorrelation 0).re - (hX.autocorrelation (s - t)).re) := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_sq_eq_autocorrelation_zero, norm_sq_eq_autocorrelation_zero,
      inner_product_eq_autocorrelation]
    change _ - 2 * (hX.autocorrelation (s - t)).re + _ = _
    ring
  have hContinuous : Continuous (fun t : ℝ ↦
      2 * ((hX.autocorrelation 0).re - (hX.autocorrelation (s - t)).re)) := by
    fun_prop
  have hSqZero : Tendsto (fun t ↦ ‖processAtTime hX t - processAtTime hX s‖ ^ 2) (𝓝 s) (𝓝 0) := by
    simpa only [hSq, sub_self, mul_zero] using (hContinuous.continuousAt (x := s)).tendsto
  have hSqrt : ContinuousAt Real.sqrt 0 := Real.continuous_sqrt.continuousAt
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    hSqrt.tendsto.comp hSqZero

private theorem windowed_process_square_integrable_in_time (hX : IsWideSenseStationary X P)
    (hR : Continuous hX.autocorrelation) (T : ℝ) :
    MemLp ((Icc 0 T).indicator (processAtTime hX)) 2 (volume : Measure ℝ) := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  let _ : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc 0 T)) := by
    exact ⟨by simp⟩
  refine MemLp.of_bound (continuous_processAtTime hX hR).aestronglyMeasurable ‖processAtTime hX 0‖
    (Eventually.of_forall fun t ↦ ?_)
  have h : ‖processAtTime hX t‖ = ‖processAtTime hX 0‖ := by
    have hSq := (norm_sq_eq_autocorrelation_zero hX t).trans
      (norm_sq_eq_autocorrelation_zero hX 0).symm
    simpa [Real.sqrt_sq (norm_nonneg _)] using congrArg Real.sqrt hSq
  exact h.le

/-- The process restricted to `[0, T]` and set to zero outside, viewed in L² over time. -/
@[no_expose] noncomputable def IsWideSenseStationary.windowedProcess
    (hX : IsWideSenseStationary X P) (hR : Continuous hX.autocorrelation) (T : ℝ) :
    Lp (Lp ℂ 2 P) 2 (volume : Measure ℝ) :=
  (windowed_process_square_integrable_in_time hX hR T).toLp _

/-- The expected periodogram at frequency `ξ` for an observation window of positive length `T`.
It is the squared L² norm of the Fourier transform of the windowed process, divided by `T`.
The Fourier transform is an L² element, so its representative specifies the density
almost everywhere. -/
noncomputable def IsWideSenseStationary.periodogram
    (hX : IsWideSenseStationary X P) (hR : Continuous hX.autocorrelation) (T ξ : ℝ) : ℝ :=
  ‖(𝓕 (hX.windowedProcess hR T)) ξ‖ ^ 2 / T

/-- The measure with density given by the expected periodogram. -/
noncomputable def IsWideSenseStationary.periodogramMeasure
    (hX : IsWideSenseStationary X P) (hR : Continuous hX.autocorrelation) (T : ℝ) : Measure ℝ :=
  volume.withDensity (fun ξ ↦ ENNReal.ofReal (hX.periodogram hR T ξ))

private theorem periodogramMeasure_eq_inv_smul_powerSpectrum (hX : IsWideSenseStationary X P)
    (hR : Continuous hX.autocorrelation) (T : ℝ) :
    hX.periodogramMeasure hR T =
      ENNReal.ofReal T⁻¹ • WienerKhinchin.powerSpectrum (hX.windowedProcess hR T) := by
  rw [IsWideSenseStationary.periodogramMeasure, WienerKhinchin.powerSpectrum,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext ξ
  rw [Pi.smul_apply, smul_eq_mul, IsWideSenseStationary.periodogram, div_eq_inv_mul,
    ENNReal.ofReal_mul' (sq_nonneg _)]

instance (hX : IsWideSenseStationary X P) (hR : Continuous hX.autocorrelation) (T : ℝ) :
    IsFiniteMeasure (hX.periodogramMeasure hR T) := by
  rw [periodogramMeasure_eq_inv_smul_powerSpectrum]
  exact (WienerKhinchin.powerSpectrum (hX.windowedProcess hR T)).smul_finite ENNReal.ofReal_ne_top

private theorem charFun_window (hX : IsWideSenseStationary X P)
    (hR : Continuous hX.autocorrelation) (T τ : ℝ) :
    charFun (WienerKhinchin.powerSpectrum (hX.windowedProcess hR T)) (2 * Real.pi * τ) =
      (↑(max 0 (T - |τ|)) : ℂ) * hX.autocorrelation τ := by
  let B : Set ℝ := {t | t ∈ Icc 0 T ∧ t + τ ∈ Icc 0 T}
  have hB : B = Icc (max 0 (-τ)) (min T (T - τ)) := by
    ext t
    simp only [B, mem_ofPred_eq, mem_Icc, max_le_iff, le_min_iff]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hOverlap :
      min T (T - τ) - max 0 (-τ) = T - |τ| := by
    rcases le_total 0 τ with hτ | hτ
    · rw [abs_of_nonneg hτ, min_eq_right (by linarith), max_eq_left (by linarith), sub_zero]
    · rw [abs_of_nonpos hτ, min_eq_left (by linarith), max_eq_right (by linarith)]
  rw [WienerKhinchin.charFun_powerSpectrum, L2.inner_def]
  calc
    _ = ∫ t, B.indicator (fun _ ↦ hX.autocorrelation τ) t := by
      apply integral_congr_ae
      have hCoe : hX.windowedProcess hR T =ᵐ[volume] (Icc 0 T).indicator (processAtTime hX) :=
        (windowed_process_square_integrable_in_time hX hR T).coeFn_toLp
      filter_upwards [hCoe, WienerKhinchin.coe_translate τ (hX.windowedProcess hR T),
        (measurePreserving_add_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae_eq_comp
          hCoe] with t h₁ h₂ h₃
      change ⟪hX.windowedProcess hR T t, WienerKhinchin.translate τ (hX.windowedProcess hR T) t⟫ = _
      simp only [Function.comp_apply] at h₃
      rw [h₁, h₂, h₃]
      have htB : t ∈ B ↔ t ∈ Icc 0 T ∧ t + τ ∈ Icc 0 T := Iff.rfl
      by_cases ht : t ∈ Icc 0 T <;> by_cases hs : t + τ ∈ Icc 0 T <;>
        simp only [indicator_apply, htB, ht, hs, true_and, false_and, ite_true, ite_false,
          inner_zero_left, inner_zero_right, inner_product_eq_autocorrelation, add_sub_cancel_left]
    _ = _ := by
      rw [hB, integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def,
        Real.volume_Icc, hOverlap, ENNReal.toReal_ofReal', max_comm (T - |τ|) 0,
        Algebra.smul_def]
      rfl

/-- The characteristic function of the periodogram measure equals the autocorrelation
weighted by the fraction of the window that overlaps its translate. -/
theorem IsWideSenseStationary.charFun_periodogramMeasure
    (hX : IsWideSenseStationary X P) (hR : Continuous hX.autocorrelation)
    {T : ℝ} (hT : 0 < T) (τ : ℝ) :
    charFun (hX.periodogramMeasure hR T) (2 * Real.pi * τ) =
      (↑(max 0 (1 - |τ| / T)) : ℂ) * hX.autocorrelation τ := by
  have hWeight : max 0 (T - |τ|) = T * max 0 (1 - |τ| / T) := by
    rw [mul_max_of_nonneg _ _ hT.le, mul_zero, mul_sub, mul_one, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hT.ne']
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [periodogramMeasure_eq_inv_smul_powerSpectrum, charFun_smul_ofReal _ (inv_nonneg.mpr hT.le),
    charFun_window, hWeight, Complex.ofReal_inv, Complex.ofReal_mul, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ hTC, one_mul]

end ObservationWindow

private theorem exists_spectral_measure {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ → Ω → ℂ} {P : Measure Ω} (hX : IsWideSenseStationary X P)
    (hR : Continuous hX.autocorrelation) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ τ, hX.autocorrelation τ = charFun ν (2 * Real.pi * τ) := by
  let mass : ℝ := ∫ ω, Complex.normSq (X 0 ω) ∂P
  have hAutoZero : hX.autocorrelation 0 = (mass : ℂ) := by
    change (∫ ω, X 0 ω * conj (X 0 ω) ∂P) = _
    simp_rw [Complex.mul_conj, integral_complex_ofReal]
    rfl
  have hMassNonneg : 0 ≤ mass := by
    simpa [hAutoZero] using
      hX.autocorrelation_positive_definite ({()} : Finset Unit) (fun _ ↦ 0) (fun _ ↦ 1)
  by_cases hMassZero : mass = 0
  · have hInt : Integrable (fun ω ↦ Complex.normSq (X 0 ω)) P := by
      simpa only [Complex.normSq_eq_norm_sq] using
        (hX.square_integrable_at_all_t 0).norm.integrable_sq
    have hNormSqZero :=
      (integral_eq_zero_iff_of_nonneg (fun ω ↦ Complex.normSq_nonneg (X 0 ω)) hInt).mp
        hMassZero
    refine ⟨0, inferInstance, fun τ ↦ ?_⟩
    rw [charFun_zero_measure]
    change (∫ ω, X τ ω * conj (X 0 ω) ∂P) = 0
    calc
      (∫ ω, X τ ω * conj (X 0 ω) ∂P) = ∫ _ : Ω, (0 : ℂ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hNormSqZero] with ω hω
        have h : X 0 ω = 0 := Complex.normSq_eq_zero.mp hω
        simp [h]
      _ = 0 := integral_zero Ω ℂ
  · let normalized (u : ℝ) := hX.autocorrelation (u / (2 * Real.pi)) / (mass : ℂ)
    have hContinuous : Continuous normalized :=
      (hR.comp (continuous_id.div_const _)).div_const _
    have hMassPos : 0 < mass := lt_of_le_of_ne hMassNonneg (fun h ↦ hMassZero h.symm)
    let width (n : ℕ) : ℝ := (n : ℝ) + 1
    have hWidth (n : ℕ) : 0 < width n := by dsimp [width]; positivity
    let approx (n : ℕ) := hX.periodogramMeasure hR (width n)
    have hApprox (n : ℕ) (τ : ℝ) :
        charFun (approx n) (2 * Real.pi * τ) =
          (↑(max 0 (1 - |τ| / width n)) : ℂ) * hX.autocorrelation τ :=
      hX.charFun_periodogramMeasure hR (hWidth n) τ
    have hApproxMass (n : ℕ) : (approx n).real univ = mass := by
      simpa only [mul_zero, charFun_zero, abs_zero, zero_div, sub_zero,
        max_eq_right zero_le_one, Complex.ofReal_one, one_mul, hAutoZero, Complex.ofReal_re] using
        congrArg Complex.re (hApprox n 0)
    -- Dividing by the second moment turns the periodogram measure into a probability measure.
    let μ (n : ℕ) : ProbabilityMeasure ℝ :=
      ⟨ENNReal.ofReal mass⁻¹ • approx n, isProbabilityMeasure_iff_real.mpr (by
        rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (inv_nonneg.mpr hMassNonneg),
          hApproxMass, inv_mul_cancel₀ hMassPos.ne'])⟩
    have hπ : 2 * Real.pi ≠ 0 := by positivity
    have hμ (u : ℝ) :
        Tendsto (fun n ↦ charFun (μ n : Measure ℝ) u) atTop (𝓝 (normalized u)) := by
      let τ := u / (2 * Real.pi)
      have hu : 2 * Real.pi * τ = u := by
        dsimp only [τ]
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hπ]
      have hChar (n : ℕ) : charFun (μ n : Measure ℝ) u =
          (↑(max 0 (1 - |τ| / width n)) : ℂ) * normalized u := by
        change charFun (ENNReal.ofReal mass⁻¹ • approx n) u = _
        rw [charFun_smul_ofReal _ (inv_nonneg.mpr hMassNonneg), ← hu, hApprox]
        simp only [normalized, hu, Complex.ofReal_inv, div_eq_mul_inv]
        change _ * (_ * hX.autocorrelation τ) = _ * (hX.autocorrelation τ * _)
        ring
      have hSmall : Tendsto (fun n ↦ |τ| / width n) atTop (𝓝 0) := by
        simpa only [width, div_eq_mul_inv, one_mul, mul_zero] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |τ|
      have hWeight : Tendsto (fun n : ℕ ↦ max 0 (1 - |τ| / width n)) atTop (𝓝 1) := by
        simpa only [sub_zero, max_eq_right zero_le_one] using
          (tendsto_const_nhds (x := (0 : ℝ))).max
            ((tendsto_const_nhds (x := (1 : ℝ))).sub hSmall)
      simpa only [hChar, Function.comp_def, Complex.ofReal_one, one_mul] using
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hWeight).mul_const (normalized u)
    obtain ⟨ν, hν⟩ :=
      exists_probabilityMeasure_of_tendsto_charFun μ hContinuous.continuousAt hμ
    refine ⟨ENNReal.ofReal mass • (ν : Measure ℝ),
      (ν : Measure ℝ).smul_finite ENNReal.ofReal_ne_top, fun τ ↦ ?_⟩
    rw [charFun_smul_ofReal _ hMassNonneg, hν]
    dsimp only [normalized]
    rw [mul_div_cancel_left₀ τ hπ, mul_comm, div_mul_cancel₀ _ (by exact_mod_cast hMassZero)]

universe u

/-- The spectral-measure statement of the Wiener–Khinchin theorem for continuous time.
The factor `2 * Real.pi` expresses frequencies in cycles per unit time. -/
def WienerKhinchin : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    {X : ℝ → Ω → ℂ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : IsWideSenseStationary X P), (hR : Continuous hX.autocorrelation) →
    ∃! ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ τ, hX.autocorrelation τ = charFun ν (2 * Real.pi * τ)

/-- The continuous-time Wiener–Khinchin theorem. -/
theorem wiener_khinchin : WienerKhinchin.{u} := by
  intro Ω _ X P _ hX hR
  obtain ⟨ν, hν, hν_spec⟩ := exists_spectral_measure hX hR
  refine ⟨ν, ⟨hν, hν_spec⟩, ?_⟩
  rintro μ ⟨hμ, hμ_spec⟩
  let _ := hν
  let _ := hμ
  apply Measure.ext_of_charFun
  funext u
  have hu : 2 * Real.pi * (u / (2 * Real.pi)) = u := by
    field_simp [Real.pi_ne_zero]
  rw [← hu, ← hμ_spec, hν_spec]
