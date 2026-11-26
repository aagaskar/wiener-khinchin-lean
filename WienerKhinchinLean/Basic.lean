module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

import WienerKhinchinLean.CharacteristicFunction
import WienerKhinchinLean.FourierCorrelation

/-!
# The Wiener–Khinchin theorem

A continuous-time wide-sense stationary process with continuous autocorrelation has
a unique finite spectral measure representing its autocorrelation.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexInnerProductSpace Topology

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

/-- A quadratic form built from autocorrelation is the expected squared magnitude of the
corresponding finite linear combination of process values. -/
theorem autocorrelation_sum_eq_integral_normSq (hX : IsWideSenseStationary X P)
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
  rw [hX.autocorrelation_sum_eq_integral_normSq indices t c, Complex.ofReal_re]
  exact integral_nonneg fun ω ↦ Complex.normSq_nonneg _

end IsWideSenseStationary

section ObservationWindow

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℂ} {P : Measure Ω}
  (hX : IsWideSenseStationary X P)

private noncomputable def processL2 (t : ℝ) : Lp ℂ 2 P :=
  (hX.square_integrable_at_all_t t).toLp (X t)

private theorem inner_processL2 (t s : ℝ) :
    ⟪processL2 hX s, processL2 hX t⟫ = hX.autocorrelation (t - s) := by
  change ⟪processL2 hX s, processL2 hX t⟫ = autocorrelation X P (t - s) 0
  rw [← hX.autocorrelation_depends_only_on_lag t s, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hX.square_integrable_at_all_t s).coeFn_toLp,
    (hX.square_integrable_at_all_t t).coeFn_toLp] with ω hs ht
  change ⟪processL2 hX s ω, processL2 hX t ω⟫ = _
  change processL2 hX s ω = _ at hs
  change processL2 hX t ω = _ at ht
  rw [hs, ht, RCLike.inner_apply]

private theorem norm_processL2_sq (t : ℝ) :
    ‖processL2 hX t‖ ^ 2 = (hX.autocorrelation 0).re := by
  have hInner := inner_processL2 hX t t
  rw [sub_self, inner_self_eq_norm_sq_to_K] at hInner
  change (↑‖processL2 hX t‖ : ℂ) ^ 2 = _ at hInner
  rw [← Complex.ofReal_pow] at hInner
  simpa only [Complex.ofReal_re] using congrArg Complex.re hInner

private theorem continuous_processL2 (hR : Continuous hX.autocorrelation) :
    Continuous (processL2 hX) := by
  refine continuous_iff_continuousAt.mpr fun s ↦ tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  -- The autocorrelation controls the L² distance between two process values.
  have hSq (t : ℝ) : ‖processL2 hX t - processL2 hX s‖ ^ 2 =
      2 * ((hX.autocorrelation 0).re - (hX.autocorrelation (s - t)).re) := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_processL2_sq, norm_processL2_sq, inner_processL2]
    change _ - 2 * (hX.autocorrelation (s - t)).re + _ = _
    ring
  have hContinuous : Continuous (fun t : ℝ ↦
      2 * ((hX.autocorrelation 0).re - (hX.autocorrelation (s - t)).re)) := by
    fun_prop
  have hSqZero : Tendsto (fun t ↦ ‖processL2 hX t - processL2 hX s‖ ^ 2) (𝓝 s) (𝓝 0) := by
    simpa only [hSq, sub_self, mul_zero] using (hContinuous.continuousAt (x := s)).tendsto
  have hSqrt : ContinuousAt Real.sqrt 0 := Real.continuous_sqrt.continuousAt
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    hSqrt.tendsto.comp hSqZero

private theorem memLp_window (hR : Continuous hX.autocorrelation) (T : ℝ) :
    MemLp ((Icc 0 T).indicator (processL2 hX)) 2 (volume : Measure ℝ) := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  let _ : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc 0 T)) := by
    exact ⟨by simp⟩
  refine MemLp.of_bound (continuous_processL2 hX hR).aestronglyMeasurable ‖processL2 hX 0‖
    (Eventually.of_forall fun t ↦ ?_)
  have h : ‖processL2 hX t‖ = ‖processL2 hX 0‖ := by
    have hSq := (norm_processL2_sq hX t).trans (norm_processL2_sq hX 0).symm
    simpa [Real.sqrt_sq (norm_nonneg _)] using congrArg Real.sqrt hSq
  exact h.le

private noncomputable def windowLp (hR : Continuous hX.autocorrelation) (T : ℝ) :
    Lp (Lp ℂ 2 P) 2 (volume : Measure ℝ) :=
  (memLp_window hX hR T).toLp _

private theorem charFun_window (hR : Continuous hX.autocorrelation)
    (T τ : ℝ) :
    charFun (WienerKhinchin.powerSpectrum (windowLp hX hR T)) (2 * Real.pi * τ) =
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
      have hCoe : windowLp hX hR T =ᵐ[volume] (Icc 0 T).indicator (processL2 hX) :=
        (memLp_window hX hR T).coeFn_toLp
      filter_upwards [hCoe, WienerKhinchin.coe_translate τ (windowLp hX hR T),
        (measurePreserving_add_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae_eq_comp
          hCoe] with t h₁ h₂ h₃
      change ⟪windowLp hX hR T t, WienerKhinchin.translate τ (windowLp hX hR T) t⟫ = _
      simp only [Function.comp_apply] at h₃
      rw [h₁, h₂, h₃]
      have htB : t ∈ B ↔ t ∈ Icc 0 T ∧ t + τ ∈ Icc 0 T := Iff.rfl
      by_cases ht : t ∈ Icc 0 T <;> by_cases hs : t + τ ∈ Icc 0 T <;>
        simp only [indicator_apply, htB, ht, hs, true_and, false_and, ite_true, ite_false,
          inner_zero_left, inner_zero_right, inner_processL2, add_sub_cancel_left]
    _ = _ := by
      rw [hB, integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def,
        Real.volume_Icc, hOverlap, ENNReal.toReal_ofReal', max_comm (T - |τ|) 0,
        Algebra.smul_def]
      rfl

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
    let approx (n : ℕ) := WienerKhinchin.powerSpectrum (windowLp hX hR (width n))
    have hApprox (n : ℕ) (τ : ℝ) :
        charFun (approx n) (2 * Real.pi * τ) =
          (↑(max 0 (width n - |τ|)) : ℂ) * hX.autocorrelation τ :=
      charFun_window hX hR (width n) τ
    have hApproxMass (n : ℕ) : (approx n).real univ = width n * mass := by
      simpa only [mul_zero, charFun_zero, abs_zero, sub_zero, max_eq_right (hWidth n).le,
        hAutoZero, ← Complex.ofReal_mul, Complex.ofReal_re] using
        congrArg Complex.re (hApprox n 0)
    -- The window length and the second moment account for all of the spectral mass.
    let μ (n : ℕ) : ProbabilityMeasure ℝ :=
      ⟨ENNReal.ofReal (width n * mass)⁻¹ • approx n, isProbabilityMeasure_iff_real.mpr (by
        rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (by positivity),
          hApproxMass, inv_mul_cancel₀ (mul_pos (hWidth n) hMassPos).ne'])⟩
    have hπ : 2 * Real.pi ≠ 0 := by positivity
    have hμ (u : ℝ) :
        Tendsto (fun n ↦ charFun (μ n : Measure ℝ) u) atTop (𝓝 (normalized u)) := by
      let τ := u / (2 * Real.pi)
      have hu : 2 * Real.pi * τ = u := by
        dsimp only [τ]
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hπ]
      have hChar (n : ℕ) : charFun (μ n : Measure ℝ) u =
          (↑(max 0 (1 - |τ| / width n)) : ℂ) * normalized u := by
        change charFun (ENNReal.ofReal (width n * mass)⁻¹ • approx n) u = _
        have hInv : 0 ≤ (width n * mass)⁻¹ := inv_nonneg.mpr (mul_pos (hWidth n) hMassPos).le
        have hWeight : max 0 (width n - |τ|) = width n * max 0 (1 - |τ| / width n) := by
          rw [mul_max_of_nonneg _ _ (hWidth n).le, mul_zero, mul_sub, mul_one,
            ← mul_div_assoc, mul_div_cancel_left₀ _ (hWidth n).ne']
        rw [charFun_smul_ofReal _ hInv, ← hu, hApprox, hWeight]
        have hWidthC : (width n : ℂ) ≠ 0 := by exact_mod_cast (hWidth n).ne'
        have hMassC : (mass : ℂ) ≠ 0 := by exact_mod_cast hMassZero
        simp only [normalized, hu, Complex.ofReal_inv, Complex.ofReal_mul]
        field_simp
        rfl
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
    (X : ℝ → Ω → ℂ) (P : Measure Ω) [IsProbabilityMeasure P]
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
  