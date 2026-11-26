module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Spectral measures for signals in L²

Plancherel identifies the autocorrelation of an L² signal with the characteristic
function of its squared Fourier magnitude.
-/

@[expose] public section

open FourierTransform MeasureTheory
open scoped ComplexInnerProductSpace ENNReal FourierTransform SchwartzMap

namespace WienerKhinchin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Translation by adding `τ` to the argument of an L² signal. -/
noncomputable def translate (τ : ℝ) :
    Lp H 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp H 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (· + τ) (measurePreserving_add_right volume τ)

theorem coe_translate (τ : ℝ) (f : Lp H 2 (volume : Measure ℝ)) :
    translate τ f =ᵐ[volume] fun x ↦ f (x + τ) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume τ)

private noncomputable def phase (τ ξ : ℝ) : ℂ :=
  Real.fourierChar (τ * ξ)

private theorem memLp_phase_smul (τ : ℝ) (f : Lp H 2 (volume : Measure ℝ)) :
    MemLp (fun ξ ↦ phase τ ξ • f ξ) 2 volume := by
  have hPhase : MemLp (phase τ) ∞ volume :=
    memLp_top_of_bound (by unfold phase; fun_prop) 1
      (Filter.Eventually.of_forall fun ξ ↦ by simp [phase])
  exact hPhase.smul (Lp.memLp f)

private noncomputable def modulate (τ : ℝ) (f : Lp H 2 (volume : Measure ℝ)) :
    Lp H 2 (volume : Measure ℝ) :=
  (memLp_phase_smul τ f).toLp _

private theorem coe_modulate (τ : ℝ) (f : Lp H 2 (volume : Measure ℝ)) :
    modulate τ f =ᵐ[volume] fun ξ ↦ phase τ ξ • f ξ :=
  (memLp_phase_smul τ f).coeFn_toLp

private theorem isometry_modulate (τ : ℝ) :
    Isometry (modulate τ : Lp H 2 (volume : Measure ℝ) → _) := by
  refine Isometry.of_dist_eq fun f g ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  apply Lp.norm_eq_norm_of_ae_eq
  filter_upwards [Lp.coeFn_sub (modulate τ f) (modulate τ g), Lp.coeFn_sub f g,
    coe_modulate τ f, coe_modulate τ g] with ξ h₁ h₂ hf hg
  rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply, hf, hg, ← smul_sub, norm_smul]
  simp [phase]

variable [CompleteSpace H]

private theorem fourier_translate (τ : ℝ) (f : Lp H 2 (volume : Measure ℝ)) :
    𝓕 (translate τ f) = modulate τ (𝓕 f) := by
  refine DenseRange.induction_on (p := fun f : Lp H 2 (volume : Measure ℝ) ↦
      𝓕 (translate τ f) = modulate τ (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f ?_ ?_
  · exact isClosed_eq (continuous_fourier.comp (translate τ).continuous)
      ((isometry_modulate τ).continuous.comp continuous_fourier)
  · intro g
    change 𝓕 (translate τ (g.toLp 2)) = modulate τ (𝓕 (g.toLp 2))
    have hTranslate : translate τ (g.toLp 2) = (g.compSubConstCLM ℂ (-τ)).toLp 2 := by
      apply Lp.ext
      filter_upwards [coe_translate τ (g.toLp 2),
        (measurePreserving_add_right (volume : Measure ℝ) τ).quasiMeasurePreserving.ae_eq_comp
          (g.coeFn_toLp 2), (g.compSubConstCLM ℂ (-τ)).coeFn_toLp 2] with ξ h₁ h₂ h₃
      rw [h₁, h₃, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
      exact h₂
    rw [hTranslate, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [(𝓕 (g.compSubConstCLM ℂ (-τ))).coeFn_toLp 2,
      coe_modulate τ ((𝓕 g).toLp 2), (𝓕 g).coeFn_toLp 2] with ξ h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    simp_rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
    simpa only [Fourier.fourierIntegral_def, Function.comp_apply,
      SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, phase, Circle.smul_def]
      using congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume
        (g : ℝ → H) τ) ξ

/-- The measure with density equal to the squared Fourier magnitude of an L² signal. -/
noncomputable def powerSpectrum (f : Lp H 2 (volume : Measure ℝ)) : Measure ℝ :=
  volume.withDensity fun ξ ↦ ENNReal.ofReal (‖(𝓕 f) ξ‖ ^ 2)

instance (f : Lp H 2 (volume : Measure ℝ)) : IsFiniteMeasure (powerSpectrum f) :=
  isFiniteMeasure_withDensity_ofReal (Lp.memLp (𝓕 f)).norm.integrable_sq.hasFiniteIntegral

/-- The characteristic function of the power spectrum is the L² autocorrelation. -/
theorem charFun_powerSpectrum (f : Lp H 2 (volume : Measure ℝ)) (τ : ℝ) :
    charFun (powerSpectrum f) (2 * Real.pi * τ) = ⟪f, translate τ f⟫ := by
  rw [← Lp.inner_fourier_eq, fourier_translate, L2.inner_def, charFun_apply_real, powerSpectrum]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((Lp.memLp (𝓕 f)).norm.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [coe_modulate τ (𝓕 f)] with ξ hξ
  rw [hξ, inner_smul_right, inner_self_eq_norm_sq_to_K, ENNReal.toReal_ofReal (sq_nonneg _),
    Algebra.smul_def, phase, Real.fourierChar_apply, mul_comm]
  simp [mul_assoc]

end WienerKhinchin
