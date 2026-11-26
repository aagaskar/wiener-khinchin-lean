module

public import Mathlib.MeasureTheory.Measure.LevyConvergence

import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Limits of characteristic functions

A pointwise limit of characteristic functions of probability measures is itself a
characteristic function if the limit is continuous at zero.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

/-- Scaling a measure by a nonnegative real scales its characteristic function. -/
theorem charFun_smul_ofReal (μ : Measure ℝ) {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    charFun (ENNReal.ofReal r • μ) u = (r : ℂ) * charFun μ u := by
  rw [charFun_apply_real, charFun_apply_real, integral_smul_measure, ENNReal.toReal_ofReal hr]
  exact Algebra.smul_def _ _

/-- Tightness and compactness give a probability measure representing the pointwise limit. -/
theorem exists_probabilityMeasure_of_tendsto_charFun (μ : ℕ → ProbabilityMeasure ℝ)
    {f : ℝ → ℂ} (hf : ContinuousAt f 0)
    (hμ : ∀ t, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) atTop (𝓝 (f t))) :
    ∃ ν : ProbabilityMeasure ℝ, ∀ t, charFun (ν : Measure ℝ) t = f t := by
  have hTight := isTightMeasureSet_of_tendsto_charFun hf hμ
  have hCompact : IsCompact (closure (range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by simpa [Set.range] using hTight)
  let U := hyperfilter ℕ
  obtain ⟨ν, -, hν : Tendsto μ U (𝓝 ν)⟩ :=
    hCompact.ultrafilter_le_nhds (U.map μ)
      ((by simp : (U.map μ).toFilter ≤ 𝓟 (range μ)).trans
        (monotone_principal subset_closure))
  refine ⟨ν, fun t ↦ ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at hν
  have ht := hν (BoundedContinuousFunction.innerProbChar t)
  simp_rw [← charFun_eq_integral_innerProbChar] at ht
  exact tendsto_nhds_unique ht ((hμ t).mono_left Nat.hyperfilter_le_atTop)
