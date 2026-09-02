/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Zeta.Proportion
public import ZetaZeros.Zeta.Transfer
public import ZetaZeros.Numeric.MontgomeryTaylor

/-!
# Proportion bounds for zeta zeros

This combines the kernel construction, the finite-set bounds transferred to zeta zeros, and the
Riemann--von Mangoldt asymptotic to obtain the two asymptotic proportion bounds.
-/

@[expose] public section

namespace ZetaZeros

open Filter Topology

private lemma nontrivialZeros_nonempty_of_zeroCount_pos {T : ℝ}
    (h : 0 < (zeroCount T : ℝ)) : (nontrivialZeros T).Nonempty := by
  by_contra hne
  have hz : nontrivialZeros T = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  rw [zeroCount, hz] at h
  simp at h

@[zz_tag "thm_simple"]
theorem simple_proportion_lower
    (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (hMT : MontgomeryTaylor) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  obtain ⟨eta, C, heta, hC, hsum⟩ := kernelConstruction hPC hMT (ε / 2) (by positivity)
  have hNscale := hRvM.tendsto
  have hscale : ∀ᶠ T : ℝ in atTop, zeroScale T ≠ 0 :=
    zeroScale_pos_eventually.mono fun _ h => ne_of_gt h
  have hratio : Tendsto
      (fun T => (unweightedKernelSum eta T).re / (zeroCount T : ℝ))
      atTop (nhds C) :=
    tendsto_ratio_of_tendsto_div_scale _ _ _ _ hNscale hsum hscale
  have hNpos := hRvM.zeroCount_pos_eventually
  have hbound : ∀ᶠ T : ℝ in atTop,
      2 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re ≤
        (simpleOnLineCount T : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hNpos] with T hT hNT
    exact simpleOnLineCount_lower hT (nontrivialZeros_nonempty_of_zeroCount_pos hNT) heta
  have hprop := eventually_simple_proportion
    (fun T => (zeroCount T : ℝ)) (fun T => (simpleOnLineCount T : ℝ))
    (fun T => (unweightedKernelSum eta T).re) C (ε / 2) (by positivity)
    hNpos hratio hbound
  have hconst :
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        2 - C - ε / 2 := by
    rw [show 3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) =
      2 - montgomeryTaylorConst by
        rw [montgomeryTaylorConst]
        ring]
    rw [abs_lt] at hC
    linarith
  have hfinal : ∀ᶠ T : ℝ in atTop,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
    hprop.mono fun T hT => hconst.trans hT
  exact eventually_atTop.1 hfinal

@[zz_tag "thm_distinct"]
theorem distinct_proportion_lower
    (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (hMT : MontgomeryTaylor) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) := by
  obtain ⟨eta, C, heta, hC, hsum⟩ := kernelConstruction hPC hMT (ε / 2) (by positivity)
  have hNscale := hRvM.tendsto
  have hscale : ∀ᶠ T : ℝ in atTop, zeroScale T ≠ 0 :=
    zeroScale_pos_eventually.mono fun _ h => ne_of_gt h
  have hratio : Tendsto
      (fun T => (unweightedKernelSum eta T).re / (zeroCount T : ℝ))
      atTop (nhds C) :=
    tendsto_ratio_of_tendsto_div_scale _ _ _ _ hNscale hsum hscale
  have hNpos := hRvM.zeroCount_pos_eventually
  have hbound : ∀ᶠ T : ℝ in atTop,
      (3 / 2 : ℝ) * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re / 2 ≤
        (distinctZeroCount T : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hNpos] with T hT hNT
    exact distinctZeroCount_lower hT (nontrivialZeros_nonempty_of_zeroCount_pos hNT) heta
  have hprop := eventually_distinct_proportion
    (fun T => (zeroCount T : ℝ)) (fun T => (distinctZeroCount T : ℝ))
    (fun T => (unweightedKernelSum eta T).re) C (ε / 2) (by positivity)
    hNpos hratio hbound
  have hconst :
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        3 / 2 - C / 2 - ε / 2 := by
    rw [show 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) =
      3 / 2 - montgomeryTaylorConst / 2 by
        rw [montgomeryTaylorConst]
        ring]
    rw [abs_lt] at hC
    linarith
  have hfinal : ∀ᶠ T : ℝ in atTop,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
    hprop.mono fun T hT => hconst.trans hT
  exact eventually_atTop.1 hfinal

/-- **`thm_simple_numeric`.** Beyond some height, more than `67.25%` of the non-trivial zeros of
the Riemann zeta function are simple and lie on the critical line. -/
@[zz_tag "thm_simple_numeric"]
theorem simple_proportion_d4 (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (hMT : MontgomeryTaylor) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.6725 < (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) := by
  have hconst : (0.6725 : ℝ) <
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) := by
    rw [show 3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) =
      2 - montgomeryTaylorConst by
        rw [montgomeryTaylorConst]
        ring]
    linarith [montgomeryTaylorConst_lt]
  obtain ⟨T₀, hT₀⟩ := simple_proportion_lower hRvM hPC hMT
    (3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - 0.6725)
    (sub_pos.mpr hconst)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- **`thm_distinct_numeric`.** Beyond some height, more than `83.625%` of the non-trivial zeros
of the Riemann zeta function are distinct. -/
@[zz_tag "thm_distinct_numeric"]
theorem distinct_proportion_d5 (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (hMT : MontgomeryTaylor) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.83625 < (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) := by
  have hconst : (0.83625 : ℝ) <
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) := by
    rw [show 5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) =
      3 / 2 - montgomeryTaylorConst / 2 by
        rw [montgomeryTaylorConst]
        ring]
    linarith [montgomeryTaylorConst_lt]
  obtain ⟨T₀, hT₀⟩ := distinct_proportion_lower hRvM hPC hMT
    (5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - 0.83625)
    (sub_pos.mpr hconst)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

end ZetaZeros
