/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ZetaZeros.Hilbert.AlphaExpansion
public import ZetaZeros.Main

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace ZetaZeros.Challenge

/-- **`prop_simple_real_lower`.** The number of real points of multiplicity one is at least
`2 ∑_{z ∈ 𝒵} 1 - ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_simple_real_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    2 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simpleRealPart Z m).card : ℝ) :=
  card_simpleRealPart_lower h hZ hZne

/-- **`prop_distinct_lower`.** The number of distinct points is at least
`(3/2) ∑_{z ∈ 𝒵} 1 - (1/2) ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_distinct_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    (3 / 2 : ℝ) * (∑ z ∈ Z, (m z : ℝ))
        - (1 / 2 : ℝ) *
          (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ (Z.card : ℝ) :=
  card_lower h hZ hZne

/-- **`thm_simple`.** Beyond a height depending on `ε`, the proportion of non-trivial zeros
that are simple and lie on the critical line exceeds
`3/2 - (1/√2) cot(1/√2) - ε = 0.6725007037… - ε`. -/
theorem thm_simple (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  simple_proportion_lower hRvM hPC ε hε

/-- **`thm_distinct`.** Beyond a height depending on `ε`, the proportion of non-trivial zeros
that are distinct exceeds `5/4 - (1/(2√2)) cot(1/√2) - ε = 0.8362503518… - ε`. -/
theorem thm_distinct (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  distinct_proportion_lower hRvM hPC ε hε

/-- **`thm_simple_numeric`.** Beyond some height, more than `67.25%` of the non-trivial zeros of
the Riemann zeta function are simple and lie on the critical line. -/
theorem thm_simple_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.6725 < (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  simple_proportion_d4 hRvM hPC

/-- **`thm_distinct_numeric`.** Beyond some height, more than `83.625%` of the non-trivial zeros
of the Riemann zeta function are distinct. -/
theorem thm_distinct_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.83625 < (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  distinct_proportion_d5 hRvM hPC

end ZetaZeros.Challenge
