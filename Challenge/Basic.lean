/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Simple zeros of the Riemann zeta function on the critical line

More than `67.25%` of the non-trivial zeros of the Riemann zeta function are simple and lie on
the critical line, and more than `83.62%` of them are distinct, given three classical analytic
inputs.

Y. Lamzouri, *A new proof that more than `2/3` of the zeros of the Riemann zeta function are
simple and on the critical line*, **Theorem 1.1**.
-/

@[expose] public section

namespace ZetaZeros

/-- The non-trivial zeros of the Riemann zeta function with imaginary part in `(0, T]`: the
zeros lying in the critical strip `0 < re s < 1`, as a set, so without multiplicity. -/
def nontrivialZeros (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- The multiplicity of `ρ` as a zero of the Riemann zeta function, i.e. its order of
vanishing there. -/
noncomputable def zeroMultiplicity (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- The number of non-trivial zeros with imaginary part in `(0, T]`, counted with multiplicity.
This is `N T` in the source. -/
noncomputable def zeroCount (T : ℝ) : ℕ := ∑ᶠ ρ ∈ nontrivialZeros T, zeroMultiplicity ρ

/-- The number of non-trivial zeros with imaginary part in `(0, T]` that are simple and lie on
the critical line `re s = 1/2`. This is `N₀ˢ T` in the source. -/
noncomputable def simpleOnLineCount (T : ℝ) : ℕ :=
  {ρ ∈ nontrivialZeros T | ρ.re = 1 / 2 ∧ zeroMultiplicity ρ = 1}.ncard

/-- The number of distinct non-trivial zeros with imaginary part in `(0, T]`. This is `N_d T`
in the source. -/
noncomputable def distinctZeroCount (T : ℝ) : ℕ := (nontrivialZeros T).ncard

/-- The Fourier transform of a compactly supported real function, at a complex argument. -/
noncomputable def fourierC (f : ℝ → ℝ) (ξ : ℂ) : ℂ :=
  ∫ u : ℝ, (f u : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ξ * (u : ℂ))

/-! ## The key proposition

The Hilbert-space inequality at the heart of the proof.  It speaks only of a finite
conjugation-invariant multiset of complex numbers and a test function; no zeta function appears.
The multiset is presented by its finite support `Z` together with a multiplicity function `m`, so
that `∑_{z ∈ 𝒵} 1` is `∑ z ∈ Z, (m z : ℝ)` and `∑_{z, s ∈ 𝒵} K (z - s) ^ 2` is
`∑ z ∈ Z, ∑ s ∈ Z, (m z * m s) * testKernel eta (z - s) ^ 2`.

Y. Lamzouri, *A new proof that more than `2/3` of the zeros of the Riemann zeta function are
simple and on the critical line*, **Proposition 2.1**.
-/

/-- `eta` is `lam`-admissible: square-integrable, real-valued, even, supported in
`(-lam, lam)`, and normalised so that its square has Fourier transform `1` at `0`. -/
structure IsAdmissible (lam : ℝ) (eta : ℝ → ℝ) : Prop where
  /-- `eta` is square-integrable. -/
  memLp : MeasureTheory.MemLp eta 2 MeasureTheory.volume
  /-- `eta` is even. -/
  even : ∀ x, eta (-x) = eta x
  /-- `eta` vanishes off `(-lam, lam)`. -/
  support : ∀ x, lam ≤ |x| → eta x = 0
  /-- `eta` is normalised: its square has Fourier transform `1` at `0`. -/
  fourier_sq_zero : fourierC (eta ^ 2) 0 = 1

/-- The kernel `K = η̂²` of a test function. -/
noncomputable def testKernel (eta : ℝ → ℝ) : ℂ → ℂ := fourierC (eta ^ 2)

/-- The support `Z` with multiplicities `m` is conjugation-invariant: every multiplicity is at
least one, and conjugation permutes `Z` preserving multiplicity. -/
structure IsConjInvariant (Z : Finset ℂ) (m : ℂ → ℕ) : Prop where
  /-- Every point of the support has multiplicity at least one. -/
  one_le : ∀ z ∈ Z, 1 ≤ m z
  /-- Conjugation maps the support to itself. -/
  conj_mem : ∀ z ∈ Z, (starRingEnd ℂ) z ∈ Z
  /-- Conjugation preserves multiplicity. -/
  mult_conj : ∀ z ∈ Z, m ((starRingEnd ℂ) z) = m z

/-- The simple real part of the support: real points of multiplicity one. -/
noncomputable def simpleRealPart (Z : Finset ℂ) (m : ℂ → ℕ) : Finset ℂ :=
  Z.filter fun x => x.im = 0 ∧ m x = 1

/-! ## The three external inputs, as hypotheses

* **Riemann--von Mangoldt**: E. C. Titchmarsh, *The theory of the Riemann zeta-function*,
  2nd ed., Oxford University Press, 1986, **Theorem 9.4**.
* **Unconditional pair correlation**: S. A. C. Baluyot, D. A. Goldston, A. I. Suriajaya and
  C. L. Turnage-Butterbaugh, *An unconditional Montgomery theorem for pair correlation of zeros
  of the Riemann zeta-function*, Acta Arith. **214** (2024), 357--376, **Lemma 5**.
* **Montgomery--Taylor**: H. L. Montgomery, *Distribution of the zeros of the Riemann zeta
  function*, Proc. ICM (Vancouver, 1974), Vol. 1, 379--381.
-/

/-- The weight `4 / (4 - z²)` carried by the unconditional pair-correlation formula. -/
noncomputable def pairWeight (z : ℂ) : ℂ := 4 / (4 - z ^ 2)

/-- The rescaled difference `i(ρ - ρ') log T / (2π)` of two zeros. -/
noncomputable def rescaledDiff (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  Complex.I * (ρ - ρ') * ((Real.log T / (2 * Real.pi) : ℝ) : ℂ)

/-- The weighted sum of `fourierC f` over ordered pairs of non-trivial zeros with imaginary part
in `(0, T]`, each zero counted with multiplicity. -/
noncomputable def pairCorrelationSum (f : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ nontrivialZeros T, ∑ᶠ ρ' ∈ nontrivialZeros T,
    ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
      fourierC f (rescaledDiff T ρ ρ') * pairWeight (ρ - ρ')

/-- The main term `f 0 + 2 ∫₀¹ α f α` of the pair-correlation formula. -/
noncomputable def pairMainTerm (f : ℝ → ℝ) : ℝ := f 0 + 2 * ∫ α in (0:ℝ)..1, α * f α

/-- A test function admissible for the pair-correlation formula: even, integrable, supported in
`[-1, 1]`, and Lipschitz continuous at `0`. -/
def IsPairTestFunction (f : ℝ → ℝ) : Prop :=
  (∀ x, f (-x) = f x) ∧ MeasureTheory.Integrable f ∧ (∀ x, 1 < |x| → f x = 0) ∧
    ∃ C : ℝ, ∀ x, |f x - f 0| ≤ C * |x|

/-- The extremal test function `cos(√2 x) / (√2 sin(1/√2))` on `[-1/2, 1/2]`, zero elsewhere. -/
noncomputable def extremalTest (x : ℝ) : ℝ :=
  if |x| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))
  else 0

/-- The self-convolution of the extremal test function. -/
noncomputable def extremalSelfConv (x : ℝ) : ℝ := ∫ t : ℝ, extremalTest t * extremalTest (x - t)

/-- The Montgomery--Taylor constant `1/2 + (1/√2) cot(1/√2) = 1.3274992963…`. -/
noncomputable def montgomeryTaylorConst : ℝ :=
  1 / 2 + (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2)

/-- **The Riemann--von Mangoldt formula.** The number of non-trivial zeros up to height `T`,
counted with multiplicity, is asymptotic to `(T / 2π) log T`. -/
def RiemannVonMangoldt : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    |(zeroCount T : ℝ) / (T / (2 * Real.pi) * Real.log T) - 1| < ε

/-- **The unconditional pair correlation formula.** For every admissible test function the
weighted pair-correlation sum is `(T / 2π) log T` times its main term, with an error
`O(1 / √log T)`. -/
def PairCorrelation : Prop :=
  ∀ f : ℝ → ℝ, IsPairTestFunction f →
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ‖pairCorrelationSum f T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) -
          ((pairMainTerm f : ℝ) : ℂ)‖ ≤ C / Real.sqrt (Real.log T)

/-- **The Montgomery--Taylor computation.** The pair-correlation functional evaluated at the
self-convolution of the extremal test function is the Montgomery--Taylor constant. -/
def MontgomeryTaylor : Prop :=
  extremalSelfConv 0 + 2 * ∫ α in (0:ℝ)..1, α * extremalSelfConv α = montgomeryTaylorConst

end ZetaZeros

namespace ZetaZeros.Challenge

/-- **`prop_simple_real_lower`.** The number of real points of multiplicity one is at least
`2 ∑_{z ∈ 𝒵} 1 - ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_simple_real_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    2 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simpleRealPart Z m).card : ℝ) :=
  sorry

/-- **`prop_distinct_lower`.** The number of distinct points is at least
`(3/2) ∑_{z ∈ 𝒵} 1 - (1/2) ∑_{z, s ∈ 𝒵} K (z - s) ^ 2`. -/
theorem prop_distinct_lower {lam : ℝ} {eta : ℝ → ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (hZne : Z.Nonempty) :
    (3 / 2 : ℝ) * (∑ z ∈ Z, (m z : ℝ))
        - (1 / 2 : ℝ) *
          (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ (Z.card : ℝ) :=
  sorry

/-- **`thm_simple`.** Beyond a height depending on `ε`, the proportion of non-trivial zeros
that are simple and lie on the critical line exceeds
`3/2 - (1/√2) cot(1/√2) - ε = 0.6725007037… - ε`. -/
theorem thm_simple (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (hMT : MontgomeryTaylor) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 2 - (1 / Real.sqrt 2) * Real.cot (1 / Real.sqrt 2) - ε <
        (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

/-- **`thm_distinct`.** Beyond a height depending on `ε`, the proportion of non-trivial zeros
that are distinct exceeds `5/4 - (1/(2√2)) cot(1/√2) - ε = 0.8362503518… - ε`. -/
theorem thm_distinct (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (hMT : MontgomeryTaylor) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      5 / 4 - (1 / (2 * Real.sqrt 2)) * Real.cot (1 / Real.sqrt 2) - ε <
        (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

/-- **`thm_simple_numeric`.** Beyond some height, more than `67.25%` of the non-trivial zeros of
the Riemann zeta function are simple and lie on the critical line. -/
theorem thm_simple_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (hMT : MontgomeryTaylor) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.6725 < (simpleOnLineCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

/-- **`thm_distinct_numeric`.** Beyond some height, more than `83.625%` of the non-trivial zeros
of the Riemann zeta function are distinct. -/
theorem thm_distinct_numeric (hRvM : RiemannVonMangoldt) (hPC : PairCorrelation)
    (hMT : MontgomeryTaylor) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0.83625 < (distinctZeroCount T : ℝ) / (zeroCount T : ℝ) :=
  sorry

end ZetaZeros.Challenge
