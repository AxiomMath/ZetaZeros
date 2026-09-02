/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Zeta.Kernel
public import ZetaZeros.Zeta.OrderConj

/-!
# Transfer of the Hilbert-space inequalities to zeta zeros

Conjugation invariance of the rescaled zero multiset, the identification of its finite kernel sum
with the canonical sum over zeros, and the transfer of the two abstract finite-set inequalities to
the three zero-counting functions.
-/

@[expose] public section

namespace ZetaZeros

private noncomputable def reflectedZero (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

private lemma zeroMultiplicity_reflected {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZeros T) :
    zeroMultiplicity (reflectedZero ρ) = zeroMultiplicity ρ := by
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hre := hρ.2.2.1
    rw [h] at hre
    norm_num at hre
  calc
    zeroMultiplicity (reflectedZero ρ) = zeroMultiplicity ((starRingEnd ℂ) ρ) := by
      apply zeroMultiplicity_one_sub
      · simpa only [Complex.conj_re] using hρ.2.1
      · simpa only [Complex.conj_re] using hρ.2.2.1
    _ = zeroMultiplicity ρ := zeroMultiplicity_conj hρ1

private lemma reflectedZero_mem {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZeros T) : reflectedZero ρ ∈ nontrivialZeros T := by
  have hm : zeroMultiplicity (reflectedZero ρ) ≠ 0 := by
    rw [zeroMultiplicity_reflected hρ]
    exact Nat.ne_of_gt (one_le_zeroMultiplicity hρ)
  have hzeta : riemannZeta (reflectedZero ρ) = 0 := by
    apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
    simpa only [zeroMultiplicity] using hm
  refine ⟨hzeta, ?_, ?_, ?_, ?_⟩
  · simp only [reflectedZero, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hρ.2.2.1]
  · simp only [reflectedZero, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith [hρ.2.1]
  · simp only [reflectedZero, Complex.sub_im, Complex.one_im, Complex.conj_im]
    linarith [hρ.2.2.2.1]
  · simp only [reflectedZero, Complex.sub_im, Complex.one_im, Complex.conj_im]
    linarith [hρ.2.2.2.2]

private lemma rescale_reflected (T : ℝ) (ρ : ℂ) :
    rescale T (reflectedZero ρ) = (starRingEnd ℂ) (rescale T ρ) := by
  simp only [rescale, reflectedZero, map_mul, map_sub, map_one, map_div₀, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal]
  ring

theorem rescaledZeros_isConjInvariant {T : ℝ} (hT : 1 < T) :
    IsConjInvariant (rescaledZerosFinset T) (rescaledMult T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [rescaledZerosFinset, Finset.mem_image] at hz
    obtain ⟨ρ, hρ, rfl⟩ := hz
    rw [rescaledMult_rescale hT]
    exact one_le_zeroMultiplicity (by simpa using hρ)
  · intro z hz
    rw [rescaledZerosFinset, Finset.mem_image] at hz ⊢
    obtain ⟨ρ, hρ, rfl⟩ := hz
    refine ⟨reflectedZero ρ, ?_, ?_⟩
    · simpa using reflectedZero_mem (by simpa using hρ)
    · exact rescale_reflected T ρ
  · intro z hz
    rw [rescaledZerosFinset, Finset.mem_image] at hz
    obtain ⟨ρ, hρ, rfl⟩ := hz
    rw [← rescale_reflected, rescaledMult_rescale hT, rescaledMult_rescale hT]
    exact zeroMultiplicity_reflected (by simpa using hρ)

private lemma unweightedKernelSum_eq_finset (eta : ℝ → ℝ) (T : ℝ) :
    unweightedKernelSum eta T =
      ∑ ρ ∈ (nontrivialZeros_finite T).toFinset,
        ∑ ρ' ∈ (nontrivialZeros_finite T).toFinset,
          ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
            testKernel eta (rescaledDiff T ρ ρ') ^ 2 := by
  rw [unweightedKernelSum, finsum_mem_eq_finite_toFinset_sum _ (nontrivialZeros_finite T)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [finsum_mem_eq_finite_toFinset_sum _ (nontrivialZeros_finite T)]

theorem rescaled_kernel_sum_eq_unweightedKernelSum {lam : ℝ} {eta : ℝ → ℝ} {T : ℝ}
    (hT : 1 < T) (_hη : IsAdmissible lam eta) :
    (∑ z ∈ rescaledZerosFinset T, ∑ s ∈ rescaledZerosFinset T,
      ((rescaledMult T z * rescaledMult T s : ℕ) : ℂ) *
        testKernel eta (z - s) ^ 2) = unweightedKernelSum eta T := by
  rw [unweightedKernelSum_eq_finset]
  simp only [rescaledZerosFinset]
  rw [Finset.sum_image (rescale_injective hT).injOn]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Finset.sum_image (rescale_injective hT).injOn]
  apply Finset.sum_congr rfl
  intro ρ' hρ'
  rw [rescaledMult_rescale hT, rescaledMult_rescale hT, rescale_sub_rescale]

/-- **The finite-set lower bound transferred to simple zeros on the critical line.** -/
@[zz_tag "lem_N_simple_lower"]
theorem simpleOnLineCount_lower {lam T : ℝ} {eta : ℝ → ℝ}
    (hT : 1 < T) (hzeros : (nontrivialZeros T).Nonempty)
    (hη : IsAdmissible lam eta) :
    2 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re
      ≤ (simpleOnLineCount T : ℝ) := by
  have hZne : (rescaledZerosFinset T).Nonempty := by
    obtain ⟨ρ, hρ⟩ := hzeros
    refine ⟨rescale T ρ, ?_⟩
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨ρ, hρ, rfl⟩
  have hbound := card_simpleRealPart_lower hη (rescaledZeros_isConjInvariant hT) hZne
  have hsum :
      ∑ z ∈ rescaledZerosFinset T, (rescaledMult T z : ℝ) = (zeroCount T : ℝ) := by
    exact_mod_cast sum_rescaledMult_eq_zeroCount hT
  have hkernel := congrArg Complex.re
    (rescaled_kernel_sum_eq_unweightedKernelSum hT hη)
  simp only [Nat.cast_mul] at hkernel
  have hcard :
      ((simpleRealPart (rescaledZerosFinset T) (rescaledMult T)).card : ℝ) =
        (simpleOnLineCount T : ℝ) := by
    exact_mod_cast card_simpleRealPart_rescaled_eq_simpleOnLineCount hT
  rwa [hsum, hkernel, hcard] at hbound

/-- **The finite-set lower bound transferred to distinct zeros.** -/
@[zz_tag "lem_N_distinct_lower"]
theorem distinctZeroCount_lower {lam T : ℝ} {eta : ℝ → ℝ}
    (hT : 1 < T) (hzeros : (nontrivialZeros T).Nonempty)
    (hη : IsAdmissible lam eta) :
    3 / 2 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re / 2
      ≤ (distinctZeroCount T : ℝ) := by
  have hZne : (rescaledZerosFinset T).Nonempty := by
    obtain ⟨ρ, hρ⟩ := hzeros
    refine ⟨rescale T ρ, ?_⟩
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨ρ, hρ, rfl⟩
  have hbound := card_lower hη (rescaledZeros_isConjInvariant hT) hZne
  have hsum :
      ∑ z ∈ rescaledZerosFinset T, (rescaledMult T z : ℝ) = (zeroCount T : ℝ) := by
    exact_mod_cast sum_rescaledMult_eq_zeroCount hT
  have hkernel := congrArg Complex.re
    (rescaled_kernel_sum_eq_unweightedKernelSum hT hη)
  simp only [Nat.cast_mul] at hkernel
  have hcard : ((rescaledZerosFinset T).card : ℝ) = (distinctZeroCount T : ℝ) := by
    exact_mod_cast card_rescaledZerosFinset_eq_distinctZeroCount hT
  rw [hsum, hkernel, hcard] at hbound
  calc
    3 / 2 * (zeroCount T : ℝ) - (unweightedKernelSum eta T).re / 2 =
        (3 / 2 : ℝ) * (zeroCount T : ℝ) -
          (1 / 2 : ℝ) * (unweightedKernelSum eta T).re := by ring
    _ ≤ (distinctZeroCount T : ℝ) := hbound

end ZetaZeros
