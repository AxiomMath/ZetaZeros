/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ZetaZeros.Hilbert.Subspaces

/-!
# Adapted orthonormal bases and the Bessel coefficients

An orthonormal basis of `W` whose initial segments span `U` and `V`, and the coefficients of the
two-variable kernel against its tensor squares.

The three subspaces are finite-dimensional — each is spanned by a finite family — which is what
makes `Module.finrank` the right index bound and Gram–Schmidt applicable.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

instance finiteDimensional_subspaceU (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    FiniteDimensional ℂ (subspaceU h Z m) :=
  FiniteDimensional.span_of_finite ℂ
    (((Finset.finite_toSet _).image _).union ((Finset.finite_toSet _).image _))

instance finiteDimensional_subspaceW (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    FiniteDimensional ℂ (subspaceW h Z m) :=
  FiniteDimensional.span_of_finite ℂ
    ((((Finset.finite_toSet _).image _).union ((Finset.finite_toSet _).image _)).union
      ((Finset.finite_toSet _).image _))

instance finiteDimensional_subspaceV (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    FiniteDimensional ℂ (subspaceV h Z m) :=
  FiniteDimensional.span_of_finite ℂ
    (((Finset.finite_toSet _).image _).union ((Finset.finite_toSet _).image _))

/-- A tuple is an *adapted orthonormal basis*: orthonormal, spanning `W`, and with the initial
segments of lengths `dim U` and `dim V` spanning `U` and `V`. The nesting proved in
`subspaceU_le_subspaceV` is what makes such a tuple possible. -/
@[zz_tag "def_adapted_basis"]
structure IsAdaptedBasis (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ)
    (psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam) : Prop where
  /-- The tuple is orthonormal. -/
  orthonormal : Orthonormal ℂ psi
  /-- It spans `W`. -/
  span_W : Submodule.span ℂ (Set.range psi) = subspaceW h Z m
  /-- Its first `dim U` members span `U`. -/
  span_U : Submodule.span ℂ
    (psi '' {j | (j : ℕ) < Module.finrank ℂ (subspaceU h Z m)}) = subspaceU h Z m
  /-- Its first `dim V` members span `V`. -/
  span_V : Submodule.span ℂ
    (psi '' {j | (j : ℕ) < Module.finrank ℂ (subspaceV h Z m)}) = subspaceV h Z m

/-- The Bessel coefficient `alpha j`: the coefficient of the two-variable kernel against the
tensor square of the `j`-th basis vector. -/
@[zz_tag "def_alpha"]
noncomputable def alphaCoeff (eta : ℝ → ℝ) (lam : ℝ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (psi : ℕ → L2Interval lam) (j : ℕ) : ℂ :=
  ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
    bigF eta Z m u v * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v)

end ZetaZeros
