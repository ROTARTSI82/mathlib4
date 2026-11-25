/-
Copyright (c) 2026 Grant Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The generalized Laplace expansion

The generalized Laplace expansion of a determinant along a set of rows `S`:
`det A = ∑_{#T = #S} ε(S, T) * det A[S, T] * det A[Sᶜ, Tᶜ]`.

Over an arbitrary index type, there is no canonical way to index the minors `A[S, T]` and
`A[Sᶜ, Tᶜ]` by the same type. We instead match the rows with the columns by a permutation `σ` of
the index type sending `S` onto `T`: the minors are `A.submatrix (↑) (σ ∘ (↑))` on `S` and on
`Sᶜ`, and the sign is `Equiv.Perm.sign σ`. The product of the sign and the two minors does not
depend on the choice of `σ` (`Matrix.sign_mul_det_mul_det_eq_of_map_eq`), so the expansion takes
an arbitrary family `σ T` of such permutations.

## Main results

* `Matrix.sum_sign_mul_prod_eq_det_mul_det`: the terms of the Leibniz formula whose permutation
  preserves `S` sum to `det A[S, S] * det A[Sᶜ, Sᶜ]`.
* `Matrix.sum_sign_mul_prod_eq_sign_mul_det_mul_det`: the terms sending `S` onto `σ(S)` sum to
  `sign σ * det A[S, σ(S)] * det A[Sᶜ, σ(Sᶜ)]`.
* `Matrix.det_eq_sum_sign_mul_det_mul_det_row`, `Matrix.det_eq_sum_sign_mul_det_mul_det_col`:
  the generalized Laplace expansion along a set of rows or of columns.

## Implementation notes

The proof groups the terms of the Leibniz formula `det A = ∑ τ, sign τ * ∏ i, A i (τ i)` by
`T = τ(S)`. Writing `τ = σ T * ρ`, the permutations with `τ(S) = T` correspond to the `ρ` that
preserve `S`, and those terms are the Leibniz expansion of the block-diagonal part of
`A.submatrix id (σ T)`.

## References

* https://en.wikipedia.org/wiki/Laplace_expansion
-/

public section

open Finset
open Equiv (Perm)

variable {n R : Type*} [CommRing R] [DecidableEq n] [Fintype n]

namespace Matrix

/-- The terms of the Leibniz formula whose permutation preserves `S` sum to the product of the
principal minors on `S` and on `Sᶜ`. -/
theorem sum_sign_mul_prod_eq_det_mul_det (A : Matrix n n R) (S : Finset n) :
    ∑ ρ : Perm n with S.map ρ.toEmbedding = S, (Perm.sign ρ : R) * ∏ i, A i (ρ i) =
      (A.submatrix ((↑) : S → n) (↑)).det * (A.submatrix ((↑) : ↥Sᶜ → n) (↑)).det := by
  -- the block-diagonal part of `A`
  let B : Matrix n n R := of fun i j ↦ if (i ∈ S ↔ j ∈ S) then A i j else 0
  have hB : B.det =
      (A.submatrix ((↑) : S → n) (↑)).det * (A.submatrix ((↑) : ↥Sᶜ → n) (↑)).det := by
    rw [twoBlockTriangular_det B (· ∈ S) fun i hi j hj ↦ by simp [B, hi, hj]]
    congr 1
    · convert rfl using 2
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp [B, toSquareBlockProp_def]
    · let e : ↥Sᶜ ≃ {k // k ∉ S} := Equiv.subtypeEquivRight fun _ ↦ mem_compl
      rw [← det_submatrix_equiv_self e]
      convert rfl using 2
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [mem_compl] at hi hj
      simp [B, e, toSquareBlockProp_def, hi, hj]
  rw [← hB, ← det_transpose, det_apply, sum_filter]
  refine sum_congr rfl fun ρ _ ↦ ?_
  rw [Units.smul_def, zsmul_eq_mul]
  split_ifs with h
  · -- `ρ` preserves `S`, so it preserves `Sᶜ` too
    have hρ (i : n) : ρ i ∈ S ↔ i ∈ S := by
      conv_lhs => rw [← h, mem_map_equiv, Equiv.symm_apply_apply]
    simp [B, hρ]
  · -- otherwise some `i ∈ S` has `ρ i ∉ S`, and the corresponding factor vanishes
    have hsub : ¬S.map ρ.toEmbedding ⊆ S := fun hs ↦
      h (eq_of_subset_of_card_le hs (card_map _).ge)
    obtain ⟨_, hk, hkS⟩ := not_subset.1 hsub
    obtain ⟨i, hi, rfl⟩ := mem_map.1 hk
    rw [Equiv.coe_toEmbedding] at hkS
    rw [prod_eq_zero (mem_univ i) (by simp [B, hi, hkS]), mul_zero]

/-- The terms of the Leibniz formula whose permutation sends `S` onto `σ(S)` sum to
`sign σ * det A[S, σ(S)] * det A[Sᶜ, σ(Sᶜ)]`. -/
theorem sum_sign_mul_prod_eq_sign_mul_det_mul_det (A : Matrix n n R) (S : Finset n)
    (σ : Perm n) :
    ∑ τ : Perm n with S.map τ.toEmbedding = S.map σ.toEmbedding,
        (Perm.sign τ : R) * ∏ i, A i (τ i) =
      Perm.sign σ * (A.submatrix ((↑) : S → n) (σ ∘ (↑))).det *
        (A.submatrix ((↑) : ↥Sᶜ → n) (σ ∘ (↑))).det := by
  -- substitute `τ = σ * ρ`; then `τ(S) = σ(S)` iff `ρ` preserves `S`
  rw [mul_assoc]
  refine Eq.trans ?_ (congrArg _ (sum_sign_mul_prod_eq_det_mul_det (A.submatrix id σ) S))
  rw [mul_sum, sum_filter, sum_filter]
  refine (Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun ρ ↦ ?_).symm
  have h : S.map (σ * ρ).toEmbedding = (S.map ρ.toEmbedding).map σ.toEmbedding := by
    rw [Perm.mul_def, Equiv.trans_toEmbedding, Finset.map_map]
  simp only [Equiv.coe_mulLeft, h, Finset.map_inj]
  split_ifs
  · simp [Perm.sign_mul, mul_assoc]
  · rfl

/-- The product `sign σ * det A[S, σ(S)] * det A[Sᶜ, σ(Sᶜ)]` only depends on `σ(S)`. -/
theorem sign_mul_det_mul_det_eq_of_map_eq (A : Matrix n n R) (S : Finset n) {σ τ : Perm n}
    (h : S.map σ.toEmbedding = S.map τ.toEmbedding) :
    Perm.sign σ * (A.submatrix ((↑) : S → n) (σ ∘ (↑))).det *
        (A.submatrix ((↑) : ↥Sᶜ → n) (σ ∘ (↑))).det =
      Perm.sign τ * (A.submatrix ((↑) : S → n) (τ ∘ (↑))).det *
        (A.submatrix ((↑) : ↥Sᶜ → n) (τ ∘ (↑))).det := by
  rw [← sum_sign_mul_prod_eq_sign_mul_det_mul_det, ← sum_sign_mul_prod_eq_sign_mul_det_mul_det, h]

/-- **Generalized Laplace expansion** along the set of rows `S`. For each `T` with `#T = #S`,
`σ T` is a permutation sending `S` onto `T`; the minors are `A[S, T]` and `A[Sᶜ, Tᶜ]`, with
rows and columns matched by `σ T`. -/
theorem det_eq_sum_sign_mul_det_mul_det_row (A : Matrix n n R) (S : Finset n)
    (σ : Finset n → Perm n) (hσ : ∀ T, #T = #S → S.map (σ T).toEmbedding = T) :
    A.det = ∑ T with #T = #S, Perm.sign (σ T) *
      (A.submatrix ((↑) : S → n) (σ T ∘ (↑))).det *
        (A.submatrix ((↑) : ↥Sᶜ → n) (σ T ∘ (↑))).det := by
  rw [← det_transpose, det_apply]
  simp_rw [Units.smul_def, zsmul_eq_mul, transpose_apply]
  rw [← sum_fiberwise_of_maps_to (g := fun τ : Perm n ↦ S.map τ.toEmbedding)
    (t := univ.filter fun T : Finset n ↦ #T = #S) (by simp)]
  refine sum_congr rfl fun T hT ↦ ?_
  have h := sum_sign_mul_prod_eq_sign_mul_det_mul_det A S (σ T)
  rwa [hσ T (mem_filter.1 hT).2] at h

/-- **Generalized Laplace expansion** along the set of columns `S`. For each `T` with
`#T = #S`, `σ T` is a permutation sending `S` onto `T`; the minors are `A[T, S]` and
`A[Tᶜ, Sᶜ]`, with rows and columns matched by `σ T`. -/
theorem det_eq_sum_sign_mul_det_mul_det_col (A : Matrix n n R) (S : Finset n)
    (σ : Finset n → Perm n) (hσ : ∀ T, #T = #S → S.map (σ T).toEmbedding = T) :
    A.det = ∑ T with #T = #S, Perm.sign (σ T) *
      (A.submatrix (σ T ∘ (↑)) ((↑) : S → n)).det *
        (A.submatrix (σ T ∘ (↑)) ((↑) : ↥Sᶜ → n)).det := by
  rw [← det_transpose, det_eq_sum_sign_mul_det_mul_det_row _ S σ hσ]
  simp_rw [← transpose_submatrix, det_transpose]

end Matrix
