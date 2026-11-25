/-
Copyright (c) 2026 Grant Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib.GroupTheory.Perm.Fin
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
* `Matrix.det_eq_sum_neg_one_pow_mul_det_mul_det`: in a linear order, with the minors indexed
  increasingly (`Finset.orderEmbOfFin`) and the sign `(-1)` to the sum of the positions
  `#{b | b < a}` of the elements of `S` and of `T`.
* `Matrix.det_eq_sum_neg_one_pow_mul_det_mul_det_fin`: the textbook form for `Fin N`, with the
  sign `(-1) ^ (∑ i ∈ S, i + ∑ j ∈ T, j)`.

## Implementation notes

The proof groups the terms of the Leibniz formula `det A = ∑ τ, sign τ * ∏ i, A i (τ i)` by
`T = τ(S)`. Writing `τ = σ T * ρ`, the permutations with `τ(S) = T` correspond to the `ρ` that
preserve `S`, and those terms are the Leibniz expansion of the block-diagonal part of
`A.submatrix id (σ T)`.

In a linear order, we take for `σ T` the permutation sending `S` onto `T` and `Sᶜ` onto `Tᶜ`
increasingly, and compute its sign by counting inversions.

## References

* https://en.wikipedia.org/wiki/Laplace_expansion
-/

public section

open Finset
open Equiv (Perm)

namespace Finset

variable {α : Type*} [LinearOrder α]

theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] (S : Finset α) (f : α → M) :
    ∏ i : Fin #S, f (S.orderEmbOfFin rfl i) = ∏ a ∈ S, f a := by
  rw [← prod_coe_sort S, ← (S.orderIsoOfFin rfl).toEquiv.prod_comp]
  simp [coe_orderIsoOfFin_apply]

/-- `S.orderEmbOfFin rfl i` is the `i`-th smallest element of `S`. -/
theorem card_filter_lt_orderEmbOfFin (S : Finset α) (i : Fin #S) :
    #(S.filter (· < S.orderEmbOfFin rfl i)) = i := by
  have h : S.filter (· < S.orderEmbOfFin rfl i) =
      (Iio i).map (S.orderEmbOfFin rfl).toEmbedding := by
    ext y
    simp only [mem_filter, mem_map, mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hy, hlt⟩
      obtain ⟨j, rfl⟩ : y ∈ Set.range (S.orderEmbOfFin rfl) := by
        rwa [range_orderEmbOfFin]
      exact ⟨j, (S.orderEmbOfFin rfl).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨orderEmbOfFin_mem _ _ _, (S.orderEmbOfFin rfl).lt_iff_lt.2 hj⟩
  rw [h, card_map, Fin.card_Iio]

end Finset

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

/-! ### Increasing minors in a linear order -/

section LinearOrder

variable [LinearOrder n]

/-- If `σ` sends `S` onto `T` and is increasing on `S` and on `Sᶜ`, its inversions are the pairs
`a ∈ S`, `b ∉ S` such that exactly one of `a < b` and `σ a < σ b` holds. -/
private theorem sign_eq_of_strictMonoOn (σ : Perm n) {S T : Finset n}
    (hmap : S.map σ.toEmbedding = T) (hS : StrictMonoOn σ S) (hSc : StrictMonoOn σ ↑Sᶜ) :
    Perm.sign σ = (∏ a ∈ S, ∏ b ∈ Sᶜ, if a < b then 1 else -1) *
      ∏ a ∈ T, ∏ b ∈ Tᶜ, if a < b then 1 else -1 := by
  have hmapc : Sᶜ.map σ.toEmbedding = Tᶜ := by
    rw [← hmap]
    ext
    simp [mem_map_equiv]
  let K (a b : n) : ℤˣ := if a < b then (if σ a < σ b then 1 else -1) else 1
  -- pairs inside `S` or inside `Sᶜ` are not inversions
  have hK (a b : n) (hab : a ∈ S ↔ b ∈ S) : K a b = 1 := by
    simp only [K]
    split_ifs with h₁ h₂ <;> try rfl
    by_cases ha : a ∈ S
    · exact absurd (hS ha (hab.1 ha) h₁) h₂
    · exact absurd (hSc (by simpa using ha) (by simpa [hab] using ha) h₁) h₂
  have hK' (a b : n) (ha : a ∈ S) (hb : b ∉ S) :
      K b a * K a b = (if a < b then 1 else -1) * (if σ a < σ b then 1 else -1) := by
    have hab : a ≠ b := by rintro rfl; exact hb ha
    have hσ : σ a ≠ σ b := σ.injective.ne hab
    rcases hab.lt_or_gt with h | h <;> rcases hσ.lt_or_gt with h' | h' <;>
      simp [K, h, h', h.not_gt, h'.not_gt]
  have h₁ : Perm.sign σ = ∏ b, ∏ a, K a b := by
    rw [Perm.sign_eq_prod_prod_lt]
    simp_rw [prod_filter]
    rfl
  have h₂ (b : n) (hb : b ∈ S) : ∏ a, K a b = ∏ a ∈ Sᶜ, K a b :=
    (prod_subset (subset_univ _) fun a _ ha ↦ hK a b (by simp_all)).symm
  have h₃ (b : n) (hb : b ∈ Sᶜ) : ∏ a, K a b = ∏ a ∈ S, K a b :=
    (prod_subset (subset_univ _) fun a _ ha ↦ hK a b (by simp_all)).symm
  rw [h₁, ← prod_mul_prod_compl S, prod_congr rfl h₂, prod_congr rfl h₃, prod_comm (s := Sᶜ),
    ← prod_mul_distrib]
  simp_rw [← prod_mul_distrib]
  rw [prod_congr rfl fun a ha ↦ prod_congr rfl fun b hb ↦ hK' a b ha (mem_compl.1 hb)]
  simp_rw [prod_mul_distrib]
  rw [← hmapc, ← hmap, prod_map]
  simp_rw [prod_map]
  rfl

/-- Up to a correction depending only on `#S`, the sign `∏ a ∈ S, ∏ b ∉ S, ±1` is `(-1)` to the
sum of the positions of the elements of `S`. -/
private theorem prod_prod_ite_lt_mul (S : Finset n) :
    (∏ a ∈ S, ∏ b ∈ Sᶜ, if a < b then 1 else -1 : ℤˣ) * ∏ i ∈ range #S, (-1) ^ i =
      (-1) ^ ∑ a ∈ S, #{b | b < a} := by
  rw [← Fin.prod_univ_eq_prod_range (fun i ↦ ((-1 : ℤˣ) ^ i))]
  simp_rw [← card_filter_lt_orderEmbOfFin S]
  rw [prod_orderEmbOfFin S (fun a ↦ (-1 : ℤˣ) ^ #(S.filter (· < a))), ← prod_mul_distrib,
    ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun a ha ↦ ?_
  -- `b < a` for `a ∈ S`, `b ∉ S` is the only way to get `-1`
  have hsign : ∏ b ∈ Sᶜ, (if a < b then 1 else -1 : ℤˣ) = (-1) ^ #(Sᶜ.filter (· < a)) := by
    rw [← prod_const, prod_filter]
    refine prod_congr rfl fun b hb ↦ ?_
    have hab : a ≠ b := by rintro rfl; exact (mem_compl.1 hb) ha
    rcases hab.lt_or_gt with h | h
    · simp [h, h.not_gt]
    · simp [h, h.not_gt]
  have hcard : #(Sᶜ.filter (· < a)) + #(S.filter (· < a)) = #{b | b < a} := by
    rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_compl_left), ← filter_union]
    congr 1
    ext b
    simp only [mem_filter, mem_compl, mem_union, mem_univ, true_and]
    tauto
  rw [hsign, ← pow_add, hcard]

omit [LinearOrder n] in
private theorem card_compl_eq_of_card_eq {S T : Finset n} {k m : ℕ} (hS : #S = k)
    (hSc : #Sᶜ = m) (hT : #T = k) : #Tᶜ = m := by
  rw [card_compl, hT, ← hS, ← card_compl, hSc]

/-- The permutation sending `S` onto `T` and `Sᶜ` onto `Tᶜ`, increasingly. -/
private def orderShuffle {S T : Finset n} {k m : ℕ} (hS : #S = k) (hSc : #Sᶜ = m)
    (hT : #T = k) (hTc : #Tᶜ = m) : Perm n :=
  (finSumEquivOfFinset hS hSc).symm.trans (finSumEquivOfFinset hT hTc)

section orderShuffle

variable {S T : Finset n} {k m : ℕ} (hS : #S = k) (hSc : #Sᶜ = m) (hT : #T = k)
  (hTc : #Tᶜ = m)

private theorem orderShuffle_orderEmbOfFin (i : Fin k) :
    orderShuffle hS hSc hT hTc (S.orderEmbOfFin hS i) = T.orderEmbOfFin hT i := by
  rw [orderShuffle, Equiv.trans_apply, ← finSumEquivOfFinset_inl hS hSc, Equiv.symm_apply_apply,
    finSumEquivOfFinset_inl]

private theorem orderShuffle_orderEmbOfFin_compl (j : Fin m) :
    orderShuffle hS hSc hT hTc (Sᶜ.orderEmbOfFin hSc j) = Tᶜ.orderEmbOfFin hTc j := by
  rw [orderShuffle, Equiv.trans_apply, ← finSumEquivOfFinset_inr hS hSc, Equiv.symm_apply_apply,
    finSumEquivOfFinset_inr]

private theorem map_orderShuffle : S.map (orderShuffle hS hSc hT hTc).toEmbedding = T := by
  refine eq_of_subset_of_card_le (fun x hx ↦ ?_) (by rw [card_map, hS, hT])
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
  obtain ⟨i, rfl⟩ : y ∈ Set.range (S.orderEmbOfFin hS) := by rwa [range_orderEmbOfFin]
  rw [Equiv.coe_toEmbedding, orderShuffle_orderEmbOfFin]
  exact orderEmbOfFin_mem _ _ _

private theorem sign_orderShuffle :
    Perm.sign (orderShuffle hS hSc hT hTc) =
      (-1) ^ (∑ a ∈ S, #{b | b < a} + ∑ a ∈ T, #{b | b < a}) := by
  have hmonoS : StrictMonoOn (orderShuffle hS hSc hT hTc) S := by
    intro a ha b hb hab
    obtain ⟨i, rfl⟩ : a ∈ Set.range (S.orderEmbOfFin hS) := by rwa [range_orderEmbOfFin]
    obtain ⟨j, rfl⟩ : b ∈ Set.range (S.orderEmbOfFin hS) := by rwa [range_orderEmbOfFin]
    rw [orderShuffle_orderEmbOfFin, orderShuffle_orderEmbOfFin]
    exact (T.orderEmbOfFin hT).lt_iff_lt.2 ((S.orderEmbOfFin hS).lt_iff_lt.1 hab)
  have hmonoSc : StrictMonoOn (orderShuffle hS hSc hT hTc) ↑Sᶜ := by
    intro a ha b hb hab
    obtain ⟨i, rfl⟩ : a ∈ Set.range (Sᶜ.orderEmbOfFin hSc) := by rwa [range_orderEmbOfFin]
    obtain ⟨j, rfl⟩ : b ∈ Set.range (Sᶜ.orderEmbOfFin hSc) := by rwa [range_orderEmbOfFin]
    rw [orderShuffle_orderEmbOfFin_compl, orderShuffle_orderEmbOfFin_compl]
    exact (Tᶜ.orderEmbOfFin hTc).lt_iff_lt.2 ((Sᶜ.orderEmbOfFin hSc).lt_iff_lt.1 hab)
  have hS' := prod_prod_ite_lt_mul S
  have hT' := prod_prod_ite_lt_mul T
  rw [hS, ← hT] at hS'
  rw [sign_eq_of_strictMonoOn _ (map_orderShuffle hS hSc hT hTc) hmonoS hmonoSc, pow_add, ← hS',
    ← hT']
  have hc : (∏ i ∈ range #T, (-1 : ℤˣ) ^ i) * ∏ i ∈ range #T, (-1) ^ i = 1 :=
    Int.units_mul_self _
  calc _ = (∏ a ∈ S, ∏ b ∈ Sᶜ, if a < b then 1 else -1 : ℤˣ) *
        (∏ a ∈ T, ∏ b ∈ Tᶜ, if a < b then 1 else -1) *
          ((∏ i ∈ range #T, (-1 : ℤˣ) ^ i) * ∏ i ∈ range #T, (-1) ^ i) := by rw [hc, mul_one]
    _ = _ := by ac_rfl

end orderShuffle

/-- **Generalized Laplace expansion** along the set of rows `S`, in a linear order: the minors
are indexed increasingly, and the sign is `(-1)` to the sum of the positions `#{b | b < a}` of
the elements `a` of `S` and of `T`. -/
theorem det_eq_sum_neg_one_pow_mul_det_mul_det (A : Matrix n n R) {k m : ℕ} (S : Finset n)
    (hS : #S = k) (hSc : #Sᶜ = m) :
    A.det = ∑ T : {T : Finset n // #T = k},
      (-1) ^ (∑ a ∈ S, #{b | b < a} + ∑ a ∈ T.val, #{b | b < a}) *
        (A.submatrix (S.orderEmbOfFin hS) (T.val.orderEmbOfFin T.property)).det *
        (A.submatrix (Sᶜ.orderEmbOfFin hSc) (T.valᶜ.orderEmbOfFin (k := m)
          (by rw [card_compl, T.property, ← hS, ← card_compl, hSc]))).det := by
  let σ (T : Finset n) : Perm n := if hT : #T = k then
    orderShuffle hS hSc hT (card_compl_eq_of_card_eq hS hSc hT) else 1
  have hσ (T : Finset n) (hT : #T = k) :
      σ T = orderShuffle hS hSc hT (card_compl_eq_of_card_eq hS hSc hT) := by
    simp [σ, hT]
  rw [det_eq_sum_sign_mul_det_mul_det_row A S σ fun T hT ↦ by
      rw [hσ T (hT.trans hS)]; exact map_orderShuffle _ _ _ _,
    sum_subtype (univ.filter fun T : Finset n ↦ #T = #S) (p := fun T ↦ #T = k) (by simp [hS])]
  refine Fintype.sum_congr _ _ fun ⟨T, hT⟩ ↦ ?_
  have h₁ : (A.submatrix ((↑) : S → n) (σ T ∘ (↑))).submatrix
      (S.orderIsoOfFin hS).toEquiv (S.orderIsoOfFin hS).toEquiv =
        A.submatrix (S.orderEmbOfFin hS) (T.orderEmbOfFin hT) := by
    ext i j
    simp only [submatrix_apply, Function.comp_apply, OrderIso.coe_toEquiv,
      coe_orderIsoOfFin_apply, hσ T hT, orderShuffle_orderEmbOfFin]
  have h₂ : (A.submatrix ((↑) : ↥Sᶜ → n) (σ T ∘ (↑))).submatrix
      (Sᶜ.orderIsoOfFin hSc).toEquiv (Sᶜ.orderIsoOfFin hSc).toEquiv =
        A.submatrix (Sᶜ.orderEmbOfFin hSc)
          (Tᶜ.orderEmbOfFin (card_compl_eq_of_card_eq hS hSc hT)) := by
    ext i j
    simp only [submatrix_apply, Function.comp_apply, OrderIso.coe_toEquiv,
      coe_orderIsoOfFin_apply, hσ T hT, orderShuffle_orderEmbOfFin_compl]
  rw [← det_submatrix_equiv_self (S.orderIsoOfFin hS).toEquiv, h₁,
    ← det_submatrix_equiv_self (Sᶜ.orderIsoOfFin hSc).toEquiv, h₂, hσ T hT, sign_orderShuffle]
  push_cast
  rfl

end LinearOrder

private theorem card_compl_fin {N : ℕ} {S : Finset (Fin N)} {k : ℕ} (hS : #S = k) :
    #Sᶜ = N - k := by
  rw [card_compl, Fintype.card_fin, hS]

/-- **Generalized Laplace expansion** of a determinant indexed by `Fin N` along the set of rows
`S`, with the minors indexed increasingly and the sign `(-1) ^ (∑ i ∈ S, i + ∑ j ∈ T, j)`. -/
theorem det_eq_sum_neg_one_pow_mul_det_mul_det_fin {N : ℕ} (A : Matrix (Fin N) (Fin N) R)
    {k : ℕ} (S : Finset (Fin N)) (hS : #S = k) :
    A.det = ∑ T : {T : Finset (Fin N) // #T = k},
      (-1) ^ (∑ i ∈ S, (i : ℕ) + ∑ j ∈ T.val, (j : ℕ)) *
        (A.submatrix (S.orderEmbOfFin hS) (T.val.orderEmbOfFin T.property)).det *
        (A.submatrix (Sᶜ.orderEmbOfFin (k := N - k) (by rw [card_compl, Fintype.card_fin, hS]))
          (T.valᶜ.orderEmbOfFin (k := N - k)
            (by rw [card_compl, Fintype.card_fin, T.property]))).det := by
  have hpos (a : Fin N) : #{b | b < a} = (a : ℕ) := by
    rw [← Fin.card_Iio]
    congr 1
    ext
    simp
  simpa only [hpos] using det_eq_sum_neg_one_pow_mul_det_mul_det A S hS (card_compl_fin hS)

end Matrix
