/-
Copyright (c) 2026 Anders Lewis, Grant Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anders Lewis, Grant Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Jacobi's complementary minor theorem and the Desnanot–Jacobi identity

Jacobi's complementary minor theorem relates the minors of the adjugate of a matrix `M` to the
complementary minors of `M`. We prove it for principal minors: for a nonempty set `S` of indices,
`det adj(M)[S, S] = det M ^ (#S - 1) * det M[Sᶜ, Sᶜ]`. The case `#S = 2` is the
**Desnanot–Jacobi identity** (also known as Dodgson condensation or the Lewis Carroll identity),
which we state in adjugate form for any two distinct indices `i ≠ j`:
`adj(M) i i * adj(M) j j - adj(M) i j * adj(M) j i = det M * det M[{i, j}ᶜ, {i, j}ᶜ]`.

Here `S` is given by a predicate `p`, and minors are `Matrix.submatrix (↑) (↑)` on subtypes.

## Main results

* `Matrix.det_mul_det_adjugate_submatrix`: `det M * det adj(M)[S, S] = det M ^ #S * det M[Sᶜ, Sᶜ]`.
* `Matrix.det_adjugate_submatrix`: Jacobi's complementary minor theorem for principal minors.
* `Matrix.adjugate_mul_adjugate_sub_adjugate_mul_adjugate`: the Desnanot–Jacobi identity.

## Implementation notes

Let `C` be the identity matrix with the columns in `S` replaced by those of `adj(M)`. Both `C`
and `M * C` are block triangular with respect to `S`, so `det C = det adj(M)[S, S]` and
`det (M * C) = det M ^ #S * det M[Sᶜ, Sᶜ]`. This gives the identity multiplied by `det M`. To
cancel `det M`, we prove the identity for the generic matrix `Matrix.mvPolynomialX`, whose
determinant is a nonzero element of an integral domain, and specialize.

## References

* D. M. Bressoud, *Proofs and Confirmations: The Story of the Alternating Sign Matrix
  Conjecture*, Cambridge University Press, 1999.
* https://en.wikipedia.org/wiki/Dodgson_condensation
-/

public section

variable {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]

namespace Matrix

/-- The identity matrix with the columns in `S` replaced by those of `adjugate M`. -/
private def adjugateCols (M : Matrix n n R) (p : n → Prop) [DecidablePred p] : Matrix n n R :=
  of fun k l ↦ if p l then M.adjugate k l else if k = l then 1 else 0

private theorem adjugateCols_apply (M : Matrix n n R) (p : n → Prop) [DecidablePred p] (k l : n) :
    adjugateCols M p k l = if p l then M.adjugate k l else if k = l then 1 else 0 :=
  rfl

private theorem det_adjugateCols (M : Matrix n n R) (p : n → Prop) [DecidablePred p] :
    (adjugateCols M p).det = ((adjugate M).submatrix ((↑) : {k // p k} → n) (↑)).det := by
  rw [twoBlockTriangular_det' _ p]
  · have h : (adjugateCols M p).toSquareBlockProp (fun k ↦ ¬p k) = 1 := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp [adjugateCols_apply, toSquareBlockProp_def, hb, Matrix.one_apply, Subtype.ext_iff]
    rw [h, det_one, mul_one]
    congr 1
    ext ⟨a, ha⟩ ⟨b, hb⟩
    simp [adjugateCols_apply, toSquareBlockProp_def, hb]
  · intro k hk l hl
    have hkl : k ≠ l := by rintro rfl; exact hl hk
    simp [adjugateCols_apply, hl, hkl]

private theorem det_mul_adjugateCols (M : Matrix n n R) (p : n → Prop) [DecidablePred p] :
    (M * adjugateCols M p).det =
      M.det ^ Fintype.card {k // p k} * (M.submatrix ((↑) : {k // ¬p k} → n) (↑)).det := by
  have happly (k l : n) : (M * adjugateCols M p) k l =
      if p l then (M.det • (1 : Matrix n n R)) k l else M k l := by
    by_cases hl : p l
    · simp only [Matrix.mul_apply, adjugateCols_apply, hl, ite_true]
      rw [← Matrix.mul_apply, mul_adjugate]
    · simp [Matrix.mul_apply, adjugateCols_apply, hl]
  rw [twoBlockTriangular_det _ p]
  · have h₁ : (M * adjugateCols M p).toSquareBlockProp p = M.det • (1 : Matrix _ _ R) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp [toSquareBlockProp_def, happly, hb, Matrix.one_apply]
    have h₂ : (M * adjugateCols M p).toSquareBlockProp (fun k ↦ ¬p k) =
        M.submatrix (↑) (↑) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp [toSquareBlockProp_def, happly, hb]
    rw [h₁, h₂, det_smul, det_one, mul_one]
  · intro k hk l hl
    have hkl : k ≠ l := by rintro rfl; exact hk hl
    simp [happly, hl, hkl]

/-- **Jacobi's complementary minor theorem** for principal minors, multiplied by `det M`:
`det M * det adj(M)[S, S] = det M ^ #S * det M[Sᶜ, Sᶜ]`. -/
theorem det_mul_det_adjugate_submatrix (M : Matrix n n R) (p : n → Prop) [DecidablePred p] :
    M.det * ((adjugate M).submatrix ((↑) : {k // p k} → n) (↑)).det =
      M.det ^ Fintype.card {k // p k} * (M.submatrix ((↑) : {k // ¬p k} → n) (↑)).det := by
  rw [← det_adjugateCols, ← det_mul, det_mul_adjugateCols]

/-- **Jacobi's complementary minor theorem** for principal minors: for a nonempty set `S`,
`det adj(M)[S, S] = det M ^ (#S - 1) * det M[Sᶜ, Sᶜ]`. -/
theorem det_adjugate_submatrix (M : Matrix n n R) (p : n → Prop) [DecidablePred p]
    (hp : ∃ i, p i) :
    ((adjugate M).submatrix ((↑) : {k // p k} → n) (↑)).det =
      M.det ^ (Fintype.card {k // p k} - 1) * (M.submatrix ((↑) : {k // ¬p k} → n) (↑)).det := by
  have hcard : Fintype.card {k // p k} = Fintype.card {k // p k} - 1 + 1 := by
    obtain ⟨i, hi⟩ := hp
    have : 0 < Fintype.card {k // p k} := Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
    omega
  let A := mvPolynomialX n n ℤ
  suffices ((adjugate A).submatrix ((↑) : {k // p k} → n) (↑)).det =
      A.det ^ (Fintype.card {k // p k} - 1) * (A.submatrix ((↑) : {k // ¬p k} → n) (↑)).det by
    let f := MvPolynomial.aeval (R := ℤ) fun q : n × n ↦ M q.1 q.2
    have hA : f.mapMatrix A = M := mvPolynomialX_mapMatrix_aeval ℤ M
    have h := congrArg f this
    simp only [map_mul, map_pow, AlgHom.map_det] at h
    rw [← hA, ← AlgHom.map_adjugate]
    exact h
  refine mul_left_cancel₀ (det_mvPolynomialX_ne_zero n ℤ) ?_
  rw [det_mul_det_adjugate_submatrix, ← mul_assoc, ← pow_succ', ← hcard]

/-- The **Desnanot–Jacobi identity** (Dodgson condensation), in adjugate form: for `i ≠ j`,
`adj(M) i i * adj(M) j j - adj(M) i j * adj(M) j i = det M * det M[{i, j}ᶜ, {i, j}ᶜ]`. -/
theorem adjugate_mul_adjugate_sub_adjugate_mul_adjugate (M : Matrix n n R) {i j : n}
    (hij : i ≠ j) :
    M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i =
      M.det * (M.submatrix ((↑) : {k // k ≠ i ∧ k ≠ j} → n) (↑)).det := by
  have h := det_adjugate_submatrix M (fun k ↦ k = i ∨ k = j) ⟨i, .inl rfl⟩
  have hl : [i, j].Nodup := by simpa
  let e : Fin 2 ≃ {k // k = i ∨ k = j} :=
    (hl.getEquiv [i, j]).trans (Equiv.subtypeEquivRight fun x ↦ by simp)
  have hcard : Fintype.card {k // k = i ∨ k = j} = 2 := by
    rw [← Fintype.card_fin 2, Fintype.card_congr e]
  rw [← det_submatrix_equiv_self e, det_fin_two, hcard] at h
  have h₂ : (M.submatrix ((↑) : {k // ¬(k = i ∨ k = j)} → n) (↑)).det =
      (M.submatrix ((↑) : {k // k ≠ i ∧ k ≠ j} → n) (↑)).det := by
    rw [← det_submatrix_equiv_self (Equiv.subtypeEquivRight fun _ ↦ not_or).symm]
    rfl
  calc _ = _ := by simp [e, List.Nodup.getEquiv]
    _ = _ := h
    _ = _ := by rw [h₂, pow_one]

end Matrix
