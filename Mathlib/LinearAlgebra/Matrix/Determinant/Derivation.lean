/-
Copyright (c) 2026 Grant Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Jacobi's formula for derivations

For a derivation `D` of a commutative ring `A` and a square matrix `M` over `A`, `D (det M)` is
the sum over the rows `i` of the determinant of `M` with row `i` replaced by its image under `D`.
Equivalently, `D (det M) = ∑ i j, adj(M) j i * D (M i j)`, i.e. `D (det M) = tr (adj(M) D(M))`.

Applied to `MvPolynomial.pderiv`, this is the multivariate Jacobi formula.

## Main results

* `Derivation.leibniz_det`: `D (det M) = ∑ i, det (M with row i replaced by D (M i ·))`.
* `Derivation.leibniz_det_eq_sum_adjugate`: `D (det M) = ∑ i, ∑ j, adj(M) j i * D (M i j)`.
-/

public section

open Finset Matrix

namespace Derivation

variable {R A n : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq n] [Fintype n]

/-- **Jacobi's formula** for a derivation: `D (det M)` is the sum over the rows `i` of the
determinant of `M` with row `i` differentiated. -/
theorem leibniz_det (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j ↦ D (M i j)).det := by
  simp only [det_apply, map_sum, Units.smul_def, map_zsmul, D.leibniz_prod, smul_sum]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun σ _ ↦ ?_
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← mul_prod_erase univ _ (mem_univ j), updateRow_self, smul_eq_mul, mul_comm]
  exact congrArg _ <| congrArg _ <| prod_congr rfl fun k hk ↦
    (congrFun (updateRow_ne (σ.injective.ne (ne_of_mem_erase hk))) k).symm

/-- **Jacobi's formula** for a derivation, in terms of the adjugate:
`D (det M) = ∑ i j, adj(M) j i * D (M i j)`, the trace of `adj(M) * D(M)`. -/
theorem leibniz_det_eq_sum_adjugate (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, ∑ j, M.adjugate j i * D (M i j) := by
  rw [leibniz_det]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose, mulVec,
    dotProduct]
  simp

end Derivation
