# Upstreaming report: Determinantal-Polynomials → mathlib4

Date: 2026-11-24. Base: mathlib `master` at `zyrtooxn` / `d909317e0a29`
(`feat(Combinatorics/SimpleGraph/Girth): relate girth and egirth (#41380)`), toolchain
`leanprover/lean4:v4.37.0-rc1`.

This file only exists in the **test merge commit** (see §2). It is not part of any PR.

Source: `../Determinant-Polynomials`, branches `grant` (`d3c99d02fdcf`) and `grant-clean`
(`04dbb93bff76`). Files used:

| source file (branch) | used for |
|---|---|
| `DetPoly/JacobiFormula.lean` (`grant`) | PRs 1, 2 |
| `DetPoly/PrincipalCofactors.lean` (`grant`) | PR 3 |
| `LEAN_Warmup/Grant/Laplace.lean` (`grant`) | PR 4 |
| `DetPoly/RankOne.lean` (`grant-clean`) | PRs 5, 6, 7 |
| `LEAN_Warmup/Grant/GeneralizedLaplace.lean` (`grant`) | PRs 8, 9, 10 |
| `DetPoly/DesnanotJacobi.lean` (both branches, identical; author Anders Lewis) | PR 11 |
| `DetPoly/Basic.lean` (`Matrix.det_diagonal_add`) | PR 12 |

---

## 1. Summary

12 jj commits, each intended as one mathlib PR, all local (nothing pushed, no bookmarks).
Every commit has a full mathlib-style commit message (title + body) to use as the PR
title/description, ending in `Co-Authored-By: Claude Opus 5.5`.

Verification done on the combined tree (the merge commit below):

* `lake build` of every touched module: succeeds, **no warnings** (this runs mathlib's syntax
  linters: line length, numeric projections, unclosed namespaces, unused simp args, ...).
* `lake exe runLinter <Module>` (the `#lint` environment linters: docstrings, simp-nf, unused
  arguments, ...) on all 9 touched modules: **passed**.
* `lake exe mk_all` run; `Mathlib.lean` includes the 3 new files.
* **Not done:** a full `lake build` of all of Mathlib (downstream of `Adjugate`, `Rank`,
  `Perm/Fin`, `Derivation/Basic` is large). New names were grepped for clashes, and the one risk
  (`Matrix.rank_eq_zero_iff` shadowing root `rank_eq_zero_iff` inside `namespace Matrix`) was
  checked by grep: no file in `namespace Matrix`/`open Matrix` uses the root name. CI will do the
  full build. Also not run: `lake test`, `scripts/lint-style`, the `shake`/import-cost tools.

---

## 2. Revisions

Change ids are stable across rewrites; commit ids are as of writing.

### Test merge commit

| change | contents |
|---|---|
| `qnpulvyp` | Merge of all 7 heads below + `lake exe mk_all` resolution of `Mathlib.lean` + this report. **Do not push / do not PR.** |

Parents: `pktrwtwz omuzrmqx vlvpnymk kwkospkt ktosyytn wznzuspw osqmttqo`.
To recreate after rewriting the PR commits: `jj new <those 7> && lake exe mk_all`.

### PR commits

"Parent" is `master` unless stated. Line counts are from `jj diff --stat`.

| # | change | commit | parent | files | title |
|---|---|---|---|---|---|
| 1 | `vyowsyww` | `326d733da5ed` | master | `RingTheory/Derivation/Basic.lean` (+13) | feat(RingTheory/Derivation/Basic): Leibniz rule for finite products |
| 2 | `osqmttqo` | `cb38d149b2c4` | #1 | new `LinearAlgebra/Matrix/Determinant/Derivation.lean` (+58 incl. `Mathlib.lean`) | feat(LinearAlgebra/Matrix/Determinant/Derivation): Jacobi's formula for derivations |
| 3 | `wqnppwly` | `a6146398e87e` | master | `LinearAlgebra/Matrix/Adjugate.lean` (+26) | feat(LinearAlgebra/Matrix/Adjugate): diagonal entries of the adjugate over any index type |
| 4 | `wznzuspw` | `6bc0378f147f` | #3 | `LinearAlgebra/Matrix/Adjugate.lean` (+68) | feat(LinearAlgebra/Matrix/Adjugate): Laplace expansion over an arbitrary index type |
| 5 | `mwvqlyxz` | `3e9f0e8e6049` | master | `LinearAlgebra/Matrix/SchurComplement.lean` (+35 −3) | feat(LinearAlgebra/Matrix/SchurComplement): matrix determinant lemma without invertibility |
| 6 | `ktosyytn` | `dd9eaf3d41f1` | #5 | `LinearAlgebra/Matrix/SchurComplement.lean` (+56) | feat(LinearAlgebra/Matrix/SchurComplement): determinants of blocks with rank-one corners |
| 7 | `kwkospkt` | `fb17e14eb744` | master | `LinearAlgebra/Matrix/Rank.lean` (+26) | feat(LinearAlgebra/Matrix/Rank): matrices of rank zero and at most one |
| 8 | `vttpooum` | `bf89cf1fb6cd` | master | new `LinearAlgebra/Matrix/Determinant/Laplace.lean` (+146 incl. `Mathlib.lean`) | feat(LinearAlgebra/Matrix/Determinant/Laplace): generalized Laplace expansion |
| 9 | `mvyumlsv` | `de8e73fad9a4` | master | `GroupTheory/Perm/Fin.lean` (+17) | feat(GroupTheory/Perm/Fin): sign of a permutation of a finite linear order |
| 10 | `vlvpnymk` | `b8ba1e79405c` | **#8 and #9** (jj merge) | `LinearAlgebra/Matrix/Determinant/Laplace.lean` (+230) | feat(LinearAlgebra/Matrix/Determinant/Laplace): generalized Laplace expansion in a linear order |
| 11 | `omuzrmqx` | `0083a7f8b336` | master | new `LinearAlgebra/Matrix/Determinant/ComplementaryMinor.lean` (+145 incl. `Mathlib.lean`) | feat(LinearAlgebra/Matrix/Determinant/ComplementaryMinor): Jacobi's complementary minor theorem and Desnanot–Jacobi |
| 12 | `pktrwtwz` | `29774b5309cc` | master | `LinearAlgebra/Matrix/Charpoly/Coeff.lean` (+24) | feat(LinearAlgebra/Matrix/Charpoly/Coeff): expand `det (diagonal x + A)` in principal minors |

Dependency graph:

```
master ─┬─ 1 ── 2
        ├─ 3 ── 4
        ├─ 5 ── 6
        ├─ 7
        ├─ 8 ─┐
        ├─ 9 ─┴─ 10
        ├─ 11
        └─ 12
```

Commits 2, 8 and 11 each add a line to `Mathlib.lean` at nearly the same place, so any two of
them conflict textually when combined. That only matters for the test merge: in the real PRs
each is rebased on `master` separately, and `lake exe mk_all` fixes it.

---

## 3. Contents of each commit

`R`/`α` is a `CommRing` and `n`, `m` are `Fintype` + `DecidableEq` unless stated.

### PR 1: `Derivation.leibniz_prod`

```lean
theorem Derivation.leibniz_prod {ι} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) • D (f i)
```
Placed after `leibniz_pow` in `RingTheory/Derivation/Basic.lean`. No new imports.

### PR 2: Jacobi's formula for derivations (new file `Determinant/Derivation.lean`)

```lean
theorem Derivation.leibniz_det (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j ↦ D (M i j)).det
theorem Derivation.leibniz_det_eq_sum_adjugate (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, ∑ j, M.adjugate j i * D (M i j)
```
The second statement (`tr (adj M · DM)`) is new. The source only had the row form.
Imports: `Matrix.Adjugate`, `RingTheory.Derivation.Basic`.

### PR 3: diagonal entries of the adjugate (`Adjugate.lean`)

```lean
theorem det_updateRow_single_self (A : Matrix n n α) (i : n) :
    (A.updateRow i (Pi.single i 1)).det = (A.submatrix (↑) ((↑) : {k // k ≠ i} → n)).det
theorem det_updateCol_single_self ...
theorem adjugate_apply_self (A : Matrix n n α) (i : n) :
    A.adjugate i i = (A.submatrix (↑) ((↑) : {k // k ≠ i} → n)).det
```
**Changed from source:** the source proof used `twoBlockTriangular_det`, but `Adjugate.lean`
doesn't import `Matrix.Block`. Reproved with `Equiv.sumCompl` + `det_fromBlocks_zero₁₂` so no
import is added. `adjugate_submatrix_apply_self` (the second-order principal cofactor) was not
ported; it's now a corollary of PR 11 if anyone needs it.

### PR 4: Laplace expansion over an arbitrary `Fintype` (`Adjugate.lean`)

```lean
theorem det_updateRow_single (A : Matrix n n α) (er ec : Option m ≃ n) :
    (A.updateRow (er none) (Pi.single (ec none) 1)).det =
      Perm.sign (er.symm.trans ec) * (A.submatrix (er ∘ some) (ec ∘ some)).det
theorem det_updateCol_single ...
theorem adjugate_apply_eq_det_submatrix (A : Matrix n n α) (er ec : Option m ≃ n) :
    A.adjugate (ec none) (er none) =
      Perm.sign (er.symm.trans ec) * (A.submatrix (er ∘ some) (ec ∘ some)).det
theorem adjugate_apply_eq_det_submatrix_swap (A : Matrix n n α) (i j : n) :
    A.adjugate i j = Perm.sign (swap j i) *
      (A.submatrix (↑) fun k : {k // k ≠ j} ↦ swap j i k).det
theorem det_eq_sum_mul_det_submatrix_row (A : Matrix n n α) (i : n) :
    A.det = ∑ j, Perm.sign (swap i j) * A i j *
      (A.submatrix (↑) fun k : {k // k ≠ i} ↦ swap i j k).det
theorem det_eq_sum_mul_det_submatrix_col ...
```
**Changed from source:** dropped the "family" versions
(`det_eq_sum_mul_det_submatrix_row` taking `ec : n → Option m ≃ n` with `hec : ∀ j, ec j none = j`).
They're awkward to use, and the same result follows from `det_eq_sum_mul_adjugate_row` plus
`adjugate_apply_eq_det_submatrix`. The swap versions took over the plain names.

### PR 5: matrix determinant lemma without invertibility (`SchurComplement.lean`)

```lean
theorem det_add_vecMulVec (A : Matrix m m α) (u v : m → α) :
    (A + vecMulVec u v).det = A.det + v ⬝ᵥ A.adjugate *ᵥ u
```
This **completes an existing TODO** in the docstring of `det_add_replicateCol_mul_replicateRow`
("show the more general version without `hA : IsUnit A.det`"). The TODO text is replaced by a
pointer to the new lemma (that's the `−3` in the diff).

### PR 6: blocks with rank-one corners (`SchurComplement.lean`)

```lean
theorem adjugate_fromBlocks_vecMulVec_apply₁₂ (A : Matrix m m α) (C : Matrix n m α)
    (D : Matrix n n α) (u : m → α) (v : n → α) (i : m) (j : n) :
    (fromBlocks A (vecMulVec u v) C D).adjugate (.inl i) (.inr j) =
      -((A.updateCol i u).det * (D.updateRow j v).det)
theorem det_fromBlocks_vecMulVec (A : Matrix m m α) (D : Matrix n n α) (p v : m → α)
    (q u : n → α) :
    (fromBlocks A (vecMulVec p q) (vecMulVec u v) D).det =
      A.det * D.det - (v ⬝ᵥ A.adjugate *ᵥ p) * (q ⬝ᵥ D.adjugate *ᵥ u)
```

### PR 7: rank zero / rank at most one (`Rank.lean`, `section Field`)

```lean
@[simp] theorem rank_eq_zero_iff [Finite n] {A : Matrix m n R} : A.rank = 0 ↔ A = 0
theorem rank_pos_iff [Finite n] {A : Matrix m n R} : 0 < A.rank ↔ A ≠ 0
theorem rank_le_one_iff_exists_eq_vecMulVec [Finite n] {A : Matrix m n R} :
    A.rank ≤ 1 ↔ ∃ u v, A = vecMulVec u v
```
**Changed from source:** `one_le_rank_of_apply_ne_zero` became the more standard pair
`rank_eq_zero_iff` / `rank_pos_iff`. The source used `rank_eq_finrank_span_cols`, which is
deprecated (2026-10-21), so the port uses `finrank_span_range_col`.

### PR 8: generalized Laplace expansion (new file `Determinant/Laplace.lean`)

Over any index type, matching rows and columns by permutations:
```lean
theorem sum_sign_mul_prod_eq_det_mul_det (A : Matrix n n R) (S : Finset n) :
    ∑ ρ : Perm n with S.map ρ.toEmbedding = S, (Perm.sign ρ : R) * ∏ i, A i (ρ i) =
      (A.submatrix ((↑) : S → n) (↑)).det * (A.submatrix ((↑) : ↥Sᶜ → n) (↑)).det
theorem sum_sign_mul_prod_eq_sign_mul_det_mul_det (A) (S) (σ : Perm n) : ...
theorem sign_mul_det_mul_det_eq_of_map_eq (A) (S) {σ τ : Perm n}
    (h : S.map σ.toEmbedding = S.map τ.toEmbedding) : ...
theorem det_eq_sum_sign_mul_det_mul_det_row (A : Matrix n n R) (S : Finset n)
    (σ : Finset n → Perm n) (hσ : ∀ T, #T = #S → S.map (σ T).toEmbedding = T) :
    A.det = ∑ T with #T = #S, Perm.sign (σ T) *
      (A.submatrix ((↑) : S → n) (σ T ∘ (↑))).det *
        (A.submatrix ((↑) : ↥Sᶜ → n) (σ T ∘ (↑))).det
theorem det_eq_sum_sign_mul_det_mul_det_col ...
```
Import: `Matrix.Block`.
**Changed from source:**
* Renamed `det_eq_sum_det_mul_det_row/col` → `det_eq_sum_sign_mul_det_mul_det_row/col`, since
  the term starts with the sign.
* Dropped `laplacePerm` (a `Classical.choose`-based def) and `det_eq_sum_laplacePerm_row/col`.
  Mathlib reviewers generally dislike choice-defined data with no characterizing API. Its helper
  `exists_perm_map_eq` was dropped too.
* No paper citation in the docstrings. Cites Wikipedia instead.

### PR 9: `Equiv.Perm.sign_eq_prod_prod_lt` (`GroupTheory/Perm/Fin.lean`)

```lean
theorem Equiv.Perm.sign_eq_prod_prod_lt {α} [Fintype α] [LinearOrder α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    σ.sign = ∏ b, ∏ a with a < b, if σ a < σ b then 1 else -1
```
**Adds `public import Mathlib.Data.Fintype.Sort`** to `GroupTheory/Perm/Fin.lean` (for
`monoEquivOfFin`). The import is light (`Data.Finset.Sort`), but see §5.

### PR 10: generalized Laplace in a linear order (`Determinant/Laplace.lean`)

Public additions:
```lean
theorem Finset.prod_orderEmbOfFin (S : Finset α) (f : α → M) :
    ∏ i : Fin #S, f (S.orderEmbOfFin rfl i) = ∏ a ∈ S, f a
theorem Finset.card_filter_lt_orderEmbOfFin (S : Finset α) (i : Fin #S) :
    #(S.filter (· < S.orderEmbOfFin rfl i)) = i
theorem Matrix.det_eq_sum_neg_one_pow_mul_det_mul_det [LinearOrder n] (A) {k m} (S)
    (hS : #S = k) (hSc : #Sᶜ = m) :
    A.det = ∑ T : {T : Finset n // #T = k},
      (-1) ^ (∑ a ∈ S, #{b | b < a} + ∑ a ∈ T.val, #{b | b < a}) *
        (A.submatrix (S.orderEmbOfFin hS) (T.val.orderEmbOfFin T.property)).det *
        (A.submatrix (Sᶜ.orderEmbOfFin hSc) (T.valᶜ.orderEmbOfFin (k := m) _)).det
theorem Matrix.det_eq_sum_neg_one_pow_mul_det_mul_det_fin (A : Matrix (Fin N) (Fin N) R) ...
    -- sign (-1) ^ (∑ i ∈ S, (i : ℕ) + ∑ j ∈ T.val, (j : ℕ))
```
Private helpers: `sign_eq_of_strictMonoOn`, `prod_prod_ite_lt_mul`, `card_compl_eq_of_card_eq`,
`orderShuffle` (+ 4 lemmas). Import added: `GroupTheory.Perm.Fin`.
**Changed from source:**
* Helpers made `private`. The source had them public in `Matrix`.
* `prod_orderEmbOfFin` and `card_filter_lt_orderEmbOfFin` moved to `Finset`.
* `T.1`/`T.2` became `T.val`/`T.property`, because mathlib's numeric-projection linter rejects
  `.1`/`.2` on `Subtype`.
* The cardinality proofs for the complement sizes are inline `by rw ...` terms with an explicit
  `(k := …)`. Without it, elaboration got stuck on a metavariable.

### PR 11: Jacobi's complementary minor theorem + Desnanot–Jacobi (new file `Determinant/ComplementaryMinor.lean`)

**This is a generalization, not a port.** The source proved only the 2×2 case. The same proof
(the "adjugate columns" matrix `C`, block triangularity, then cancelling `det M` via the generic
matrix `mvPolynomialX`) works for any principal set `S = {k | p k}`:

```lean
theorem det_mul_det_adjugate_submatrix (M : Matrix n n R) (p : n → Prop) [DecidablePred p] :
    M.det * ((adjugate M).submatrix ((↑) : {k // p k} → n) (↑)).det =
      M.det ^ Fintype.card {k // p k} * (M.submatrix ((↑) : {k // ¬p k} → n) (↑)).det
theorem det_adjugate_submatrix (M) (p) [DecidablePred p] (hp : ∃ i, p i) :
    ((adjugate M).submatrix ((↑) : {k // p k} → n) (↑)).det =
      M.det ^ (Fintype.card {k // p k} - 1) * (M.submatrix ((↑) : {k // ¬p k} → n) (↑)).det
theorem adjugate_mul_adjugate_sub_adjugate_mul_adjugate (M : Matrix n n R) {i j : n}
    (hij : i ≠ j) :
    M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i =
      M.det * (M.submatrix ((↑) : {k // k ≠ i ∧ k ≠ j} → n) (↑)).det
```
The Desnanot–Jacobi statement and name are the same as the source's. Private: `adjugateCols`,
`adjugateCols_apply`, `det_adjugateCols`, `det_mul_adjugateCols`. The source's public helper
`det_toSquareBlockProp_pair` was not ported; its use is inlined with `List.Nodup.getEquiv` +
`det_fin_two`. Header: `Copyright (c) 2026 Anders Lewis, Grant Yang`, authors in that order.

### PR 12: `det (diagonal x + A)` (`Charpoly/Coeff.lean`)

```lean
theorem det_diagonal_add (x : n → R) (A : Matrix n n R) :
    (diagonal x + A).det = ∑ s : Finset n, (∏ i ∈ s, x i) * (A.submatrix ((↑) : ↥sᶜ → n) (↑)).det
theorem det_add_diagonal (A : Matrix n n R) (x : n → R) : (A + diagonal x).det = ...
```
Placed right after `det_piecewise_one_eq_submatrix_det`, which it uses. **Changed from source:**
the project's `principalMinor` is unfolded to `submatrix`, and the `add_diagonal` mirror is new.

---

## 4. Modifications still needed before opening PRs

1. **Authorship and copyright headers.** The new files say `Copyright (c) 2026 Grant Yang` (PRs
   2, 8/10) and `Anders Lewis, Grant Yang` (PR 11). The source headers say
   "University of Washington Math AI Lab". Mathlib wants the copyright holders' names, so confirm
   with the lab and with Anders. Shaoda Ji is credited on `RankOne.lean` in the source, but PRs
   5–7 edit existing files, which have no per-lemma authorship. Mention them in the PR
   description if appropriate.
2. **AI disclosure.** Mathlib's contribution guidelines require stating AI use in the PR
   description. The #37716 thread shows reviewers ask about it and watch for "AI-looking" code
   (long `have` chains, etc.). The commit messages end with `Co-Authored-By: Claude Opus 5.5`.
   Keep or drop that per the guidelines, but add an explicit sentence to each PR body.
3. **PR descriptions.** The commit bodies are written to be PR bodies. Add, for stacked PRs:
   * PR 2: `- [ ] depends on: #<PR 1>`
   * PR 4: `- [ ] depends on: #<PR 3>`
   * PR 6: `- [ ] depends on: #<PR 5>`
   * PR 10: `- [ ] depends on: #<PR 8>` and `- [ ] depends on: #<PR 9>`

   With jj, push each change as its own branch to your fork (e.g.
   `jj git push --change <id> --remote <fork>`). For a dependent PR, open it against `master`
   anyway: the diff then includes the parent, which is normal for mathlib, and the "depends on"
   line tells reviewers.
4. **PR 11 and the open PR #37716.** That PR (Desnanot–Jacobi, by `slavanaprienko`, new
   contributor, label `merge-conflict`, last activity 2026-07-28) proves the corner-entries form
   on `Fin (n+2)`. A reviewer (`kim-em`) asked for "deleting any two elements from the
   row/column index set (which need not even be `Fin n`)". The author replied that it was messier.
   PR 11 is exactly that form, and more general. Options:
   * comment on #37716 first, linking our version and offering to coordinate or co-author;
   * open PR 11 and mention #37716 in its description (it would supersede it);
   * hold PR 11.

   The kind option is to comment first. Reviewers will notice the overlap either way.
5. **Labels:** `t-algebra` for all. PR 1 is small enough for `easy`.
6. **Run once more after any rebase:** `lake build` of the touched modules (not just
   `lake env lean`, which skips the syntax linters) and `lake exe runLinter <Module>`.

---

## 5. Things likely to come up in review

### General
* **Proof style.** Several proofs are long `have` chains or `rcases … <;> simp [...] <;>
  split_ifs <;> simp_all` combos (PR 6 `adjugate_fromBlocks_vecMulVec_apply₁₂`, PR 5
  `det_add_vecMulVec`, PR 10 `sign_eq_of_strictMonoOn`). Expect golfing requests and possibly
  "non-terminal simp" complaints (`simp [...]` followed by more tactics).
* **The generic-matrix trick** (PR 11): standard in mathlib (`adjugate_adjugate`,
  `det_smul_adjugate_adjugate` use `mvPolynomialX`). Should be fine.
* **`Perm.sign σ * …`**: coerces `ℤˣ → ℤ → R` implicitly (`↑↑`). This matches `det_permute'`.

### PR 1/2
* A reviewer may ask for `leibniz_prod` in `Multiset`/`List` form too, or for
  `Derivation.leibniz_prod` with `(s.erase i).prod` written as `∏ j ∈ s with j ≠ i`. A
  `Finset.prod_univ`/`Fintype` corollary might be requested.
* The file name `Determinant/Derivation.lean` might be questioned. `RingTheory/Derivation/Matrix.lean`
  is an alternative. Link `derivative_det_one_add_X_smul` (`Charpoly/Coeff.lean`), which is the
  special case for `Polynomial.derivative`. A reviewer might ask to reprove it from the new lemma.

### PR 3/4
* **Naming.** `det_eq_sum_mul_det_submatrix_row` is close to the existing
  `det_eq_sum_mul_adjugate_row` and `det_eq_sum_column_mul_submatrix_succAbove_succAbove_det`
  (`Determinant/Misc.lean`). Reviewers may suggest names mentioning `swap`, or `laplace`.
* **The swap matching is a design choice.** `sign (swap j i)` is `-1` for `i ≠ j` and `1` for
  `i = j`. Someone may suggest stating `adjugate_apply_eq_det_submatrix_swap` with
  `if i = j then 1 else -1`, or splitting into `i = j` (already `adjugate_apply_self`) and
  `i ≠ j` (sign `-1`). The current form keeps the uniform statement used by the Laplace sum.
* Using `Option m ≃ n` for "a matrix with one row deleted" follows
  `detp_option_expand_row_none` (`SemiringInverse.lean`) and `Equiv.optionSubtypeNe`. A reviewer
  may prefer `Equiv.optionSubtypeNe` built in.
* `adjugate_fin_succ_eq_det_submatrix` could be reproved from `adjugate_apply_eq_det_submatrix`.
  A reviewer may request that, or the reverse (no new proof machinery).
* `det_updateRow_single_self` generalizes to `Pi.single i c` (gives `c * minor`). Might be asked.

### PR 5/6
* There may be a request to derive the old `det_add_replicateCol_mul_replicateRow` from the new
  lemma, or to deprecate it.
* Alternative proof of `det_add_vecMulVec`: generic matrix + the invertible version. That's
  shorter, but heavier imports.
* `det_fromBlocks_vecMulVec` puts `(v ⬝ᵥ A.adjugate *ᵥ p) * (q ⬝ᵥ D.adjugate *ᵥ u)`. Note the
  asymmetric roles of `p q u v`, which the docstring explains. Variable naming may get
  bikeshedded.
* A reviewer might ask why these live in `SchurComplement.lean`. Answer: they sit next to the
  invertible versions `det_fromBlocks₁₁` and `det_add_replicateCol_mul_replicateRow`.

### PR 7
* `rank_eq_zero_iff` is `@[simp]`. Check that the simp-normal-form linter is happy (it was:
  `runLinter` passed).
* Name `rank_le_one_iff_exists_eq_vecMulVec`: reviewers may want `exists_vecMulVec` order or an
  `rank_le_one_iff` short name.
* Only over a field. Over a domain it's false for `rank_le_one_iff` in general (torsion-free but
  non-principal), so keep it as is.

### PR 8/10 (generalized Laplace)
* **The hypothesis-family statement** `(σ : Finset n → Perm n) (hσ : …)` is unusual. Alternatives
  reviewers might propose:
  * sum over `T ∈ univ.powersetCard #S` instead of `with #T = #S`, matching
    `coeff_det_one_add_X_smul_eq_sum_minors`, which uses `powersetCard`;
  * take bijections `e T : S ≃ T` and `f T : Sᶜ ≃ Tᶜ` as data and use
    `sign (Equiv.subtypeCongr …)`. That's arguably more natural than a permutation of `n`;
  * state with `Finset` index types for the minors directly, without a matching.
* The ordered form's statement uses `{T : Finset n // #T = k}` and `orderEmbOfFin`. It's verbose,
  but it's the only way to write "increasingly indexed minors" in mathlib today. The inline
  `by rw` proofs inside the statement may be disliked. An alternative is a public lemma
  `Finset.card_compl_eq_of_card_eq`.
* `#{b | b < a}` as "position" vs `Finset.Iio a` (needs `LocallyFiniteOrderBot`). The filter form
  avoids an extra class.
* `Finset.prod_orderEmbOfFin` / `card_filter_lt_orderEmbOfFin` may belong in
  `Data/Finset/Sort.lean`, where `orderEmbOfFin` lives. Reviewers will likely ask to move them,
  or to split them into a tiny separate PR.
* The private `orderShuffle` could be a public, reusable `Equiv` (`finSumEquivOfFinset`-based).

### PR 9
* Import change to `GroupTheory/Perm/Fin.lean`. Reviewers may prefer putting the lemma in a file
  that already imports `Data.Fintype.Sort`, or in a new `GroupTheory/Perm/Sign/…` file. The
  linear-order version could also be proved directly with `signAux`-style arguments, with no
  `Fin` detour.

### PR 11
* `p : n → Prop` + subtypes vs `S : Finset n` + `↥S`/`↥Sᶜ`. PR 8 uses `Finset`, so for
  consistency a reviewer may want one or the other everywhere.
* `det_adjugate_submatrix` with `p = ⊤` should recover `det_adjugate` (with
  `det` of a `0×0` matrix `= 1`). A reviewer may ask for that as a sanity check or to reprove
  `det_adjugate`. The `#S = 1` case recovers `adjugate_apply_self` (PR 3).
* The overlap with #37716 (§4.4).

### PR 12
* A reviewer may ask to reprove `coeff_det_one_add_X_smul_eq_sum_minors` from it (it is the
  specialization `x = X`), or the other way round. The proof is short and uses the same
  `detRowAlternating.map_add_univ` technique as the existing lemma.
* Placement: `Charpoly/Coeff.lean` is heavy (polynomial imports) for a statement with no
  polynomials. `Determinant/Basic.lean` or `Determinant/Misc.lean` can't host it, because it uses
  `det_piecewise_one_eq_submatrix_det`. Moving that helper up would let both move.

---

## 6. Possible extensions / follow-ups

* **Non-principal Jacobi complementary minor theorem:**
  `det adj(M)[I, J] = ± det M ^ (#I - 1) · det M[Jᶜ, Iᶜ]` for `#I = #J`. Same proof, with the
  sign handled like PR 8 (permutation matching). Together with PR 11 this would fully subsume
  #37716 and the "general complementary minors form" you mentioned.
* **Cauchy–Binet:** several closed attempts (#40473, #44209, #46341 closed 2026-11-24). The
  generalized Laplace machinery (sign-of-matching + `powersetCard`) is closely related and could
  support a fresh attempt.
* **Multivariate Jacobi formula for `MvPolynomial.pderiv`:** corollary of PR 2. The project's
  `Theorem2_3.lean` (`pderiv_detpoly`, `pderiv_pderiv_detpoly`) needs it.
* **Rank-`k` factorization:** `A.rank ≤ k ↔ ∃ B C, A = B * C` with inner dimension `Fin k`
  (generalizes PR 7).
* **Rank-`k` matrix determinant lemma** (`det (A + U V)` without invertibility) via Cauchy–Binet.
* **Multiaffinity of `det (diagonal X + A)`** in `MvPolynomial` (`detpoly_mem_restrictDegree`
  and `coeff_detpoly` in `DetPoly/Basic.lean`). This builds on PR 12 and is general enough for
  mathlib if phrased without `detpoly`.
* **`BlockTriangular.det_eq_det`** (`DetPoly/IrreducibleMatrix.lean`): two block-triangular
  matrices that agree on diagonal blocks have equal determinants. Small and general, a good
  quick PR.
* **`Matrix.submatrix_sumCompl_eq_fromBlocks`** (`DetPoly/Basic.lean`): trivial `rfl` lemma.
  Check whether mathlib already has an equivalent (`toBlocks`/`Equiv.sumCompl` API).

### Not proposed (and why)
* **Irreducible matrices over a ring** (`DetPoly/IrreducibleMatrix.lean`): mathlib already has
  `Matrix.IsIrreducible` (`LinearAlgebra/Matrix/Irreducible/Defs.lean`), but for **nonnegative
  matrices over an ordered ring** (positive-entry quiver, Perron–Frobenius). The project's notion
  (nonzero-pattern quiver, any ring) would clash in name and meaning, so it needs a design
  discussion on Zulip first.
* **`DiagSimilar`/`DiagEquivalent`, cut-transposes, `rayleighDiff`, `detpoly`/`principalMinor`:**
  project-specific notation and too specialized for now.
* **Shaoda's files** (`Lemma3_2_Shaoda`, `Lemma4_3_Shaoda`, counterexample): warmup-style, `Fin n`,
  not mathlib-ready.

---

## 7. Related existing work found

* mathlib4 PR #37716, "feat(LinearAlgebra/Matrix/Determinant): Desnanot-Jacobi identity" (open,
  merge conflicts): https://github.com/leanprover-community/mathlib4/pull/37716. It links the
  Zulip thread "Determinantal identity and the Cauchy matrix determinant" in `#Is there code for X?`.
* Cauchy–Binet PRs (all closed, not merged): #40473, #44209, #46341, #44757.
* Matrix determinant lemma history: #7086 (merged 2024, the invertible version, source of the
  TODO resolved by PR 5). Sherman–Morrison #34875 (open).
* Zulip "Determinant for low rank":
  https://leanprover-community.github.io/archive/stream/116395-maths/topic/Determinant.20for.20low.20rank.html
* No GitHub PRs or Zulip threads found for: generalized Laplace expansion, Laplace over a
  `Fintype`, Jacobi's formula for derivations, `Derivation.leibniz_prod`, rank ≤ 1 iff outer
  product.
* Darij Grinberg's algebraic-combinatorics blueprint also formalizes Desnanot–Jacobi (outside
  mathlib): https://faabian.github.io/algebraic-combinatorics/docs/AlgebraicCombinatorics/DesnanotJacobi.html

---

## 8. Practical notes

* `lake env lean <file>` checks a file without running mathlib's syntax linters and needs its
  imports built (`lake build <Dep>` after editing an upstream file). Use `lake build <Module>`
  for the real check, plus `lake exe runLinter <Module>`.
* `Matrix.mul_apply` and `Matrix.one_apply` are `protected`: inside `namespace Matrix`, bare
  `mul_apply` resolves to a different root lemma and fails in confusing ways ("function expected").
* To edit a PR commit while on the merge: make the change in the merge working copy and run
  `jj absorb`. It moves hunks into the commit that last touched those lines. Used here for the
  `end Derivation` / `end Matrix` fixes.
* Local notes for Claude are in `CLAUDE.md` (untracked, excluded via `.git/info/exclude`).
