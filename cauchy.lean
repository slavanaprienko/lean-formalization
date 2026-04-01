/-
Copyright (c) 2026 Slava Naprienko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Slava Naprienko
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import MyProject.dj

/-!
# The Cauchy matrix determinant

This file proves that the determinant of the Cauchy matrix
`C_{ij} = (x_i + y_j)⁻¹` equals the Cauchy product
`det(C) = (∏_{i < j} (x_i - x_j)(y_i - y_j)) / ∏_{i, j} (x_i + y_j)`.

The proof uses strong induction on the matrix size `n`. The inductive
step employs the **Desnanot–Jacobi identity** (Dodgson condensation) to
reduce the determinant of an `(n+2) × (n+2)` Cauchy matrix to a
combination of its `(n+1) × (n+1)` and `n × n` minors.

## Main definitions

* `cauchyMatrix`: the matrix with entries `(x_i + y_j)⁻¹`.
* `diffProd`: the product `∏_{i < j} (x_i - x_j)`.
* `sumProd`: the product `∏_{i, j} (x_i + y_j)`.
* `cauchyProd`: the ratio `(diffProd x * diffProd y) / sumProd x y`.

## Main results

* `cauchyMatrix_det`: the determinant of the Cauchy matrix equals
  `cauchyProd x y`, assuming `∀ i j, x i + y j ≠ 0`.
-/

open Finset

variable {F : Type*} [Field F]

/-- The product of pairwise differences `∏_{i < j} (x_i - x_j)`. -/
noncomputable def diffProd {n : ℕ} (x : Fin n → F) : F :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then (x i - x j) else 1

/-- The product of all sums `∏_{i, j} (x_i + y_j)`. -/
noncomputable def sumProd {n : ℕ} (x y : Fin n → F) : F :=
  ∏ i : Fin n, ∏ j : Fin n, (x i + y j)

/-- The closed-form value of the Cauchy determinant:
`(diffProd x * diffProd y) / sumProd x y`. -/
noncomputable def cauchyProd {n : ℕ} (x y : Fin n → F) : F :=
  (diffProd x * diffProd y) / sumProd x y

@[simp]
lemma succ_castSucc_eq_castSucc_succ {m : ℕ} (i : Fin m) :
    i.succ.castSucc = (i.castSucc.succ : Fin (m + 2)) := by
  rfl

/-! ## Decomposition of `sumProd` and `diffProd`

The lemmas in this section decompose `sumProd` and `diffProd` of size
`n + 2` into boundary factors (involving `x 0`, `x (Fin.last _)`,
`y 0`, `y (Fin.last _)`) and an interior part of size `n`.
-/

/-- Split a product over `Fin (n + 2)` into the first element, the
interior elements `{1, …, n}`, and the last element. -/
private lemma prod_split_first_last {n : ℕ} {M : Type*} [CommMonoid M]
    (f : Fin (n + 2) → M) :
    ∏ i : Fin (n + 2), f i =
      f 0 * (∏ i : Fin n, f i.castSucc.succ) * f (Fin.last (n + 1)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc, Fin.succ_last, mul_assoc]

private lemma sumProd_corners_walls {n : ℕ} (x y : Fin (n + 2) → F) :
    sumProd x y =
      (x 0 + y 0) * (x 0 + y (Fin.last (n + 1))) *
      (x (Fin.last (n + 1)) + y 0) * (x (Fin.last (n + 1)) + y (Fin.last (n + 1))) *
      (∏ i : Fin n, (x 0 + y i.castSucc.succ)) *
      (∏ i : Fin n, (x i.castSucc.succ + y 0)) *
      (∏ i : Fin n, (x (Fin.last (n + 1)) + y i.castSucc.succ)) *
      (∏ i : Fin n, (x i.castSucc.succ + y (Fin.last (n + 1)))) *
      sumProd (fun i => x i.castSucc.succ) (fun i => y i.castSucc.succ) := by
  unfold sumProd
  simp_rw [prod_split_first_last, Finset.prod_mul_distrib]
  ring

private lemma diffProd_corners_walls {n : ℕ} (x : Fin (n + 2) → F) :
    diffProd x =
      (x 0 - x (Fin.last (n + 1))) *
      (∏ i : Fin n, (x 0 - x i.castSucc.succ)) *
      (∏ i : Fin n, (x i.castSucc.succ - x (Fin.last (n + 1)))) *
      diffProd (fun i => x i.castSucc.succ) := by
  unfold diffProd
  rw [prod_split_first_last]
  -- The last-row product vanishes: Fin.last is maximal, so every conditional is false.
  have h_row_last : (∏ j : Fin (n + 2),
      if Fin.last (n + 1) < j then x (Fin.last (n + 1)) - x j else 1) = 1 :=
    Finset.prod_eq_one fun j _ => if_neg (not_lt.mpr (Fin.le_last j))
  rw [h_row_last, mul_one]
  -- The first-row product splits via prod_split_first_last on columns.
  have h_row0 : (∏ j : Fin (n + 2),
      if (0 : Fin (n + 2)) < j then x 0 - x j else 1) =
      (∏ i : Fin n, (x 0 - x i.castSucc.succ)) *
      (x 0 - x (Fin.last (n + 1))) := by
    rw [prod_split_first_last, if_neg (lt_irrefl 0), one_mul]
    congr 1
  rw [h_row0]
  -- Each interior row's inner product splits the same way.
  have h_interior : (∏ i : Fin n, ∏ j : Fin (n + 2),
      if i.castSucc.succ < j then x i.castSucc.succ - x j else 1) =
      (∏ i : Fin n, ∏ j : Fin n,
        if i < j then x i.castSucc.succ - x j.castSucc.succ else 1) *
      (∏ i : Fin n, (x i.castSucc.succ - x (Fin.last (n + 1)))) := by
    have h_inner (i : Fin n) : (∏ j : Fin (n + 2),
        if i.castSucc.succ < j then x i.castSucc.succ - x j else 1) =
        (∏ j : Fin n,
          if i < j then x i.castSucc.succ - x j.castSucc.succ else 1) *
        (x i.castSucc.succ - x (Fin.last (n + 1))) := by
      rw [prod_split_first_last, if_neg (Fin.not_lt_zero _), one_mul,
        if_pos (show i.castSucc.succ < Fin.last (n + 1) by
          rw [← Fin.succ_last, Fin.succ_lt_succ_iff]; exact Fin.castSucc_lt_last i)]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      have iff_lt : i.castSucc.succ < j.castSucc.succ ↔ i < j := by
        rw [Fin.succ_lt_succ_iff, Fin.castSucc_lt_castSucc_iff]
      simp only [iff_lt]
    simp_rw [h_inner, Finset.prod_mul_distrib]
  rw [h_interior]
  ring

/-! ### Submatrix decompositions of `sumProd`

Each of the four submatrices obtained by dropping one row index
(`0` or `last`) and one column index (`0` or `last`) gives an
`(n + 1) × (n + 1)` `sumProd` that factors into a single boundary
element, two boundary "wall" products, and the interior `n × n`
`sumProd`.  The proofs all follow the same pattern: peel the outer
product, peel each inner product, simplify compositions, distribute,
and close with `ring`.
-/

private lemma sumProd_00 {n : ℕ} (x y : Fin (n + 2) → F) :
    sumProd (x ∘ Fin.castSucc) (y ∘ Fin.castSucc) =
    (x 0 + y 0) * (∏ i : Fin n, (x 0 + y i.castSucc.succ)) *
    (∏ i : Fin n, (x i.castSucc.succ + y 0)) *
    sumProd (fun i => x i.castSucc.succ) (fun i => y i.castSucc.succ) := by
  unfold sumProd
  simp_rw [Fin.prod_univ_succ, Function.comp_apply, Fin.castSucc_zero,
    succ_castSucc_eq_castSucc_succ, Finset.prod_mul_distrib]
  ring

private lemma sumProd_nn {n : ℕ} (x y : Fin (n + 2) → F) :
    sumProd (x ∘ Fin.succ) (y ∘ Fin.succ) =
    (x (Fin.last (n + 1)) + y (Fin.last (n + 1))) *
    (∏ i : Fin n, (x (Fin.last (n + 1)) + y i.castSucc.succ)) *
    (∏ i : Fin n, (x i.castSucc.succ + y (Fin.last (n + 1)))) *
    sumProd (fun i => x i.castSucc.succ) (fun i => y i.castSucc.succ) := by
  unfold sumProd
  simp_rw [Fin.prod_univ_castSucc, Function.comp_apply, Fin.succ_last,
    Finset.prod_mul_distrib]
  ring

private lemma sumProd_n0 {n : ℕ} (x y : Fin (n + 2) → F) :
    sumProd (x ∘ Fin.succ) (y ∘ Fin.castSucc) =
    (x (Fin.last (n + 1)) + y 0) *
    (∏ i : Fin n, (x (Fin.last (n + 1)) + y i.castSucc.succ)) *
    (∏ i : Fin n, (x i.castSucc.succ + y 0)) *
    sumProd (fun i => x i.castSucc.succ) (fun i => y i.castSucc.succ) := by
  unfold sumProd
  rw [Fin.prod_univ_castSucc]
  simp_rw [Fin.prod_univ_succ, Function.comp_apply, Fin.succ_last,
    Fin.castSucc_zero, succ_castSucc_eq_castSucc_succ, Finset.prod_mul_distrib]
  ring

private lemma sumProd_0n {n : ℕ} (x y : Fin (n + 2) → F) :
    sumProd (x ∘ Fin.castSucc) (y ∘ Fin.succ) =
    (x 0 + y (Fin.last (n + 1))) *
    (∏ i : Fin n, (x 0 + y i.castSucc.succ)) *
    (∏ i : Fin n, (x i.castSucc.succ + y (Fin.last (n + 1)))) *
    sumProd (fun i => x i.castSucc.succ) (fun i => y i.castSucc.succ) := by
  unfold sumProd
  rw [Fin.prod_univ_succ]
  simp_rw [Fin.prod_univ_castSucc, Function.comp_apply, Fin.castSucc_zero,
    Fin.succ_last, succ_castSucc_eq_castSucc_succ, Finset.prod_mul_distrib]
  ring

/-! ### Submatrix decompositions of `diffProd` -/

private lemma diffProd_0 {n : ℕ} (x : Fin (n + 2) → F) :
    diffProd (x ∘ Fin.castSucc) =
    (∏ i : Fin n, (x 0 - x i.castSucc.succ)) *
    diffProd (fun i => x i.castSucc.succ) := by
  unfold diffProd
  rw [Fin.prod_univ_succ]
  have h_row0 : (∏ j : Fin (n + 1), if (0 : Fin (n + 1)) < j
      then (x ∘ Fin.castSucc) 0 - (x ∘ Fin.castSucc) j else 1) =
      ∏ i : Fin n, (x 0 - x i.castSucc.succ) := by
    rw [Fin.prod_univ_succ, if_neg (lt_irrefl 0), one_mul]
    exact Finset.prod_congr rfl fun j _ => by
      simp only [Fin.succ_pos, if_true, Function.comp_apply,
        succ_castSucc_eq_castSucc_succ, Fin.castSucc_zero]
  have h_rest : (∏ i : Fin n, ∏ j : Fin (n + 1), if i.succ < j
      then (x ∘ Fin.castSucc) i.succ - (x ∘ Fin.castSucc) j else 1) =
      diffProd (fun i => x i.castSucc.succ) := by
    unfold diffProd
    exact Finset.prod_congr rfl fun i _ => by
      rw [Fin.prod_univ_succ, if_neg (Fin.not_lt_zero _), one_mul]
      exact Finset.prod_congr rfl fun j _ => by
        simp only [Fin.succ_lt_succ_iff, Function.comp_apply,
          succ_castSucc_eq_castSucc_succ]
  rw [h_row0, h_rest]
  rfl

private lemma diffProd_n {n : ℕ} (x : Fin (n + 2) → F) :
    diffProd (x ∘ Fin.succ) =
    (∏ i : Fin n, (x i.castSucc.succ - x (Fin.last (n + 1)))) *
    diffProd (fun i => x i.castSucc.succ) := by
  unfold diffProd
  rw [Fin.prod_univ_castSucc]
  have h_last_prod : (∏ j : Fin (n + 1), if (Fin.last n) < j
      then (x ∘ Fin.succ) (Fin.last n) - (x ∘ Fin.succ) j else 1) = 1 :=
    Finset.prod_eq_one fun j _ => if_neg (not_lt_of_ge (Fin.le_last j))
  rw [h_last_prod, mul_one]
  have h_rest : (∏ i : Fin n, ∏ j : Fin (n + 1), if i.castSucc < j
      then (x ∘ Fin.succ) i.castSucc - (x ∘ Fin.succ) j else 1) =
      (∏ i : Fin n, ∏ j : Fin n,
        if i < j then (x i.castSucc.succ - x j.castSucc.succ) else 1) *
      (∏ i : Fin n, (x i.castSucc.succ - x (Fin.last (n + 1)))) := by
    have split_inner : (∏ i : Fin n, ∏ j : Fin (n + 1), if i.castSucc < j
        then (x ∘ Fin.succ) i.castSucc - (x ∘ Fin.succ) j else 1) =
        ∏ i : Fin n, ((∏ j : Fin n, if i < j
          then (x i.castSucc.succ - x j.castSucc.succ) else 1) *
          (x i.castSucc.succ - x (Fin.last (n + 1)))) := by
      exact Finset.prod_congr rfl fun i _ => by
        rw [Fin.prod_univ_castSucc, if_pos (Fin.castSucc_lt_last i)]
        congr 1
    rw [split_inner, Finset.prod_mul_distrib]
  have h_bulk : (∏ i : Fin n, ∏ j : Fin n, if i < j
      then x i.castSucc.succ - x j.castSucc.succ else 1) =
      diffProd (fun i => x i.castSucc.succ) := rfl
  rw [h_bulk] at h_rest
  rw [h_rest, mul_comm]
  rfl

/-! ## Auxiliary nonvanishing lemma -/

private lemma sumProd_ne_zero {m : ℕ} (x y : Fin m → F)
    (h : ∀ i j, x i + y j ≠ 0) : sumProd x y ≠ 0 := by
  unfold sumProd
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j _
  exact h i j

/-! ## Algebraic identities for the inductive step -/

private lemma corner_identity (x0 xn y0 yn : F) :
    (x0 - xn) * (y0 - yn) = (xn + y0) * (x0 + yn) - (x0 + y0) * (xn + yn) := by
  ring

private lemma cauchy_algebra_core
    (a b c d e f Wx0 Wxn Bx Wy0 Wyn By Wx0y Wxy0 Wxny Wxyn Bxy : F)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (h_Wx0y : Wx0y ≠ 0) (h_Wxy0 : Wxy0 ≠ 0) (h_Wxny : Wxny ≠ 0)
    (h_Wxyn : Wxyn ≠ 0) (h_Bxy : Bxy ≠ 0)
    (h_corner : a * b = e * d - c * f) :
    (((a * Wx0 * Wxn * Bx) * (b * Wy0 * Wyn * By)) /
      (c * d * e * f * Wx0y * Wxy0 * Wxny * Wxyn * Bxy)) * ((Bx * By) / Bxy) =
    (((Wxn * Bx) * (Wyn * By)) / (f * Wxny * Wxyn * Bxy)) *
      (((Wx0 * Bx) * (Wy0 * By)) / (c * Wx0y * Wxy0 * Bxy)) -
      (((Wxn * Bx) * (Wy0 * By)) / (e * Wxny * Wxy0 * Bxy)) *
      (((Wx0 * Bx) * (Wyn * By)) / (d * Wx0y * Wxyn * Bxy)) := by
  have h_num : (a * Wx0 * Wxn * Bx) * (b * Wy0 * Wyn * By) =
      (a * b) * (Wx0 * Wxn * Bx * Wy0 * Wyn * By) := by ring
  rw [h_num, h_corner]
  field_simp

/-! ## The Desnanot–Jacobi relation for `cauchyProd`

We show that `cauchyProd` satisfies the same recurrence as the
determinant under the Desnanot–Jacobi identity.
-/

private lemma cauchyProd_satisfies_dj {n : ℕ} (x y : Fin (n + 2) → F)
    (h : ∀ i j, x i + y j ≠ 0) :
    cauchyProd x y * cauchyProd (x ∘ Fin.succ ∘ Fin.castSucc)
      (y ∘ Fin.succ ∘ Fin.castSucc) =
    cauchyProd (x ∘ Fin.succ) (y ∘ Fin.succ) *
      cauchyProd (x ∘ Fin.castSucc) (y ∘ Fin.castSucc) -
      cauchyProd (x ∘ Fin.succ) (y ∘ Fin.castSucc) *
      cauchyProd (x ∘ Fin.castSucc) (y ∘ Fin.succ) := by
  unfold cauchyProd
  have h_comp_x : (x ∘ Fin.succ ∘ Fin.castSucc) = (fun i => x i.castSucc.succ) := by ext; rfl
  have h_comp_y : (y ∘ Fin.succ ∘ Fin.castSucc) = (fun i => y i.castSucc.succ) := by ext; rfl
  rw [h_comp_x, h_comp_y]
  rw [sumProd_corners_walls x y, diffProd_corners_walls x, diffProd_corners_walls y,
      sumProd_00 x y, sumProd_nn x y, sumProd_n0 x y, sumProd_0n x y,
      diffProd_0 x, diffProd_n x, diffProd_0 y, diffProd_n y]
  apply cauchy_algebra_core
  all_goals first
    | exact h _ _
    | (rw [Finset.prod_ne_zero_iff]; intro i _; exact h _ _)
    | (apply sumProd_ne_zero; intro i j; exact h _ _)
    | exact corner_identity _ _ _ _

/-- The Cauchy matrix with entries `(x_i + y_j)⁻¹`. -/
noncomputable def cauchyMatrix {n : ℕ} (x y : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of (fun i j => (x i + y j)⁻¹)

/-! ## Submatrix lemmas for `cauchyMatrix` -/

@[simp]
private lemma M11_cauchy {n : ℕ} (x y : Fin (n + 2) → F) :
    M11 (cauchyMatrix x y) = cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) := by
  ext i j; simp [M11, cauchyMatrix, Matrix.submatrix_apply, Fin.succAbove_zero]

@[simp]
private lemma Mkk_cauchy {n : ℕ} (x y : Fin (n + 2) → F) :
    Mkk (cauchyMatrix x y) = cauchyMatrix (x ∘ Fin.castSucc) (y ∘ Fin.castSucc) := by
  ext i j; simp [Mkk, cauchyMatrix, Matrix.submatrix_apply, Fin.succAbove_last]

@[simp]
private lemma M1k_cauchy {n : ℕ} (x y : Fin (n + 2) → F) :
    M1k (cauchyMatrix x y) = cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.castSucc) := by
  ext i j; simp [M1k, cauchyMatrix, Matrix.submatrix_apply, Fin.succAbove_zero,
                 Fin.succAbove_last]

@[simp]
private lemma Mk1_cauchy {n : ℕ} (x y : Fin (n + 2) → F) :
    Mk1 (cauchyMatrix x y) = cauchyMatrix (x ∘ Fin.castSucc) (y ∘ Fin.succ) := by
  ext i j; simp [Mk1, cauchyMatrix, Matrix.submatrix_apply, Fin.succAbove_zero,
                 Fin.succAbove_last]

@[simp]
private lemma M1k_1k_cauchy {n : ℕ} (x y : Fin (n + 2) → F) :
    M1k_1k (cauchyMatrix x y) = cauchyMatrix (x ∘ Fin.succ ∘ Fin.castSucc)
      (y ∘ Fin.succ ∘ Fin.castSucc) := by
  ext i j; simp [M1k_1k, cauchyMatrix, Matrix.submatrix_apply, Fin.succAbove_zero,
                 Fin.succAbove_last]

/-! ## Nonvanishing lemmas -/

/-- `diffProd x` is nonzero when all entries of `x` are distinct. -/
lemma diffProd_ne_zero {n : ℕ} (x : Fin n → F)
    (hx : ∀ i j, i ≠ j → x i ≠ x j) : diffProd x ≠ 0 := by
  unfold diffProd
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j _
  split_ifs with h
  · exact sub_ne_zero.mpr (hx i j (Fin.ne_of_lt h))
  · exact one_ne_zero

/-- `cauchyProd x y` is nonzero under natural distinctness and
nonvanishing hypotheses. -/
lemma cauchyProd_ne_zero {n : ℕ} (x y : Fin n → F)
    (h_sum : ∀ i j, x i + y j ≠ 0)
    (hx : ∀ i j, i ≠ j → x i ≠ x j)
    (hy : ∀ i j, i ≠ j → y i ≠ y j) : cauchyProd x y ≠ 0 := by
  unfold cauchyProd
  exact div_ne_zero
    (mul_ne_zero (diffProd_ne_zero x hx) (diffProd_ne_zero y hy))
    (sumProd_ne_zero x y h_sum)

/-! ## Main theorem -/

/-- The inductive step: assuming the Cauchy determinant formula for
all five `(n+1) × (n+1)` and `n × n` submatrices, deduce it for
`(n+2) × (n+2)` via the Desnanot–Jacobi identity. -/
private lemma cauchy_det_step {n : ℕ} (x y : Fin (n + 2) → F)
    (h_sum : ∀ i j, x i + y j ≠ 0)
    (hx : ∀ i j, i ≠ j → x i ≠ x j)
    (hy : ∀ i j, i ≠ j → y i ≠ y j)
    (IH_11 : (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det =
      cauchyProd (x ∘ Fin.succ) (y ∘ Fin.succ))
    (IH_kk : (cauchyMatrix (x ∘ Fin.castSucc) (y ∘ Fin.castSucc)).det =
      cauchyProd (x ∘ Fin.castSucc) (y ∘ Fin.castSucc))
    (IH_1k : (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.castSucc)).det =
      cauchyProd (x ∘ Fin.succ) (y ∘ Fin.castSucc))
    (IH_k1 : (cauchyMatrix (x ∘ Fin.castSucc) (y ∘ Fin.succ)).det =
      cauchyProd (x ∘ Fin.castSucc) (y ∘ Fin.succ))
    (IH_1k_1k : (cauchyMatrix (x ∘ Fin.succ ∘ Fin.castSucc)
      (y ∘ Fin.succ ∘ Fin.castSucc)).det =
      cauchyProd (x ∘ Fin.succ ∘ Fin.castSucc) (y ∘ Fin.succ ∘ Fin.castSucc)) :
    (cauchyMatrix x y).det = cauchyProd x y := by
  have hDJ := desnanot_jacobi (cauchyMatrix x y)
  simp only [M11_cauchy, Mkk_cauchy, M1k_cauchy, Mk1_cauchy, M1k_1k_cauchy] at hDJ
  rw [IH_11, IH_kk, IH_1k, IH_k1, IH_1k_1k] at hDJ
  rw [← cauchyProd_satisfies_dj x y h_sum] at hDJ
  have h_inner_ne : cauchyProd (x ∘ Fin.succ ∘ Fin.castSucc)
      (y ∘ Fin.succ ∘ Fin.castSucc) ≠ 0 :=
    cauchyProd_ne_zero _ _
      (fun i j => h_sum _ _)
      (fun i j hij => hx _ _ (fun h => hij (Fin.castSucc_injective _ (Fin.succ_injective _ h))))
      (fun i j hij => hy _ _ (fun h => hij (Fin.castSucc_injective _ (Fin.succ_injective _ h))))
  exact mul_right_cancel₀ h_inner_ne hDJ

/-! ### Degenerate cases -/

/-- `diffProd x` vanishes when two inputs coincide. -/
private lemma diffProd_eq_zero {n : ℕ} (x : Fin n → F) {i j : Fin n}
    (hij : i ≠ j) (hx : x i = x j) : diffProd x = 0 := by
  unfold diffProd
  rcases lt_or_gt_of_ne hij with h | h
  · exact Finset.prod_eq_zero (Finset.mem_univ i) <|
      Finset.prod_eq_zero (Finset.mem_univ j) <| by rw [if_pos h, hx, sub_self]
  · exact Finset.prod_eq_zero (Finset.mem_univ j) <|
      Finset.prod_eq_zero (Finset.mem_univ i) <| by rw [if_pos h, ← hx, sub_self]

private lemma cauchyMatrix_row_eq {n : ℕ} (x y : Fin n → F)
    {i j : Fin n} (hx : x i = x j) : (cauchyMatrix x y) i = (cauchyMatrix x y) j := by
  ext k; simp [cauchyMatrix, hx]

private lemma det_eq_zero_of_row_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    {i j : Fin n} (hij : i ≠ j) (h : M i = M j) : M.det = 0 :=
  Matrix.detRowAlternating.map_eq_zero_of_eq M h hij

/-! ### Induction on `n` -/

/-- The Cauchy determinant formula under distinctness hypotheses,
proved by strong induction on `n`. -/
private theorem cauchyMatrix_det_of_distinct {n : ℕ} (x y : Fin n → F)
    (h_sum : ∀ i j, x i + y j ≠ 0)
    (hx : ∀ i j, i ≠ j → x i ≠ x j)
    (hy : ∀ i j, i ≠ j → y i ≠ y j) :
    (cauchyMatrix x y).det = cauchyProd x y := by
  induction n using Nat.strong_induction_on
  next n ih =>
  match n with
  | 0 => simp [cauchyMatrix, cauchyProd, diffProd, sumProd]
  | 1 => simp [cauchyMatrix, cauchyProd, diffProd, sumProd]
  | n + 2 =>
    apply cauchy_det_step x y h_sum hx hy
    · exact ih (n + 1) (by omega) _ _
        (fun i j => h_sum _ _)
        (fun i j hij => hx _ _ (fun h => hij (Fin.succ_injective _ h)))
        (fun i j hij => hy _ _ (fun h => hij (Fin.succ_injective _ h)))
    · exact ih (n + 1) (by omega) _ _
        (fun i j => h_sum _ _)
        (fun i j hij => hx _ _ (fun h => hij (Fin.castSucc_injective _ h)))
        (fun i j hij => hy _ _ (fun h => hij (Fin.castSucc_injective _ h)))
    · exact ih (n + 1) (by omega) _ _
        (fun i j => h_sum _ _)
        (fun i j hij => hx _ _ (fun h => hij (Fin.succ_injective _ h)))
        (fun i j hij => hy _ _ (fun h => hij (Fin.castSucc_injective _ h)))
    · exact ih (n + 1) (by omega) _ _
        (fun i j => h_sum _ _)
        (fun i j hij => hx _ _ (fun h => hij (Fin.castSucc_injective _ h)))
        (fun i j hij => hy _ _ (fun h => hij (Fin.succ_injective _ h)))
    · exact ih n (by omega) _ _
        (fun i j => h_sum _ _)
        (fun i j hij => hx _ _ (fun h => hij (Fin.castSucc_injective _ (Fin.succ_injective _ h))))
        (fun i j hij => hy _ _ (fun h => hij (Fin.castSucc_injective _ (Fin.succ_injective _ h))))

/-- **Cauchy determinant formula.** The determinant of the Cauchy
matrix with entries `(x_i + y_j)⁻¹` equals
`(∏_{i<j} (x_i - x_j) · ∏_{i<j} (y_i - y_j)) / ∏_{i,j} (x_i + y_j)`.

No distinctness assumption on `x` or `y` is needed: when either has
repeated entries, both sides vanish. -/
theorem cauchyMatrix_det {n : ℕ} (x y : Fin n → F)
    (h_sum : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det = cauchyProd x y := by
  by_cases hx : ∀ i j, i ≠ j → x i ≠ x j
  · by_cases hy : ∀ i j, i ≠ j → y i ≠ y j
    · exact cauchyMatrix_det_of_distinct x y h_sum hx hy
    · -- y not injective → both sides vanish
      push_neg at hy
      obtain ⟨i, j, hij, hyij⟩ := hy
      have h_det : (cauchyMatrix x y).det = 0 := by
        rw [← Matrix.det_transpose]
        exact det_eq_zero_of_row_eq _ hij (by ext k; simp [cauchyMatrix, hyij])
      have h_prod : cauchyProd x y = 0 := by
        simp [cauchyProd, diffProd_eq_zero y hij hyij]
      rw [h_det, h_prod]
  · -- x not injective → both sides vanish
    push_neg at hx
    obtain ⟨i, j, hij, hxij⟩ := hx
    have h_det : (cauchyMatrix x y).det = 0 :=
      det_eq_zero_of_row_eq _ hij (cauchyMatrix_row_eq x y hxij)
    have h_prod : cauchyProd x y = 0 := by
      simp [cauchyProd, diffProd_eq_zero x hij hxij]
    rw [h_det, h_prod]
