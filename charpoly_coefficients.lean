/-
Copyright (c) 2026 Slava Naprienko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Slava Naprienko
-/
import Mathlib

/-!
# Coefficients of the characteristic polynomial as sums of principal minors

We prove that the k-th coefficient of `det(1 + X • M)` equals the sum of all
k×k principal minors of M, and derive the corresponding formula for the
coefficients of the characteristic polynomial.

## Main results

- `Matrix.det_piecewise_one_eq_submatrix_det`: the determinant of a matrix with
  rows outside `s` replaced by identity rows equals the principal submatrix determinant.
- `Matrix.coeff_det_one_add_X_smul_eq_sum_minors`: the k-th coefficient of
  `det(1 + X • M)` equals the sum of all k×k principal minors.
- `Matrix.charpoly_coeff_eq_sum_minors`: the (n-k)-th coefficient of the
  characteristic polynomial equals `(-1)^k` times the sum of k×k principal minors.
-/

open Finset Matrix Polynomial

variable {R : Type u} [CommRing R]
variable {n : Type v} [DecidableEq n] [Fintype n]

namespace Matrix

/-- The determinant of the matrix obtained by replacing rows outside `s` with identity rows
equals the determinant of the principal submatrix indexed by `s`. -/
lemma det_piecewise_one_eq_submatrix_det
    (M : Matrix n n R) (s : Finset n) :
    det (s.piecewise M (1 : Matrix n n R)) =
    (M.submatrix (↑) (↑) : Matrix s s R).det := by
  let e := Equiv.sumCompl (fun x => x ∈ s)
  let A : Matrix n n R := Matrix.of (s.piecewise M (1 : Matrix n n R))
  have hdet : det (s.piecewise M (1 : Matrix n n R)) = A.det := rfl
  rw [hdet, ← Matrix.det_submatrix_equiv_self e A]
  have h_blocks : A.submatrix e e =
      Matrix.fromBlocks
        (M.submatrix Subtype.val Subtype.val)
        (M.submatrix Subtype.val Subtype.val) 0 1 := by
    ext (i | i) (j | j) <;> dsimp [A, e]
    · -- i j : ↥s
      simp only [Finset.piecewise, if_pos i.prop]
    · -- i : ↥s, j : {a // a ∉ s}
      simp only [Finset.piecewise, if_pos i.prop]
    · -- i : {a // a ∉ s}, j : ↥s
      simp only [Finset.piecewise, if_neg i.prop]
      exact Matrix.one_apply_ne (fun h => i.prop (h ▸ j.prop))
    · -- i j : {a // a ∉ s}
      simp only [Finset.piecewise, if_neg i.prop, Matrix.one_apply,
        Subtype.ext_iff]
  rw [h_blocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- The k-th coefficient of `det (1 + X • M)` equals the sum of all k×k principal minors of M.
This generalizes `coeff_det_one_add_X_smul_one` (the k = 1 case, which gives the trace)
and `det_eq_sign_charpoly_coeff` (the k = n case, which gives the determinant). -/
theorem coeff_det_one_add_X_smul_eq_sum_minors
    (M : Matrix n n R) (k : ℕ) :
    (det (1 + (X : R[X]) • M.map C)).coeff k =
    ∑ s ∈ Finset.univ.filter
        (fun s : Finset n => s.card = k),
      (M.submatrix (↑) (↑) : Matrix s s R).det := by
  simp only [det]
  let D := (detRowAlternating : (n → R[X]) [⋀^n]→ₗ[R[X]] R[X]).toMultilinearMap
  rw [add_comm]
  change (D (fun i => ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i)).coeff k = _
  conv_lhs => rw [show (fun i ↦ ((X : R[X]) • M.map C) i + (1 : Matrix n n R[X]) i) =
      (fun i => ((X : R[X]) • M.map C) i) + (fun i => (1 : Matrix n n R[X]) i) from rfl]
  conv_lhs => rw [D.map_add_univ]
  have h_map : ∀ s : Finset n,
        (s.piecewise (fun i ↦ (M.map C) i)
          (fun i ↦ (1 : Matrix n n R[X]) i) : Matrix n n R[X]) =
        Matrix.map (s.piecewise M (1 : Matrix n n R)) C := by
      intro s; ext i j
      simp only [Finset.piecewise, Matrix.map_apply]
      split_ifs with h <;> simp [Matrix.one_apply]
  have h_det : ∀ s : Finset n,
      D (s.piecewise (fun i ↦ (M.map C) i)
        (fun i ↦ (1 : Matrix n n R[X]) i)) =
      C (det (s.piecewise M (1 : Matrix n n R))) := by
    intro s; change det _ = _
    rw [h_map]; exact (RingHom.map_det C _).symm
  calc (∑ s : Finset n, D (Finset.piecewise s (fun i ↦ ((X : R[X]) • M.map C) i)
            (fun i ↦ (1 : Matrix n n R[X]) i))).coeff k
      _ = (∑ s : Finset n, (X : R[X]) ^ s.card •
            D (s.piecewise (fun i ↦ (M.map C) i)
              (fun i ↦ (1 : Matrix n n R[X]) i))).coeff k := by
        congr 1; apply Finset.sum_congr rfl; intro s _
        have h_smul : s.piecewise (fun i ↦ ((X : R[X]) • M.map C) i)
            (fun i ↦ (1 : Matrix n n R[X]) i) =
            fun i => (if i ∈ s then (X : R[X]) else 1) •
              s.piecewise (fun i ↦ (M.map C) i) (fun i ↦ (1 : Matrix n n R[X]) i) i := by
          funext i j
          simp only [piecewise, Pi.smul_apply, smul_eq_mul, ite_mul, one_mul]
          split_ifs <;> rfl
        rw [h_smul, D.map_smul_univ]
        congr 1
        simp only [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
      _ = ∑ s : Finset n, ((X : R[X]) ^ s.card •
            D (Finset.piecewise s (fun i ↦ (M.map C) i)
              (fun i ↦ (1 : Matrix n n R[X]) i))).coeff k := by
        simp only [Polynomial.finset_sum_coeff]
      _ = _ := by
        simp_rw [h_det, smul_eq_mul,
          mul_comm (X ^ _) (C _),
          C_mul_X_pow_eq_monomial, coeff_monomial,
          Finset.sum_filter,
          det_piecewise_one_eq_submatrix_det]

/-- The coefficients of the characteristic polynomial are signed sums of principal minors.
Specifically, the (n-k)-th coefficient of the characteristic polynomial of M equals
(-1)^k times the sum of all k×k principal minors of M. -/
theorem charpoly_coeff_eq_sum_minors
    [Nontrivial R] (M : Matrix n n R) (k : ℕ)
    (hk : k ≤ Fintype.card n) :
    M.charpoly.coeff (Fintype.card n - k) =
    (-1) ^ k *
      ∑ s ∈ Finset.univ.filter
          (fun s : Finset n => s.card = k),
        (M.submatrix (↑) (↑) :
          Matrix s s R).det := by
  have hnd := M.charpoly_natDegree_eq_dim
  have hrev :
      M.charpoly.coeff (Fintype.card n - k) =
      M.charpoly.reverse.coeff k := by
    simp [Polynomial.coeff_reverse, hnd, hk]
  rw [hrev, M.reverse_charpoly]
  have hcharpolyRev :
      M.charpolyRev =
      det (1 + (X : R[X]) • (-M).map C) := by
    simp only [charpolyRev, sub_eq_add_neg]
    congr 2; ext i j
    simp [Matrix.smul_apply, Matrix.map_apply]
  rw [hcharpolyRev,
    coeff_det_one_add_X_smul_eq_sum_minors]
  simp only [univ_filter_card_eq, submatrix_neg, Pi.neg_apply, det_neg, Fintype.card_coe, mul_sum]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [(Finset.mem_powersetCard.mp hs).2]

end Matrix
