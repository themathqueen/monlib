/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import data.matrix.basic
import linear_algebra.matrix.hermitian
import preq.ites

/-!
 # Conjugate of a matrix

This file defines the conjugate of a matrix, `matrix.conj` with the notation of this being `ᴴᵀ` (i.e., `xᴴᵀ i j = star (x i j)`), and shows basic properties about it.
-/

namespace matrix

open_locale matrix

variables {α n₁ n₂ : Type*}

/-- conjugate of matrix defined as $\bar{x} := {(x^*)}^\top$, i.e., $\bar{x}_{ij}=\overline{x_{ij}}$ -/
def conj [has_star α] (x : matrix n₁ n₂ α) :
  matrix n₁ n₂ α :=
xᴴᵀ

localized "postfix (name := matrix.conj) `ᴴᵀ`:1500 := matrix.conj" in matrix

lemma conj_apply [has_star α] (x : matrix n₁ n₂ α) (i : n₁) (j : n₂) :
  xᴴᵀ i j = star (x i j) :=
rfl

lemma conj_conj [has_involutive_star α] (x : matrix n₁ n₂ α) :
  (xᴴᵀ)ᴴᵀ = x :=
calc (xᴴᵀ)ᴴᵀ = xᵀᵀᴴᴴ : rfl
  ... = xᵀᵀ : conj_transpose_conj_transpose _
  ... = x : transpose_transpose _

lemma conj_add [add_monoid α] [star_add_monoid α]
  (x y : matrix n₁ n₂ α) : (x + y)ᴴᵀ = xᴴᵀ + yᴴᵀ :=
by { simp_rw [conj, ← transpose_add, ← conj_transpose_add], }

lemma conj_smul {R : Type*} [has_star R] [has_star α] [has_smul R α]
  [star_module R α] (c : R) (x : matrix n₁ n₂ α) :
  (c • x)ᴴᵀ = star c • xᴴᵀ :=
by { simp_rw [conj, ← transpose_smul, ← conj_transpose_smul], }

lemma conj_conj_transpose [has_involutive_star α] (x : matrix n₁ n₂ α) :
  xᴴᵀᴴ = xᵀ :=
calc xᴴᵀᴴ = xᵀᴴᴴ : rfl
  ... = xᵀ : conj_transpose_conj_transpose _

lemma conj_transpose_conj [has_involutive_star α] (x : matrix n₁ n₂ α) :
  xᴴᴴᵀ = xᵀ :=
calc xᴴᴴᵀ = xᴴᵀᴴ : rfl
  ... = xᵀ : conj_conj_transpose _

lemma transpose_conj_eq_conj_transpose [has_star α] (x : matrix n₁ n₂ α) :
  xᴴᵀᵀ = xᴴ :=
rfl

lemma is_hermitian.conj {α n : Type*} [has_star α]
  {x : matrix n n α} (hx : x.is_hermitian) :
  xᴴᵀ = xᵀ :=
by { simp_rw [conj, hx.eq], }

lemma conj_mul {α m n p : Type*} [fintype n]
  [comm_semiring α] [star_ring α] (x : matrix m n α)
  (y : matrix n p α) :
  (x ⬝ y)ᴴᵀ = xᴴᵀ ⬝ yᴴᵀ :=
begin
  ext1,
  simp_rw [conj_apply, mul_apply, star_sum, star_semigroup.star_mul, conj_apply, mul_comm],
end

lemma conj_one {α n : Type*} [decidable_eq n] [comm_semiring α]
  [star_ring α] :
  (1 : matrix n n α)ᴴᵀ = 1 :=
begin
  ext1,
  simp_rw [conj_apply, one_apply, star_ite, star_one, star_zero],
end


end matrix
