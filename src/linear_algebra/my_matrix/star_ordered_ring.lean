/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_matrix.pos_def_rpow

/-!
# Matrix algebras are star ordered rings

This file contains the instance of `star_ordered_ring` for `matrix n n ℂ`.

## Main definitions

* `matrix.partial_order`: The partial order on `matrix n n ℂ` induced by the positive semidefinite
  matrices.
* `matrix.pos_semidef.add_submonoid`: The additive submonoid of positive semidefinite matrices.
* `matrix.star_ordered_ring`: The instance of `star_ordered_ring` for `matrix n n ℂ`.

You need to `open_locale matrix_order` to use these instances.

-/

lemma matrix.pos_semidef.zero {n : Type*} [fintype n] :
  (0 : matrix n n ℂ).pos_semidef :=
begin
  simp_rw [matrix.pos_semidef, matrix.is_hermitian_zero, true_and,
    matrix.zero_mul_vec, matrix.dot_product_zero, map_zero, le_refl, implies_true_iff],
end
lemma matrix.pos_semidef.add {n : Type*} [fintype n] {x y : matrix n n ℂ}
  (hx : x.pos_semidef) (hy : y.pos_semidef) :
  (x + y).pos_semidef :=
begin
  simp_rw [matrix.pos_semidef, matrix.is_hermitian.add hx.1 hy.1, true_and,
    matrix.add_mul_vec, matrix.dot_product_add, map_add],
  exact λ a, add_nonneg (hx.2 a) (hy.2 a),
end
open_locale matrix
lemma matrix.eq_zero_iff {n : Type*} [fintype n] [decidable_eq n] {x : matrix n n ℂ} :
  x = 0 ↔ ∀ a : n → ℂ, (star a) ⬝ᵥ (x.mul_vec a) = 0 :=
begin
  calc x = 0 ↔ x.to_euclidean_lin = 0 : by simp only [linear_equiv.map_eq_zero_iff]
  ... ↔ ∀ a : euclidean_space ℂ n, ⟪a, x.to_euclidean_lin a⟫_ℂ = 0 :
  by { simp_rw [← inner_map_self_eq_zero, inner_eq_zero_symm], }
  ... ↔ ∀ a : euclidean_space ℂ n, (star (a : n → ℂ) : n → ℂ) ⬝ᵥ (x.mul_vec a) = 0 : by refl
  ... ↔ ∀ a : n → ℂ, star a ⬝ᵥ (x.mul_vec a) = 0 : by refl,
end
lemma matrix.to_euclidean_lin_apply {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ)
  (a : n → ℂ) :
  x.to_euclidean_lin a = x.mul_vec a :=
rfl
open_locale complex_order
def matrix.partial_order {n : Type*} [fintype n] [decidable_eq n] :
  partial_order (matrix n n ℂ) :=
{ le := λ x y, (y - x).pos_semidef,
  le_refl := λ x, by simp only [sub_self, matrix.pos_semidef.zero],
  le_trans := λ x y z hx hy, by {
    have := matrix.pos_semidef.add hx hy,
    simp only [sub_add_sub_cancel'] at this,
    exact this, },
  le_antisymm := λ x y hx hy, by {
    rw [← sub_eq_zero, matrix.eq_zero_iff],
    intro a,
    have := hx.2 a,
    rw [← neg_sub, matrix.neg_mul_vec, matrix.dot_product_neg, map_neg,
      ← complex.zero_le_real, complex.of_real_neg, le_neg, neg_zero] at this,
    ext,
    exact le_antisymm this (complex.zero_le_real.mpr (hy.2 a)),
    simp_rw [complex.zero_im, ← complex.conj_eq_iff_im, ← euclidean_space.inner_eq,
      ← matrix.to_euclidean_lin_apply, inner_conj_symm, ← linear_map.adjoint_inner_left,
      ← matrix.to_euclidean_lin_conj_transpose_eq_adjoint, hy.1.eq], } }

localized "attribute [instance] matrix.partial_order" in matrix_order

lemma matrix.le_iff {n : Type*} [fintype n] [decidable_eq n] {x y : matrix n n ℂ} :
  x ≤ y ↔ (y - x).pos_semidef :=
iff.rfl
def matrix.pos_semidef.add_submonoid (n : Type*) [fintype n] [decidable_eq n] :
  add_submonoid (matrix n n ℂ) :=
{ carrier := {x : matrix n n ℂ | x.pos_semidef},
  zero_mem' := matrix.pos_semidef.zero,
  add_mem' := λ x y hx hy, matrix.pos_semidef.add hx hy }
lemma matrix.pos_semidef.mem_add_submonoid {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
  x ∈ (matrix.pos_semidef.add_submonoid n : add_submonoid (matrix n n ℂ)) ↔ x.pos_semidef :=
iff.rfl
lemma matrix.pos_semidef.star_mul_self_mem_add_submonoid {n : Type*} [fintype n] [decidable_eq n]
  (x : matrix n n ℂ) :
  xᴴ ⬝ x ∈ matrix.pos_semidef.add_submonoid n :=
begin
  simp_rw [matrix.pos_semidef.mem_add_submonoid, matrix.pos_semidef.star_mul_self],
end
noncomputable def matrix.star_ordered_ring {n : Type*} [fintype n] [decidable_eq n] :
  star_ordered_ring (matrix n n ℂ) :=
{ add_le_add_left := λ a b hab c, by {
    simp_rw [matrix.le_iff, add_sub_add_left_eq_sub],
    exact hab, },
  le_iff := λ a b, by {
    simp_rw [matrix.le_iff, matrix.pos_semidef_iff, matrix.star_eq_conj_transpose,
      matrix.mul_eq_mul, add_submonoid.mem_closure, set.range_subset_iff],
    refine ⟨λ ⟨y, hy⟩, ⟨yᴴ ⬝ y, λ S hy, hy _, by rw [← hy, add_sub_cancel'_right]⟩, _⟩,
    rintros ⟨p, h, rfl⟩,
    rw [add_sub_cancel'],
    simp only [set_like.mem_coe] at h,
    specialize h (matrix.pos_semidef.add_submonoid n) matrix.pos_semidef.star_mul_self_mem_add_submonoid,
    rw [matrix.pos_semidef.mem_add_submonoid, matrix.pos_semidef_iff] at h,
    exact h, },
  ..matrix.partial_order }

localized "attribute [instance] matrix.star_ordered_ring" in matrix_order
