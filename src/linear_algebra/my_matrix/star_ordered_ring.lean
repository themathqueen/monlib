/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_matrix.pos_def_rpow
import linear_algebra.pi_star_ordered_ring
import linear_algebra.my_matrix.pos_def_rpow
import linear_algebra.my_ips.functional
import linear_algebra.my_ips.quantum_set

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
      ← matrix.to_euclidean_lin_conj_transpose_eq_adjoint, hy.1.eq], }, }
  -- lt := λ x y, (y - x).pos_def,
  -- lt_iff_le_not_le := λ x y, by {  } }

localized "attribute [instance] matrix.partial_order" in matrix_order

lemma matrix.le_iff {n : Type*} [fintype n] [decidable_eq n] {x y : matrix n n ℂ} :
  x ≤ y ↔ (y - x).pos_semidef :=
iff.rfl
-- def matrix.pos_semidef.add_submonoid (n : Type*) [fintype n] [decidable_eq n] :
--   add_submonoid (matrix n n ℂ) :=
-- { carrier := {x : matrix n n ℂ | x.pos_semidef},
--   zero_mem' := matrix.pos_semidef.zero,
--   add_mem' := λ x y hx hy, matrix.pos_semidef.add hx hy }
-- lemma matrix.pos_semidef.mem_add_submonoid {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
--   x ∈ (matrix.pos_semidef.add_submonoid n : add_submonoid (matrix n n ℂ)) ↔ x.pos_semidef :=
-- iff.rfl
-- lemma matrix.pos_semidef.star_mul_self_mem_add_submonoid {n : Type*} [fintype n] [decidable_eq n]
--   (x : matrix n n ℂ) :
--   xᴴ ⬝ x ∈ matrix.pos_semidef.add_submonoid n :=
-- begin
--   simp_rw [matrix.pos_semidef.mem_add_submonoid, matrix.pos_semidef.star_mul_self],
-- end
noncomputable def matrix.star_ordered_ring {n : Type*} [fintype n] [decidable_eq n] :
  star_ordered_ring (matrix n n ℂ) :=
begin
  apply star_ordered_ring.of_le_iff,
  { intros a b hab c,
    simp_rw [matrix.le_iff, add_sub_add_left_eq_sub],
    exact hab, },
  { intros x y,
    simp_rw [matrix.le_iff, matrix.pos_semidef_iff, sub_eq_iff_eq_add',
      matrix.star_eq_conj_transpose, matrix.mul_eq_mul], },
end

localized "attribute [instance] matrix.star_ordered_ring" in matrix_order

open_locale matrix_order
lemma matrix.pi.le_iff_sub_nonneg
  {ι : Type*} [fintype ι] [decidable_eq ι]
  {n : ι → Type*} [Π i, fintype (n i)] [Π i, decidable_eq (n i)] (x y : Π i, matrix (n i) (n i) ℂ) :
  x ≤ y ↔ ∃ z : Π i, matrix (n i) (n i) ℂ, y = x + star z * z :=
begin
  simp_rw [@function.funext_iff _ _ _ (_ + star _ * _), pi.add_apply, pi.mul_apply, pi.star_apply,
    pi.le_def, matrix.le_iff, matrix.pos_semidef_iff, sub_eq_iff_eq_add',
    matrix.star_eq_conj_transpose, matrix.mul_eq_mul],
  exact ⟨λ hx, ⟨(λ i, (hx i).some), λ i, (hx i).some_spec⟩,
    λ ⟨y, hy⟩ i, ⟨y i, (hy i)⟩⟩,
end

noncomputable def matrix.pi.star_ordered_ring
  {ι : Type*} [fintype ι] [decidable_eq ι]
  {n : ι → Type*} [Π i, fintype (n i)] [Π i, decidable_eq (n i)] :
  star_ordered_ring (Π i, matrix (n i) (n i) ℂ) :=
by
{ refine star_ordered_ring.of_le_iff
   (λ a b hab c i, by {
    simp_rw [pi.add_apply],
    exact add_le_add_left (hab _) _, }) _,
  intros a b,
  simp_rw [pi.le_def, matrix.le_iff],
  rw ← matrix.pi.le_iff_sub_nonneg,
  refl, }

localized "attribute [instance] matrix.pi.star_ordered_ring" in matrix_order

def matrix.neg_semidef {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
  Prop :=
(x.is_hermitian ∧ ∀ (a : n → ℂ),
  is_R_or_C.re (matrix.dot_product (has_star.star a) (x.mul_vec a)) ≤ 0)

lemma matrix.is_hermitian.neg_iff {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
  (- x).is_hermitian ↔ x.is_hermitian :=
begin
  split,
  { intro h,
    rw [← neg_neg x],
    exact matrix.is_hermitian.neg h, },
  { exact matrix.is_hermitian.neg, },
end

lemma matrix.neg_semidef_iff_neg_pos_semidef {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
  x.neg_semidef ↔ (-x).pos_semidef :=
begin
  simp_rw [matrix.neg_semidef, matrix.pos_semidef, matrix.is_hermitian.neg_iff,
    matrix.neg_mul_vec, matrix.dot_product_neg, map_neg, @le_neg _ _ _ _ _ (0 : ℝ),
    neg_zero],
end

lemma matrix.neg_semidef_iff_nonpos {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
  x.neg_semidef ↔ x ≤ 0 :=
by rw [matrix.neg_semidef_iff_neg_pos_semidef, matrix.le_iff, zero_sub]

open_locale complex_order

lemma matrix.pos_semidef_and_neg_semidef_iff_eq_zero {n : Type*} [fintype n] [decidable_eq n]
  {x : matrix n n ℂ} :
  (x.pos_semidef ∧ x.neg_semidef) ↔ x = 0 :=
begin
  simp_rw [matrix.neg_semidef_iff_neg_pos_semidef, matrix.eq_zero_iff,
    pos_semidef.complex, matrix.neg_mul_vec, matrix.dot_product_neg,
    neg_nonneg, le_antisymm_iff, forall_and_distrib, and_comm],
end

-- lemma matrix.pos_semidef_and_not_neg_semidef_iff_pos_def
--   {n : Type*} [fintype n] [decidable_eq n] (x : matrix n n ℂ) :
--   (x.pos_semidef ∧ ¬ x.neg_semidef) ↔ x.pos_def :=
-- begin
--   nth_rewrite 0 ← sub_zero x,
--   rw [← matrix.le_iff, matrix.neg_semidef_iff_nonpos, ← lt_iff_le_not_le,
--     lt_iff_le_and_ne, ne.def, eq_comm],
--   split,
--   { rintro ⟨⟨hx1, hx2⟩, h⟩,
--     rw ← sub_zero x,
--     refine ⟨hx1, _⟩,
--     intros a ha,
--     specialize hx2 a,
--     apply lt_of_le_not_le hx2,
--     intro hi,
--     simp_rw [sub_zero] at hi hx2,
    
--   }
-- end

-- def matrix.pos_def.has_pow {n : Type*} [fintype n] [decidable_eq n] :
--   has_pow ({x : matrix n n ℂ // 0 < x}) ℝ :=
-- { pow := λ x r, @matrix.pos_def.rpow x _ r, }

-- open_locale functional
-- noncomputable def module.dual.is_faithful_pos_map.normed_add_comm_group_of_ring
--   {n : Type*} [fintype n] [decidable_eq n] (f : module.dual ℂ (matrix n n ℂ))
--   [hf : fact f.is_faithful_pos_map] :
--   normed_add_comm_group_of_ring (matrix n n ℂ) :=
-- { to_has_norm := normed_add_comm_group.to_has_norm,
--   ..matrix.ring }

-- local attribute [instance] algebra.of_is_scalar_tower_smul_comm_class
-- def matrix_is_quantum_set {n : Type*} [fintype n] [decidable_eq n]
--   {f : module.dual ℂ (matrix n n ℂ)} [hf : fact f.is_faithful_pos_map] :
--   quantum_set (matrix n n ℂ) :=
-- begin
--   refine { to_normed_add_comm_group_of_ring := module.dual.is_faithful_pos_map.normed_add_comm_group_of_ring f,
--   to_inner_product_space := @module.dual.is_faithful_pos_map.inner_product_space _ _ _ _ hf,
--   to_partial_order := @matrix.partial_order n _ _,
--   to_star_ordered_ring := @matrix.star_ordered_ring n _ _,
--   to_has_smul_comm_class := by { apply_instance },
--   to_is_scalar_tower := by { apply_instance },
--   to_finite_dimensional := by { apply_instance },
--   to_has_inv := by { apply_instance },
--   φ := f,
--   hφ := hf.elim,
--   inner_eq := λ x y, rfl,
--   functional_adjoint_eq := module.dual.is_faithful_pos_map.adjoint_eq,
--   ..},
-- end
