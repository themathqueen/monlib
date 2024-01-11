/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.contraction
import ring_theory.matrix_algebra
import data.matrix.kronecker
import data.matrix.dmatrix
import linear_algebra.my_matrix.basic
import linear_algebra.tensor_finite

/-!
# Kronecker product to the tensor product

This file contains the definition of `tensor_to_kronecker` and `kronecker_to_tensor`, the linear equivalences between `⊗ₜ` and `⊗ₖ`.

-/

open_locale tensor_product big_operators kronecker

section

variables {R m n : Type*} [comm_semiring R]
  [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]

def tensor_product.to_kronecker :
  (matrix m m R ⊗[R] matrix n n R) →ₗ[R] matrix (m × n) (m × n) R :=
{ to_fun := λ x ij kl, (matrix_equiv_tensor _ _ _).symm x ij.2 kl.2 ij.1 kl.1,
  map_add' := λ x y, by { simp_rw [alg_equiv.map_add, dmatrix.add_apply], refl, },
  map_smul' := λ r x, by { simp only [alg_equiv.map_smul, pi.smul_apply, algebra.id.smul_eq_mul,
    ring_hom.id_apply], refl, } }

lemma tensor_product.to_kronecker_apply (x : matrix m m R) (y : matrix n n R) :
  (x ⊗ₜ[R] y).to_kronecker = x ⊗ₖ y :=
begin
  simp_rw [tensor_product.to_kronecker, linear_map.coe_mk, matrix_equiv_tensor_apply_symm,
    algebra.algebra_map_eq_smul_one, matrix.map_apply, matrix.mul_eq_mul, matrix.mul_apply,
    pi.smul_apply, matrix.one_apply, smul_eq_mul, mul_boole, mul_ite, mul_zero,
    finset.sum_ite_eq', finset.mem_univ, if_true],
  refl,
end

def matrix.kronecker_to_tensor_product :
  matrix (m × n) (m × n) R →ₗ[R] (matrix m m R ⊗[R] matrix n n R) :=
{ to_fun := λ x, (matrix_equiv_tensor _ (matrix m m R) n) (λ i j k l, x (k, i) (l, j)),
  map_add' := λ x y, by { simp_rw [dmatrix.add_apply, ← alg_equiv.map_add], refl, },
  map_smul' := λ r x, by { simp_rw [pi.smul_apply, ← alg_equiv.map_smul, ring_hom.id_apply],
    refl, } }

lemma tensor_product.to_kronecker_to_tensor_product (x : matrix m m R ⊗[R] matrix n n R) :
  x.to_kronecker.kronecker_to_tensor_product = x :=
begin
  simp_rw [tensor_product.to_kronecker, matrix.kronecker_to_tensor_product, linear_map.coe_mk,
    alg_equiv.apply_symm_apply],
end

lemma matrix.kronecker_to_tensor_product_apply (x : matrix m m R) (y : matrix n n R) :
  (x ⊗ₖ y).kronecker_to_tensor_product = x ⊗ₜ[R] y :=
by rw [← tensor_product.to_kronecker_apply, tensor_product.to_kronecker_to_tensor_product]

lemma matrix.kronecker_to_tensor_product_to_kronecker (x : matrix (m × n) (m × n) R) :
  x.kronecker_to_tensor_product.to_kronecker = x :=
by simp_rw [matrix.kronecker_to_tensor_product, tensor_product.to_kronecker,
  linear_map.coe_mk, alg_equiv.symm_apply_apply, prod.mk.eta]

open_locale matrix

lemma tensor_product.matrix_star {R m n : Type*} [field R] [star_ring R]
  [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
  (x : matrix m m R) (y : matrix n n R) :
  star (x ⊗ₜ[R] y) = xᴴ ⊗ₜ yᴴ :=
tensor_product.star_tmul _ _

lemma tensor_product.to_kronecker_star {R m n : Type*} [is_R_or_C R]
  [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
  (x : matrix m m R) (y : matrix n n R) :
  star (x ⊗ₜ y).to_kronecker = (star (x ⊗ₜ y)).to_kronecker :=
begin
  simp_rw [tensor_product.matrix_star, tensor_product.to_kronecker_apply,
    matrix.star_eq_conj_transpose, matrix.kronecker_conj_transpose],
end

lemma matrix.kronecker_to_tensor_product_star {R m n : Type*} [is_R_or_C R]
  [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
  (x : matrix m m R) (y : matrix n n R) :
  star (x ⊗ₖ y).kronecker_to_tensor_product = (star (x ⊗ₖ y)).kronecker_to_tensor_product :=
begin
  simp only [matrix.kronecker_to_tensor_product_apply, tensor_product.matrix_star,
    matrix.star_eq_conj_transpose, matrix.kronecker_conj_transpose],
end

open matrix

lemma matrix.kronecker_eq_sum_std_basis (x : matrix (m × n) (m × n) R) :
  x = ∑ i j k l, x (i,k) (j,l) • (std_basis_matrix i j 1 ⊗ₖ std_basis_matrix k l 1) :=
kmul_representation _

lemma tensor_product.matrix_eq_sum_std_basis (x : matrix m m R ⊗[R] matrix n n R) :
  x = ∑ i j k l,
    x.to_kronecker (i,k) (j,l) • (std_basis_matrix i j 1 ⊗ₜ std_basis_matrix k l 1) :=
begin
  rw eq_comm,
  calc ∑ i j k l, x.to_kronecker (i,k) (j,l)
      • (std_basis_matrix i j (1 : R) ⊗ₜ std_basis_matrix k l (1 : R))
    = ∑ i j k l, x.to_kronecker (i,k) (j,l)
      • (std_basis_matrix i j (1 : R)
        ⊗ₜ std_basis_matrix k l (1 : R)).to_kronecker.kronecker_to_tensor_product :
  by simp_rw [tensor_product.to_kronecker_to_tensor_product]
    ... = ∑ i j k l, x.to_kronecker (i,k) (j,l)
      • (std_basis_matrix i j (1 : R)
        ⊗ₖ std_basis_matrix k l (1 : R)).kronecker_to_tensor_product :
  by simp_rw [tensor_product.to_kronecker_apply]
    ... = (∑ i j k l, x.to_kronecker (i,k) (j,l)
      • (std_basis_matrix i j (1 : R)
        ⊗ₖ std_basis_matrix k l (1 : R))).kronecker_to_tensor_product :
  by simp_rw [map_sum, smul_hom_class.map_smul]
    ... = x.to_kronecker.kronecker_to_tensor_product :
  by rw ← matrix.kronecker_eq_sum_std_basis
    ... = x : tensor_product.to_kronecker_to_tensor_product _,
end

lemma tensor_product.to_kronecker_mul
  (x y : matrix m m R ⊗[R] matrix n n R) :
  (x * y).to_kronecker = x.to_kronecker ⬝ y.to_kronecker :=
begin
  nth_rewrite_lhs 0 x.matrix_eq_sum_std_basis,
  nth_rewrite_lhs 0 y.matrix_eq_sum_std_basis,
  simp_rw [finset.sum_mul, finset.mul_sum, smul_mul_smul, map_sum, smul_hom_class.map_smul,
    algebra.tensor_product.tmul_mul_tmul, tensor_product.to_kronecker_apply, mul_eq_mul,
    matrix.mul_kronecker_mul, ← mul_eq_mul, ← smul_mul_smul, ← finset.mul_sum, ← finset.sum_mul],
  rw [← x.to_kronecker.kronecker_eq_sum_std_basis, ← y.to_kronecker.kronecker_eq_sum_std_basis],
end

lemma matrix.kronecker_to_tensor_product_mul
  (x y : matrix m m R) (z w : matrix n n R) :
  ((x ⊗ₖ z) ⬝ (y ⊗ₖ w)).kronecker_to_tensor_product
    = (x ⊗ₖ z).kronecker_to_tensor_product * (y ⊗ₖ w).kronecker_to_tensor_product :=
begin
  simp_rw [← matrix.mul_kronecker_mul, matrix.kronecker_to_tensor_product_apply,
    algebra.tensor_product.tmul_mul_tmul, matrix.mul_eq_mul],
end

def tensor_to_kronecker :
  (matrix m m R ⊗[R] matrix n n R) ≃ₐ[R] (matrix (m × n) (m × n) R) :=
{ to_fun := tensor_product.to_kronecker,
  inv_fun := matrix.kronecker_to_tensor_product,
  left_inv := tensor_product.to_kronecker_to_tensor_product,
  right_inv := kronecker_to_tensor_product_to_kronecker,
  map_add' := linear_map.map_add' _,
  map_mul' := tensor_product.to_kronecker_mul,
  commutes' := λ r, by { simp_rw [algebra.algebra_map_eq_smul_one, smul_hom_class.map_smul],
    rw [algebra.tensor_product.one_def, tensor_product.to_kronecker_apply, one_kronecker_one], } }

def kronecker_to_tensor :
  matrix (m × n) (m × n) R ≃ₐ[R] (matrix m m R ⊗[R] matrix n n R) :=
tensor_to_kronecker.symm

lemma kronecker_to_tensor_to_linear_map_eq :
  (kronecker_to_tensor : matrix (n × m) (n × m) R ≃ₐ[R] _).to_linear_map
    = (kronecker_to_tensor_product
      : matrix (n × m) (n × m) R →ₗ[R] matrix n n R ⊗[R] matrix m m R) :=
rfl

end

lemma tensor_to_kronecker_to_linear_map_eq {R m n : Type*} [comm_semiring R]
  [fintype m] [fintype n] [decidable_eq m] [decidable_eq n] :
  (tensor_to_kronecker
    : (matrix m m R ⊗[R] matrix n n R) ≃ₐ[R] matrix (m × n) (m × n) R).to_linear_map
  = (tensor_product.to_kronecker
    : (matrix m m R ⊗[R] matrix n n R) →ₗ[R] matrix (m × n) (m × n) R) :=
rfl
