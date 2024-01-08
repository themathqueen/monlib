/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_matrix.conj

/-!

# Reshaping matrices

This defines the identitication between `Mₙₓₘ(R)` and `Rⁿˣᵐ` (see `matrix.reshape`), and shows some obvious properties of this identification.

-/

namespace matrix

open_locale matrix

variables {R I J : Type*} [semiring R]

/-- identifies matrices $M_{I\times J}(R)$ with $R^{I \times J}$,
  this is given by $\varrho (x)_{(i,j)} = x_{ij}$ -/
def reshape :
  matrix I J R ≃ₗ[R] (I × J → R) :=
(linear_equiv.curry R _ _).symm

lemma reshape_apply (x : matrix I J R) (ij : I × J) :
  x.reshape ij = x ij.1 ij.2 :=
rfl

lemma reshape_symm_apply (x : I × J → R) (i : I) (j : J) :
  (reshape : matrix I J R ≃ₗ[R] (I × J → R)).symm x i j = x (i,j) :=
rfl

lemma reshape_symm_apply' (x : I × J → R) (ij : I × J) :
  (reshape : matrix I J R ≃ₗ[R] (I × J → R)).symm x ij.1 ij.2 = x ij :=
by rw [reshape_symm_apply x ij.1 ij.2, prod.mk.eta]

lemma reshape_one [decidable_eq I] (x y : I) :
  (1 : matrix I I R).reshape (x,y) = ite (x = y) 1 0 :=
begin
  simp_rw [matrix.reshape_apply, matrix.one_apply],
end

/-- ${\varrho(x)}^*=\varrho(\bar{x})$ -/
lemma reshape_aux_star [has_star R] (x : matrix I J R) :
  star x.reshape = xᴴᵀ.reshape :=
begin
  ext1,
  simp_rw [pi.star_apply, matrix.reshape_apply, matrix.conj_apply],
end

end matrix
