/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.tensor_product_basis
import linear_algebra.finite_dimensional
import data.is_R_or_C.basic
import linear_algebra.is_real
import linear_algebra.my_ips.op_unop
import linear_algebra.my_ips.mul_op

/-!

# tensor_finite

This file defines the star operation on a tensor product of finite-dimensional star-modules $E,F$,
i.e., ${(x \otimes y)}^*=x^* \otimes y^*$ for $x\in{E}$ and $x\in{F}$.

-/

open_locale tensor_product big_operators


section

variables {𝕜 E F G : Type*} [field 𝕜] [add_comm_group E] [add_comm_group F]
  [add_comm_group G]
  [star_add_monoid E] [star_add_monoid F] [star_add_monoid G] [module 𝕜 E] [module 𝕜 F]
  [module 𝕜 G] [star_ring 𝕜]
  [star_module 𝕜 G]
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] [finite_dimensional 𝕜 G]

noncomputable instance tensor_product.has_star :
  has_star (E ⊗[𝕜] F) :=
{ star := λ x,
   by { let b₁ := basis.of_vector_space 𝕜 E,
    let b₂ := basis.of_vector_space 𝕜 F,
    exact ∑ i j, star (((b₁.tensor_product b₂).repr x) (i,j))
      • (star (b₁ i) ⊗ₜ[𝕜] star (b₂ j)), } }

@[simp] lemma tensor_product.star_tmul [star_module 𝕜 E] [star_module 𝕜 F] (x : E) (y : F) :
  star (x ⊗ₜ[𝕜] y) = (star x) ⊗ₜ[𝕜] (star y) :=
begin
  simp_rw [star, basis.tensor_product_repr_tmul_apply, star_mul',
    mul_comm _ (star ((((basis.of_vector_space 𝕜 F).repr) y) _)), tensor_product.smul_tmul',
    ← smul_smul, tensor_product.smul_tmul (star ((((basis.of_vector_space 𝕜 F).repr) y) _)),
    ← tensor_product.tmul_sum, ← tensor_product.sum_tmul, ← @star_module.star_smul 𝕜,
    ← star_sum, basis.sum_repr],
end

lemma tensor_product.star_add
  (x y : E ⊗[𝕜] F) :
  star (x + y) = star x + star y :=
begin
  simp only [star, map_add, map_add, add_smul, star_add, finsupp.add_apply,
    finset.sum_add_distrib],
end

def tensor_product.star_is_involutive [star_module 𝕜 E] [star_module 𝕜 F] :
  function.involutive (tensor_product.has_star.star : E ⊗[𝕜] F → E ⊗[𝕜] F) :=
begin
  intros a,
  apply a.induction_on,
  { simp only [star, map_zero, finsupp.zero_apply, star_zero, zero_smul, finset.sum_const_zero], },
  { intros x y,
    simp_rw [tensor_product.star_tmul, star_star], },
  { intros x y hx hy,
    nth_rewrite 1 ← hx,
    nth_rewrite 1 ← hy,
    simp_rw [← tensor_product.star_add], },
end

@[instance] noncomputable def tensor_product.has_involutive_star [star_module 𝕜 E] [star_module 𝕜 F] :
  has_involutive_star (E ⊗[𝕜] F) :=
{ to_has_star := tensor_product.has_star,
  star_involutive := tensor_product.star_is_involutive }

@[instance] noncomputable def tensor_product.star_add_monoid [star_module 𝕜 E] [star_module 𝕜 F] :
  star_add_monoid (E ⊗[𝕜] F) :=
{ to_has_involutive_star := tensor_product.has_involutive_star,
  star_add := tensor_product.star_add }

@[instance] def tensor_product.star_module :
  star_module 𝕜 (E ⊗[𝕜] F) :=
{ star_smul := λ α x, by { simp only [star, map_smul, finsupp.smul_apply, star_smul,
    smul_assoc, ← finset.smul_sum], } }

lemma tensor_product.map_real
  {A B E F : Type*} [add_comm_group A] [add_comm_group B]
  [add_comm_group E] [add_comm_group F]
  [star_add_monoid A] [star_add_monoid B] [star_add_monoid E] [star_add_monoid F]
  [module 𝕜 A] [module 𝕜 B] [module 𝕜 E] [module 𝕜 F]
  [star_module 𝕜 A] [star_module 𝕜 B] [star_module 𝕜 E] [star_module 𝕜 F]
  [finite_dimensional 𝕜 A] [finite_dimensional 𝕜 B] [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F]
  (f : E →ₗ[𝕜] F) (g : A →ₗ[𝕜] B) :
  (tensor_product.map f g).real = (tensor_product.map f.real g.real) :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  simp only [linear_map.real_eq, tensor_product, tensor_product.star_tmul,
    tensor_product.map_tmul],
end

variables (A : Type*)
  [ring A] [module 𝕜 A] [star_ring A] [star_module 𝕜 A]
  [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A]
  [finite_dimensional 𝕜 A]

lemma linear_map.mul'_real :
  (linear_map.mul' 𝕜 A).real = linear_map.mul' 𝕜 A ∘ₗ (tensor_product.comm 𝕜 A A).to_linear_map :=
begin
  rw tensor_product.ext_iff,
  intros a b,
  simp only [linear_map.real_eq, tensor_product.star_tmul,
    linear_equiv.to_linear_map_eq_coe, linear_equiv.coe_coe, linear_map.comp_apply,
    tensor_product.comm_tmul, linear_map.mul'_apply, star_mul, star_star],
end

variables [star_module 𝕜 E] [star_module 𝕜 F]

lemma tensor_product.assoc_real :
  (tensor_product.assoc 𝕜 E F G : E ⊗[𝕜] F ⊗[𝕜] G →ₗ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G)).real
    = tensor_product.assoc 𝕜 E F G :=
begin
  apply tensor_product.ext_threefold,
  intros a b c,
  simp only [linear_map.real_eq, tensor_product.star_tmul, linear_equiv.coe_coe,
    tensor_product.assoc_tmul, star_star],
end

lemma tensor_product.comm_real :
  (tensor_product.comm 𝕜 E F : E ⊗[𝕜] F →ₗ[𝕜] F ⊗[𝕜] E).real
    = tensor_product.comm 𝕜 E F :=
begin
  apply tensor_product.ext',
  intros a b,
  simp only [linear_map.real_eq, tensor_product.star_tmul, linear_equiv.coe_coe,
    tensor_product.comm_tmul, star_star],
end

lemma tensor_product.lid_real :
  (tensor_product.lid 𝕜 E : 𝕜 ⊗[𝕜] E →ₗ[𝕜] E).real = tensor_product.lid 𝕜 E :=
begin
  apply tensor_product.ext',
  intros a b,
  simp only [linear_map.real_eq, tensor_product.star_tmul, linear_equiv.coe_coe,
    tensor_product.lid_tmul, star_star, star_smul],
end

lemma tensor_product.rid_real :
  (tensor_product.rid 𝕜 E : E ⊗[𝕜] 𝕜 →ₗ[𝕜] E).real = tensor_product.rid 𝕜 E :=
begin
  apply tensor_product.ext',
  intros a b,
  simp only [linear_map.real_eq, tensor_product.star_tmul, linear_equiv.coe_coe,
    tensor_product.rid_tmul, star_star, star_smul],
end

lemma tensor_op_star_apply (x : E) (y : Eᵐᵒᵖ) :
  star (x ⊗ₜ[𝕜] y) = star x ⊗ₜ[𝕜] (op : E →ₗ[𝕜] Eᵐᵒᵖ) (star ((unop : Eᵐᵒᵖ →ₗ[𝕜] E) y)) :=
begin
  simp only [tensor_product.star_tmul],
  refl,
end

lemma ten_swap_star (x : E ⊗[𝕜] Eᵐᵒᵖ) :
  star (ten_swap x) = ten_swap (star x) :=
begin
  apply x.induction_on,
  { simp only [star_zero, map_zero], },
  { intros,
    simp only [ten_swap_apply, tensor_op_star_apply, unop_apply, op_apply, mul_opposite.unop_op,
      mul_opposite.op_unop], },
  { intros z w hz hw,
    simp only [map_add, star_add_monoid.star_add, hz, hw], },
end


end
