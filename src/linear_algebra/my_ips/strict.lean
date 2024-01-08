/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.tensor_product
import algebra.algebra.bilinear

/-!
 # Strict tensor product (wip)
-/

variables {R E F G : Type*} [comm_semiring R] [add_comm_group E]
  [add_comm_group F] [add_comm_group G] [module R E] [module R F] [module R G]

open_locale tensor_product

@[instance] def tensor_product.assoc_has_coe :
  has_coe (E ⊗[R] F ⊗[R] G) (E ⊗[R] (F ⊗[R] G)) :=
{ coe := λ x, tensor_product.assoc R E F G x }
@[instance] def tensor_product.assoc_symm_has_coe :
  has_coe (E ⊗[R] (F ⊗[R] G)) (E ⊗[R] F ⊗[R] G) :=
{ coe := λ x, (tensor_product.assoc R E F G).symm x }
@[simp] lemma tensor_product.assoc_tmul_coe
  (a : E) (b : F) (c : G) :
  a ⊗ₜ[R] b ⊗ₜ[R] c = ↑(a ⊗ₜ[R] (b ⊗ₜ[R] c)) :=
rfl
lemma tensor_product.assoc_coe_coe (a : E ⊗[R] F ⊗[R] G) :
  a = ↑(a : E ⊗[R] (F ⊗[R] G)) :=
by unfold_coes; simp only [linear_equiv.to_fun_eq_coe, linear_equiv.symm_apply_apply]
@[simp] lemma tensor_product.tmul_assoc_coe
  (a : E) (b : F) (c : G) :
  a ⊗ₜ[R] (b ⊗ₜ[R] c) = ↑((a ⊗ₜ[R] b) ⊗ₜ[R] c) :=
rfl
lemma tensor_product.coe_coe_assoc (a : E ⊗[R] (F ⊗[R] G)) :
  a = ↑(a : E ⊗[R] F ⊗[R] G) :=
by unfold_coes; simp only [linear_equiv.to_fun_eq_coe, linear_equiv.apply_symm_apply]

@[instance] def tensor_product.lid_has_coe :
  has_coe (R ⊗[R] E) E :=
{ coe := λ x, tensor_product.lid R E x }
@[instance] def tensor_product.rid_has_coe :
  has_coe (E ⊗[R] R) E :=
{ coe := λ x, tensor_product.rid R E x }
@[instance] def tensor_product.lid_symm_has_coe :
  has_coe E (R ⊗[R] E) :=
{ coe := λ x, (tensor_product.lid R E).symm x }
@[instance] def tensor_product.rid_symm_has_coe :
  has_coe E (E ⊗[R] R) :=
{ coe := λ x, (tensor_product.rid R E).symm x }

lemma tensor_product.lid_coe (x : E) (r : R) :
  ↑(r ⊗ₜ[R] x) = r • x :=
rfl
lemma tensor_product.rid_coe (x : E) (r : R) :
  ↑(x ⊗ₜ[R] r) = r • x :=
rfl
lemma tensor_product.lid_symm_coe (x : E) :
  (x : R ⊗[R] E) = (1 : R) ⊗ₜ[R] x :=
rfl
lemma tensor_product.rid_symm_coe (x : E) :
  (x : E ⊗[R] R) = x ⊗ₜ[R] (1 : R) :=
rfl
lemma tensor_product.lid_coe' (x : E) (r : R) :
  r ⊗ₜ[R] x = r • x :=
by rw [tensor_product.lid_symm_coe, tensor_product.smul_tmul', smul_eq_mul, mul_one]
lemma tensor_product.rid_coe' (x : E) (r : R) :
  x ⊗ₜ[R] r = r • x :=
by rw [tensor_product.rid_symm_coe, tensor_product.smul_tmul', tensor_product.smul_tmul,
  smul_eq_mul, mul_one]
lemma tensor_product.lid_coe_rid_coe (x : E) :
  (x : R ⊗[R] E) = (x : E ⊗[R] R) :=
begin
  unfold_coes,
  simp only [linear_equiv.to_fun_eq_coe, linear_equiv.apply_symm_apply],
end

@[instance] def fun_tensor_product_assoc_has_coe {A : Type*} :
  has_coe ((E ⊗[R] F ⊗[R] G) → A) ((E ⊗[R] (F ⊗[R] G)) → A) :=
{ coe := λ f x, f x }
@[instance] def linear_map.tensor_product_assoc_has_coe {A : Type*}
  [add_comm_monoid A] [module R A] :
  has_coe ((E ⊗[R] F ⊗[R] G) →ₗ[R] A) ((E ⊗[R] (F ⊗[R] G)) →ₗ[R] A) :=
{ coe := λ f, f ∘ₗ (((tensor_product.assoc R E F G).symm
  : E ⊗[R] (F ⊗[R] G) ≃ₗ[R] E ⊗[R] F ⊗[R] G) : E ⊗[R] (F ⊗[R] G) →ₗ[R] E ⊗[R] F ⊗[R] G) }
@[instance] def fun_tensor_product_assoc_has_coe' {A : Type*} :
  has_coe ((E ⊗[R] (F ⊗[R] G)) → A) (((E ⊗[R] F) ⊗[R] G) → A) :=
{ coe := λ f x, f x }
@[instance] def linear_map.tensor_product_assoc_has_coe' {A : Type*}
  [add_comm_monoid A] [module R A] :
  has_coe (E ⊗[R] (F ⊗[R] G) →ₗ[R] A) ((E ⊗[R] F ⊗[R] G) →ₗ[R] A) :=
{ coe := λ f, f ∘ₗ (((tensor_product.assoc R E F G)
  : E ⊗[R] F ⊗[R] G ≃ₗ[R] E ⊗[R] (F ⊗[R] G)) : E ⊗[R] F ⊗[R] G →ₗ[R] E ⊗[R] (F ⊗[R] G)) }
@[instance] def fun_lid_has_coe {A : Type*} :
  has_coe ((R ⊗[R] E) → A) (E → A) :=
{ coe := λ f x, f x }
@[instance] def linear_map.tensor_product_lid_has_coe {A : Type*}
  [add_comm_monoid A] [module R A] :
  has_coe (R ⊗[R] E →ₗ[R] A) (E →ₗ[R] A) :=
{ coe := λ f, f ∘ₗ ↑(tensor_product.lid R E).symm }
@[instance] def fun_lid_has_coe' {A : Type*} :
  has_coe (E → A) ((R ⊗[R] E) → A) :=
{ coe := λ f x, f x }
@[instance] def linear_map.tensor_product_lid_has_coe' {A : Type*}
  [add_comm_monoid A] [module R A] :
  has_coe (E →ₗ[R] A) (R ⊗[R] E →ₗ[R] A) :=
{ coe := λ f, f ∘ₗ ↑(tensor_product.lid R E) }
@[instance] def fun_rid_has_coe {A : Type*} :
  has_coe ((E ⊗[R] R) → A) (E → A) :=
{ coe := λ f x, f x }
@[instance] def linear_map.tensor_product_rid_has_coe {A : Type*}
  [add_comm_monoid A] [module R A] :
  has_coe (E ⊗[R] R →ₗ[R] A) (E →ₗ[R] A)  :=
{ coe := λ f, f ∘ₗ ↑(tensor_product.rid R E).symm }
@[instance] def fun_rid_has_coe' {A : Type*} :
  has_coe (E → A) ((E ⊗[R] R) → A) :=
{ coe := λ f x, f x }
@[instance] def linear_map.tensor_product_rid_has_coe' {A : Type*}
  [add_comm_monoid A] [module R A] :
  has_coe (E →ₗ[R] A) (E ⊗[R] R →ₗ[R] A) :=
{ coe := λ f, f ∘ₗ ↑(tensor_product.rid R E) }

lemma linear_map.lid_coe {A : Type*}
  [add_comm_monoid A] [module R A] (f : E →ₗ[R] A) :
  f = (f : R ⊗[R] E →ₗ[R] A) :=
by unfold_coes; { simp only [linear_map.comp_assoc, linear_equiv.to_linear_map_eq_coe,
  linear_equiv.comp_coe, linear_equiv.symm_trans_self, linear_equiv.refl_to_linear_map,
  linear_map.comp_id], }
lemma linear_map.lid_symm_coe {A : Type*}
  [add_comm_monoid A] [module R A] (f : R ⊗[R] E →ₗ[R] A) :
  f = (f : E →ₗ[R] A) :=
by unfold_coes; { simp only [linear_map.comp_assoc, linear_equiv.to_linear_map_eq_coe,
  linear_equiv.comp_coe, linear_equiv.self_trans_symm, linear_equiv.refl_to_linear_map,
  linear_map.comp_id], }
lemma linear_map.rid_coe {A : Type*}
  [add_comm_monoid A] [module R A] (f : E →ₗ[R] A) :
  f = (f : E ⊗[R] R →ₗ[R] A) :=
by unfold_coes; { simp only [linear_map.comp_assoc, linear_equiv.to_linear_map_eq_coe,
  linear_equiv.comp_coe, linear_equiv.symm_trans_self, linear_equiv.refl_to_linear_map,
  linear_map.comp_id], }
lemma linear_map.rid_symm_coe {A : Type*}
  [add_comm_monoid A] [module R A] (f : E ⊗[R] R →ₗ[R] A) :
  f = (f : E →ₗ[R] A) :=
by unfold_coes; { simp only [linear_map.comp_assoc, linear_equiv.to_linear_map_eq_coe,
  linear_equiv.comp_coe, linear_equiv.self_trans_symm, linear_equiv.refl_to_linear_map,
  linear_map.comp_id], }

example {A : Type*} (f : (E ⊗[R] (F ⊗[R] G)) → A) (g : ((E ⊗[R] F) ⊗[R] G) → A) :
  f = ↑(↑f : E ⊗[R] F ⊗[R] G → A) :=
begin
  unfold_coes,
  simp only [linear_equiv.to_fun_eq_coe, linear_equiv.apply_symm_apply],
end
