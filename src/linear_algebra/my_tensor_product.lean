/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.tensor_product_basis
import algebra.algebra.bilinear
import ring_theory.tensor_product

/-!
 # Some lemmas about `tensor_product`
-/

open_locale tensor_product big_operators

namespace tensor_product

variables {R M N P Q : Type*} [comm_semiring R]
  [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q]
  [module R M] [module R N] [module R P] [module R Q]

protected lemma ext_iff {g h : M ⊗[R] N →ₗ[R] P} :
  g = h ↔ (∀ (x : M) (y : N), g (x ⊗ₜ[R] y) = h (x ⊗ₜ[R] y)) :=
⟨λ h x y, by rw h, tensor_product.ext'⟩

lemma ext'_iff {g h : (M ⊗[R] N) ⊗[R] Q →ₗ[R] P} :
  (∀ (x : (M ⊗[R] N) ⊗[R] Q), g x = h x)
    ↔ ∀ (x : M) (y : N) (z : Q), g ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = h ((x ⊗ₜ[R] y) ⊗ₜ[R] z) :=
begin
  refine ⟨λ h x y z, by rw h, _⟩,
  rw ← linear_map.ext_iff,
  exact tensor_product.ext_threefold,
end

@[simp] lemma map_apply (f : M →ₗ[R] P) (t : N →ₗ[R] Q) (x : M) (y : N) :
  (tensor_product.map f t) (x ⊗ₜ[R] y) = f x ⊗ₜ t y :=
rfl

@[simp] lemma comm_commutes {g : M ⊗[R] N →ₗ[R] P}  {h : M ⊗[R] N →ₗ[R] Q} :
  (tensor_product.comm R P Q).to_linear_map ∘ₗ (tensor_product.map g h)
    = (tensor_product.map h g) ∘ₗ (tensor_product.comm R (M ⊗[R] N) (M ⊗[R] N)).to_linear_map :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  simp_rw [linear_map.comp_apply, linear_equiv.to_linear_map_eq_coe,
    linear_equiv.coe_coe, tensor_product.comm_tmul, tensor_product.map_apply,
    tensor_product.comm_tmul],
end

lemma comm_commutes' {g : M →ₗ[R] M} {h : M →ₗ[R] R} :
  (tensor_product.comm R M R).to_linear_map ∘ₗ (tensor_product.map g h)
  = (tensor_product.map h g) ∘ₗ (tensor_product.comm R M M).to_linear_map :=
begin
  simp_rw [tensor_product.ext_iff, linear_map.comp_apply, linear_equiv.to_linear_map_eq_coe,
    linear_equiv.coe_coe, tensor_product.comm_tmul, tensor_product.map_apply,
    tensor_product.comm_tmul, eq_self_iff_true, forall_2_true_iff],
end

lemma assoc_comp_map {R : Type*}
  [comm_semiring R] {M N M₂ N₂ P Q : Type*}
  [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid M₂] [add_comm_monoid N₂]
  [add_comm_monoid P] [add_comm_monoid Q]
  [module R M] [module R N] [module R M₂] [module R N₂] [module R P] [module R Q]
  (f : M →ₗ[R] P) (t : N →ₗ[R] Q) (s : M₂ →ₗ[R] N₂) :
  (tensor_product.assoc R P Q N₂).to_linear_map ∘ₗ
    (tensor_product.map (tensor_product.map f t) s) =
  (tensor_product.map f (tensor_product.map t s)) ∘ₗ
    (tensor_product.assoc R M N M₂).to_linear_map :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  simp_rw [linear_map.comp_apply, linear_equiv.to_linear_map_eq_coe,
    linear_equiv.coe_coe, tensor_product.map_apply,
    tensor_product.assoc_tmul, tensor_product.map_apply],
end

lemma ext_threefold' {R : Type*} [comm_semiring R]
  {M N P Q : Type*} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q]
  [module R M] [module R N] [module R P] [module R Q] {g h : M ⊗[R] (N ⊗[R] P) →ₗ[R] Q}
  (H : ∀ (x : M) (y : N) (z : P), g (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = h (x ⊗ₜ[R] (y ⊗ₜ[R] z))) :
  g = h :=
begin
  apply tensor_product.ext,
  ext1 x,
  rw [tensor_product.mk, tensor_product.ext_iff],
  intros y z,
  exact H x y z,
end

lemma assoc_symm_comp_map {R : Type*}
  [comm_semiring R] {M N M₂ N₂ P Q : Type*}
  [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid M₂] [add_comm_monoid N₂]
  [add_comm_monoid P] [add_comm_monoid Q]
  [module R M] [module R N] [module R M₂] [module R N₂] [module R P] [module R Q]
  (f : M →ₗ[R] P) (t : N →ₗ[R] Q) (s : M₂ →ₗ[R] N₂) :
  (tensor_product.assoc R P Q N₂).symm.to_linear_map ∘ₗ
    (tensor_product.map f (tensor_product.map t s)) =
  (tensor_product.map (tensor_product.map f t) s) ∘ₗ
    (tensor_product.assoc R M N M₂).symm.to_linear_map :=
begin
  apply tensor_product.ext_threefold',
  intros x y z,
  simp_rw [linear_map.comp_apply, linear_equiv.to_linear_map_eq_coe,
    linear_equiv.coe_coe, tensor_product.map_apply,
    tensor_product.assoc_symm_tmul, tensor_product.map_apply],
end

lemma comm_map {R : Type*}
  [comm_semiring R] {M N P Q : Type*}
  [add_comm_monoid M] [add_comm_monoid N]
  [add_comm_monoid P] [add_comm_monoid Q]
  [module R M] [module R N] [module R P] [module R Q]
  (f : M →ₗ[R] P) (t : N →ₗ[R] Q) :
  (tensor_product.comm R P Q).to_linear_map ∘ₗ
  (tensor_product.map f t) =
  (tensor_product.map t f) ∘ₗ
  (tensor_product.comm R M N).to_linear_map :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  simp_rw [linear_map.comp_apply, linear_equiv.to_linear_map_eq_coe,
    linear_equiv.coe_coe, tensor_product.map_apply,
    tensor_product.comm_tmul, tensor_product.map_apply],
end

lemma comm_symm_map {R : Type*}
  [comm_semiring R] {M N P Q : Type*}
  [add_comm_monoid M] [add_comm_monoid N]
  [add_comm_monoid P] [add_comm_monoid Q]
  [module R M] [module R N] [module R P] [module R Q]
  (f : M →ₗ[R] P) (t : N →ₗ[R] Q) :
  (tensor_product.comm R P Q).symm.to_linear_map ∘ₗ
  (tensor_product.map t f) =
  (tensor_product.map f t) ∘ₗ
  (tensor_product.comm R M N).symm.to_linear_map :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  simp_rw [linear_map.comp_apply, linear_equiv.to_linear_map_eq_coe,
    linear_equiv.coe_coe, tensor_product.map_apply,
    tensor_product.comm_symm_tmul, tensor_product.map_apply],
end

protected lemma map_sum {R : Type*} [comm_semiring R]
  {M₁ M₂ N₁ N₂ : Type*} [add_comm_monoid M₁] [add_comm_monoid M₂]
  [add_comm_monoid N₁] [add_comm_monoid N₂] [module R M₁] [module R M₂] [module R N₁] [module R N₂]
  (x : M₁ →ₗ[R] M₂) {α : Type*} (s : finset α) (n : α → (N₁ →ₗ[R] N₂)) :
  map x (∑ (a : α) in s, n a) = ∑ (a : α) in s, map x (n a) :=
begin
  simp_rw [tensor_product.ext_iff, linear_map.sum_apply, map_apply,
    linear_map.coe_fn_sum, finset.sum_apply, tmul_sum, eq_self_iff_true,
    forall_2_true_iff],
end

lemma sum_map {R : Type*} [comm_semiring R]
  {M₁ M₂ N₁ N₂ : Type*} [add_comm_monoid M₁] [add_comm_monoid M₂]
  [add_comm_monoid N₁] [add_comm_monoid N₂] [module R M₁] [module R M₂] [module R N₁] [module R N₂]
  {α : Type*} (s : finset α) (n : α → (N₁ →ₗ[R] N₂)) (x : M₁ →ₗ[R] M₂) :
  map (∑ (a : α) in s, n a) x = ∑ (a : α) in s, map (n a) x :=
begin
  simp_rw [tensor_product.ext_iff, linear_map.sum_apply, map_apply,
    linear_map.coe_fn_sum, finset.sum_apply, sum_tmul, eq_self_iff_true,
    forall_2_true_iff],
end

protected lemma map_smul {R : Type*} [comm_semiring R]
  {M₁ M₂ N₁ N₂ : Type*} [add_comm_monoid M₁] [add_comm_monoid M₂]
  [add_comm_monoid N₁] [add_comm_monoid N₂] [module R M₁] [module R M₂] [module R N₁] [module R N₂]
  (x : M₁ →ₗ[R] M₂) (y : N₁ →ₗ[R] N₂) (a : R) :
  map x (a • y) = a • (map x y) :=
begin
  simp_rw [tensor_product.ext_iff, linear_map.smul_apply, map_apply,
    linear_map.smul_apply, tmul_smul, eq_self_iff_true, forall_2_true_iff],
end

lemma smul_map {R : Type*} [comm_semiring R]
  {M₁ M₂ N₁ N₂ : Type*} [add_comm_monoid M₁] [add_comm_monoid M₂]
  [add_comm_monoid N₁] [add_comm_monoid N₂] [module R M₁] [module R M₂] [module R N₁] [module R N₂]
  (x : M₁ →ₗ[R] M₂) (y : N₁ →ₗ[R] N₂) (a : R) :
  map (a • x) y = a • (map x y) :=
begin
  simp_rw [tensor_product.ext_iff, linear_map.smul_apply, map_apply,
    linear_map.smul_apply, smul_tmul', eq_self_iff_true, forall_2_true_iff],
end

-- MOVE:
lemma add_map {R : Type*} [comm_semiring R] {M₁ M₂ N₁ N₂ : Type*}
  [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid N₁] [add_comm_monoid N₂]
  [module R M₁] [module R M₂] [module R N₁] [module R N₂]
  (x y : M₁ →ₗ[R] M₂) (z : N₁ →ₗ[R] N₂) :
  tensor_product.map (x + y) z = tensor_product.map x z + tensor_product.map y z :=
begin
  apply ext',
  intros u v,
  simp only [tensor_product.map_apply, linear_map.add_apply, add_tmul],
end

protected lemma map_zero {R : Type*} [comm_semiring R] {M₁ N₁ M₂ N₂ : Type*}
  [add_comm_monoid M₁] [add_comm_monoid N₁] [add_comm_monoid M₂] [add_comm_monoid N₂]
  [module R M₁] [module R N₁] [module R M₂] [module R N₂] (x : M₁ →ₗ[R] N₁) :
  tensor_product.map x (0 : M₂ →ₗ[R] N₂) = 0 :=
begin
  apply tensor_product.ext',
  intros,
  simp_rw [tensor_product.map_tmul, linear_map.zero_apply, tensor_product.tmul_zero],
end

protected lemma zero_map {R : Type*} [comm_semiring R] {M₁ N₁ M₂ N₂ : Type*}
  [add_comm_monoid M₁] [add_comm_monoid N₁] [add_comm_monoid M₂] [add_comm_monoid N₂]
  [module R M₁] [module R N₁] [module R M₂] [module R N₂] (x : M₁ →ₗ[R] N₁) :
  tensor_product.map (0 : M₂ →ₗ[R] N₂) x = 0 :=
begin
  apply tensor_product.ext',
  intros,
  simp_rw [tensor_product.map_tmul, linear_map.zero_apply, tensor_product.zero_tmul],
end

lemma tmul_eq_zero {R : Type*} [field R]
  {M N : Type*}
  [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  {x : M} {y : N} :
  x ⊗ₜ[R] y = 0 ↔ x = 0 ∨ y = 0 :=
begin
  let b₁ := basis.of_vector_space R M,
  let b₂ := basis.of_vector_space R N,
  split,
  { intros h,
    apply_fun (b₁.tensor_product b₂).repr at h,
    simp only [basis.tensor_product_repr_tmul_apply, finsupp.ext_iff, prod.forall,
      map_zero, finsupp.zero_apply, mul_eq_zero] at h,
    simp only [basis.ext_elem_iff b₁, b₂.ext_elem_iff, map_zero, finsupp.zero_apply,
      ← forall_or_distrib_left, ← forall_or_distrib_right],
    exact h, },
  { rintros (rfl|rfl),
    exact tensor_product.zero_tmul _ _,
    exact tensor_product.tmul_zero _ _, },
end

lemma zero_tmul_zero {R : Type*} [comm_semiring R]
  {M N : Type*}
  [add_comm_group M] [add_comm_group N] [module R M] [module R N] :
  (0 : M ⊗[R] N) = 0 ⊗ₜ 0 :=
by rw [tensor_product.zero_tmul]

lemma map_mul'_commute_iff {R M N : Type*} [comm_semiring R]
  [non_unital_non_assoc_semiring M] [non_unital_non_assoc_semiring N]
  [module R M] [module R N] [smul_comm_class R M M]
  [smul_comm_class R N N] [is_scalar_tower R M M] [is_scalar_tower R N N] {f : M →ₗ[R] N} :
  (linear_map.mul' R N).comp (tensor_product.map f f) = f.comp (linear_map.mul' R M)
    ↔ ∀ x y, f (x * y) = f x * f y :=
begin
  simp only [tensor_product.ext_iff, linear_map.comp_apply, tensor_product.map_tmul,
    linear_map.mul'_apply, eq_comm],
end

end tensor_product

lemma algebra.tensor_product.map_to_linear_map {R M N P Q : Type*} [comm_semiring R]
  [semiring M] [semiring N] [semiring P] [semiring Q] [algebra R M] [algebra R N]
  [algebra R P] [algebra R Q] (f : M →ₐ[R] N) (g : P →ₐ[R] Q) :
  (algebra.tensor_product.map f g).to_linear_map
    = tensor_product.map f.to_linear_map g.to_linear_map :=
rfl

lemma alg_hom.commute_map_mul' {R M N : Type*} [comm_semiring R]
  [semiring M] [semiring N] [algebra R M] [algebra R N] (f : M →ₐ[R] N) :
  (linear_map.mul' R N).comp
    (algebra.tensor_product.map f f).to_linear_map
    = f.to_linear_map.comp (linear_map.mul' R M) :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  simp only [linear_map.comp_apply, alg_hom.to_linear_map_apply, linear_map.mul'_apply,
    algebra.tensor_product.map_tmul, _root_.map_mul],
end

lemma alg_hom.commute_map_mul'_apply {R M N : Type*} [comm_semiring R]
  [semiring M] [semiring N] [algebra R M] [algebra R N] (f : M →ₐ[R] N) (x : M ⊗[R] M) :
  (linear_map.mul' R N)
    ((algebra.tensor_product.map f f) x)
    = f ((linear_map.mul' R M) x) :=
begin
  simp only [← linear_map.comp_apply, ← alg_hom.to_linear_map_apply],
  revert x,
  rw ← linear_map.ext_iff,
  exact alg_hom.commute_map_mul' _,
end

open tensor_product
lemma tensor_product.map_add {R : Type*} [comm_semiring R] {M₁ M₂ N₁ N₂ : Type*}
  [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid N₁] [add_comm_monoid N₂]
  [module R M₁] [module R M₂] [module R N₁] [module R N₂] (x y : M₁ →ₗ[R] M₂) (z : N₁ →ₗ[R] N₂) :
  tensor_product.map z (x + y) = map z x + map z y :=
begin
  rw tensor_product.ext_iff,
  intros,
  simp only [tensor_product.map_tmul, tmul_add, add_tmul, linear_map.add_apply],
end
