/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.algebra.bilinear
import linear_algebra.my_tensor_product

/-!
 # lmul and rmul (the left and right multiplication maps)

 Basically just copies of `linear_map.mul_left` and `linear_map.mul_right` but defined as linear maps.

-/

section

variables {R E F : Type*} [comm_semiring R] [non_unital_non_assoc_semiring E]
  [non_unital_non_assoc_semiring F] [module R E] [module R F]
  [smul_comm_class R E E] [smul_comm_class R F F] [is_scalar_tower R E E] [is_scalar_tower R F F]
  (f : E ≃* F)

lemma linear_map.mul_left_conj_of_mul_equiv (x : E) :
  f ∘ (linear_map.mul_left R x) ∘ f.symm = linear_map.mul_left R (f x) :=
begin
  ext,
  simp_rw [function.comp_apply, linear_map.mul_left_apply, map_mul, mul_equiv.apply_symm_apply],
end

lemma linear_map.mul_right_conj_of_mul_equiv (x : E) :
  f ∘ (linear_map.mul_right R x) ∘ f.symm = linear_map.mul_right R (f x) :=
begin
  ext,
  simp_rw [function.comp_apply, linear_map.mul_right_apply, map_mul, mul_equiv.apply_symm_apply],
end

end

local notation `l(` x `,` y `)` := y →ₗ[x] y

variables {R H₁ H₂ : Type*} [comm_semiring R]
  -- [semiring H₁] [semiring H₂]
  -- [algebra R H₁] [algebra R H₂]
  [non_unital_non_assoc_semiring H₁] [module R H₁] [smul_comm_class R H₁ H₁]
  [is_scalar_tower R H₁ H₁]
  [non_unital_non_assoc_semiring H₂] [module R H₂] [smul_comm_class R H₂ H₂]
  [is_scalar_tower R H₂ H₂]

lemma left_module_map_iff {H₁ : Type*} [semiring H₁] [algebra R H₁]
  {x : l(R, H₁)} :
  (∀ a b : H₁, x (a * b) = a * x b) ↔ x = linear_map.mul_right R (x 1) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.mul_right_apply],
  split; intro h; intros,
  { rw [← h, mul_one], },
  { rw [h, mul_assoc, ← h], },
end
lemma right_module_map_iff {H₂ : Type*} [semiring H₂] [algebra R H₂] {x : l(R, H₂)} :
  (∀ a b : H₂, x (a * b) = x a * b) ↔ x = linear_map.mul_left R (x 1) :=
begin
  simp_rw [linear_map.ext_iff, linear_map.mul_left_apply],
  split; intro h; intros,
  { rw [← h, one_mul], },
  { rw [h, ← mul_assoc, ← h], },
end

def lmul :
  H₁ →ₗ[R] l(R, H₁) :=
{ to_fun := λ x, linear_map.mul_left R x,
  map_add' := λ x y, by { ext1,
    simp only [linear_map.mul_left_apply, add_mul, linear_map.add_apply], },
  map_smul' := λ r x, by { ext1,
    simp only [linear_map.mul_left_apply, linear_map.smul_apply,
      ring_hom.id_apply, smul_mul_assoc], } }

lemma lmul_apply (x y : H₁) :
  (lmul x : l(R, H₁)) y = x * y :=
rfl

lemma lmul_eq_mul (x : H₁) :
  lmul x = linear_map.mul_left R x :=
rfl

lemma lmul_eq_alg_lmul {H₁ : Type*} [semiring H₁] [algebra R H₁] (x : H₁) :
  (lmul x : l(R, H₁)) = algebra.lmul R H₁ x :=
rfl

lemma lmul_one {H₁ : Type*} [non_assoc_semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁] :
  (lmul (1 : H₁) : l(R, H₁)) = 1 :=
by { ext, simp_rw [lmul_apply, linear_map.one_apply, one_mul], }

def rmul :
  H₂ →ₗ[R] l(R, H₂) :=
{ to_fun := λ x, linear_map.mul_right R x,
  map_add' := λ x y, by { ext1,
    simp only [linear_map.mul_right_apply, mul_add, linear_map.add_apply], },
  map_smul' := λ r x, by { ext1,
    simp only [linear_map.mul_right_apply, linear_map.smul_apply,
      ring_hom.id_apply,  mul_smul_comm], } }

lemma rmul_apply (x y : H₂) :
  (rmul x : l(R, H₂)) y = y * x :=
rfl

lemma rmul_eq_mul (x : H₂) :
  rmul x = linear_map.mul_right R x :=
rfl

lemma rmul_one {H₁ : Type*} [non_assoc_semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁] :
  (rmul (1 : H₁) : l(R, H₁)) = 1 :=
begin
  ext,
  simp only [rmul_apply, mul_one, linear_map.one_apply],
end

open_locale tensor_product
local notation x ` ⊗ₘ ` y := tensor_product.map x y

def rmul_map_lmul :
  (H₁ ⊗[R] H₂) →ₗ[R] l(R, H₁ ⊗[R] H₂) :=
(tensor_product.hom_tensor_hom_map R H₁ H₂ H₁ H₂) ∘ₗ (rmul ⊗ₘ lmul)

lemma rmul_map_lmul_apply (x : H₁) (y : H₂) :
  rmul_map_lmul (x ⊗ₜ[R] y) = (rmul x ⊗ₘ lmul y) :=
rfl

lemma rmul_map_lmul_one
  {H₁ : Type*} [non_assoc_semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁]
  {H₂ : Type*} [non_assoc_semiring H₂] [module R H₂]
  [smul_comm_class R H₂ H₂] [is_scalar_tower R H₂ H₂] :
  rmul_map_lmul (1 ⊗ₜ 1 : H₁ ⊗[R] H₂) = 1 :=
begin
  rw tensor_product.ext_iff,
  intros a b,
  simp_rw [rmul_map_lmul_apply, tensor_product.map_tmul,
    rmul_apply, lmul_apply, mul_one, one_mul, linear_map.one_apply],
end

open_locale big_operators
lemma linear_map.mul_left_sum {R : Type*} {A : Type*} [comm_semiring R]
  [non_unital_non_assoc_semiring A] [module R A] [smul_comm_class R A A]
  [is_scalar_tower R A A] {n : Type*} [fintype n] {s : finset n} {x : n → A} :
  ∑ i : n in s, linear_map.mul_left R (x i) = linear_map.mul_left R (∑ i : n in s, x i) :=
(linear_map.map_sum lmul).symm
lemma linear_map.mul_right_sum {R : Type*} {A : Type*} [comm_semiring R]
  [non_unital_non_assoc_semiring A] [module R A] [smul_comm_class R A A]
  [is_scalar_tower R A A] {n : Type*} [fintype n] {s : finset n} {x : n → A} :
  ∑ i : n in s, linear_map.mul_right R (x i) = linear_map.mul_right R (∑ i : n in s, x i) :=
(linear_map.map_sum rmul).symm

lemma lmul_eq_zero_iff {H₁ : Type*} [semiring H₁] [algebra R H₁] (x : H₁) :
  (lmul x : l(R, H₁)) = 0 ↔ x = 0 :=
linear_map.mul_left_eq_zero_iff _

lemma rmul_eq_zero_iff {H₁ : Type*} [semiring H₁] [algebra R H₁] (x : H₁) :
  (rmul x : l(R, H₁)) = 0 ↔ x = 0 :=
linear_map.mul_right_eq_zero_iff _

lemma lmul_eq_one_iff {H₁ : Type*} [non_assoc_semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁] (x : H₁) :
  (lmul x : l(R, H₁)) = 1 ↔ x = 1 :=
begin
  simp_rw [linear_map.ext_iff, lmul_apply, linear_map.one_apply],
  refine ⟨λ h, _, λ h a, by rw [h, one_mul]⟩,
  { specialize h 1,
    rw [mul_one] at h,
    exact h, },
end

lemma linear_map.mul_left_eq_one_iff {H₁ : Type*} [non_assoc_semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁] (x : H₁) :
  linear_map.mul_left R x = 1 ↔ x = 1 :=
lmul_eq_one_iff _

lemma rmul_eq_one_iff {H₁ : Type*} [non_assoc_semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁] (x : H₁) :
  (rmul x : l(R, H₁)) = 1 ↔ x = 1 :=
begin
  simp_rw [linear_map.ext_iff, rmul_apply, linear_map.one_apply],
  refine ⟨λ h, _, λ h a, by rw [h, mul_one]⟩,
  { specialize h 1,
    rw [one_mul] at h,
    exact h, },
end

lemma linear_map.mul_right_eq_one_iff {H₁ : Type*} [non_assoc_semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁] (x : H₁) :
  linear_map.mul_right R x = 1 ↔ x = 1 :=
rmul_eq_one_iff _

lemma linear_map.mul_left_eq_one_or_zero_iff_mul_right_tfae {H₁ : Type*} [semiring H₁] [algebra R H₁]
  (x : H₁) (p : Prop) [decidable p] :
  tfae [linear_map.mul_left R x = ite p 1 0,
    linear_map.mul_right R x = ite p 1 0,
    x = ite p 1 0] :=
begin
  by_cases p,
  { simp_rw [h, if_true, linear_map.mul_left_eq_one_iff, linear_map.mul_right_eq_one_iff],
    tfae_finish, },
  { simp_rw [h, if_false, linear_map.mul_left_eq_zero_iff, linear_map.mul_right_eq_zero_iff],
    tfae_finish, },
end
lemma linear_map.mul_left_eq_one_or_zero_iff_mul_right {H₁ : Type*}
  [semiring H₁] [algebra R H₁] (x : H₁) (p : Prop) [decidable p] :
  linear_map.mul_left R x = ite p 1 0 ↔ linear_map.mul_right R x = ite p 1 0 :=
list.tfae.out (@linear_map.mul_left_eq_one_or_zero_iff_mul_right_tfae R _ H₁ _ _ x p _) 0 1


lemma linear_map.mul_right_smul (x : H₁) (α : R) :
  linear_map.mul_right R (α • x) = α • linear_map.mul_right R x :=
rmul.map_smul _ _

lemma linear_map.mul_left_smul (x : H₁) (α : R) :
  linear_map.mul_left R (α • x) = α • linear_map.mul_left R x :=
lmul.map_smul _ _

lemma linear_map.mul_left_comp_inj {H₁ : Type*} [semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁]
  (f g : H₁ →ₗ[R] H₂) (x : H₁) [invertible x] :
  f ∘ₗ linear_map.mul_left R x = g ∘ₗ linear_map.mul_left R x ↔ f = g :=
begin
  refine ⟨_, λ h, by rw h⟩,
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, linear_map.mul_left_apply],
  intros h y,
  specialize h (⅟ x * y),
  simp_rw [← mul_assoc, mul_inv_of_self, one_mul] at h,
  exact h,
end
lemma linear_map.mul_left_inj {H₁ : Type*} [semiring H₁] [module R H₁]
  [smul_comm_class R H₁ H₁] [is_scalar_tower R H₁ H₁] (x : H₁) [invertible x] (y z : H₁) :
  linear_map.mul_left R x y = linear_map.mul_left R x z ↔ y = z :=
is_unit.mul_right_inj (is_unit_of_invertible x)
