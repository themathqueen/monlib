/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.star.star_alg_hom
import algebra.algebra.equiv
import algebra.ring.idempotents

/-!
 # Some stuff on star algebra equivalences

 This file contains some obvious definitions and lemmas on star algebra equivalences.
-/


lemma alg_equiv.comp_inj {R A B C : Type*} [comm_semiring R]
  [semiring A] [semiring B] [semiring C] [algebra R A] [algebra R B] [algebra R C]
  (f : B ≃ₐ[R] C) (S T : A →ₗ[R] B) :
  f.to_linear_map ∘ₗ S = f.to_linear_map ∘ₗ T ↔ S = T :=
begin
  simp only [linear_map.ext_iff, linear_map.comp_apply, alg_equiv.to_linear_map_apply,
    f.injective.eq_iff],
end

lemma alg_equiv.inj_comp {R A B C : Type*} [comm_semiring R]
  [semiring A] [semiring B] [semiring C] [algebra R A] [algebra R B] [algebra R C]
  (f : C ≃ₐ[R] A) (S T : A →ₗ[R] B) :
  S ∘ₗ f.to_linear_map = T ∘ₗ f.to_linear_map ↔ S = T :=
begin
  refine ⟨λ h, _, λ h, by rw h⟩,
  simp_rw [linear_map.ext_iff, linear_map.comp_apply, alg_equiv.to_linear_map_apply] at h ⊢,
  intros x,
  specialize h (f.symm x),
  rw [alg_equiv.apply_symm_apply] at h,
  exact h,
end

def star_alg_equiv.to_alg_equiv {R A B : Type*} [comm_semiring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B] (f : A ≃⋆ₐ[R] B) :
  A ≃ₐ[R] B :=
{ to_fun := λ x, f x,
  inv_fun := λ x, f.symm x,
  left_inv := λ x, f.left_inv x,
  right_inv := λ x, f.right_inv x,
  map_add' := λ x y, f.map_add' x y,
  map_mul' := λ x y, f.map_mul' x y,
  commutes' := λ r, by { simp_rw [algebra.algebra_map_eq_smul_one, smul_hom_class.map_smul,
    _root_.map_one], } }

@[simp] lemma star_alg_equiv.coe_to_alg_equiv {R A B : Type*} [comm_semiring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B] (f : A ≃⋆ₐ[R] B) :
  ⇑f.to_alg_equiv = f :=
rfl

@[hint_tactic] lemma star_alg_equiv.symm_apply_eq {R A B : Type*} [comm_semiring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B] (f : A ≃⋆ₐ[R] B)
  (x : A) (y : B) :
  f.symm y = x ↔ y = f x :=
equiv.symm_apply_eq _

def star_alg_equiv.of_alg_equiv {R A B : Type*} [comm_semiring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B] (f : A ≃ₐ[R] B)
  (hf : ∀ (x : A), f (star x) = star (f x)) :
  A ≃⋆ₐ[R] B :=
{ to_fun := λ x, f x,
  inv_fun := λ x, f.symm x,
  left_inv := λ x, f.left_inv x,
  right_inv := λ x, f.right_inv x,
  map_add' := λ x y, f.map_add' x y,
  map_mul' := λ x y, f.map_mul' x y,
  map_smul' := λ r x, map_smul _ _ _,
  map_star' := λ x, hf x }

@[simp] lemma star_alg_equiv.of_alg_equiv_coe {R A B : Type*} [comm_semiring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B] (f : A ≃ₐ[R] B)
  (hf : ∀ (x : A), f (star x) = star (f x)) :
  ⇑(star_alg_equiv.of_alg_equiv f hf) = f :=
rfl

@[simp] lemma star_alg_equiv.of_alg_equiv_symm_coe {R A B : Type*} [comm_semiring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B] (f : A ≃ₐ[R] B)
  (hf : ∀ (x : A), f (star x) = star (f x)) :
  ⇑(star_alg_equiv.of_alg_equiv f hf).symm = f.symm :=
rfl

lemma star_alg_equiv.comp_eq_iff {R E₁ E₂ E₃ : Type*} [comm_semiring R] [semiring E₁]
  [semiring E₂] [add_comm_group E₃] [algebra R E₁] [algebra R E₂] [module R E₃] [has_star E₁] [has_star E₂]
  (f : E₁ ≃⋆ₐ[R] E₂) (x : E₂ →ₗ[R] E₃) (y : E₁ →ₗ[R] E₃) :
  x ∘ₗ f.to_alg_equiv.to_linear_map = y ↔ x = y ∘ₗ f.symm.to_alg_equiv.to_linear_map :=
begin
  split,
  { intros h,
    ext1,
    rw [← h],
    simp only [linear_map.comp_apply, alg_equiv.to_linear_map_apply,
      star_alg_equiv.coe_to_alg_equiv, star_alg_equiv.apply_symm_apply], },
  { rintros rfl,
    ext1,
    simp only [linear_map.comp_apply, alg_equiv.to_linear_map_apply,
      star_alg_equiv.coe_to_alg_equiv, star_alg_equiv.symm_apply_apply], },
end

lemma alg_equiv.one_to_linear_map {R E : Type*} [comm_semiring R] [semiring E] [algebra R E] :
  (1 : E ≃ₐ[R] E).to_linear_map = 1 :=
rfl


lemma alg_equiv.map_eq_zero_iff {R E₁ E₂ : Type*} [comm_semiring R] [semiring E₁]
  [semiring E₂] [algebra R E₁] [algebra R E₂] (f : E₁ ≃ₐ[R] E₂) (x : E₁) :
  f x = 0 ↔ x = 0 :=
ring_equiv.map_eq_zero_iff f.to_ring_equiv
lemma star_alg_equiv.map_eq_zero_iff {R E₁ E₂ : Type*} [comm_semiring R] [semiring E₁]
  [semiring E₂] [algebra R E₁] [algebra R E₂] [has_star E₁] [has_star E₂]
  (f : E₁ ≃⋆ₐ[R] E₂) (x : E₁) :
  f x = 0 ↔ x = 0 :=
alg_equiv.map_eq_zero_iff f.to_alg_equiv _


lemma is_idempotent_elem.mul_equiv {H₁ H₂ : Type*}
  [semiring H₁] [semiring H₂] (f : H₁ ≃* H₂) (x : H₁) :
  is_idempotent_elem (f x) ↔ is_idempotent_elem x :=
begin
  simp_rw [is_idempotent_elem, ← _root_.map_mul, function.injective.eq_iff f.injective],
end
lemma is_idempotent_elem.alg_equiv {R H₁ H₂ : Type*} [comm_semiring R]
  [semiring H₁] [semiring H₂] [algebra R H₁] [algebra R H₂] (f : H₁ ≃ₐ[R] H₂) (x : H₁) :
  is_idempotent_elem (f x) ↔ is_idempotent_elem x :=
is_idempotent_elem.mul_equiv f.to_mul_equiv x
lemma is_idempotent_elem.star_alg_equiv {R H₁ H₂ : Type*} [comm_semiring R]
  [semiring H₁] [semiring H₂] [algebra R H₁] [algebra R H₂] [has_star H₁]
  [has_star H₂] (f : H₁ ≃⋆ₐ[R] H₂) (x : H₁) :
  is_idempotent_elem (f x) ↔ is_idempotent_elem x :=
is_idempotent_elem.alg_equiv f.to_alg_equiv x

lemma star_alg_equiv.injective {R α β : Type*} [comm_semiring R]
  [semiring α] [semiring β] [algebra R α] [algebra R β] [has_star α]
  [has_star β] (f : α ≃⋆ₐ[R] β) :
  function.injective f :=
alg_equiv.injective f.to_alg_equiv


lemma alg_equiv.eq_apply_iff_symm_eq {R A B : Type*} [comm_semiring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B]
  (f : A ≃ₐ[R] B) {a : B} {b : A} :
  a = f b ↔ f.symm a = b :=
begin
  have : ∀ e : A ≃ B, a = e b ↔ e.symm a = b,
  { intros e,
    rw [← equiv.apply_eq_iff_eq e, equiv.apply_symm_apply],
    -- simp only [iff_self], 
    },
  exact this f.to_equiv,
end
lemma star_alg_equiv.eq_apply_iff_symm_eq {R A B : Type*} [comm_semiring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [has_star B]
  (f : A ≃⋆ₐ[R] B) {a : B} {b : A} :
  a = f b ↔ f.symm a = b :=
alg_equiv.eq_apply_iff_symm_eq f.to_alg_equiv
