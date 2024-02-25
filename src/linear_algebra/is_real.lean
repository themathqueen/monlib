/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.star.star_alg_hom
import algebra.star.big_operators
import linear_algebra.inner_aut
import algebra.algebra.basic

/-!
 # Real linear maps (a.k.a. star-preserving linear maps)

 This file defines the function `linear_map.real` which maps a linear map `φ.real (x) = star (φ (star x))`; so that `φ` is real (star-preserving) if and only if `φ = φ.real`.
-/

def linear_map.is_real {E F K : Type*} [semiring K] [add_comm_monoid E]
  [add_comm_monoid F] [module K E] [module K F] [has_star E] [has_star F]
  (φ : E →ₗ[K] F) : Prop :=
∀ x, φ (star x) = star (φ x)

section sec

variables {E F K : Type*} [add_comm_monoid E] [star_add_monoid E]
  [add_comm_monoid F] [star_add_monoid F] [semiring K]
  [module K E] [module K F] [has_involutive_star K] [star_module K E] [star_module K F]
def linear_map.real (φ : E →ₗ[K] F) :
  (E →ₗ[K] F) :=
{ to_fun := λ x, star (φ (star x)),
  map_add' := λ x y, by { simp only [star_add, map_add], },
  map_smul' := λ r x, by { simp only [star_smul, smul_hom_class.map_smul,
    star_star, ring_hom.id_apply], } }

lemma linear_map.real_eq (φ : E →ₗ[K] F) (x : E) :
  φ.real x = star (φ (star x)) :=
rfl

lemma linear_map.is_real_iff (φ : E →ₗ[K] F) :
  φ.is_real ↔ φ.real = φ :=
begin
  simp_rw [linear_map.is_real, linear_map.ext_iff, linear_map.real, linear_map.coe_mk,
    eq_star_iff_eq_star, eq_comm],
end

lemma linear_map.real_add (f g : E →ₗ[K] F) :
  (f + g).real = f.real + g.real :=
begin
  ext1,
  simp only [linear_map.real, linear_map.add_apply, linear_map.coe_mk, star_add],
end

open_locale big_operators
lemma linear_map.real_sum {n : Type*} {s : finset n} (f : n → (E →ₗ[K] F)) :
  (∑ i : n in s, f i).real = ∑ i : n in s, (f i).real :=
begin
  ext1,
  simp only [linear_map.real, linear_map.sum_apply, linear_map.coe_mk, star_sum],
end

lemma linear_map.real_real (f : E →ₗ[K] F) :
  f.real.real = f :=
begin
  ext1,
  simp only [linear_map.real, linear_map.coe_mk, star_star],
end

lemma linear_map.real_comp {G : Type*} [non_unital_semiring G] [star_ring G] [module K G]
  [star_module K G] (f : E →ₗ[K] F) (g : G →ₗ[K] E) :
  (f ∘ₗ g).real = f.real ∘ₗ g.real :=
begin
  ext1,
  simp only [linear_map.real, linear_map.comp_apply, linear_map.coe_mk, star_star],
end

lemma linear_map.real_star_alg_equiv_conj {E K : Type*} [comm_semiring K] [semiring E]
  [algebra K E] [has_involutive_star K] [star_ring E] [star_module K E]
  (f : E →ₗ[K] E) (φ : E ≃⋆ₐ[K] E) :
(φ.to_alg_equiv.to_linear_equiv.to_linear_map ∘ₗ f
  ∘ₗ φ.symm.to_alg_equiv.to_linear_equiv.to_linear_map).real
    = φ.to_alg_equiv.to_linear_equiv.to_linear_map ∘ₗ f.real
      ∘ₗ φ.symm.to_alg_equiv.to_linear_equiv.to_linear_map :=
begin
  ext1,
  simp only [linear_map.real, linear_map.coe_mk, linear_map.comp_apply,
    linear_equiv.coe_to_linear_map, alg_equiv.to_linear_equiv_apply,
    star_alg_equiv.coe_to_alg_equiv, map_star],
end

lemma linear_map.real_star_alg_equiv_conj_iff {E K : Type*} [comm_semiring K] [semiring E]
  [algebra K E] [has_involutive_star K] [star_ring E] [star_module K E]
  (f : E →ₗ[K] E) (φ : E ≃⋆ₐ[K] E) :
(φ.to_alg_equiv.to_linear_equiv.to_linear_map ∘ₗ f
  ∘ₗ φ.symm.to_alg_equiv.to_linear_equiv.to_linear_map).is_real
    ↔ f.is_real :=
begin
  simp_rw [linear_map.is_real_iff, linear_map.real_star_alg_equiv_conj, linear_map.ext_iff,
    linear_map.comp_apply, linear_equiv.coe_to_linear_map, alg_equiv.to_linear_equiv_apply,
    star_alg_equiv.coe_to_alg_equiv, ← star_alg_equiv.symm_apply_eq,
    star_alg_equiv.symm_apply_apply],
  refine ⟨λ h x, _, λ h x, h _⟩,
  specialize h (φ x),
  simp_rw [star_alg_equiv.symm_apply_apply] at h,
  exact h,
end

def linear_map.real_ring_equiv {R E : Type*} [semiring R]
  [non_unital_normed_ring E] [star_ring E] [module R E]
  [has_involutive_star R] [star_module R E] :
  (E →ₗ[R] E) ≃+* (E →ₗ[R] E) :=
{ to_fun := λ f, f.real,
  inv_fun := λ f, f.real,
  map_add' := λ f g, linear_map.real_add _ _,
  map_mul' := λ f g, linear_map.real_comp _ _,
  left_inv := λ f, linear_map.real_real _,
  right_inv := λ f, linear_map.real_real _ }

lemma linear_map.mul_right_real {E K : Type*} [comm_semiring K] [non_unital_semiring E]
  [has_involutive_star K] [star_ring E] [module K E]
  [star_module K E] [smul_comm_class K E E] [is_scalar_tower K E E] (x : E) :
  (linear_map.mul_right K x).real = linear_map.mul_left K (star x) :=
begin
  ext1 u,
  simp_rw [linear_map.real_eq, linear_map.mul_right_apply, linear_map.mul_left_apply,
    star_mul, star_star],
end

lemma linear_map.mul_left_real {E K : Type*} [comm_semiring K] [non_unital_semiring E]
  [has_involutive_star K] [star_ring E] [module K E]
  [star_module K E] [smul_comm_class K E E] [is_scalar_tower K E E] (x : E) :
  (linear_map.mul_left K x).real = linear_map.mul_right K (star x) :=
begin
  ext1 u,
  simp_rw [linear_map.real_eq, linear_map.mul_right_apply, linear_map.mul_left_apply,
    star_mul, star_star],
end

end sec

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [star_add_monoid E] [star_module 𝕜 E]
  [finite_dimensional 𝕜 E]

lemma linear_map.real.spectrum (φ : E →ₗ[𝕜] E) :
  spectrum 𝕜 φ.real = star (spectrum 𝕜 φ) :=
begin
  ext,
  simp_rw [set.mem_star, ← module.End.has_eigenvalue_iff_mem_spectrum,
    ← module.End.has_eigenvector_iff_has_eigenvalue, linear_map.real_eq,
    star_eq_iff_star_eq, star_smul],
  split; rintros ⟨v, ⟨h, hv⟩⟩,
  { exact ⟨star v, h.symm, star_ne_zero.mpr hv⟩, },
  { refine ⟨star v, _, star_ne_zero.mpr hv⟩,
    rw star_star,
    exact h.symm, },
end

lemma linear_map.real.eigenspace {E : Type*} [normed_add_comm_group E] [inner_product_space 𝕜 E]
  [star_add_monoid E] [star_module 𝕜 E]
  (φ : E →ₗ[𝕜] E) (α : 𝕜) (x : E) :
  x ∈ module.End.eigenspace φ.real α ↔ star x ∈ module.End.eigenspace φ (star α) :=
begin
  simp_rw [module.End.mem_eigenspace_iff, linear_map.real_eq, star_eq_iff_star_eq,
    star_smul, eq_comm],
end

lemma linear_map.real_neg {E : Type*} {F : Type*} {K : Type*} [add_comm_monoid E]
  [star_add_monoid E] [add_comm_group F] [star_add_monoid F]
  [semiring K]  [module K E] [module K F] [has_involutive_star K]
  [star_module K E] [star_module K F] (f : E →ₗ[K] F) :
  (-f).real = - f.real :=
begin
  ext,
  simp only [linear_map.neg_apply, linear_map.real_eq, star_neg],
end

lemma linear_map.real_sub {E : Type*} {F : Type*} {K : Type*} [add_comm_monoid E]
  [star_add_monoid E] [add_comm_group F] [star_add_monoid F]
  [semiring K]  [module K E] [module K F] [has_involutive_star K]
  [star_module K E] [star_module K F] (f g : E →ₗ[K] F) :
  (f - g).real = f.real - g.real :=
begin
  simp_rw [sub_eq_add_neg, ← linear_map.real_neg],
  exact linear_map.real_add _ _,
end

lemma linear_map.real_smul {E F K : Type*} [comm_semiring K] [non_unital_semiring E]
  [non_unital_semiring F] [star_ring K] [star_ring E] [star_ring F]
  [module K E] [module K F] [star_module K E] [star_module K F] (f : E →ₗ[K] F) (α : K) :
  (α • f).real = (star_ring_end K α) • f.real :=
begin
  ext,
  simp_rw [linear_map.real_eq, linear_map.smul_apply, star_smul, star_ring_end_apply],
  refl,
end

lemma linear_map.real_inj_eq {E F K : Type*} [semiring K] [non_unital_semiring E]
  [non_unital_semiring F] [has_involutive_star K] [star_ring E] [star_ring F] [module K E]
  [module K F] [star_module K E] [star_module K F] (f g : E →ₗ[K] F) :
  f = g ↔ f.real = g.real :=
begin
  refine ⟨λ h, by rw h, λ h, _⟩,
  rw [← linear_map.real_real f, h, linear_map.real_real],
end

lemma linear_map.is_real_one {E K : Type*} [semiring K] [add_comm_monoid E]
  [module K E] [has_star E] :
  (1 : E →ₗ[K] E).is_real :=
λ _, rfl

lemma linear_map.real_one {E K : Type*} [semiring K] [has_involutive_star K] [add_comm_monoid E]
  [star_add_monoid E] [module K E] [star_module K E] :
  (1 : E →ₗ[K] E).real = 1 :=
(linear_map.is_real_iff _).mp linear_map.is_real_one

