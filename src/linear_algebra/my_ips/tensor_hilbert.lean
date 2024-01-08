/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.adjoint
import preq.finset
import linear_algebra.my_ips.basic

/-!

 # Tensor product of inner product spaces

  This file constructs the tensor product of finite-dimensional inner product spaces.

-/

section

variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E] [normed_add_comm_group F]
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F]

open_locale tensor_product big_operators

noncomputable instance tensor_product.has_inner :
  has_inner 𝕜 (E ⊗[𝕜] F) :=
{ inner := λ (x y : E ⊗[𝕜] F), by { 
    let b₁ := std_orthonormal_basis 𝕜 E,
    let b₂ := std_orthonormal_basis 𝕜 F,
    exact ∑ i j, star (((b₁.to_basis.tensor_product b₂.to_basis).repr x) (i,j))
      * (((b₁.to_basis.tensor_product b₂.to_basis).repr y) (i,j)), } }

-- lemma orthonormal.to_basis_tensor_product {n m : Type*} [fintype n] [fintype m]
--   (b₁ : orthonormal_basis n 𝕜 E) (b₂ : orthonormal_basis m 𝕜 F) :
--   (b₁.to_basis.tensor_product b₂.to_basis).repr 

lemma tensor_product.inner_tmul (x z : E) (y w : F) :
  (inner (x ⊗ₜ[𝕜] y) (z ⊗ₜ[𝕜] w) : 𝕜) = (inner x z) * (inner y w) :=
begin
  simp_rw [inner, basis.tensor_product_repr_tmul_apply, orthonormal_basis.coe_to_basis_repr_apply,
    star_mul', mul_mul_mul_comm, is_R_or_C.star_def, orthonormal_basis.repr_apply_apply,
    inner_conj_symm, ← finset.mul_sum, ← finset.sum_mul, orthonormal_basis.sum_inner_mul_inner],
end

protected lemma tensor_product.inner_add_left (x y z : E ⊗[𝕜] F) :
  (inner (x + y) z : 𝕜) = inner x z + inner y z :=
begin
  simp_rw [inner, ← finset.sum_add_distrib, map_add, finsupp.add_apply,
    star_add, add_mul],
end

protected lemma tensor_product.inner_zero_right (x : E ⊗[𝕜] F) :
  (inner x (0 : E ⊗[𝕜] F) : 𝕜) = 0 :=
begin
  apply x.induction_on,
  all_goals { rw [← tensor_product.zero_tmul E (0 : F)] },
  { rw [tensor_product.inner_tmul],
    simp_rw [inner_zero_left, zero_mul], },
  { intros,
    simp_rw [tensor_product.inner_tmul, inner_zero_right, mul_zero], },
  { intros a b ha hb,
    simp_rw [tensor_product.inner_add_left, ha, hb, add_zero], },
end

protected lemma tensor_product.inner_conj_symm (x y : E ⊗[𝕜] F) :
  star_ring_end 𝕜 (inner x y : 𝕜) = inner y x :=
by simp_rw [inner, star_ring_end_apply, star_sum, star_mul', star_star, mul_comm]

protected lemma tensor_product.inner_zero_left (x : E ⊗[𝕜] F) :
  (inner (0 : E⊗[𝕜]F) x : 𝕜) = 0 :=
by rw [← tensor_product.inner_conj_symm, tensor_product.inner_zero_right, map_zero]

protected lemma tensor_product.inner_add_right (x y z : E ⊗[𝕜] F) :
  (inner x (y + z) : 𝕜) = inner x y + inner x z :=
by rw [← tensor_product.inner_conj_symm, tensor_product.inner_add_left, map_add,
  tensor_product.inner_conj_symm, tensor_product.inner_conj_symm]

protected lemma tensor_product.inner_sum {n : Type*} [fintype n] (x : n → (E⊗[𝕜]F)) (y : E⊗[𝕜]F) :
  (inner (∑ i, x i) y : 𝕜) = ∑ i, inner (x i) y :=
begin
  simp_rw [inner, map_sum, finset.sum_apply', star_sum, finset.sum_mul],
  rw finset.sum_rotate,
end
protected lemma tensor_product.sum_inner {n : Type*} [fintype n] (y : E⊗[𝕜]F) (x : n → (E⊗[𝕜]F)) :
  (inner y (∑ i, x i) : 𝕜) = ∑ i, inner y (x i) :=
by rw [← tensor_product.inner_conj_symm, tensor_product.inner_sum, map_sum];
  simp_rw [tensor_product.inner_conj_symm]

protected lemma tensor_product.inner_nonneg_re (x : E ⊗[𝕜] F) :
  0 ≤ is_R_or_C.re (inner x x : 𝕜) :=
begin
  simp_rw [inner, map_sum, is_R_or_C.star_def, is_R_or_C.conj_mul, is_R_or_C.of_real_re,
    ← finset.sum_product', finset.univ_product_univ, prod.mk.eta],
  apply finset.sum_nonneg,
  intros,
  exact is_R_or_C.norm_sq_nonneg _,
end

lemma tensor_product.eq_span {𝕜 E F : Type*} [is_R_or_C 𝕜] [add_comm_group E]
  [module 𝕜 E] [add_comm_group F] [module 𝕜 F] [finite_dimensional 𝕜 E]
  [finite_dimensional 𝕜 F] (x : E ⊗[𝕜] F) :
  ∃ (α : basis.of_vector_space_index 𝕜 E × basis.of_vector_space_index 𝕜 F → E)
    (β : basis.of_vector_space_index 𝕜 E × basis.of_vector_space_index 𝕜 F → F),
    ∑ i, (α i) ⊗ₜ[𝕜] (β i) = x :=
begin
  let b₁ := basis.of_vector_space 𝕜 E,
  let b₂ := basis.of_vector_space 𝕜 F,
  rw ← basis.sum_repr (b₁.tensor_product b₂) x,
  simp_rw [basis.tensor_product_apply', tensor_product.smul_tmul'],
  exact ⟨λ i, (((b₁.tensor_product b₂).repr) x) i • b₁ i.fst, λ i, b₂ i.snd, rfl⟩,
end

@[instance, reducible] noncomputable def tensor_product.normed_add_comm_group :
  normed_add_comm_group (E ⊗[𝕜] F) :=
@inner_product_space.core.to_normed_add_comm_group 𝕜 (E ⊗[𝕜] F) _ _ _
{ inner := λ x y, tensor_product.has_inner.inner x y,
  conj_symm := λ x y, y.inner_conj_symm x,
  nonneg_re := λ x, x.inner_nonneg_re,
  definite := λ x hx, by { 
    simp_rw [inner, is_R_or_C.star_def, is_R_or_C.conj_mul, ← finset.sum_product',
      finset.univ_product_univ, prod.mk.eta, ← is_R_or_C.of_real_sum,
      is_R_or_C.of_real_eq_zero] at hx,
    rw finset.sum_eq_zero_iff_of_nonneg at hx,
    { simp_rw [is_R_or_C.norm_sq_eq_zero, finset.mem_univ, true_implies_iff] at hx,
      apply basis.ext_elem ((std_orthonormal_basis 𝕜 E).to_basis.tensor_product
        (std_orthonormal_basis 𝕜 F).to_basis),
      simp_rw [map_zero, finsupp.zero_apply],
      exact hx, },
    { intros y hy,
      exact is_R_or_C.norm_sq_nonneg _, }, },
  add_left := λ x y z, x.inner_add_left _ _,
  smul_left := λ x y r,
    by { apply x.induction_on,
      { simp_rw [smul_zero, tensor_product.inner_zero_left, mul_zero], },
      { intros a b,
        apply y.induction_on,
        { simp_rw [smul_zero, tensor_product.inner_zero_right, mul_zero], },
        { intros c d,
          all_goals { simp only [tensor_product.smul_tmul', tensor_product.inner_tmul,
            inner_smul_left, mul_assoc, tensor_product.inner_add_right,
            tensor_product.inner_add_left, smul_add, mul_add], }, },
          { intros α β ha hb,
            simp_rw [tensor_product.inner_add_right, ha, hb, mul_add], }, },
      { intros a b ha hb,
        simp_rw [smul_add, tensor_product.inner_add_left, ha, hb, mul_add], }, } }

@[instance, reducible] noncomputable def tensor_product.inner_product_space :
  @inner_product_space 𝕜 (E ⊗[𝕜] F) _ (tensor_product.normed_add_comm_group) :=
inner_product_space.of_core _

example (α β : 𝕜) (x y : E) :
  tensor_product.inner_product_space.inner (α ⊗ₜ[𝕜] x) (β ⊗ₜ[𝕜] y)
    = inner α β * inner x y :=
tensor_product.inner_tmul _ _ _ _

lemma tensor_product.lid_adjoint :
  (tensor_product.lid 𝕜 E : 𝕜 ⊗[𝕜] E →ₗ[𝕜] E).adjoint = (tensor_product.lid 𝕜 E).symm :=
begin
  ext1,
  apply @ext_inner_right 𝕜,
  intros y,
  simp only [linear_map.comp_apply, linear_map.adjoint_inner_left,
    linear_equiv.coe_to_linear_map, linear_equiv.coe_coe,
    tensor_product.lid_symm_apply],
  apply y.induction_on,
  { simp only [inner_zero_right, map_zero], },
  { intros α z,
    simp only [tensor_product.lid_tmul, tensor_product.inner_tmul, is_R_or_C.inner_apply,
      star_ring_end_apply, star_one, one_mul, inner_smul_right], },
  { intros z w hz hw,
    simp only [map_add, inner_add_right, hz, hw], },
end

lemma tensor_product.comm_adjoint :
  (tensor_product.comm 𝕜 E F : E ⊗[𝕜] F →ₗ[𝕜] F ⊗[𝕜] E).adjoint
    = (tensor_product.comm 𝕜 E F).symm :=
begin
  apply tensor_product.ext',
  intros x y,
  apply @ext_inner_right 𝕜,
  intros z,
  simp only [linear_map.comp_apply, linear_map.adjoint_inner_left,
    linear_equiv.coe_to_linear_map, linear_equiv.coe_coe,
    tensor_product.comm_symm_tmul],
  apply z.induction_on,
  { simp only [inner_zero_right, map_zero], },
  { intros α z,
    simp only [tensor_product.comm_tmul, tensor_product.inner_tmul, mul_comm], },
  { intros z w hz hw,
    simp only [map_add, inner_add_right, hz, hw], },
end

lemma tensor_product.assoc_symm_adjoint {G : Type*} [normed_add_comm_group G]
  [inner_product_space 𝕜 G] [finite_dimensional 𝕜 G] :
  ((tensor_product.assoc 𝕜 E F G).symm : (E ⊗[𝕜] (F ⊗[𝕜] G)) →ₗ[𝕜] E ⊗[𝕜] F ⊗[𝕜] G).adjoint
    = (tensor_product.assoc 𝕜 E F G) :=
begin
  apply tensor_product.ext_threefold,
  intros x y z,
  apply @ext_inner_right 𝕜,
  intros w,
  obtain ⟨w₁, w₂, rfl⟩ := w.eq_span,
  simp only [linear_map.comp_apply, linear_map.adjoint_inner_left,
    linear_equiv.coe_to_linear_map, linear_equiv.coe_coe,
    tensor_product.assoc_tmul, inner_sum],
  apply finset.sum_congr rfl,
  intros i hi,
  obtain ⟨w₃, w₄, hw⟩ := (w₂ i).eq_span,
  simp only [← hw, tensor_product.assoc_symm_tmul, tensor_product.tmul_sum,
    map_sum, inner_sum, tensor_product.inner_tmul, mul_assoc],
end

lemma tensor_product.assoc_adjoint {G : Type*} [normed_add_comm_group G]
  [inner_product_space 𝕜 G] [finite_dimensional 𝕜 G] :
  (tensor_product.assoc 𝕜 E F G : (E ⊗[𝕜] F ⊗[𝕜] G) →ₗ[𝕜] E ⊗[𝕜] (F ⊗[𝕜] G)).adjoint
    = (tensor_product.assoc 𝕜 E F G).symm :=
begin
  have := @tensor_product.assoc_symm_adjoint 𝕜 E F _ _ _ _ _ _ _ G _ _ _,
  apply_fun linear_map.adjoint at this,
  rw [linear_map.adjoint_adjoint] at this,
  exact this.symm,
end

lemma tensor_product.map_adjoint {A B C D : Type*} [normed_add_comm_group A]
  [normed_add_comm_group B] [normed_add_comm_group C] [normed_add_comm_group D]
  [inner_product_space 𝕜 A] [inner_product_space 𝕜 B] [inner_product_space 𝕜 C]
  [inner_product_space 𝕜 D] [finite_dimensional 𝕜 A] [finite_dimensional 𝕜 B]
  [finite_dimensional 𝕜 C] [finite_dimensional 𝕜 D] (f : A →ₗ[𝕜] B) (g : C →ₗ[𝕜] D) :
  (tensor_product.map f g).adjoint = tensor_product.map f.adjoint g.adjoint :=
begin
  apply tensor_product.ext',
  intros x y,
  apply @ext_inner_right 𝕜,
  intros z,
  obtain ⟨w₁, w₂, rfl⟩ := z.eq_span,
  simp only [linear_map.comp_apply, linear_map.adjoint_inner_left,
    linear_equiv.coe_to_linear_map, linear_equiv.coe_coe,
    tensor_product.map_tmul, inner_sum, tensor_product.inner_tmul],
end

lemma tensor_product.inner_ext_iff (x z : E) (y w : F) :
  x ⊗ₜ y = z ⊗ₜ[𝕜] w ↔ ∀ (a : E) (b : F),
    inner (x ⊗ₜ[𝕜] y) (a ⊗ₜ[𝕜] b) = (inner (z ⊗ₜ[𝕜] w) (a ⊗ₜ[𝕜] b) : 𝕜) :=
begin
  refine ⟨λ h a b, by rw h, λ h, _⟩,
  apply @ext_inner_right 𝕜,
  intros z,
  obtain ⟨w₁, w₂, rfl⟩ := z.eq_span,
  simp_rw [inner_sum],
  repeat { apply finset.sum_congr rfl,
    intros, },
  rw [h],
end

lemma tensor_product.forall_inner_eq_zero
  {𝕜 E F : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [normed_add_comm_group F] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] (x : E ⊗[𝕜] F) :
  (∀ (a : E) (b : F), (inner x (a ⊗ₜ[𝕜] b) : 𝕜) = 0) ↔ x = 0 :=
begin
  refine ⟨λ h, _, λ h a b, by rw [h, inner_zero_left]⟩,
  rw ← @forall_inner_eq_zero_iff 𝕜,
  intros y,
  apply tensor_product.induction_on y,
  { exact inner_zero_right _, },
  { exact h, },
  { intros c d hc hd,
    rw [inner_add_right, hc, hd, add_zero], },
end

lemma tensor_product.inner_ext_iff'
  {𝕜 E F : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E]
  [normed_add_comm_group F] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] (x y : E ⊗[𝕜] F) :
  x = y ↔ ∀ (a : E) (b : F), inner x (a ⊗ₜ[𝕜] b) = (inner y (a ⊗ₜ[𝕜] b) : 𝕜) :=
begin
  simp_rw [← @sub_eq_zero 𝕜 _ _ (inner _ _ : 𝕜), ← inner_sub_left,
    tensor_product.forall_inner_eq_zero, sub_eq_zero],
end

lemma tensor_product.lid_symm_adjoint {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E] :
  ((tensor_product.lid 𝕜 E).symm).to_linear_map.adjoint
    = (tensor_product.lid 𝕜 E) :=
begin
  have := @tensor_product.lid_adjoint 𝕜 E _ _ _ _,
  apply_fun linear_map.adjoint at this,
  rw linear_map.adjoint_adjoint at this,
  exact this.symm,
end

lemma tensor_product.comm_symm_adjoint {𝕜 E V : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [normed_add_comm_group V]
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 V]
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 V] :
  ((tensor_product.comm 𝕜 E V).symm).to_linear_map.adjoint
    = tensor_product.comm 𝕜 E V :=
begin
  have := @tensor_product.comm_adjoint 𝕜 E V _ _ _ _ _ _ _,
  apply_fun linear_map.adjoint at this,
  rw linear_map.adjoint_adjoint at this,
  exact this.symm,
end

end

