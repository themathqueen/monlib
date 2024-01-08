/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.module.opposites
import linear_algebra.basis
import linear_algebra.finite_dimensional
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2

/-!

# Some results on the opposite vector space

This file contains the construction of the basis of an opposite space; and the construction of the opposite inner product space.

-/

variables {R H : Type*} [ring R] [add_comm_group H] [module R H]
  {ι : Type*} [fintype ι]

noncomputable def basis.mul_opposite (b : basis ι R H) :
  basis ι R Hᵐᵒᵖ :=
begin
  refine basis.mk _ _,
  { exact λ i, mul_opposite.op (b i), },
  { have := b.linear_independent,
    simp_rw [linear_independent_iff', ← mul_opposite.op_smul, ← finset.op_sum,
      mul_opposite.op_eq_zero_iff] at ⊢ this,
    exact this, },
  { simp_rw [top_le_iff],
    ext,
    simp_rw [submodule.mem_top, iff_true, mem_span_range_iff_exists_fun,
      ← mul_opposite.op_smul, ← finset.op_sum],
    use b.repr (mul_opposite.unop x),
    rw [basis.sum_repr, mul_opposite.op_unop], },
end

lemma basis.mul_opposite_apply (b : basis ι R H) (i : ι) :
  b.mul_opposite i = mul_opposite.op (b i) :=
begin
  rw [basis.mul_opposite, basis.coe_mk],
end
lemma basis.mul_opposite_repr_eq (b : basis ι R H) :
  b.mul_opposite.repr = (mul_opposite.op_linear_equiv R).symm.trans b.repr :=
begin
  simp_rw [basis.repr_eq_iff', linear_equiv.trans_apply, mul_opposite.coe_op_linear_equiv_symm,
    basis.mul_opposite_apply, mul_opposite.unop_op],
  exact basis.repr_self _,
end
lemma basis.mul_opposite_repr_apply (b : basis ι R H) (x : Hᵐᵒᵖ) :
  b.mul_opposite.repr x = b.repr (mul_opposite.unop x) :=
begin
  rw basis.mul_opposite_repr_eq,
  refl,
end

@[instance] lemma mul_opposite_finite_dimensional {R H : Type*} [division_ring R]
  [add_comm_group H] [module R H] [finite_dimensional R H] :
  finite_dimensional R Hᵐᵒᵖ :=
begin
  let b := basis.of_vector_space R H,
  let bm := b.mul_opposite,
  apply finite_dimensional.of_finite_basis bm,
  exact (basis.of_vector_space_index R H).to_finite,
end

@[instance] def mul_opposite.has_inner {𝕜 H : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group H] [inner_product_space 𝕜 H] :
  has_inner 𝕜 Hᵐᵒᵖ :=
{ inner := λ x y, inner (mul_opposite.unop x) (mul_opposite.unop y) }

@[instance, reducible] def mul_opposite.inner_product_space
  {𝕜 H : Type*} [is_R_or_C 𝕜] [normed_add_comm_group H] [inner_product_space 𝕜 H] :
  inner_product_space 𝕜 Hᵐᵒᵖ :=
{ norm_sq_eq_inner := λ x, by { simp only [inner, inner_self_eq_norm_sq,
    mul_opposite.norm_unop], },
  conj_symm := λ x y, by { simp only [inner, inner_conj_symm], },
  add_left := λ x y z, by { simp only [inner, inner_add_left, mul_opposite.unop_add], },
  smul_left := λ r x y, by { simp only [inner, inner_smul_left, mul_opposite.unop_smul], } }

lemma mul_opposite.inner_eq
  {𝕜 H : Type*} [is_R_or_C 𝕜] [normed_add_comm_group H] [inner_product_space 𝕜 H] (x y : Hᵐᵒᵖ) :
  (inner x y : 𝕜) = inner (mul_opposite.unop x) (mul_opposite.unop y) :=
rfl

lemma mul_opposite.inner_eq' {𝕜 H : Type*} [is_R_or_C 𝕜] [normed_add_comm_group H] [inner_product_space 𝕜 H]
  (x y : H) :
  inner (mul_opposite.op x) (mul_opposite.op y) = (inner x y : 𝕜) :=
rfl

lemma basis.mul_opposite_is_orthonormal_iff {𝕜 H : Type*} [is_R_or_C 𝕜] [normed_add_comm_group H] [inner_product_space 𝕜 H]
  {ι : Type*} [fintype ι] (b : basis ι 𝕜 H) :
  orthonormal 𝕜 b ↔ orthonormal 𝕜 b.mul_opposite :=
begin
  simp only [orthonormal, basis.mul_opposite_apply, mul_opposite.inner_eq',
    mul_opposite.norm_op],
end

noncomputable def orthonormal_basis.mul_opposite
  {𝕜 H : Type*} [is_R_or_C 𝕜] [normed_add_comm_group H] [inner_product_space 𝕜 H]
  {ι : Type*} [fintype ι] (b : orthonormal_basis ι 𝕜 H) :
  orthonormal_basis ι 𝕜 Hᵐᵒᵖ :=
begin
  refine @basis.to_orthonormal_basis ι _ _ _ _ _ _ _ _,
  { exact basis.mul_opposite b.to_basis, },
  { rw ← basis.mul_opposite_is_orthonormal_iff,
    exact b.orthonormal, },
end

instance mul_opposite.star_module
  {R H : Type*} [semiring R] [has_star R] [add_comm_monoid H] [has_smul R H] [has_star H] [star_module R H] :
  star_module R Hᵐᵒᵖ :=
{ star_smul := λ r a, by { simp_rw [star, mul_opposite.unop_smul, star_smul,
    mul_opposite.op_smul], }  }
