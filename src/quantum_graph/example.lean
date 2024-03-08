/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import quantum_graph.nontracial
-- import quantum_graph.basic

/-!
  # Basic examples on quantum adjacency matrices

  This file contains elementary examples of quantum adjacency matrices, such as the complete graph and the trivial graph.
-/

open tensor_product matrix
open_locale tensor_product big_operators kronecker matrix functional

variables {p : Type*} [fintype p] [decidable_eq p] {n : p → Type*}
  [Π i, fintype (n i)] [Π i, decidable_eq (n i)]
local notation `ℍ` := Π i, matrix (n i) (n i) ℂ
local notation `ℍ_`i := matrix (n i) (n i) ℂ
-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation `l(` x `)` := x →ₗ[ℂ] x

variables {φ : Π i, module.dual ℂ (ℍ_ i)} [hφ : Π i, fact (φ i).is_faithful_pos_map]

local notation `|` x `⟩⟨` y `|` := @rank_one ℂ _ _ _ _ x y
local notation `m` := linear_map.mul' ℂ ℍ
local notation `η` := algebra.linear_map ℂ ℍ
local notation x ` ⊗ₘ ` y := tensor_product.map x y
local notation `υ` :=
  ((tensor_product.assoc ℂ ℍ ℍ ℍ)
    : (ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ) →ₗ[ℂ]
      ℍ ⊗[ℂ] (ℍ ⊗[ℂ] ℍ))
local notation `υ⁻¹` :=
  ((tensor_product.assoc ℂ ℍ ℍ ℍ).symm
    : ℍ ⊗[ℂ] (ℍ ⊗[ℂ] ℍ) →ₗ[ℂ]
      (ℍ ⊗[ℂ] ℍ ⊗[ℂ] ℍ))
local notation `ϰ` := (↑(tensor_product.comm ℂ ℍ ℂ)
  : (ℍ ⊗[ℂ] ℂ) →ₗ[ℂ] (ℂ ⊗[ℂ] ℍ))
local notation `ϰ⁻¹` := ((tensor_product.comm ℂ ℍ ℂ).symm
  : (ℂ ⊗[ℂ] ℍ) →ₗ[ℂ] (ℍ ⊗[ℂ] ℂ))
local notation `τ` := ((tensor_product.lid ℂ ℍ)
  : (ℂ ⊗[ℂ] ℍ) →ₗ[ℂ] ℍ)
local notation `τ⁻¹` := ((tensor_product.lid ℂ ℍ).symm
  : ℍ →ₗ[ℂ] (ℂ ⊗[ℂ] ℍ))
local notation `id` := (1 : ℍ →ₗ[ℂ] ℍ)

noncomputable def qam.complete_graph
  (E : Type*) [has_one E] [normed_add_comm_group E] [inner_product_space ℂ E] :
  E →ₗ[ℂ] E :=
|(1 : E)⟩⟨(1 : E)|

lemma qam.complete_graph_eq {E : Type*} [has_one E]
  [normed_add_comm_group E] [inner_product_space ℂ E] :
  qam.complete_graph E = (|(1 : E)⟩⟨(1 : E)|) :=
rfl


lemma qam.complete_graph_eq' {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map] :
  qam.complete_graph (matrix p p ℂ)
    = (algebra.linear_map ℂ (matrix p p ℂ))
      ∘ₗ (algebra.linear_map ℂ (matrix p p ℂ)).adjoint :=
begin
  rw [linear_map.ext_iff],
  intros x,
  simp_rw [qam.complete_graph_eq, continuous_linear_map.coe_coe, linear_map.comp_apply,
    rank_one_apply, nontracial.unit_adjoint_eq, module.dual.is_faithful_pos_map.inner_eq,
    conj_transpose_one, matrix.one_mul],
  refl,
end


lemma pi.qam.complete_graph_eq' [hφ : Π i, fact (φ i).is_faithful_pos_map] :
  qam.complete_graph ℍ
    = (η) ∘ₗ (η).adjoint :=
begin
  rw [linear_map.ext_iff],
  intros x,
  simp_rw [qam.complete_graph_eq, continuous_linear_map.coe_coe, linear_map.comp_apply,
    rank_one_apply, nontracial.pi.unit_adjoint_eq, module.dual.pi.is_faithful_pos_map.inner_eq, star_one, one_mul],
  refl,
end

lemma qam.nontracial.complete_graph.qam {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E] :
  schur_idempotent (qam.complete_graph E) (qam.complete_graph E) = (qam.complete_graph E) :=
begin
  rw [qam.complete_graph, schur_idempotent.apply_rank_one, one_mul],
end
lemma qam.nontracial.complete_graph.is_self_adjoint
  {E : Type*} [has_one E] [normed_add_comm_group E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E] :
  @_root_.is_self_adjoint _ _ (qam.complete_graph E) :=
begin
  simp_rw [_root_.is_self_adjoint, qam.complete_graph, linear_map.star_eq_adjoint,
    ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint],
end
lemma qam.nontracial.complete_graph.is_real
  {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map] :
  (qam.complete_graph (matrix p p ℂ)).is_real :=
begin
  rw [qam.complete_graph, linear_map.is_real_iff, rank_one_real_apply,
    conj_transpose_one, _root_.map_one],
end
lemma qam.nontracial.complete_graph.is_symm
  {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map] :
  linear_equiv.symm_map ℂ (matrix p p ℂ) (qam.complete_graph (matrix p p ℂ))
    = qam.complete_graph (matrix p p ℂ) :=
by simp_rw [qam.complete_graph, qam.rank_one.symmetric_eq, conj_transpose_one, _root_.map_one]
lemma pi.qam.nontracial.complete_graph.is_real
  [hφ : Π i, fact (φ i).is_faithful_pos_map] :
  (qam.complete_graph ℍ).is_real :=
begin
  rw [qam.complete_graph, ← rank_one_lm_eq_rank_one,
    linear_map.is_real_iff, pi.rank_one_lm_real_apply,
    star_one, _root_.map_one],
end
lemma pi.qam.nontracial.complete_graph.is_symm
  [hφ : Π i, fact (φ i).is_faithful_pos_map] :
  linear_equiv.symm_map ℂ ℍ (qam.complete_graph ℍ) = qam.complete_graph ℍ :=
by simp_rw [qam.complete_graph, linear_equiv.symm_map_rank_one_apply, star_one, _root_.map_one]

lemma qam.nontracial.complete_graph.is_reflexive
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E] :
  schur_idempotent (qam.complete_graph E) 1 = 1 :=
begin
  obtain ⟨α, β, hαβ⟩ := (1 : l(E)).exists_sum_rank_one,
  nth_rewrite_lhs 0 hαβ,
  simp_rw [map_sum, qam.complete_graph, schur_idempotent.apply_rank_one, one_mul, ← hαβ],
end

lemma linear_map.mul'_comp_mul'_adjoint_of_delta_form
  {φ : module.dual ℂ (matrix p p ℂ)}
  {δ : ℂ} [hφ : fact φ.is_faithful_pos_map]
  (hφ₂ : φ.matrix⁻¹.trace = δ) :
  linear_map.mul' ℂ (matrix p p ℂ) ∘ₗ (linear_map.mul' ℂ (matrix p p ℂ)).adjoint = δ • 1 :=
begin
  rw [qam.nontracial.mul_comp_mul_adjoint, hφ₂],
end

lemma linear_map.pi_mul'_comp_mul'_adjoint_of_delta_form
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  m ∘ₗ (m).adjoint = δ • id :=
begin
  rw [linear_map.pi_mul'_comp_mul'_adjoint_eq_smul_id_iff δ],
  exact hφ₂,
  exact _inst_5,
end

lemma qam.nontracial.delta_ne_zero
  [nonempty p] {φ : module.dual ℂ (matrix p p ℂ)}
  {δ : ℂ} [hφ : fact φ.is_faithful_pos_map]
  (hφ₂ : φ.matrix⁻¹.trace = δ) :
  δ ≠ 0 :=
begin
  rw ← hφ₂,
  exact matrix.pos_def.trace_ne_zero (pos_def.inv hφ.elim.matrix_is_pos_def),
end

lemma pi.qam.nontracial.delta_ne_zero
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  δ ≠ 0 :=
begin
  have : ∀ i, (φ i).matrix⁻¹.trace ≠ 0,
  { intro i,
    exact matrix.pos_def.trace_ne_zero (pos_def.inv (hφ i).elim.matrix_is_pos_def), },
  have this' : δ ≠ 0 ↔ ∀ i, (φ i).matrix⁻¹.trace ≠ 0,
  { split; rintros h i,
    { exact this _, },
    { rw i at *,
      let j : p := classical.arbitrary p,
      exact (h j) (hφ₂ j), }, },
  rw this',
  exact this,
end

@[instance] noncomputable def qam.nontracial.mul'_comp_mul'_adjoint.invertible
  [nonempty p] {φ : module.dual ℂ (matrix p p ℂ)}
  {δ : ℂ} [hφ : fact φ.is_faithful_pos_map]
  (hφ₂ : φ.matrix⁻¹.trace = δ) :
  @invertible (l(matrix p p ℂ)) {mul := (∘ₗ)} {one := 1}
    (linear_map.mul' ℂ (matrix p p ℂ)
      ∘ₗ (linear_map.mul' ℂ (matrix p p ℂ)).adjoint)
     :=
begin
  rw linear_map.mul'_comp_mul'_adjoint_of_delta_form hφ₂,
  apply is_unit.invertible,
  rw [linear_map.is_unit_iff_ker_eq_bot, linear_map.ker_smul _ _ _,
    linear_map.one_eq_id, linear_map.ker_id],
  exact qam.nontracial.delta_ne_zero hφ₂,
end
@[instance] noncomputable def pi.qam.nontracial.mul'_comp_mul'_adjoint.invertible
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  @invertible (ℍ →ₗ[ℂ] ℍ) {mul := (∘ₗ)} {one := id}
    (m ∘ₗ (m).adjoint)
     :=
begin
  rw linear_map.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂,
  apply is_unit.invertible,
  rw [linear_map.is_unit_iff_ker_eq_bot, linear_map.ker_smul _ _ _,
    linear_map.one_eq_id, linear_map.ker_id],
  exact pi.qam.nontracial.delta_ne_zero hφ₂,
end

noncomputable def qam.trivial_graph
  [nonempty p] {φ : module.dual ℂ (matrix p p ℂ)}
  {δ : ℂ} (hφ : fact φ.is_faithful_pos_map)
  (hφ₂ : φ.matrix⁻¹.trace = δ) :
  l(matrix p p ℂ) :=
begin
  letI := hφ,
  letI := qam.nontracial.mul'_comp_mul'_adjoint.invertible hφ₂,
  exact ⅟ (linear_map.mul' ℂ (matrix p p ℂ) ∘ₗ (linear_map.mul' ℂ (matrix p p ℂ)).adjoint),
end

noncomputable def pi.qam.trivial_graph
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} (hφ : Π i, fact (φ i).is_faithful_pos_map)
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  l(ℍ) :=
begin
  letI := hφ,
  letI := pi.qam.nontracial.mul'_comp_mul'_adjoint.invertible hφ₂,
  exact ⅟ (m ∘ₗ (m).adjoint),
end

lemma qam.trivial_graph_eq
  [nonempty p] {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
  qam.trivial_graph hφ hφ₂ = δ⁻¹ • (1 : l(matrix p p ℂ)) :=
begin
  haveI := @qam.nontracial.mul'_comp_mul'_adjoint.invertible p _ _ _ φ δ hφ hφ₂,
  simp_rw [qam.trivial_graph],
  apply inv_of_eq_right_inv,
  rw [linear_map.mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_mul_smul, one_mul, mul_inv_cancel, one_smul],
  { exact qam.nontracial.delta_ne_zero hφ₂, },
end

lemma pi.qam.trivial_graph_eq
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  pi.qam.trivial_graph hφ hφ₂ = δ⁻¹ • (1 : ℍ →ₗ[ℂ] ℍ) :=
begin
  haveI := @pi.qam.nontracial.mul'_comp_mul'_adjoint.invertible p _ _ n _ _ φ _ _ δ _ hφ₂,
  simp_rw [pi.qam.trivial_graph],
  apply inv_of_eq_right_inv,
  rw [linear_map.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_mul_smul, one_mul, mul_inv_cancel, one_smul],
  { exact pi.qam.nontracial.delta_ne_zero hφ₂, },
end

lemma qam.nontracial.trivial_graph.qam
  [nonempty p] {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
  schur_idempotent (qam.trivial_graph hφ hφ₂) (qam.trivial_graph hφ hφ₂)
    = qam.trivial_graph hφ hφ₂ :=
begin
  rw qam.trivial_graph_eq,
  let hQ := module.dual.is_faithful_pos_map.matrix_is_pos_def hφ.elim,
  simp_rw [smul_hom_class.map_smul, linear_map.smul_apply,
    smul_smul, schur_idempotent, linear_map.coe_mk, tensor_product.map_one, linear_map.one_eq_id,
    linear_map.id_comp, linear_map.mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul, mul_assoc],
  rw [inv_mul_cancel _, mul_one, linear_map.one_eq_id],
  exact qam.nontracial.delta_ne_zero hφ₂,
end

lemma pi.qam.nontracial.trivial_graph.qam
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  schur_idempotent (pi.qam.trivial_graph hφ hφ₂) (pi.qam.trivial_graph hφ hφ₂)
    = pi.qam.trivial_graph hφ hφ₂ :=
begin
  rw pi.qam.trivial_graph_eq,
  let hQ := module.dual.pi.is_faithful_pos_map.matrix_is_pos_def hφ,
  let Q := module.dual.pi.matrix_block φ,
  simp_rw [smul_hom_class.map_smul, linear_map.smul_apply,
    smul_smul, schur_idempotent, linear_map.coe_mk, tensor_product.map_one, linear_map.one_eq_id,
    linear_map.id_comp, linear_map.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul, mul_assoc],
  rw [inv_mul_cancel _, mul_one, linear_map.one_eq_id],
  exact pi.qam.nontracial.delta_ne_zero hφ₂,
end

lemma qam.nontracial.trivial_graph.qam.is_self_adjoint [nonempty p]
  {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
  (qam.trivial_graph hφ hφ₂).adjoint = qam.trivial_graph hφ hφ₂ :=
begin
  simp_rw [qam.trivial_graph_eq, linear_map.adjoint_smul, linear_map.adjoint_one,
    star_ring_end_apply, star_inv', ← star_ring_end_apply],
  congr' 2,
  rw [← hφ₂, star_ring_end_apply, trace_star, hφ.elim.matrix_is_pos_def.1.inv.eq],
end

lemma pi.qam.nontracial.trivial_graph.qam.is_self_adjoint
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  (pi.qam.trivial_graph hφ hφ₂).adjoint = pi.qam.trivial_graph hφ hφ₂ :=
begin
  simp_rw [pi.qam.trivial_graph_eq, linear_map.adjoint_smul, linear_map.adjoint_one,
    star_ring_end_apply, star_inv', ← star_ring_end_apply],
  congr' 2,
  have : ∀ i, ((φ i).matrix⁻¹.trace.re : ℂ) = (φ i).matrix⁻¹.trace,
  { intro i,
    rw [← complex.conj_eq_iff_re, star_ring_end_apply, trace_star,
      (hφ i).elim.matrix_is_pos_def.1.inv.eq], },
  simp_rw [hφ₂] at this,
  rw [← this (nonempty.some _inst_5), complex.conj_of_real],
end

lemma qam.nontracial.trivial_graph [nonempty p]
  {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
  schur_idempotent (qam.trivial_graph hφ hφ₂) 1 = 1 :=
begin
  rw [qam.trivial_graph_eq, smul_hom_class.map_smul, linear_map.smul_apply],
  simp_rw [schur_idempotent, linear_map.coe_mk,
    tensor_product.map_one, linear_map.one_eq_id,
    linear_map.id_comp, linear_map.mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul,
    inv_mul_cancel (qam.nontracial.delta_ne_zero hφ₂), one_smul, linear_map.one_eq_id],
end

lemma pi.qam.nontracial.trivial_graph
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  schur_idempotent (pi.qam.trivial_graph hφ hφ₂) 1 = 1 :=
begin
  rw [pi.qam.trivial_graph_eq, smul_hom_class.map_smul, linear_map.smul_apply],
  simp_rw [schur_idempotent, linear_map.coe_mk,
    tensor_product.map_one, linear_map.one_eq_id,
    linear_map.id_comp, linear_map.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂, smul_smul,
    inv_mul_cancel (pi.qam.nontracial.delta_ne_zero hφ₂), one_smul, linear_map.one_eq_id],
end

lemma qam.refl_idempotent_one_one_of_delta [nonempty p]
  {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
  schur_idempotent (1 : l(matrix p p ℂ)) (1 : l(matrix p p ℂ)) = δ • (1 : l(matrix p p ℂ)) :=
begin
  simp_rw [schur_idempotent, linear_map.coe_mk,
    tensor_product.map_one, linear_map.one_comp, linear_map.mul'_comp_mul'_adjoint_of_delta_form hφ₂],
end

lemma pi.qam.refl_idempotent_one_one_of_delta
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  schur_idempotent (1 : l(ℍ)) (1 : l(ℍ)) = δ • (1 : l(ℍ)) :=
begin
  simp_rw [schur_idempotent, linear_map.coe_mk,
    tensor_product.map_one, linear_map.one_comp, linear_map.pi_mul'_comp_mul'_adjoint_of_delta_form hφ₂],
end

lemma qam.lm.nontracial.is_unreflexive_iff_reflexive_add_one [nonempty p]
  {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) (x : l(matrix p p ℂ)) :
  schur_idempotent x 1 = 0
    ↔ schur_idempotent (δ⁻¹ • (x + 1)) 1 = 1 :=
begin
  simp_rw [smul_hom_class.map_smul, linear_map.smul_apply,
    _root_.map_add, linear_map.add_apply, qam.refl_idempotent_one_one_of_delta hφ₂,
    smul_add, smul_smul, inv_mul_cancel (qam.nontracial.delta_ne_zero hφ₂), one_smul,
    add_left_eq_self],
  rw [smul_eq_zero_iff_eq' (inv_ne_zero (qam.nontracial.delta_ne_zero hφ₂))],
end

lemma pi.qam.lm.nontracial.is_unreflexive_iff_reflexive_add_one [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) (x : l(ℍ)) :
  schur_idempotent x 1 = 0
    ↔ schur_idempotent (δ⁻¹ • (x + 1)) 1 = 1 :=
begin
  simp_rw [smul_hom_class.map_smul, linear_map.smul_apply,
    _root_.map_add, linear_map.add_apply, pi.qam.refl_idempotent_one_one_of_delta hφ₂,
    smul_add, smul_smul, inv_mul_cancel (pi.qam.nontracial.delta_ne_zero hφ₂), one_smul,
    add_left_eq_self],
  rw [smul_eq_zero_iff_eq' (inv_ne_zero (pi.qam.nontracial.delta_ne_zero hφ₂))],
end

lemma qam.refl_idempotent_complete_graph_left {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E]
  (x : l(E)) :
  schur_idempotent (qam.complete_graph E) x = x :=
schur_idempotent_one_one_left _
lemma qam.refl_idempotent_complete_graph_right
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E] (x : l(E)) :
  schur_idempotent x (qam.complete_graph E) = x :=
schur_idempotent_one_one_right _

noncomputable def qam.complement'
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E]
  (x : l(E)) :
  l(E) :=
(qam.complete_graph E) - x

lemma qam.nontracial.complement'.qam
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E] (x : l(E)) :
  schur_idempotent x x = x ↔
    schur_idempotent (qam.complement' x) (qam.complement' x) = (qam.complement' x) :=
begin
  simp only [qam.complement', _root_.map_sub, linear_map.sub_apply,
    qam.refl_idempotent_complete_graph_left,
    qam.refl_idempotent_complete_graph_right,
    qam.nontracial.complete_graph.qam],
  simp only [sub_right_inj, sub_eq_self],
  simp only [sub_eq_zero, @eq_comm _ x],
end

lemma qam.nontracial.complement'.qam.is_real
  {φ : module.dual ℂ (matrix p p ℂ)} [hφ : fact φ.is_faithful_pos_map]
  (x : l(matrix p p ℂ)) :
  x.is_real ↔ (qam.complement' x).is_real :=
begin
  simp only [qam.complement', linear_map.is_real_iff,
    linear_map.real_sub, (linear_map.is_real_iff _).mp
      (@qam.nontracial.complete_graph.is_real p _ _ φ _)],
  simp only [sub_right_inj],
end

lemma pi.qam.nontracial.complement'.qam.is_real
  [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (x : l(ℍ)) :
  x.is_real ↔ (qam.complement' x).is_real :=
begin
  simp only [qam.complement', linear_map.is_real_iff,
    linear_map.real_sub, (linear_map.is_real_iff _).mp
      (@pi.qam.nontracial.complete_graph.is_real p _ _ n _ _ φ _)],
  simp only [sub_right_inj],
end

lemma qam.complement'_complement'
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E]
  (x : l(E)) :
  qam.complement' (qam.complement' x) = x :=
sub_sub_cancel _ _

lemma qam.nontracial.complement'.ir_reflexive
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E]
  (x : l(E)) (α : Prop) [decidable α] :
  schur_idempotent x (1 : l(E)) = ite α (1 : l(E)) (0 : l(E))
    ↔ schur_idempotent (qam.complement' x) (1 : l(E)) = ite α (0 : l(E)) (1 : l(E)) :=
begin
  simp_rw [qam.complement', _root_.map_sub, linear_map.sub_apply,
    qam.refl_idempotent_complete_graph_left],
  by_cases α; simp_rw [h],
  { simp_rw [if_true, sub_eq_zero, eq_comm], },
  { simp_rw [if_false, sub_eq_self], },
end

def qam_reflexive
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E] (x : l(E)) : Prop :=
schur_idempotent x x = x ∧ schur_idempotent x 1 = 1
def qam_irreflexive {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E] (x : l(E)) : Prop :=
schur_idempotent x x = x ∧ schur_idempotent x 1 = 0

lemma qam.complement'_is_irreflexive_iff
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E]
  (x : l(E)) :
  qam_irreflexive (qam.complement' x) ↔ qam_reflexive x :=
begin
  have := qam.nontracial.complement'.ir_reflexive x true,
  simp_rw [if_true] at this,
  rw [qam_reflexive, qam_irreflexive, ← qam.nontracial.complement'.qam],
  simp_rw [this],
end
lemma qam.complement'_is_reflexive_iff
  {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E]
  (x : l(E)) :
  qam_reflexive (qam.complement' x) ↔ qam_irreflexive x :=
begin
  have := qam.nontracial.complement'.ir_reflexive x false,
  simp_rw [if_false] at this,
  rw [qam_reflexive, qam_irreflexive, ← qam.nontracial.complement'.qam, this],
end

noncomputable def qam.complement'' [nonempty p]
  {φ : module.dual ℂ (matrix p p ℂ)}
  {δ : ℂ} (hφ : fact φ.is_faithful_pos_map)
  (hφ₂ : φ.matrix⁻¹.trace = δ) (x : l(matrix p p ℂ)) :
  l(matrix p p ℂ) :=
x - (qam.trivial_graph hφ hφ₂)
noncomputable def pi.qam.complement'' [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} (hφ : Π i, fact (φ i).is_faithful_pos_map)
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) (x : l(ℍ)) :
  l(ℍ) :=
x - (pi.qam.trivial_graph hφ hφ₂)

lemma single_schur_idempotent_real {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  (x y : l(matrix p p ℂ)) :
  (schur_idempotent x y).real = schur_idempotent y.real x.real :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  obtain ⟨γ, δ, rfl⟩ := y.exists_sum_rank_one,
  simp only [linear_map.real_sum, map_sum, linear_map.sum_apply,
    rank_one_real_apply, schur_idempotent.apply_rank_one,
    mul_eq_mul, conj_transpose_mul],
  simp only [← mul_eq_mul, _root_.map_mul],
  rw finset.sum_comm,
end

lemma schur_idempotent_reflexive_of_is_real
  {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  {x : l(matrix p p ℂ)} (hx : x.is_real) :
  schur_idempotent x 1 = 1 ↔ schur_idempotent 1 x = 1 :=
begin
  rw [linear_map.real_inj_eq, single_schur_idempotent_real, linear_map.real_one, x.is_real_iff.mp hx],
end

lemma pi.schur_idempotent_reflexive_of_is_real
  [hφ : Π i, fact (φ i).is_faithful_pos_map]
  {x : l(ℍ)} (hx : x.is_real) :
  schur_idempotent x 1 = 1 ↔ schur_idempotent 1 x = 1 :=
begin
  rw [linear_map.real_inj_eq, schur_idempotent_real, linear_map.real_one, x.is_real_iff.mp hx],
end

lemma qam.complement''_is_irreflexive_iff [nonempty p]
  {φ : module.dual ℂ (matrix p p ℂ)}
  {δ : ℂ} [hφ : fact φ.is_faithful_pos_map]
  (hφ₂ : φ.matrix⁻¹.trace = δ) {x : l(matrix p p ℂ)} (hx : x.is_real) :
  qam_irreflexive (qam.complement'' hφ hφ₂ x)
    ↔ qam_reflexive x :=
begin
  rw [qam_reflexive, qam_irreflexive],
  have t1 := qam.nontracial.trivial_graph.qam hφ₂,
  have t2 := qam.nontracial.trivial_graph hφ₂,
  have t3 : schur_idempotent (qam.complement'' hφ hφ₂ x) 1 = 0
    ↔ schur_idempotent x 1 = 1,
  { simp_rw [qam.complement'', map_sub, linear_map.sub_apply,
      t2, sub_eq_zero], },
  rw [t3],
  simp_rw [qam.complement'', map_sub, linear_map.sub_apply, t1, sub_sub],
  split; rintros ⟨h1, h2⟩; refine ⟨_, h2⟩,

  all_goals {
    simp only [qam.trivial_graph_eq, smul_hom_class.map_smul, linear_map.smul_apply,
      h2, (schur_idempotent_reflexive_of_is_real hx).mp h2,
      sub_self, add_zero, sub_left_inj] at h1 ⊢,
    exact h1, },
end

lemma pi.qam.complement''_is_irreflexive_iff [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)} (hx : x.is_real) :
  qam_irreflexive (pi.qam.complement'' hφ hφ₂ x)
    ↔ qam_reflexive x :=
begin
  rw [qam_reflexive, qam_irreflexive],
  have t1 := @pi.qam.nontracial.trivial_graph.qam p _ _ n _ _ φ _ _ δ _ hφ₂,
  have t2 := @pi.qam.nontracial.trivial_graph p _ _ n _ _ φ _ _ δ _ hφ₂,
  have t3 : schur_idempotent (pi.qam.complement'' hφ hφ₂ x) 1 = 0
    ↔ schur_idempotent x 1 = 1,
  { simp_rw [pi.qam.complement'', map_sub, linear_map.sub_apply,
      t2, sub_eq_zero], },
  rw [t3],
  simp_rw [pi.qam.complement'', map_sub, linear_map.sub_apply, t1, sub_sub],
  split; rintros ⟨h1, h2⟩; refine ⟨_, h2⟩,

  all_goals {
    simp only [pi.qam.trivial_graph_eq, smul_hom_class.map_smul, linear_map.smul_apply,
      h2, (pi.schur_idempotent_reflexive_of_is_real hx).mp h2,
      sub_self, add_zero, sub_left_inj] at h1 ⊢,
    exact h1, },
end

noncomputable def pi.qam.irreflexive_complement [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} (hφ : Π i, fact (φ i).is_faithful_pos_map)
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) (x : l(ℍ)) :
  l(ℍ) :=
(qam.complete_graph ℍ) - (pi.qam.trivial_graph hφ hφ₂) - x
noncomputable def pi.qam.reflexive_complement [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} (hφ : Π i, fact (φ i).is_faithful_pos_map)
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) (x : l(ℍ)) :
  l(ℍ) :=
(qam.complete_graph ℍ) + (pi.qam.trivial_graph hφ hφ₂) - x

lemma qam.nontracial.trivial_graph.is_real [nonempty p]
  {φ : module.dual ℂ (matrix p p ℂ)}
  [hφ : fact φ.is_faithful_pos_map]
  {δ : ℂ} (hφ₂ : φ.matrix⁻¹.trace = δ) :
  (qam.trivial_graph hφ hφ₂).is_real :=
begin
  rw [linear_map.is_real_iff, qam.trivial_graph_eq, linear_map.real_smul,
    linear_map.real_one, star_ring_end_apply, star_inv'],
  congr,
  rw ← hφ₂, 
  rw [trace_star, hφ.elim.matrix_is_pos_def.inv.1.eq],
end

lemma pi.qam.nontracial.trivial_graph.is_real [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  (pi.qam.trivial_graph hφ hφ₂).is_real :=
begin
  rw [linear_map.is_real_iff, pi.qam.trivial_graph_eq, linear_map.real_smul,
    linear_map.real_one, star_ring_end_apply, star_inv'],
  congr,
  rw ← hφ₂ (nonempty.some _inst_5), 
  rw [trace_star, (hφ _).elim.matrix_is_pos_def.inv.1.eq],
end

lemma pi.qam.irreflexive_complement.is_real
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)} (hx : x.is_real) :
  (pi.qam.irreflexive_complement hφ hφ₂ x).is_real :=
begin
  rw [linear_map.is_real_iff, pi.qam.irreflexive_complement, linear_map.real_sub,
    linear_map.real_sub,
    (linear_map.is_real_iff (qam.complete_graph ℍ)).mp
      pi.qam.nontracial.complete_graph.is_real,
    (linear_map.is_real_iff (pi.qam.trivial_graph hφ hφ₂)).mp
      (pi.qam.nontracial.trivial_graph.is_real hφ₂),
    (linear_map.is_real_iff x).mp hx],
end
lemma pi.qam.reflexive_complement.is_real
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ)
  {x : l(ℍ)} (hx : x.is_real) :
  (pi.qam.reflexive_complement hφ hφ₂ x).is_real :=
begin
  rw [linear_map.is_real_iff, pi.qam.reflexive_complement, linear_map.real_sub,
    linear_map.real_add,
    (linear_map.is_real_iff (qam.complete_graph ℍ)).mp
      pi.qam.nontracial.complete_graph.is_real,
    (linear_map.is_real_iff (pi.qam.trivial_graph hφ hφ₂)).mp
      (pi.qam.nontracial.trivial_graph.is_real hφ₂),
    (linear_map.is_real_iff x).mp hx],
end

lemma pi.qam.irreflexive_complement_irreflexive_complement [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)} :
  pi.qam.irreflexive_complement hφ hφ₂ (pi.qam.irreflexive_complement hφ hφ₂ x) = x :=
sub_sub_cancel _ _
lemma pi.qam.reflexive_complement_reflexive_complement [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)} :
  pi.qam.reflexive_complement hφ hφ₂ (pi.qam.reflexive_complement hφ hφ₂ x) = x :=
sub_sub_cancel _ _

lemma pi.qam.trivial_graph_reflexive_complement_eq_complete_graph
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  pi.qam.reflexive_complement hφ hφ₂ (pi.qam.trivial_graph hφ hφ₂)
    = qam.complete_graph ℍ :=
add_sub_cancel _ _
lemma pi.qam.complete_graph_reflexive_complement_eq_trivial_graph
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) :
  pi.qam.reflexive_complement hφ hφ₂ (qam.complete_graph ℍ)
    = pi.qam.trivial_graph hφ hφ₂ :=
add_sub_cancel' _ _

lemma qam.complement'_eq {E : Type*} [normed_add_comm_group_of_ring E]
  [inner_product_space ℂ E] [finite_dimensional ℂ E]
  [is_scalar_tower ℂ E E] [smul_comm_class ℂ E E]
  (a : l(E)) :
  qam.complement' a = qam.complete_graph E - a :=
rfl

lemma pi.qam.irreflexive_complement_is_irreflexive_qam_iff_irreflexive_qam
  [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)} (hx : x.is_real) :
  qam_irreflexive (pi.qam.irreflexive_complement hφ hφ₂ x)
    ↔ qam_irreflexive x :=
begin
  rw [pi.qam.irreflexive_complement, sub_sub, ← qam.complement'_eq,
    qam.complement'_is_irreflexive_iff, ← pi.qam.complement''_is_irreflexive_iff hφ₂,
    pi.qam.complement'', add_sub_cancel'],
  { rw [linear_map.is_real_iff, linear_map.real_add, x.is_real_iff.mp hx,
      (pi.qam.trivial_graph hφ hφ₂).is_real_iff.mp (pi.qam.nontracial.trivial_graph.is_real hφ₂)], },
end
lemma pi.qam.reflexive_complment_is_reflexive_qam_iff_reflexive_qam [nonempty p]
  [Π i, nontrivial (n i)]
  {δ : ℂ} [hφ : Π i, fact (φ i).is_faithful_pos_map]
  (hφ₂ : ∀ i, (φ i).matrix⁻¹.trace = δ) {x : l(ℍ)}
  (hx : x.is_real) :
  qam_reflexive (pi.qam.reflexive_complement hφ hφ₂ x)
    ↔ qam_reflexive x :=
begin
  rw [pi.qam.reflexive_complement, ← sub_sub_eq_add_sub, ← qam.complement'_eq,
    qam.complement'_is_reflexive_iff],
  exact pi.qam.complement''_is_irreflexive_iff hφ₂ hx,
end
