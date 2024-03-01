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

variables {p n : Type*} [fintype n] [fintype p] [decidable_eq n] [decidable_eq p]
local notation `ℍ` := matrix n n ℂ
local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation `l(` x `)` := x →ₗ[ℂ] x

variables {φ : module.dual ℂ ℍ} [hφ : fact φ.is_faithful_pos_map]
  {ψ : module.dual ℂ (matrix p p ℂ)} (hψ : ψ.is_faithful_pos_map)

local notation `|` x `⟩⟨` y `|` := @rank_one ℂ _ _ _ _ x y
local notation `m` := linear_map.mul' ℂ ℍ
local notation `η` := algebra.linear_map ℂ ℍ
local notation x ` ⊗ₘ ` y := tensor_product.map x y
local notation `υ` :=
  ((tensor_product.assoc ℂ (matrix n n ℂ) (matrix n n ℂ) (matrix n n ℂ))
    : (matrix n n ℂ ⊗[ℂ] matrix n n ℂ ⊗[ℂ] matrix n n ℂ) →ₗ[ℂ]
      matrix n n ℂ ⊗[ℂ] (matrix n n ℂ ⊗[ℂ] matrix n n ℂ))
local notation `υ⁻¹` :=
  ((tensor_product.assoc ℂ (matrix n n ℂ) (matrix n n ℂ) (matrix n n ℂ)).symm
    : matrix n n ℂ ⊗[ℂ] (matrix n n ℂ ⊗[ℂ] matrix n n ℂ) →ₗ[ℂ]
      (matrix n n ℂ ⊗[ℂ] matrix n n ℂ ⊗[ℂ] matrix n n ℂ))
local notation `ϰ` := (↑(tensor_product.comm ℂ (matrix n n ℂ) ℂ)
  : (matrix n n ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] (ℂ ⊗[ℂ] matrix n n ℂ))
local notation `ϰ⁻¹` := ((tensor_product.comm ℂ (matrix n n ℂ) ℂ).symm
  : (ℂ ⊗[ℂ] matrix n n ℂ) →ₗ[ℂ] (matrix n n ℂ ⊗[ℂ] ℂ))
local notation `τ` := ((tensor_product.lid ℂ (matrix n n ℂ))
  : (ℂ ⊗[ℂ] matrix n n ℂ) →ₗ[ℂ] matrix n n ℂ)
local notation `τ⁻¹` := ((tensor_product.lid ℂ (matrix n n ℂ)).symm
  : matrix n n ℂ →ₗ[ℂ] (ℂ ⊗[ℂ] matrix n n ℂ))
local notation `id` := (1 : matrix n n ℂ →ₗ[ℂ] matrix n n ℂ)

noncomputable def qam.complete_graph (hφ : φ.is_faithful_pos_map) :
  ℍ →ₗ[ℂ] ℍ :=
begin
  letI := fact.mk hφ,
  exact |(1 : ℍ)⟩⟨(1 : ℍ)|,
end

lemma qam.complete_graph_eq :
  qam.complete_graph hφ.elim = |(1 : ℍ)⟩⟨(1 : ℍ)| :=
rfl

lemma qam.complete_graph_eq' :
  qam.complete_graph hφ.elim = η ∘ₗ (η).adjoint :=
begin
  rw [linear_map.ext_iff],
  intros x,
  simp_rw [qam.complete_graph_eq, continuous_linear_map.coe_coe, linear_map.comp_apply,
    rank_one_apply, nontracial.unit_adjoint_eq, module.dual.is_faithful_pos_map.inner_eq,
    conj_transpose_one, matrix.one_mul],
  refl,
end

lemma qam.nontracial.complete_graph.qam :
  qam φ (qam.complete_graph hφ.elim) :=
begin
  rw [qam.complete_graph, qam, qam.rank_one.refl_idempotent_eq],
  simp_rw matrix.one_mul,
end
lemma qam.nontracial.complete_graph.is_self_adjoint :
  @qam.is_self_adjoint n _ _ φ _ (qam.complete_graph hφ.elim) :=
begin
  simp_rw [qam.is_self_adjoint, qam.complete_graph,
    ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint],
end
lemma qam.nontracial.complete_graph.is_real :
  (qam.complete_graph hφ.elim).is_real :=
begin
  simp_rw [linear_map.is_real_iff, qam.complete_graph, qam.rank_one.real,
    conj_transpose_one, _root_.map_one],
end
lemma qam.nontracial.complete_graph.is_symm :
  qam.symm hφ.elim (qam.complete_graph hφ.elim) = qam.complete_graph hφ.elim :=
by { simp_rw [qam.complete_graph, qam.rank_one.symmetric_eq, conj_transpose_one, _root_.map_one], }

lemma qam.nontracial.complete_graph.is_reflexive :
  @qam_lm_nontracial_is_reflexive _ _ _ φ _ (qam.complete_graph hφ.elim) :=
begin
  obtain ⟨α, β, hαβ⟩ := (1 : l(ℍ)).exists_sum_rank_one,
  rw [qam_lm_nontracial_is_reflexive],
  nth_rewrite_lhs 0 hαβ,
  simp_rw [map_sum, qam.complete_graph, qam.rank_one.refl_idempotent_eq, matrix.one_mul, ← hαβ],
end

@[instance] noncomputable def qam.nontracial.mul'_comp_mul'_adjoint.invertible
  [hφ : fact φ.is_faithful_pos_map]
  [nontrivial n] :
  invertible ((m ∘ₗ (m).adjoint) : ℍ →ₗ[ℂ] ℍ) :=
begin
  rw qam.nontracial.mul_comp_mul_adjoint,
  apply is_unit.invertible,
  rw [linear_map.is_unit_iff_ker_eq_bot, linear_map.ker_smul _ _ _,
    linear_map.one_eq_id, linear_map.ker_id],
  exact matrix.pos_def.trace_ne_zero (pos_def.inv hφ.elim.matrix_is_pos_def),
end

noncomputable def qam.trivial_graph (hφ : φ.is_faithful_pos_map) [nontrivial n] :
  l(ℍ) :=
begin
  letI := fact.mk hφ,
  exact ⅟ (m ∘ₗ (m).adjoint),
end

lemma qam.trivial_graph_eq [nontrivial n] :
  qam.trivial_graph hφ.elim = (φ.matrix⁻¹ : ℍ).trace⁻¹ • (1 : ℍ →ₗ[ℂ] ℍ) :=
begin
  haveI := @qam.nontracial.mul'_comp_mul'_adjoint.invertible n _ _ φ _ _,
  simp_rw [qam.trivial_graph],
  apply inv_of_eq_right_inv,
  rw [qam.nontracial.mul_comp_mul_adjoint, smul_mul_smul, one_mul, mul_inv_cancel, one_smul],
  { exact matrix.pos_def.trace_ne_zero (pos_def.inv hφ.elim.matrix_is_pos_def), },
end

lemma qam.nontracial.trivial_graph.qam [nontrivial n] :
  qam φ (qam.trivial_graph hφ.elim) :=
begin
  rw qam.trivial_graph_eq,
  let hQ := hφ.elim.matrix_is_pos_def,
  let Q := φ.matrix,
  simp_rw [qam, smul_hom_class.map_smul, linear_map.smul_apply, qam.refl_idempotent,
      smul_smul, schur_idempotent, linear_map.coe_mk, tensor_product.map_one, linear_map.one_eq_id,
      linear_map.id_comp, qam.nontracial.mul_comp_mul_adjoint, smul_smul, mul_assoc],
    rw [inv_mul_cancel _, mul_one, linear_map.one_eq_id],
    exact matrix.pos_def.trace_ne_zero (pos_def.inv hφ.elim.matrix_is_pos_def),
  -- { simp_rw [smul_hom_class.map_smul, qam.symm_one], },
end

lemma qam.nontracial.trivial_graph.qam.is_self_adjoint [nontrivial n] :
  (qam.trivial_graph hφ.elim).adjoint = qam.trivial_graph hφ.elim :=
begin
  simp_rw [qam.trivial_graph_eq, linear_map.adjoint_smul],
  have : (φ.matrix⁻¹.trace.re : ℂ) = φ.matrix⁻¹.trace,
  { rw [← complex.conj_eq_iff_re, star_ring_end_apply, trace_star,
      hφ.elim.matrix_is_pos_def.1.inv.eq], },
  rw [← this, ← complex.of_real_inv, complex.conj_of_real, linear_map.adjoint_one],
end

lemma qam.nontracial.trivial_graph [nontrivial n] :
  @qam_lm_nontracial_is_reflexive _ _ _ φ _ (qam.trivial_graph hφ.elim) :=
begin
  rw [qam_lm_nontracial_is_reflexive, qam.trivial_graph_eq,
    smul_hom_class.map_smul, linear_map.smul_apply],
  simp_rw [qam.refl_idempotent, schur_idempotent, linear_map.coe_mk,
    tensor_product.map_one, linear_map.one_eq_id,
    linear_map.id_comp, qam.nontracial.mul_comp_mul_adjoint, smul_smul,
    inv_mul_cancel (matrix.pos_def.trace_ne_zero (pos_def.inv hφ.elim.matrix_is_pos_def)), one_smul,
    linear_map.one_eq_id],
end

private lemma qam.refl_idempotent_one_one :
  qam.refl_idempotent hφ.elim (1 : l(ℍ)) (1 : l(ℍ)) = (φ.matrix⁻¹).trace • (1 : l(ℍ)) :=
begin
  simp_rw [qam.refl_idempotent, schur_idempotent, linear_map.coe_mk,
    tensor_product.map_one, linear_map.one_comp, qam.nontracial.mul_comp_mul_adjoint],
end

lemma qam.lm.nontracial.is_unreflexive_iff_reflexive_add_one [nontrivial n] (x : l(ℍ)) :
  qam.refl_idempotent hφ.elim x 1 = 0
    ↔ qam.refl_idempotent hφ.elim (((φ.matrix⁻¹ : ℍ).trace : ℂ)⁻¹ • (x + 1)) 1 = 1 :=
begin
  simp_rw [smul_hom_class.map_smul, linear_map.smul_apply,
    _root_.map_add, linear_map.add_apply, qam.refl_idempotent_one_one,
    smul_add, smul_smul, ← complex.cpow_neg_one],
  nth_rewrite 2 ← complex.cpow_one ((φ.matrix⁻¹ : ℍ).trace),
  rw [← complex.cpow_add _ _ (@matrix.pos_def.trace_ne_zero n _ _ _ _ _ _ _
      (pos_def.inv hφ.elim.matrix_is_pos_def)),
    neg_add_self, complex.cpow_zero, one_smul, add_left_eq_self, complex.cpow_neg_one,
    smul_eq_zero_iff_eq' (inv_ne_zero (@matrix.pos_def.trace_ne_zero n _ _ _ _ _ _ _
      (pos_def.inv hφ.elim.matrix_is_pos_def)))],
end

lemma qam.refl_idempotent_complete_graph_left (x : l(ℍ)) :
  qam.refl_idempotent hφ.elim (qam.complete_graph hφ.elim) x = x :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp_rw [_root_.map_sum, qam.complete_graph, qam.rank_one.refl_idempotent_eq, matrix.one_mul],
end
lemma qam.refl_idempotent_complete_graph_right (x : l(ℍ)) :
  qam.refl_idempotent hφ.elim x (qam.complete_graph hφ.elim) = x :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp_rw [_root_.map_sum, linear_map.sum_apply, qam.complete_graph,
    qam.rank_one.refl_idempotent_eq, matrix.mul_one],
end

noncomputable def qam.complement' (hφ : φ.is_faithful_pos_map) (x : l(ℍ)) :
  l(ℍ) :=
(qam.complete_graph hφ) - x

lemma qam.nontracial.complement'.qam (x : l(ℍ)) :
  qam φ x ↔ qam φ (qam.complement' hφ.elim x) :=
begin
  simp only [qam.complement', qam, _root_.map_sub, linear_map.sub_apply,
    qam.refl_idempotent_complete_graph_left,
    qam.refl_idempotent_complete_graph_right,
    qam.nontracial.complete_graph.qam],
  simp only [sub_right_inj, sub_eq_self],
  simp only [sub_eq_zero, @eq_comm _ x],
end

lemma qam.nontracial.complement'.qam.is_real (x : l(ℍ)) :
  x.is_real ↔ (qam.complement' hφ.elim x).is_real :=
begin
  simp only [qam.complement', linear_map.is_real_iff,
    linear_map.real_sub, (linear_map.is_real_iff _).mp
      (@qam.nontracial.complete_graph.is_real n _ _ φ _)],
  simp only [sub_right_inj],
end

lemma qam.complement'_complement' (x : l(ℍ)) :
  qam.complement' hφ.elim (qam.complement' hφ.elim x) = x :=
sub_sub_cancel _ _

lemma qam.nontracial.complement'.ir_reflexive (x : l(ℍ)) (α : Prop)
  [decidable α] :
  qam.refl_idempotent hφ.elim x (1 : l(ℍ)) = ite α (1 : l(ℍ)) (0 : l(ℍ))
    ↔ qam.refl_idempotent hφ.elim (qam.complement' hφ.elim x) (1 : l(ℍ)) = ite α (0 : l(ℍ)) (1 : l(ℍ)) :=
begin
  simp_rw [qam.complement', _root_.map_sub, linear_map.sub_apply,
    qam.refl_idempotent_complete_graph_left],
  by_cases α; simp_rw [h],
  { simp_rw [if_true, sub_eq_zero, eq_comm], },
  { simp_rw [if_false, sub_eq_self], },
end

def qam_reflexive (hφ : φ.is_faithful_pos_map) (x : l(ℍ)) : Prop :=
@qam n _ _ φ (fact.mk hφ) x ∧ qam.refl_idempotent hφ x 1 = 1
def qam_irreflexive (hφ : φ.is_faithful_pos_map) (x : l(ℍ)) : Prop :=
@qam n _ _ φ (fact.mk hφ) x ∧ qam.refl_idempotent hφ x 1 = 0

lemma qam.complement'_is_irreflexive_iff (x : l(ℍ)) :
  qam_irreflexive hφ.elim (qam.complement' hφ.elim x) ↔ qam_reflexive hφ.elim x :=
begin
  have := @qam.nontracial.complement'.ir_reflexive n _ _ φ _ x true _,
  simp_rw [if_true] at this,
  rw [qam_reflexive, qam_irreflexive, ← qam.nontracial.complement'.qam],
  simp_rw [this],
end
lemma qam.complement'_is_reflexive_iff (x : l(ℍ)) :
  qam_reflexive hφ.elim (qam.complement' hφ.elim x) ↔ qam_irreflexive hφ.elim x :=
begin
  have := qam.nontracial.complement'.ir_reflexive x false,
  simp_rw [if_false] at this,
  rw [qam_reflexive, qam_irreflexive, ← qam.nontracial.complement'.qam, this],
end

noncomputable def qam.complement'' (hφ : φ.is_faithful_pos_map) [nontrivial n] {x : l(ℍ)} (hx : x.is_real) :
  l(ℍ) :=
x - (qam.trivial_graph hφ)



lemma qam.complement''_is_irreflexive_iff [nontrivial n] {x : l(ℍ)}
  (hx : x.is_real) :
  qam_irreflexive hφ.elim (qam.complement'' hφ.elim hx) ↔ qam_reflexive hφ.elim x :=
begin
  rw [qam_reflexive, qam_irreflexive],
  have t1 := @qam.nontracial.trivial_graph.qam n _ _ φ _ _,
  rw [qam] at t1 ⊢,
  have t2 := @qam.nontracial.trivial_graph n _ _ φ _ _,
  rw qam_lm_nontracial_is_reflexive at t2,
  have t3 : qam.refl_idempotent hφ.elim (qam.complement'' hφ.elim hx) 1 = 0
    ↔ qam.refl_idempotent hφ.elim x 1 = 1,
  { simp_rw [qam.complement'', map_sub, linear_map.sub_apply,
      t2, sub_eq_zero], },
  rw [t3],
  simp_rw [qam, qam.complement'', map_sub, linear_map.sub_apply, t1, sub_sub],
  refine ⟨λ h, ⟨_, h.2⟩, λ h, ⟨_, h.2⟩⟩,
  all_goals { have := (@qam.ir_refl_iff_ir_refl'_of_real n _ _ φ _ _ hx true _).mp,
    simp_rw [if_true] at this,
    rcases h with ⟨h1, h2⟩,
    specialize this h2,
    simp only [qam.trivial_graph_eq, smul_hom_class.map_smul, linear_map.smul_apply,
      h2, this, sub_self, add_zero, sub_left_inj] at h1 ⊢,
    exact h1, },
end

noncomputable def qam.irreflexive_complement (hφ : φ.is_faithful_pos_map)
  [nontrivial n] {x : l(ℍ)} (hx : x.is_real) :
  l(ℍ) :=
(qam.complete_graph hφ) - (qam.trivial_graph hφ) - x
noncomputable def qam.reflexive_complement (hφ : φ.is_faithful_pos_map)
  [nontrivial n] {x : l(ℍ)} (hx : x.is_real) :
  l(ℍ) :=
(qam.complete_graph hφ) + (qam.trivial_graph hφ) - x

lemma qam.nontracial.trivial_graph.is_real [nontrivial n] :
  (qam.trivial_graph hφ.elim).is_real :=
begin
  simp only [linear_map.is_real_iff, qam.trivial_graph_eq, linear_map.real_smul,
    linear_map.real_one],
  congr,
  rw [star_ring_end_apply, star_inv', trace_star, hφ.elim.matrix_is_pos_def.inv.1.eq],
end

lemma qam.irreflexive_complement.is_real [nontrivial n] {x : l(ℍ)} (hx : x.is_real) :
  (qam.irreflexive_complement hφ.elim hx).is_real :=
begin
  simp only [linear_map.is_real_iff, qam.irreflexive_complement, linear_map.real_sub,
    (linear_map.is_real_iff (qam.complete_graph hφ.elim)).mp
      qam.nontracial.complete_graph.is_real,
    (linear_map.is_real_iff (qam.trivial_graph hφ.elim)).mp
      qam.nontracial.trivial_graph.is_real,
    (linear_map.is_real_iff x).mp hx],
end
lemma qam.reflexive_complement.is_real [nontrivial n] {x : l(ℍ)} (hx : x.is_real) :
  (qam.reflexive_complement hφ.elim hx).is_real :=
begin
  simp only [linear_map.is_real_iff, qam.reflexive_complement, linear_map.real_sub,
    linear_map.real_add,
    (linear_map.is_real_iff (qam.complete_graph hφ.elim)).mp
      qam.nontracial.complete_graph.is_real,
    (linear_map.is_real_iff (qam.trivial_graph hφ.elim)).mp
      qam.nontracial.trivial_graph.is_real,
    (linear_map.is_real_iff x).mp hx],
end

lemma qam.irreflexive_complement_irreflexive_complement [nontrivial n] {x : l(ℍ)}
  (hx : x.is_real) :
  qam.irreflexive_complement hφ.elim
    (@qam.irreflexive_complement.is_real n _ _ φ _ _ _ hx) = x :=
sub_sub_cancel _ _
lemma qam.reflexive_complement_reflexive_complement [nontrivial n] {x : l(ℍ)}
  (hx : x.is_real) :
  qam.reflexive_complement hφ.elim (@qam.reflexive_complement.is_real n _ _ φ _ _ _ hx) = x :=
sub_sub_cancel _ _

lemma qam.trivial_graph_reflexive_complement_eq_complete_graph [nontrivial n] :
  qam.reflexive_complement hφ.elim
    (@qam.nontracial.trivial_graph.is_real n _ _ φ _ _)
    = qam.complete_graph hφ.elim :=
add_sub_cancel _ _
lemma qam.complete_graph_reflexive_complement_eq_trivial_graph [nontrivial n] :
  qam.reflexive_complement hφ.elim
    (@qam.nontracial.complete_graph.is_real n _ _ φ _)
    = qam.trivial_graph hφ.elim :=
add_sub_cancel' _ _

lemma qam.complement'_eq (a : l(ℍ)) :
  qam.complement' hφ.elim a = qam.complete_graph hφ.elim - a :=
rfl

lemma qam.irreflexive_complement_is_irreflexive_qam_iff_irreflexive_qam [nontrivial n] {x : l(ℍ)} (hx : x.is_real) :
  qam_irreflexive hφ.elim (qam.irreflexive_complement hφ.elim hx)
    ↔ qam_irreflexive hφ.elim x :=
begin
  rw [qam.irreflexive_complement, sub_sub, ← qam.complement'_eq,
    qam.complement'_is_irreflexive_iff, ← qam.complement''_is_irreflexive_iff,
    qam.complement'', add_sub_cancel'],
  { rw [linear_map.is_real_iff, linear_map.real_add, x.is_real_iff.mp hx,
      (qam.trivial_graph hφ.elim).is_real_iff.mp qam.nontracial.trivial_graph.is_real], },
end
lemma qam.reflexive_complment_is_reflfexive_qam_iff_reflexive_qam [nontrivial n] {x : l(ℍ)}
  (hx : x.is_real) :
  qam_reflexive hφ.elim (qam.reflexive_complement hφ.elim hx)
    ↔ qam_reflexive hφ.elim x :=
begin
  rw [qam.reflexive_complement, ← sub_sub_eq_add_sub, ← qam.complement'_eq,
    qam.complement'_is_reflexive_iff],
  exact qam.complement''_is_irreflexive_iff hx,
end
