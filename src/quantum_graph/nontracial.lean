/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_ips.nontracial
import linear_algebra.my_ips.mat_ips
import linear_algebra.my_ips.tensor_hilbert
import linear_algebra.is_real
import linear_algebra.my_ips.frob
import linear_algebra.tensor_finite
import linear_algebra.my_ips.op_unop
import linear_algebra.lmul_rmul
import quantum_graph.schur_idempotent

/-!
 # Quantum graphs: quantum adjacency matrices

 This file defines the quantum adjacency matrix of a quantum graph.
-/

variables {n p : Type*} [fintype n] [fintype p] [decidable_eq n] [decidable_eq p]

open_locale tensor_product big_operators kronecker

local notation `ℍ` := matrix n n ℂ
local notation `⊗K` := matrix (n × n) (n × n) ℂ
local notation `l(`x`)` := x →ₗ[ℂ] x
local notation `L(`x`)` := x →L[ℂ] x

local notation `e_{` i `,` j `}` := matrix.std_basis_matrix i j (1 : ℂ)

variables {φ : module.dual ℂ ℍ} [hφ : fact φ.is_faithful_pos_map]
  {ψ : module.dual ℂ (matrix p p ℂ)} (hψ : ψ.is_faithful_pos_map)

open_locale matrix
open matrix

local notation `|` x `⟩⟨` y `|` := (@rank_one ℂ _ _ _ _ x y)
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

open_locale functional

noncomputable def qam.refl_idempotent (hφ : φ.is_faithful_pos_map) :
  l(ℍ) →ₗ[ℂ] l(ℍ) →ₗ[ℂ] l(ℍ) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x,
    { to_fun := λ y, m ∘ₗ (x ⊗ₘ y) ∘ₗ (m).adjoint,
      map_add' := λ x y, by { simp only [tensor_product.map_add_right, linear_map.add_comp,
        linear_map.comp_add], },
      map_smul' := λ r x, by { simp only [tensor_product.map_smul_right, linear_map.smul_comp,
        linear_map.comp_smul, ring_hom.id_apply], } },
    map_add' := λ x y, by { simp only [tensor_product.map_add_left, linear_map.add_comp,
      linear_map.comp_add, linear_map.ext_iff, linear_map.add_apply, linear_map.coe_mk],
      intros _ _, refl, },
    map_smul' := λ r x, by { simp only [tensor_product.map_smul_left, linear_map.smul_comp,
      linear_map.comp_smul, linear_map.ext_iff, linear_map.smul_apply, linear_map.coe_mk,
      ring_hom.id_apply],
      intros _ _, refl, }, },
end

lemma qam.rank_one.refl_idempotent_eq [hφ : fact φ.is_faithful_pos_map] (a b c d : ℍ) :
  qam.refl_idempotent hφ.elim (↑|a⟩⟨b|) (↑|c⟩⟨d|) = |a ⬝ c⟩⟨b ⬝ d| :=
begin
  rw [qam.refl_idempotent, linear_map.ext_iff_inner_map],
  intros x,
  simp only [continuous_linear_map.coe_coe, linear_map.coe_mk, rank_one_apply,
    linear_map.comp_apply],
  obtain ⟨α, β, h⟩ := tensor_product.eq_span ((linear_map.mul' ℂ ℍ).adjoint x),
  rw ← h,
  simp_rw [map_sum, tensor_product.map_tmul, continuous_linear_map.coe_coe, rank_one_apply,
    linear_map.mul'_apply, smul_mul_smul, ← tensor_product.inner_tmul, ← finset.sum_smul,
    ← inner_sum, h, linear_map.adjoint_inner_right, linear_map.mul'_apply],
  refl,
end

open tensor_product

noncomputable def qam.symm (hφ : φ.is_faithful_pos_map) :
  l(l(ℍ)) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ ((η).adjoint ∘ₗ (m)))
      ∘ₗ υ ∘ₗ ((id ⊗ₘ x) ⊗ₘ id)
      ∘ₗ (((m).adjoint ∘ₗ η) ⊗ₘ id) ∘ₗ τ⁻¹,
    map_add' := λ x y, by {
      simp only [tensor_product.map_add, tensor_product.add_map, linear_map.add_comp,
        linear_map.comp_add], },
    map_smul' := λ r x, by {
      simp only [tensor_product.map_smul, tensor_product.smul_map, linear_map.smul_comp,
        linear_map.comp_smul, ring_hom.id_apply], } },
end

lemma qam.rank_one.symmetric_eq (a b : ℍ) :
  qam.symm hφ.elim (|a⟩⟨b|)
  = |hφ.elim.sig (-1) bᴴ⟩⟨aᴴ| :=
begin
  rw [qam.symm, linear_map.coe_mk, linear_map.ext_iff_inner_map],
  intros x,
  obtain ⟨α, β, this⟩ := tensor_product.eq_span ((linear_map.mul' ℂ ℍ).adjoint (1 : ℍ)),
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, lid_symm_apply,
    map_tmul, linear_map.comp_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, one_smul],
  rw [← this],
  simp_rw [_root_.map_sum, map_tmul, linear_map.one_apply, sum_tmul, _root_.map_sum, assoc_tmul,
    map_tmul, comm_tmul, lid_tmul, sum_inner, linear_map.comp_apply,
    continuous_linear_map.coe_coe, rank_one_apply, ← smul_tmul', smul_hom_class.map_smul,
    linear_map.one_apply, nontracial.unit_adjoint_eq, smul_eq_mul, linear_map.mul'_apply,
    linear_map.is_faithful_pos_map.inner_eq aᴴ, conj_transpose_conj_transpose],
  calc ∑ x_1, inner ((inner b (β x_1) * φ (a * x)) • α x_1) x
    = star_ring_end ℂ (φ (a ⬝ x)) * ∑ x_1, inner (α x_1) x * inner (β x_1) b :
  by { simp only [inner_smul_left, _root_.map_mul, inner_conj_symm, mul_comm,
      finset.mul_sum],
    simp_rw [mul_assoc], refl, }
  ... = star_ring_end ℂ (φ (a ⬝ x)) * inner (∑ x_1, α x_1 ⊗ₜ[ℂ] β x_1) (x ⊗ₜ b) :
  by { simp_rw [← inner_tmul, ← sum_inner], }
  ... = star_ring_end ℂ (φ (a ⬝ x)) * inner ((m).adjoint 1) (x ⊗ₜ[ℂ] b) : by rw [this]
  ... = star_ring_end ℂ (φ (a ⬝ x)) * inner (hφ.elim.sig (-1) bᴴ) (x) :
  by { simp_rw [linear_map.adjoint_inner_left, linear_map.mul'_apply, mul_eq_mul,
    linear_map.is_faithful_pos_map.inner_left_conj _ _ b,
    linear_map.is_faithful_pos_map.sig_apply, neg_neg, matrix.one_mul,
    pos_def.rpow_one_eq_self, pos_def.rpow_neg_one_eq_inv_self], }
  ... = inner (φ (a ⬝ x) • hφ.elim.sig (-1) bᴴ) x : by rw inner_smul_left,
end

noncomputable def qam.symm' (hφ : φ.is_faithful_pos_map) :
  l(l(ℍ)) :=
begin
  letI := fact.mk hφ,
  exact { to_fun := λ x, τ ∘ₗ (((η).adjoint ∘ₗ m) ⊗ₘ id) ∘ₗ ((id ⊗ₘ x) ⊗ₘ id) ∘ₗ υ⁻¹
      ∘ₗ (id ⊗ₘ ((m).adjoint ∘ₗ η)) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹,
    map_add' := λ x y, by { simp only [tensor_product.map_add, tensor_product.add_map,
      linear_map.comp_add, linear_map.add_comp], },
    map_smul' := λ x y, by { simp only [tensor_product.map_smul, smul_map,
      linear_map.comp_smul, linear_map.smul_comp, ring_hom.id_apply], },  },
end

lemma qam.rank_one.symmetric'_eq (a b : ℍ) :
  qam.symm' hφ.elim (|a⟩⟨b|) = |bᴴ⟩⟨hφ.elim.sig (-1) aᴴ| :=
begin
  rw [qam.symm', linear_map.coe_mk, linear_map.ext_iff_inner_map],
  intros x,
  obtain ⟨α, β, this⟩ := tensor_product.eq_span ((linear_map.mul' ℂ ℍ).adjoint (1 : ℍ)),
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, lid_symm_apply, comm_symm_tmul,
    map_tmul, linear_map.comp_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, one_smul],
  rw ← this,
  simp_rw [tmul_sum, _root_.map_sum, assoc_symm_tmul, map_tmul,
    linear_map.one_apply, lid_tmul, sum_inner, linear_map.comp_apply,
    continuous_linear_map.coe_coe, rank_one_apply, ← smul_tmul, ← smul_tmul',
    smul_hom_class.map_smul,
    nontracial.unit_adjoint_eq, smul_eq_mul, linear_map.mul'_apply],
  calc ∑ x_1, inner ((inner b (α x_1) * φ (x * a)) • β x_1) x
    = star_ring_end ℂ (φ (x ⬝ a)) * ∑ x_1, inner (α x_1) b * inner (β x_1) x :
  by { simp only [inner_smul_left, _root_.map_mul, inner_conj_symm, finset.mul_sum],
    simp_rw [mul_assoc, mul_rotate', mul_comm], refl, }
  ... = star_ring_end ℂ (φ (x ⬝ a)) * inner (∑ x_1, α x_1 ⊗ₜ[ℂ] β x_1) (b ⊗ₜ[ℂ] x) :
  by { simp_rw [← inner_tmul, ← sum_inner], }
  ... = star_ring_end ℂ (φ (x ⬝ a)) * inner ((m).adjoint 1) (b ⊗ₜ[ℂ] x) : by rw this
  ... = star_ring_end ℂ (φ (x ⬝ a)) * inner bᴴ x :
  by { rw [linear_map.adjoint_inner_left, linear_map.mul'_apply, mul_eq_mul,
    linear_map.is_faithful_pos_map.inner_right_mul, matrix.mul_one], }
  ... = star_ring_end ℂ (inner xᴴ a) * inner bᴴ x :
  by { rw [linear_map.is_faithful_pos_map.inner_eq xᴴ a, conj_transpose_conj_transpose], }
  ... = star_ring_end ℂ (inner (hφ.elim.sig (-1) aᴴ) x) * inner bᴴ x :
  by { rw [nontracial.inner_symm, conj_transpose_conj_transpose], }
  ... = inner (inner (hφ.elim.sig (-1) aᴴ) x • bᴴ) x :
  by { rw [inner_smul_left], },
end

lemma rank_one_lm_eq_rank_one {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] (x y : E) :
  (rank_one_lm x y : E →ₗ[𝕜] E) = (rank_one x y : E →L[𝕜] E) :=
rfl

lemma qam.symm_adjoint_eq_symm'_of_adjoint (x : l(ℍ)) :
  (qam.symm hφ.elim x).adjoint = qam.symm' hφ.elim (x.adjoint) :=
begin
  obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one x,
  simp_rw [map_sum, ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint, rank_one_lm_eq_rank_one,
    qam.rank_one.symmetric_eq, qam.rank_one.symmetric'_eq, ← rank_one_lm_eq_rank_one,
    rank_one_lm_adjoint],
end

private lemma commute.adjoint_adjoint {K E : Type*} [is_R_or_C K] [normed_add_comm_group E]
  [inner_product_space K E] [complete_space E] {f g : E →L[K] E} :
  commute f.adjoint g.adjoint ↔ commute f g :=
commute_star_star
private lemma commute.adjoint_adjoint_lm {K E : Type*} [is_R_or_C K] [normed_add_comm_group E]
  [inner_product_space K E] [finite_dimensional K E] {f g : E →ₗ[K] E} :
  commute f.adjoint g.adjoint ↔ commute f g :=
commute_star_star

lemma linear_map.adjoint_real_eq (f : ℍ →ₗ[ℂ] ℍ) :
  f.adjoint.real = (hφ.elim.sig 1).to_linear_map ∘ₗ f.real.adjoint ∘ₗ (hφ.elim.sig (-1)).to_linear_map :=
begin
  rw [← ext_inner_map],
  intros u,
  nth_rewrite_lhs 0 nontracial.inner_symm,
  simp_rw [linear_map.real_eq, star_eq_conj_transpose, conj_transpose_conj_transpose,
    linear_map.adjoint_inner_right],
  nth_rewrite_lhs 0 nontracial.inner_symm,
  simp_rw [conj_transpose_conj_transpose, ← linear_map.is_faithful_pos_map.sig_conj_transpose,
    ← star_eq_conj_transpose, ← linear_map.real_eq f, linear_map.comp_apply],
  simp_rw [← linear_map.adjoint_inner_left (f.real), ← alg_equiv.to_linear_map_apply,
    ← linear_map.adjoint_inner_left (hφ.elim.sig 1).to_linear_map,
    linear_map.is_faithful_pos_map.sig_adjoint],
end

lemma linear_map.is_faithful_pos_map.sig_trans_sig (x y : ℝ) :
  (hφ.elim.sig y).trans (hφ.elim.sig x) = hφ.elim.sig (x + y) :=
begin
  ext1,
  simp_rw [alg_equiv.trans_apply, linear_map.is_faithful_pos_map.sig_apply_sig],
end

lemma linear_map.is_faithful_pos_map.sig_comp_sig (x y : ℝ) :
  (hφ.elim.sig x).to_linear_map.comp (hφ.elim.sig y).to_linear_map
    = (hφ.elim.sig (x + y)).to_linear_map :=
by ext1; simp_rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply,
  linear_map.is_faithful_pos_map.sig_apply_sig]

lemma linear_map.is_faithful_pos_map.sig_zero' :
  hφ.elim.sig 0 = 1 :=
begin
  rw alg_equiv.ext_iff,
  intros,
  rw [linear_map.is_faithful_pos_map.sig_zero],
  refl,
end

private lemma comp_sig_eq (t : ℝ) (f g : ℍ →ₗ[ℂ] ℍ) :
  f ∘ₗ (hφ.elim.sig t).to_linear_map = g
    ↔ f = g ∘ₗ (hφ.elim.sig (-t)).to_linear_map :=
begin
  split; rintros rfl,
  all_goals
  { rw [linear_map.comp_assoc, linear_map.is_faithful_pos_map.sig_comp_sig], },
  work_on_goal 1 { rw add_neg_self },
  work_on_goal 2 { rw neg_add_self },
  all_goals
  { rw [linear_map.is_faithful_pos_map.sig_zero', alg_equiv.one_to_linear_map,
      linear_map.comp_one], },
end

lemma linear_map.is_real.adjoint_is_real_iff_commute_with_sig
  {f : ℍ →ₗ[ℂ] ℍ} (hf : f.is_real) :
  f.adjoint.is_real ↔
  commute f (hφ.elim.sig 1).to_linear_map :=
begin
  rw linear_map.is_real_iff at hf,
  let σ := hφ.elim.sig,
  have : commute f (σ 1).to_linear_map ↔ commute (f.adjoint) (σ 1).to_linear_map,
  { simp_rw [σ],
    nth_rewrite_rhs 0 ← linear_map.is_faithful_pos_map.sig_adjoint,
    rw commute.adjoint_adjoint_lm, },
  rw this,
  clear this,
  rw [linear_map.is_real_iff, linear_map.adjoint_real_eq, hf, ← linear_map.comp_assoc,
    comp_sig_eq, neg_neg],
  simp_rw [commute, semiconj_by, linear_map.mul_eq_comp, @eq_comm _ _ ((σ 1).to_linear_map ∘ₗ _)],
end


lemma sig_apply_pos_def_matrix (t s : ℝ) :
  hφ.elim.sig t (hφ.elim.matrix_is_pos_def.rpow s) = hφ.elim.matrix_is_pos_def.rpow s :=
begin
  simp_rw [linear_map.is_faithful_pos_map.sig_apply, pos_def.rpow_mul_rpow,
    neg_add_cancel_comm],
end
lemma sig_apply_pos_def_matrix' (t : ℝ) :
  hφ.elim.sig t φ.matrix = φ.matrix :=
begin
  nth_rewrite_rhs 0 [← pos_def.rpow_one_eq_self hφ.elim.matrix_is_pos_def],
  rw [← sig_apply_pos_def_matrix t (1 : ℝ), pos_def.rpow_one_eq_self],
end
lemma sig_apply_pos_def_matrix_mul (t : ℝ) (x : ℍ) :
  hφ.elim.sig t (hφ.elim.matrix_is_pos_def.rpow t ⬝ x) = x ⬝ hφ.elim.matrix_is_pos_def.rpow t :=
begin
  simp_rw [linear_map.is_faithful_pos_map.sig_apply, ← matrix.mul_assoc, pos_def.rpow_mul_rpow,
    neg_add_self, pos_def.rpow_zero, matrix.one_mul],
end
lemma sig_apply_pos_def_matrix_mul' (x : ℍ) :
  hφ.elim.sig 1 (φ.matrix ⬝ x) = x ⬝ φ.matrix :=
begin
  nth_rewrite_rhs 0 [← pos_def.rpow_one_eq_self hφ.elim.matrix_is_pos_def],
  rw [← sig_apply_pos_def_matrix_mul, pos_def.rpow_one_eq_self],
end
lemma sig_apply_matrix_mul_pos_def (t : ℝ) (x : ℍ) :
  hφ.elim.sig t (x ⬝ hφ.elim.matrix_is_pos_def.rpow (-t))
    = hφ.elim.matrix_is_pos_def.rpow (-t) ⬝ x :=
begin
  simp_rw [linear_map.is_faithful_pos_map.sig_apply, matrix.mul_assoc, pos_def.rpow_mul_rpow,
    neg_add_self, pos_def.rpow_zero, matrix.mul_one],
end
lemma sig_apply_matrix_mul_pos_def' (x : ℍ) :
  hφ.elim.sig (-1) (x ⬝ φ.matrix) = φ.matrix ⬝ x :=
begin
  nth_rewrite_rhs 0 [← pos_def.rpow_one_eq_self hφ.elim.matrix_is_pos_def],
  nth_rewrite_rhs 0 [← neg_neg (1 : ℝ)],
  rw [← sig_apply_matrix_mul_pos_def, neg_neg, pos_def.rpow_one_eq_self],
end
lemma sig_apply_matrix_mul_pos_def'' (x : ℍ) :
  hφ.elim.sig 1 (x ⬝ φ.matrix⁻¹) = φ.matrix⁻¹ ⬝ x :=
begin
  nth_rewrite_rhs 0 [← pos_def.rpow_neg_one_eq_inv_self hφ.elim.matrix_is_pos_def],
  rw [← sig_apply_matrix_mul_pos_def, pos_def.rpow_neg_one_eq_inv_self],
end
lemma sig_apply_basis (i : n × n) :
  hφ.elim.sig 1 (hφ.elim.basis i)
    = φ.matrix⁻¹ ⬝ e_{i.1, i.2} ⬝ hφ.elim.matrix_is_pos_def.rpow (1/2) :=
begin
  rw linear_map.is_faithful_pos_map.basis_apply,
  simp_rw [linear_map.is_faithful_pos_map.sig_apply, matrix.mul_assoc, pos_def.rpow_mul_rpow,
    pos_def.rpow_neg_one_eq_inv_self],
  norm_num,
end

lemma qam.rank_one.real (a b : ℍ) :
  (|a⟩⟨b| : ℍ →ₗ[ℂ] ℍ).real = |aᴴ⟩⟨hφ.elim.sig (-1) bᴴ| :=
begin
  rw linear_map.ext_iff,
  intros x,
  simp_rw [linear_map.real_eq, continuous_linear_map.coe_coe, rank_one_apply, star_smul],
  rw [nontracial.inner_symm],
  simp_rw [star_eq_conj_transpose, conj_transpose_conj_transpose, complex.star_def,
    inner_conj_symm, ← alg_equiv.to_linear_map_apply],
  nth_rewrite_lhs 0 [← linear_map.is_faithful_pos_map.sig_adjoint],
  rw linear_map.adjoint_inner_right,
end

lemma qam.symm'_eq_adjoint_real (A : ℍ →ₗ[ℂ] ℍ) :
  qam.symm' hφ.elim A = A.adjoint.real :=
begin
  obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one A,
  simp_rw [map_sum, linear_map.real_sum, qam.rank_one.symmetric'_eq, ← rank_one_lm_eq_rank_one,
    rank_one_lm_adjoint, rank_one_lm_eq_rank_one, qam.rank_one.real],
end

lemma qam.symm_eq_real_adjoint (x : l(ℍ)) :
  qam.symm hφ.elim x = x.real.adjoint :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp only [map_sum, linear_map.real_sum, qam.rank_one.symmetric'_eq, qam.rank_one.symmetric_eq,
    qam.rank_one.real],
  simp only [← rank_one_lm_eq_rank_one, rank_one_lm_adjoint],
end

lemma qam.symm_is_bijective :
  function.bijective ⇑(qam.symm hφ.elim : l(ℍ) →ₗ[ℂ] l(ℍ)) :=
begin
  suffices : function.injective ⇑(qam.symm hφ.elim),
  { exact ⟨this, linear_map.surjective_of_injective this⟩, },
  intros x y,
  simp_rw [qam.symm_eq_real_adjoint, ← linear_map.star_eq_adjoint,
    star_inj, ← linear_map.real_inj_eq, imp_self],
end
lemma qam.symm'_is_bijective :
  function.bijective ⇑(qam.symm' hφ.elim : l(ℍ) →ₗ[ℂ] l(ℍ)) :=
begin
  suffices : function.injective ⇑(qam.symm' hφ.elim),
  { exact ⟨this, linear_map.surjective_of_injective this⟩, },
  intros x y,
  simp_rw [qam.symm'_eq_adjoint_real, ← linear_map.star_eq_adjoint,
    ← linear_map.real_inj_eq, star_inj, imp_self],
end

noncomputable def qam.symm.invertible :
  invertible (qam.symm hφ.elim : l(l(ℍ))) :=
begin
  use (qam.symm' hφ.elim : l(l(ℍ))),
  all_goals
  { apply linear_map.ext_of_rank_one',
    intros a b,
    simp only [linear_map.mul_apply, linear_map.one_apply,
      qam.symm_eq_real_adjoint, qam.symm'_eq_adjoint_real,
      linear_map.adjoint_adjoint, linear_map.real_real], },
end

noncomputable def qam.symm'.invertible :
  invertible (qam.symm' hφ.elim : l(l(ℍ))) :=
begin
  use (qam.symm hφ.elim : l(l(ℍ))),
  all_goals
  { apply linear_map.ext_of_rank_one',
    intros a b,
    simp only [linear_map.mul_apply, linear_map.one_apply,
      qam.symm_eq_real_adjoint, qam.symm'_eq_adjoint_real,
      linear_map.adjoint_adjoint, linear_map.real_real], },
end

lemma qam.symm_iff_symm' (a b : l(ℍ)) :
  qam.symm hφ.elim a = b ↔ qam.symm' hφ.elim b = a :=
begin
  rw [← linear_map.adjoint_adjoint (qam.symm hφ.elim a), qam.symm_adjoint_eq_symm'_of_adjoint],
  simp_rw [qam.symm'_eq_adjoint_real, linear_map.adjoint_adjoint,
    linear_map.real_inj_eq b.adjoint.real, linear_map.real_real, ← linear_map.star_eq_adjoint,
    star_eq_iff_star_eq],
end

lemma qam.symm'_symm_real_eq_adjoint_tfae (A : ℍ →ₗ[ℂ] ℍ) :
  tfae [qam.symm hφ.elim A = A,
    qam.symm' hφ.elim A = A,
    A.real = A.adjoint,
    ∀ x y, φ ((A x) ⬝ y) = φ (x ⬝ (A y))] :=
begin
  tfae_have : 1 ↔ 2,
  { exact qam.symm_iff_symm' _ _, },
  tfae_have : 2 ↔ 3,
  { rw [qam.symm'_eq_adjoint_real],
    nth_rewrite_lhs 0 linear_map.real_inj_eq,
    rw [linear_map.real_real, eq_comm], },
  tfae_have : 3 → 4,
  { intros h x y,
    calc φ (A x ⬝ y) = ⟪(A x)ᴴ, y⟫_ℂ :
    by { rw [linear_map.is_faithful_pos_map.inner_eq, conj_transpose_conj_transpose], }
    ... = ⟪A.real xᴴ, y⟫_ℂ :
    by { simp_rw [linear_map.real_eq, star_eq_conj_transpose, conj_transpose_conj_transpose], }
    ... = ⟪A.adjoint xᴴ, y⟫_ℂ : by rw h
    ... = ⟪xᴴ, A y⟫_ℂ : by rw linear_map.adjoint_inner_left
    ... = φ (x ⬝ A y) :
    by { rw [linear_map.is_faithful_pos_map.inner_eq,
      conj_transpose_conj_transpose], }, },
  tfae_have : 4 → 3,
  { intros h,
    rw linear_map.ext_iff_inner_map,
    intros u,
    rw [linear_map.adjoint_inner_left],
    nth_rewrite_rhs 0 [linear_map.is_faithful_pos_map.inner_eq],
    rw [← h, linear_map.real_eq, linear_map.is_faithful_pos_map.inner_eq,
      star_eq_conj_transpose, conj_transpose_conj_transpose],
    refl, },
  tfae_finish,
end

lemma sig_comp_eq_iff (t : ℝ) (A B : ℍ →ₗ[ℂ] ℍ) :
  (hφ.elim.sig t).to_linear_map.comp A = B ↔ A = (hφ.elim.sig (-t)).to_linear_map.comp B :=
begin
  split; rintros rfl,
  all_goals { rw [← linear_map.comp_assoc, linear_map.is_faithful_pos_map.sig_comp_sig], },
  work_on_goal 1 { rw neg_add_self, },
  work_on_goal 2 { rw add_neg_self, },
  all_goals { rw [linear_map.is_faithful_pos_map.sig_zero', alg_equiv.one_to_linear_map,
      linear_map.one_comp], },
end

lemma linear_map.is_faithful_pos_map.sig_real {t : ℝ} :
  (hφ.elim.sig t).to_linear_map.real = (hφ.elim.sig (-t)).to_linear_map :=
begin
  ext1,
  simp_rw [linear_map.real_eq, alg_equiv.to_linear_map_apply, star_eq_conj_transpose,
    linear_map.is_faithful_pos_map.sig_conj_transpose, conj_transpose_conj_transpose],
end

lemma qam.commute_with_sig_iff_symm_eq_symm' {A : ℍ →ₗ[ℂ] ℍ} :
  qam.symm hφ.elim A = qam.symm' hφ.elim A
    ↔ commute A (hφ.elim.sig 1).to_linear_map :=
begin
  rw [qam.symm_eq_real_adjoint, qam.symm'_eq_adjoint_real,
    linear_map.adjoint_real_eq, eq_comm, sig_comp_eq_iff,
    ← star_inj],
  simp_rw [linear_map.star_eq_adjoint, linear_map.adjoint_comp, linear_map.adjoint_adjoint,
    linear_map.is_faithful_pos_map.sig_adjoint],
  rw [linear_map.real_inj_eq],
  simp_rw [linear_map.real_comp, linear_map.real_real,
    linear_map.is_faithful_pos_map.sig_real, neg_neg],
  rw eq_comm,
  refl,
end

lemma qam.commute_with_sig_of_symm {A : ℍ →ₗ[ℂ] ℍ} (hA : qam.symm hφ.elim A = A) :
  commute A (hφ.elim.sig 1).to_linear_map :=
begin
  rw [← qam.commute_with_sig_iff_symm_eq_symm'],
  nth_rewrite 1 [← (qam.symm_iff_symm' _ _).mp hA] at hA,
  exact hA,
end

-- `τ ϰ (1 ⊗ η⋆ m) (m⋆ η ⊗ 1) τ⁻¹ = 1`
lemma qam.symm_one :
  qam.symm hφ.elim 1 = (1 : l(ℍ)) :=
begin
  rw [qam.symm_eq_real_adjoint, linear_map.real_one, linear_map.adjoint_one],
end

def qam (φ : ℍ →ₗ[ℂ] ℂ) [hφ : fact φ.is_faithful_pos_map] (x : l(ℍ)) :=
qam.refl_idempotent hφ.elim x x = x

def qam.is_self_adjoint [hφ : fact φ.is_faithful_pos_map] (x : l(ℍ)) : Prop :=
x.adjoint = x

def qam.is_symm (x : l(ℍ)) : Prop :=
qam.symm hφ.elim x = x

def qam_lm_nontracial_is_reflexive (x : ℍ →ₗ[ℂ] ℍ) : Prop :=
qam.refl_idempotent hφ.elim x 1 = (1 : l(ℍ))

def qam_lm_nontracial_is_unreflexive (x : ℍ →ₗ[ℂ] ℍ) : Prop :=
qam.refl_idempotent hφ.elim x 1 = (0 : l(ℍ))

lemma std_basis_matrix_squash (i j k l : n) (x : matrix n n ℂ) :
  e_{i,j} ⬝ x ⬝ e_{k,l} = x j k • e_{i,l} :=
begin
  ext1,
  simp_rw [mul_apply, pi.smul_apply, std_basis_matrix,
    smul_ite, mul_boole, boole_mul, ite_and],
  simp only [finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq',
    finset.sum_ite_eq, finset.mem_univ, if_true, smul_eq_mul, mul_one, mul_zero],
  simp_rw [← ite_and, and_comm (l = j_1) (i = i_1)],
end

lemma finset_foo {α β γ ζ ε ξ φ ι : Type*} [add_comm_monoid β]
  {a : finset α} {b : finset γ} {c : finset ζ} {d : finset ε} {e : finset ξ}
  {j : finset φ} {h : finset ι} {f : α → γ → ζ → ε → ξ → φ → ι → β} :
  ∑ (x : α) in a, ∑ (y : γ) in b, ∑ (z : ζ) in c, ∑ (w : ε) in d, ∑ (v : ξ) in e,
    ∑ (u : φ) in j, ∑ (t : ι) in h, f x y z w v u t
  = ∑ (w : ε) in d, ∑ (u : φ) in j,
      ∑ (v : ξ) in e, ∑ (t : ι) in h,
      ∑ (x : α) in a, ∑ (y : γ) in b, ∑ (z : ζ) in c,
        f x y z w v u t :=
begin
  rw finset.sum_4_rotate,
  congr, ext,
  rw finset.sum_5_rotate,
  congr, ext,
  rw finset.sum_4_rotate,
  congr, ext,
  rw finset.sum_4_rotate,
end

lemma rank_one_lm_smul {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] (x y : E) (r : 𝕜) :
  (rank_one_lm x (r • y) : E →ₗ[𝕜] E) = star_ring_end 𝕜 r • rank_one_lm x y :=
by rw [rank_one_lm, rank_one.smul_apply]; refl

lemma smul_rank_one_lm {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] (x y : E) (r : 𝕜) :
  (rank_one_lm (r • x) y : E →ₗ[𝕜] E) = r • rank_one_lm x y :=
by rw [rank_one_lm, rank_one.apply_smul]; refl

private lemma nontracial_basis_apply {Q : ℍ} (hQ : Q.pos_def) (i j k l : n) :
  (e_{i,j} ⬝ hQ.rpow (-(1/2))) k l
    = ite (i = k) (hQ.rpow (-(1/2)) j l) 0 :=
begin
  simp_rw [mul_apply, std_basis_matrix, boole_mul, ite_and, finset.sum_ite_irrel,
    finset.sum_const_zero, finset.sum_ite_eq, finset.mem_univ, if_true],
end

noncomputable def sigop (hφ : φ.is_faithful_pos_map) (t : ℝ) :
  l(ℍᵐᵒᵖ) :=
(op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) ∘ₗ (hφ.sig t).to_linear_map ∘ₗ (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ)

private lemma Psi.symmetric_rank_one (a b : ℍ) (t s : ℝ) :
  hφ.elim.Psi t s (qam.symm hφ.elim (|a⟩⟨b|))
    = ((hφ.elim.sig (t+s-1)).to_linear_map ⊗ₘ (sigop hφ.elim (-t-s)))
      (ten_swap (hφ.elim.Psi t s (|a⟩⟨b|))) :=
begin
  simp_rw [sigop, qam.rank_one.symmetric_eq, linear_map.is_faithful_pos_map.Psi,
    linear_equiv.coe_mk, linear_map.is_faithful_pos_map.Psi_to_fun'_apply,
    ten_swap_apply, map_tmul, linear_map.comp_apply, unop_apply, op_apply, mul_opposite.unop_op,
    alg_equiv.to_linear_map_apply, linear_map.is_faithful_pos_map.sig_conj_transpose,
    linear_map.is_faithful_pos_map.sig_apply_sig, conj_transpose_conj_transpose,
    sub_add_comm, ← sub_eq_add_neg, sub_sub_cancel_left],
  ring_nf,
end

lemma Psi.symmetric (a : l(ℍ)) (t s : ℝ) :
  hφ.elim.Psi t s (qam.symm hφ.elim a)
    = ((hφ.elim.sig (t+s-1)).to_linear_map ⊗ₘ (sigop hφ.elim (-t-s)))
      (ten_swap (hφ.elim.Psi t s a)) :=
begin
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one,
  simp_rw [map_sum, Psi.symmetric_rank_one],
end

private lemma Psi.symmetric'_rank_one (a b : ℍ) (t s : ℝ) :
  hφ.elim.Psi t s (qam.symm' hφ.elim (|a⟩⟨b|))
    = ((hφ.elim.sig (t+s)).to_linear_map ⊗ₘ (sigop hφ.elim (1-t-s)))
      (ten_swap (hφ.elim.Psi t s (|a⟩⟨b|))) :=
begin
  simp_rw [sigop, qam.rank_one.symmetric'_eq, linear_map.is_faithful_pos_map.Psi,
    linear_equiv.coe_mk, linear_map.is_faithful_pos_map.Psi_to_fun'_apply,
    ten_swap_apply, map_tmul, linear_map.comp_apply, op_apply, unop_apply,
    mul_opposite.unop_op, alg_equiv.to_linear_map_apply,
    linear_map.is_faithful_pos_map.sig_conj_transpose, neg_neg,
    linear_map.is_faithful_pos_map.sig_apply_sig, conj_transpose_conj_transpose],
  ring_nf,
end

lemma Psi.symmetric' (a : l(ℍ)) (t s : ℝ) :
  hφ.elim.Psi t s (qam.symm' hφ.elim a)
    = ((hφ.elim.sig (t+s)).to_linear_map ⊗ₘ (sigop hφ.elim (1-t-s)))
      (ten_swap (hφ.elim.Psi t s a)) :=
begin
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one,
  simp_rw [map_sum, Psi.symmetric'_rank_one],
end

private lemma Psi.idempotent_rank_one (a b c d : ℍ) (t s : ℝ) :
  hφ.elim.Psi t s (qam.refl_idempotent hφ.elim (↑|a⟩⟨b|) (↑|c⟩⟨d|))
    = (hφ.elim.Psi t s (|a⟩⟨b|)) * (hφ.elim.Psi t s (|c⟩⟨d|)) :=
begin
  simp_rw [qam.rank_one.refl_idempotent_eq, linear_map.is_faithful_pos_map.Psi,
    linear_equiv.coe_mk, linear_map.is_faithful_pos_map.Psi_to_fun'_apply,
    algebra.tensor_product.tmul_mul_tmul, mul_eq_mul, op_apply, ← mul_opposite.op_mul, mul_eq_mul,
    ← conj_transpose_mul, ← mul_eq_mul, _root_.map_mul],
end

lemma Psi.refl_idempotent (A B : l(ℍ)) (t s : ℝ) :
  hφ.elim.Psi t s (qam.refl_idempotent hφ.elim A B)
    = (hφ.elim.Psi t s A) * (hφ.elim.Psi t s B) :=
begin
  obtain ⟨Aα, Aβ, rfl⟩ := A.exists_sum_rank_one,
  obtain ⟨Bα, Bβ, rfl⟩ := B.exists_sum_rank_one,
  simp_rw [map_sum, linear_map.sum_apply, map_sum, Psi.idempotent_rank_one,
    finset.mul_sum, finset.sum_mul],
end

lemma ten_swap_sig (x y : ℝ) :
  (ten_swap : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ
    (tensor_product.map ((hφ.elim.sig x).to_linear_map : l(ℍ)) ((sigop hφ.elim y) : l(ℍᵐᵒᵖ)))
    = ((((hφ.elim.sig y).to_linear_map : l(ℍ)) ⊗ₘ (sigop hφ.elim x))
      : l(ℍ ⊗[ℂ] ℍᵐᵒᵖ)) ∘ₗ ten_swap
      :=
begin
  rw tensor_product.ext_iff,
  intros x y,
  simp only [linear_map.comp_apply, map_tmul, ten_swap_apply, op_apply, unop_apply,
    mul_opposite.unop_op, mul_opposite.op_unop],
  refl,
end

private lemma Psi.adjoint_rank_one (a b : ℍ) (t s : ℝ) :
  hφ.elim.Psi t s (|a⟩⟨b| : l(ℍ)).adjoint
  = ((hφ.elim.sig (t - s)).to_linear_map ⊗ₘ (sigop hφ.elim (t - s)))
      (ten_swap (star (hφ.elim.Psi t s (|a⟩⟨b|)))) :=
begin
  simp_rw [← rank_one_lm_eq_rank_one, sigop],
  rw [rank_one_lm_adjoint],
  simp_rw [rank_one_lm_eq_rank_one, linear_map.is_faithful_pos_map.Psi, linear_equiv.coe_mk,
    linear_map.is_faithful_pos_map.Psi_to_fun'_apply, tensor_op_star_apply, unop_apply,
    op_apply, mul_opposite.unop_op, star_eq_conj_transpose,
    conj_transpose_conj_transpose, ← linear_map.comp_apply],
  have := @ten_swap_sig n _ _ φ _,
  simp_rw [sigop] at this,
  simp_rw [← this, linear_map.comp_apply, map_tmul, linear_map.comp_apply, unop_apply,
    mul_opposite.unop_op,
    linear_map.is_faithful_pos_map.sig_conj_transpose, alg_equiv.to_linear_map_apply,
    linear_map.is_faithful_pos_map.sig_apply_sig, ten_swap_apply, op_apply, mul_opposite.unop_op],
  ring_nf,
end

lemma Psi.adjoint (a : l(ℍ)) (t s : ℝ) :
  hφ.elim.Psi t s a.adjoint
  = ((hφ.elim.sig (t - s)).to_linear_map ⊗ₘ (sigop hφ.elim (t - s)))
    (ten_swap (star (hφ.elim.Psi t s a))) :=
begin
  obtain ⟨α, β, rfl⟩ := a.exists_sum_rank_one,
  simp_rw [map_sum, Psi.adjoint_rank_one, star_sum, map_sum],
end

private lemma one_to_continuous_linear_map :
  (1 : ℍ →ₗ[ℂ] ℍ).to_continuous_linear_map = 1 :=
rfl

lemma qam.reflexive_eq_rank_one (a b : ℍ) :
  qam.refl_idempotent hφ.elim (|a⟩⟨b|) 1 = linear_map.mul_left ℂ (a ⬝ bᴴ) :=
begin
  simp_rw [linear_map.ext_iff_inner_map],
  intros u,
  let f := @linear_map.is_faithful_pos_map.orthonormal_basis n _ _ φ _,
  rw [← rank_one.sum_orthonormal_basis_eq_id_lm f],
  simp_rw [map_sum, linear_map.sum_apply, qam.rank_one.refl_idempotent_eq,
    continuous_linear_map.coe_coe, rank_one_apply, linear_map.mul_left_apply,
    sum_inner, mul_eq_mul, inner_product_space.core.inner_smul_left,
    linear_map.is_faithful_pos_map.inner_left_mul _ (f _), inner_conj_symm,
    orthonormal_basis.sum_inner_mul_inner, ← linear_map.is_faithful_pos_map.inner_left_mul,
    matrix.mul_assoc],
end

lemma qam.reflexive'_eq_rank_one (a b : ℍ) :
  qam.refl_idempotent hφ.elim 1 (|a⟩⟨b|) = linear_map.mul_right ℂ ((hφ.elim.sig (-1) bᴴ) ⬝ a) :=
begin
  simp_rw [← ext_inner_map],
  intros u,
  let f := @linear_map.is_faithful_pos_map.orthonormal_basis n _ _ φ _,
  rw [← rank_one.sum_orthonormal_basis_eq_id_lm f, map_sum, linear_map.sum_apply],
  simp_rw [qam.rank_one.refl_idempotent_eq, linear_map.sum_apply,
    continuous_linear_map.coe_coe, rank_one_apply,
    linear_map.mul_right_apply, mul_eq_mul, sum_inner,
    inner_product_space.core.inner_smul_left,
    linear_map.is_faithful_pos_map.inner_right_conj _ a,
    linear_map.is_faithful_pos_map.inner_right_conj _ b,
    inner_conj_symm, orthonormal_basis.sum_inner_mul_inner,
    ← linear_map.is_faithful_pos_map.inner_right_conj, linear_map.is_faithful_pos_map.sig_apply,
    neg_neg, pos_def.rpow_one_eq_self, pos_def.rpow_neg_one_eq_inv_self, matrix.mul_assoc],
end

lemma map_sig_star (t s : ℝ) (x : ℍ ⊗[ℂ] ℍᵐᵒᵖ) :
  star (((hφ.elim.sig t).to_linear_map ⊗ₘ (sigop hφ.elim s)) x)
    = ((hφ.elim.sig (-t)).to_linear_map ⊗ₘ (sigop hφ.elim (-s))) (star x) :=
begin
  apply x.induction_on,
  { simp only [star_zero, map_zero], },
  { intros,
    simp only [map_tmul, tensor_op_star_apply, linear_map.is_faithful_pos_map.sig_conj_transpose,
      linear_map.comp_apply, op_apply, unop_apply, mul_opposite.unop_op,
      mul_opposite.op_unop, alg_equiv.to_linear_map_apply, sigop,
      star_eq_conj_transpose], },
  { intros z w hz hw,
    simp only [_root_.map_add, hz, hw, star_add_monoid.star_add], },
end

lemma op_sig_unop_comp (t s : ℝ) :
  sigop hφ.elim t ∘ₗ sigop hφ.elim s
    = sigop hφ.elim (t + s) :=
begin
  rw linear_map.ext_iff,
  intros x,
  simp only [linear_map.comp_apply, sigop, unop_op, linear_map.is_faithful_pos_map.sig_apply_sig,
    alg_equiv.to_linear_map_apply],
end

theorem map_sig_injective (t s : ℝ) :
  function.injective ⇑((hφ.elim.sig t).to_linear_map ⊗ₘ (sigop hφ.elim s)) :=
begin
  intros a b h,
  have : ∀ a, a = ((hφ.elim.sig (-t)).to_linear_map ⊗ₘ (sigop hφ.elim (-s)))
    (((hφ.elim.sig t).to_linear_map ⊗ₘ sigop hφ.elim s) a),
  { intros a,
    simp only [← linear_map.comp_apply, ← map_comp, op_sig_unop_comp,
      linear_map.is_faithful_pos_map.sig_comp_sig,
      neg_add_self, linear_map.is_faithful_pos_map.sig_zero',
      linear_map.one_comp, op_comp_unop, tensor_product.map_one,
      linear_map.one_apply, alg_equiv.one_to_linear_map],
    simp only [sigop, linear_map.is_faithful_pos_map.sig_zero', alg_equiv.one_to_linear_map,
      linear_map.one_comp, op_comp_unop, tensor_product.map_one, linear_map.one_apply], },
  rw [this a],
  simp_rw [h],
  rw [← this b],
end

lemma map_sig_eq (t s : ℝ) :
  tensor_product.map (hφ.elim.sig t).to_linear_map (sigop hφ.elim s)
    = (linear_map.mul_left ℂ (hφ.elim.matrix_is_pos_def.rpow (-t)
      ⊗ₜ (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow s))) ∘ₗ
    (linear_map.mul_right ℂ (hφ.elim.matrix_is_pos_def.rpow (t)
      ⊗ₜ (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow (-s)))) :=
begin
  rw tensor_product.ext_iff,
  intros a b,
  let b' := (unop : ℍᵐᵒᵖ →ₗ[ℂ] ℍ) b,
  have : b = (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) b' := rfl,
  simp only [this, map_tmul, linear_map.comp_apply, linear_map.mul_left_apply,
    linear_map.mul_right_apply, algebra.tensor_product.tmul_mul_tmul, sigop, unop_op,
    linear_map.is_faithful_pos_map.sig_apply, linear_map.coe_mk,
    ← mul_opposite.op_mul, mul_eq_mul, matrix.mul_assoc, alg_equiv.to_linear_map_apply,
    linear_equiv.coe_coe, mul_opposite.coe_op_linear_equiv,
    mul_opposite.coe_op_linear_equiv_symm, unop_apply, op_apply, mul_opposite.unop_op],
end

lemma map_sig_mul_left_injective (t s : ℝ) :
  function.injective (linear_map.mul_left ℂ (hφ.elim.matrix_is_pos_def.rpow t
    ⊗ₜ[ℂ] (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow s))) :=
begin
  intros a b h,
  have : ∀ a, a = (linear_map.mul_left ℂ (hφ.elim.matrix_is_pos_def.rpow (-t)
    ⊗ₜ[ℂ] (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow (-s))))
      (linear_map.mul_left ℂ ((hφ.elim.matrix_is_pos_def.rpow t
    ⊗ₜ[ℂ] (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow s))) a),
  { intros a,
    simp_rw [← linear_map.comp_apply, ← linear_map.mul_left_mul,
      algebra.tensor_product.tmul_mul_tmul, op_apply, ← mul_opposite.op_mul,
      mul_eq_mul, pos_def.rpow_mul_rpow, neg_add_self, add_neg_self, pos_def.rpow_zero,
      mul_opposite.op_one, ← algebra.tensor_product.one_def, linear_map.mul_left_one,
      linear_map.id_apply], },
  rw [this a, h, ← this],
end

lemma map_sig_mul_right_injective (t s : ℝ) :
  function.injective (linear_map.mul_right ℂ (hφ.elim.matrix_is_pos_def.rpow t
    ⊗ₜ[ℂ] (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow s))) :=
begin
  intros a b h,
  have : ∀ a, a = (linear_map.mul_right ℂ (hφ.elim.matrix_is_pos_def.rpow (-t)
    ⊗ₜ[ℂ] (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow (-s))))
    (linear_map.mul_right ℂ ((hφ.elim.matrix_is_pos_def.rpow t
      ⊗ₜ[ℂ] (op : ℍ →ₗ[ℂ] ℍᵐᵒᵖ) (hφ.elim.matrix_is_pos_def.rpow s))) a),
  { intros a,
    simp_rw [← linear_map.comp_apply, ← linear_map.mul_right_mul,
      algebra.tensor_product.tmul_mul_tmul, op_apply, ← mul_opposite.op_mul,
      mul_eq_mul, pos_def.rpow_mul_rpow, neg_add_self, add_neg_self, pos_def.rpow_zero,
      mul_opposite.op_one, ← algebra.tensor_product.one_def, linear_map.mul_right_one,
      linear_map.id_apply], },
  rw [this a, h, ← this],
end

lemma linear_map.matrix.mul_right_adjoint (x : ℍ) :
  (linear_map.mul_right ℂ x).adjoint = linear_map.mul_right ℂ (hφ.elim.sig (-1) xᴴ) :=
begin
  symmetry,
  rw @linear_map.eq_adjoint_iff ℂ _,
  intros a b,
  simp_rw [linear_map.mul_right_apply, matrix.mul_eq_mul, linear_map.is_faithful_pos_map.sig_apply,
    neg_neg, pos_def.rpow_one_eq_self, pos_def.rpow_neg_one_eq_inv_self,
    ← linear_map.is_faithful_pos_map.inner_left_conj],
end

lemma linear_map.matrix.mul_left_adjoint [hφ : fact φ.is_faithful_pos_map] (x : ℍ) :
  (linear_map.mul_left ℂ x).adjoint = linear_map.mul_left ℂ xᴴ :=
begin
  symmetry,
  rw @linear_map.eq_adjoint_iff ℂ _,
  intros a b,
  simp_rw [linear_map.mul_left_apply, matrix.mul_eq_mul,
    ← linear_map.is_faithful_pos_map.inner_right_mul],
end

lemma qam.ir_refl_iff_ir_refl'_of_real {A : ℍ →ₗ[ℂ] ℍ} (hA : A.is_real) (p : Prop) [decidable p] :
  qam.refl_idempotent hφ.elim A 1 = ite p 1 0
    ↔ qam.refl_idempotent hφ.elim 1 A = ite p 1 0 :=
begin
  rw linear_map.is_real_iff at hA,
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one,
  simp_rw [linear_map.real_sum, qam.rank_one.real] at hA,
  nth_rewrite_lhs 0 ← hA,
  simp_rw [map_sum, linear_map.sum_apply, qam.reflexive_eq_rank_one,
    qam.reflexive'_eq_rank_one, ← conj_transpose_mul,
    ← @linear_map.matrix.mul_left_adjoint n _ _ φ _, ← map_sum],
  have t3 : ∀ a : l(ℍ), a.adjoint = ite p 1 0 ↔ a = ite p 1 0,
  { intros a,
    refine ⟨λ h, _, λ h, _⟩,
    { apply_fun linear_map.adjoint at h,
      simp_rw [linear_map.adjoint_adjoint, ← linear_map.star_eq_adjoint, star_ite,
        star_one, star_zero] at h,
      exact h, },
    { rw [h],
      simp_rw [← linear_map.star_eq_adjoint, star_ite, star_one, star_zero], }, },
  simp_rw [t3, linear_map.mul_left_sum, linear_map.mul_right_sum,
    linear_map.mul_left_eq_one_or_zero_iff_mul_right],
end

lemma qam.real_of_self_adjoint_symm (A : ℍ →ₗ[ℂ] ℍ)
  (h1 : A.adjoint = A) (h2 : qam.symm hφ.elim A = A) :
  A.is_real :=
begin
  rw linear_map.is_real_iff,
  have := qam.symm'_eq_adjoint_real A,
  rw [qam.symm_iff_symm', this, h1] at h2,
  exact h2,
end

lemma qam.self_adjoint_of_symm_real (A : ℍ →ₗ[ℂ] ℍ) (h1 : qam.symm hφ.elim A = A) (h2 : A.is_real) :
  A.adjoint = A :=
begin
  rw linear_map.is_real_iff at h2,
  have := qam.symm'_eq_adjoint_real A,
  rw [qam.symm_iff_symm', this, ← h2, ← linear_map.real_inj_eq, h2] at h1,
  exact h1,
end

lemma qam.symm_of_real_self_adjoint (A : ℍ →ₗ[ℂ] ℍ) (h1 : A.is_real) (h2 : A.adjoint = A) :
  qam.symm hφ.elim A = A :=
begin
  rw [qam.symm_iff_symm', qam.symm'_eq_adjoint_real, h2, ← linear_map.is_real_iff],
  exact h1,
end
lemma qam.self_adjoint_symm_real_tfae (A : ℍ →ₗ[ℂ] ℍ) :
  tfae [A.adjoint = A ∧ qam.symm hφ.elim A = A,
    A.adjoint = A ∧ A.is_real,
    qam.symm hφ.elim A = A ∧ A.is_real] :=
begin
  tfae_have : 1 → 2,
  { intros h,
    exact ⟨h.1, qam.real_of_self_adjoint_symm A h.1 h.2⟩, },
  tfae_have : 2 → 3,
  { intros h,
    exact ⟨qam.symm_of_real_self_adjoint A h.2 h.1, h.2⟩, },
  tfae_have : 3 → 1,
  { intros h,
    exact ⟨qam.self_adjoint_of_symm_real A h.1 h.2, h.1⟩, },
  tfae_finish,
end

lemma Psi.real (A : ℍ →ₗ[ℂ] ℍ) (t s : ℝ) :
  hφ.elim.Psi t s A.real
    = ((hφ.elim.sig (2 * t)).to_linear_map ⊗ₘ (sigop hφ.elim (1 - 2 * s)))
      (star (hφ.elim.Psi t s A)) :=
begin
  obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one,
  simp_rw [linear_map.real_sum, map_sum, star_sum],
  simp only [map_sum, qam.rank_one.real, linear_map.is_faithful_pos_map.Psi,
    linear_equiv.coe_mk, linear_map.is_faithful_pos_map.Psi_to_fun'_apply,
    tensor_op_star_apply, unop_op, conj_transpose_conj_transpose,
    map_tmul, linear_map.is_faithful_pos_map.sig_conj_transpose,
    linear_map.is_faithful_pos_map.sig_apply_sig, sigop, linear_map.comp_apply,
    alg_equiv.to_linear_map_apply, star_eq_conj_transpose],
  simp only [neg_add_rev, neg_neg, two_mul, add_assoc, add_neg_cancel_right],
  simp_rw [sub_add, add_sub_cancel, sub_eq_add_neg],
end

lemma sigop_zero :
  sigop hφ.elim 0 = 1 :=
by rw [sigop, linear_map.is_faithful_pos_map.sig_zero', alg_equiv.one_to_linear_map,
  linear_map.one_comp, op_comp_unop]

lemma qam.is_real_and_idempotent_iff_Psi_orthogonal_projection (A : ℍ →ₗ[ℂ] ℍ) :
  (qam.refl_idempotent hφ.elim A A = A ∧ A.is_real)
    ↔ (is_idempotent_elem (hφ.elim.Psi 0 (1/2) A)
      ∧ star (hφ.elim.Psi 0 (1/2) A) = hφ.elim.Psi 0 (1/2) A) :=
begin
  nth_rewrite_lhs 0 ← function.injective.eq_iff (hφ.elim.Psi 0 (1/2)).injective,
  rw [linear_map.is_real_iff, ← function.injective.eq_iff
      (hφ.elim.Psi 0 (1/2)).injective,
    Psi.refl_idempotent, Psi.real, mul_zero, linear_map.is_faithful_pos_map.sig_zero',
    one_div, mul_inv_cancel (two_ne_zero' ℝ), sub_self, sigop_zero,
    alg_equiv.one_to_linear_map, tensor_product.map_one, linear_map.one_apply, is_idempotent_elem],
end

lemma sig_map_sigop_comp_Psi (t s r q : ℝ) :
  (tensor_product.map (hφ.elim.sig t).to_linear_map (sigop hφ.elim s)) ∘ (hφ.elim.Psi r q)
    = hφ.elim.Psi (r + t) (q - s) :=
begin
  ext1,
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  simp_rw [function.comp_apply, map_sum, linear_map.is_faithful_pos_map.Psi,
    linear_equiv.coe_mk, linear_map.is_faithful_pos_map.Psi_to_fun'_apply,
    map_tmul, sigop, linear_map.comp_apply, unop_op, alg_equiv.to_linear_map_apply,
    linear_map.is_faithful_pos_map.sig_conj_transpose,
    linear_map.is_faithful_pos_map.sig_apply_sig, neg_sub, sub_eq_add_neg, add_comm],
end
lemma sig_map_sigop_apply_Psi (t s r q : ℝ) (A : ℍ →ₗ[ℂ] ℍ) :
  (tensor_product.map (hφ.elim.sig t).to_linear_map (sigop hφ.elim s)) (hφ.elim.Psi r q A)
  = hφ.elim.Psi (r + t) (q - s) A :=
begin
  have := @sig_map_sigop_comp_Psi n _ _ φ _ t s r q,
  simp_rw [function.funext_iff, function.comp_apply] at this,
  exact this _,
end

-- :TODO:
-- lemma qam.is_qam_iff_Psi_orthogonal_projection_and_swap (A : ℍ →ₗ[ℂ] ℍ) :
--   (qam.refl_idempotent hφ.elim A A = A ∧ A.is_real ∧ qam.symm hφ.elim A = A)
--     ↔ (is_idempotent_elem (hφ.elim.Psi 0 (1/2) A)
--     ∧ star (hφ.elim.Psi 0 (1/2) A) = hφ.elim.Psi 0 (1/2) A
--       ∧ hφ.elim.Psi 0 (1/2) A = ten_swap (hφ.elim.Psi (1/2) 0 A)) :=
-- begin
--   rw [← and_assoc, qam.is_real_and_idempotent_iff_Psi_orthogonal_projection,
--     list.tfae.out (qam.self_adjoint_symm_real_tfae hφ A) 0 2,
--     and_rotate, and_comm A.is_real],
--   -- have : ∀ t, sigop hφ t = op ∘ₗ sig hφ.matrix_is_pos_def t ∘ₗ unop := λ _, rfl,
--   refine ⟨λ h, ⟨h.2, _⟩, λ h, ⟨_, h.1⟩⟩,
--   { rcases h with ⟨h1, h2, h3⟩,
--     rw qam.symm_iff_symm' at h1,
--     apply_fun hφ.Psi 0 (1/2) at h1,
--     simp_rw [Psi.symmetric' hφ] at h1,
--     ring_nf at h1,
--     simp_rw [← linear_map.comp_apply, ← ten_swap_sig, linear_map.comp_apply,
--       sig_map_sigop_apply_Psi, sub_self, zero_add] at h1,
--     exact h1.symm, },
--   { rw qam.symm_iff_symm',
--     apply_fun hφ.Psi 0 (1/2) using (linear_equiv.injective _),
--     simp_rw [Psi.symmetric' hφ],
--     ring_nf,
--     simp_rw [← linear_map.comp_apply, ← ten_swap_sig, linear_map.comp_apply,
--       sig_map_sigop_apply_Psi, sub_self, zero_add, h.2], },
-- end
