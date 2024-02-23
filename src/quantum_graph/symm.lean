-- /-
-- Copyright (c) 2023 Monica Omar. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Monica Omar
-- -/
-- import linear_algebra.my_ips.nontracial
-- import linear_algebra.my_ips.mat_ips
-- import linear_algebra.my_ips.tensor_hilbert
-- import linear_algebra.is_real
-- import linear_algebra.my_ips.frob
-- import linear_algebra.tensor_finite
-- import linear_algebra.my_ips.op_unop
-- import linear_algebra.lmul_rmul

-- /-!
--  # Quantum graphs: quantum adjacency matrices

--  This file defines the quantum adjacency matrix of a quantum graph.
-- -/

-- variables {n p : Type*} [fintype n] [fintype p] [decidable_eq n] [decidable_eq p]
--   {s : n → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]

-- open_locale tensor_product big_operators kronecker

-- local notation `𝔹` := Π i, matrix (s i) (s i) ℂ
-- local notation `ℍ` := matrix n n ℂ
-- local notation `⊗K` := matrix (n × n) (n × n) ℂ
-- local notation `l(`x`)` := x →ₗ[ℂ] x
-- local notation `L(`x`)` := x →L[ℂ] x

-- local notation `e_{` i `,` j `}` := matrix.std_basis_matrix i j (1 : ℂ)

-- variables {φ : ℍ →ₗ[ℂ] ℂ} [hφ : fact φ.is_faithful_pos_map]
--   {ψ : matrix p p ℂ →ₗ[ℂ] ℂ} (hψ : ψ.is_faithful_pos_map)
--   {℘ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ}

-- open_locale matrix
-- open matrix

-- local notation `|` x `⟩⟨` y `|` := (@rank_one ℂ _ _ _ _ x y)
-- local notation `m` := linear_map.mul' ℂ 𝔹
-- local notation `η` := algebra.linear_map ℂ 𝔹
-- local notation x ` ⊗ₘ ` y := tensor_product.map x y
-- local notation `υ` :=
--   ((tensor_product.assoc ℂ 𝔹 𝔹 𝔹) : (𝔹 ⊗[ℂ] 𝔹 ⊗[ℂ] 𝔹) →ₗ[ℂ] 𝔹 ⊗[ℂ] (𝔹 ⊗[ℂ] 𝔹))
-- local notation `υ⁻¹` :=
--   ((tensor_product.assoc ℂ 𝔹 𝔹 𝔹).symm : 𝔹 ⊗[ℂ] (𝔹 ⊗[ℂ] 𝔹) →ₗ[ℂ] (𝔹 ⊗[ℂ] 𝔹 ⊗[ℂ] 𝔹))
-- local notation `ϰ` := (↑(tensor_product.comm ℂ 𝔹 ℂ) : (𝔹 ⊗[ℂ] ℂ) →ₗ[ℂ] (ℂ ⊗[ℂ] 𝔹))
-- local notation `ϰ⁻¹` := ((tensor_product.comm ℂ 𝔹 ℂ).symm : (ℂ ⊗[ℂ] 𝔹) →ₗ[ℂ] (𝔹 ⊗[ℂ] ℂ))
-- local notation `τ` := ((tensor_product.lid ℂ 𝔹) : (ℂ ⊗[ℂ] 𝔹) →ₗ[ℂ] 𝔹)
-- local notation `τ⁻¹` := ((tensor_product.lid ℂ 𝔹).symm : 𝔹 →ₗ[ℂ] (ℂ ⊗[ℂ] 𝔹))
-- local notation `id` := (1 : 𝔹 →ₗ[ℂ] 𝔹)

-- open_locale functional

-- noncomputable def qam.refl_idempotent (h℘ : Π i, (℘ i).is_faithful_pos_map) :
--   l(𝔹) →ₗ[ℂ] l(𝔹) →ₗ[ℂ] l(𝔹) :=
-- begin
--   letI := λ i, fact.mk (h℘ i),
--   exact { to_fun := λ x,
--     { to_fun := λ y,
--         linear_map.mul' ℂ 𝔹 ∘ₗ (x ⊗ₘ y) ∘ₗ (linear_map.mul' ℂ 𝔹).adjoint,
--       map_add' := λ x y, by { simp only [tensor_product.map_add_right, linear_map.add_comp,
--         linear_map.comp_add], },
--       map_smul' := λ r x, by { simp only [tensor_product.map_smul_right, linear_map.smul_comp,
--         linear_map.comp_smul, ring_hom.id_apply], } },
--     map_add' := λ x y, by { simp only [tensor_product.map_add_left, linear_map.add_comp,
--       linear_map.comp_add, linear_map.ext_iff, linear_map.add_apply, linear_map.coe_mk],
--       intros _ _, refl, },
--     map_smul' := λ r x, by { simp only [tensor_product.map_smul_left, linear_map.smul_comp,
--       linear_map.comp_smul, linear_map.ext_iff, linear_map.smul_apply, linear_map.coe_mk,
--       ring_hom.id_apply],
--       intros _ _, refl, }, },
-- end

-- lemma qam.rank_one.refl_idempotent_eq [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (a b c d : 𝔹) :
--   qam.refl_idempotent (λ i, (h℘ i).elim) (↑|a⟩⟨b|) (↑|c⟩⟨d|) = |a * c⟩⟨b * d| :=
-- begin
--   rw [qam.refl_idempotent, linear_map.ext_iff_inner_map],
--   intros x,
--   simp only [continuous_linear_map.coe_coe, linear_map.coe_mk, rank_one_apply,
--     linear_map.comp_apply],
--   obtain ⟨α, β, h⟩ := tensor_product.eq_span ((linear_map.mul' ℂ 𝔹).adjoint x),
--   rw ← h,
--   simp_rw [map_sum, tensor_product.map_tmul, continuous_linear_map.coe_coe, rank_one_apply,
--     linear_map.mul'_apply, smul_mul_smul, ← tensor_product.inner_tmul, ← finset.sum_smul,
--     ← inner_sum, h, linear_map.adjoint_inner_right, linear_map.mul'_apply],
-- end

-- open tensor_product

-- noncomputable def qam.symm (h℘ : Π i, (℘ i).is_faithful_pos_map) :
--   l(l(𝔹)) :=
-- begin
--   letI := λ i, fact.mk (h℘ i),
--   exact { to_fun := λ x, τ ∘ₗ ϰ ∘ₗ (id ⊗ₘ ((η).adjoint ∘ₗ (m)))
--       ∘ₗ υ ∘ₗ ((id ⊗ₘ x) ⊗ₘ id)
--       ∘ₗ (((m).adjoint ∘ₗ η) ⊗ₘ id) ∘ₗ τ⁻¹,
--     map_add' := λ x y, by {
--       simp only [tensor_product.map_add, tensor_product.add_map, linear_map.add_comp,
--         linear_map.comp_add], },
--     map_smul' := λ r x, by {
--       simp only [tensor_product.map_smul, tensor_product.smul_map, linear_map.smul_comp,
--         linear_map.comp_smul, ring_hom.id_apply], } },
-- end

-- lemma pi.pos_def.rpow_one_eq_self {Q : 𝔹} (hQ : Π i, (Q i).pos_def) :
--   pi.pos_def.rpow hQ 1 = Q :=
-- begin
--   ext1 i,
--   simp only [pi.pos_def.rpow, pos_def.rpow_one_eq_self],
-- end

-- lemma pi.pos_def.rpow_neg_one_eq_inv_self {Q : 𝔹} (hQ : Π i, (Q i).pos_def) :
--   pi.pos_def.rpow hQ (-1) = Q⁻¹ :=
-- begin
--   ext1 i,
--   simp only [pi.pos_def.rpow, pos_def.rpow_neg_one_eq_inv_self, pi.inv_apply],
-- end

-- lemma qam.rank_one.symmetric_eq [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (a b : 𝔹) :
--   qam.symm (λ i, (h℘ i).elim) (|a⟩⟨b|)
--   = |linear_map.is_faithful_pos_map.direct_sum.sig h℘ (-1) (star b)⟩⟨star a| :=
-- begin
--   rw [qam.symm, linear_map.coe_mk, linear_map.ext_iff_inner_map],
--   intros x,
--   obtain ⟨α, β, this⟩ := tensor_product.eq_span ((linear_map.mul' ℂ 𝔹).adjoint (1 : 𝔹)),
--   simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, lid_symm_apply,
--     map_tmul, linear_map.comp_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, one_smul],
--   rw [← this],
--   simp_rw [_root_.map_sum, map_tmul, linear_map.one_apply, sum_tmul, _root_.map_sum, assoc_tmul,
--     map_tmul, comm_tmul, lid_tmul, sum_inner, linear_map.comp_apply,
--     continuous_linear_map.coe_coe, rank_one_apply, ← smul_tmul', smul_hom_class.map_smul,
--     linear_map.one_apply, nontracial.direct_sum.unit_adjoint_eq, smul_eq_mul,
--     linear_map.mul'_apply, linear_map.is_faithful_pos_map.direct_sum_inner_eq (star a), star_star],
--   calc ∑ x_1, inner ((inner b (β x_1) * ((linear_map.direct_sum ℘) ((a : 𝔹) * (x : 𝔹) : 𝔹))) • α x_1) x
--     = star_ring_end ℂ ((linear_map.direct_sum ℘) (a * x)) * ∑ x_1, inner (α x_1) x * inner (β x_1) b :
--   by { simp only [inner_smul_left, _root_.map_mul, inner_conj_symm, mul_comm,
--       finset.mul_sum],
--     simp_rw [mul_assoc], }
--   ... = star_ring_end ℂ (linear_map.direct_sum ℘ (a * x)) * inner (∑ x_1, α x_1 ⊗ₜ[ℂ] β x_1) (x ⊗ₜ b) :
--   by { simp_rw [← inner_tmul, ← sum_inner], }
--   ... = star_ring_end ℂ (linear_map.direct_sum ℘ (a * x)) * inner ((m).adjoint 1) (x ⊗ₜ[ℂ] b) : by rw [this]
--   ... = star_ring_end ℂ (linear_map.direct_sum ℘ ((a : 𝔹) * (x : 𝔹)))
--     * inner (linear_map.is_faithful_pos_map.direct_sum.sig h℘ (-1) (star b)) (x) :
--   by { simp_rw [linear_map.adjoint_inner_left, linear_map.mul'_apply,
--       linear_map.is_faithful_pos_map.direct_sum_inner_left_conj _ _ b,
--       linear_map.is_faithful_pos_map.direct_sum.sig_apply, neg_neg, one_mul,
--       pi.pos_def.rpow_one_eq_self, pi.pos_def.rpow_neg_one_eq_inv_self,
--       linear_map.direct_sum_matrix_block, sum_include_block], }
--   ... = inner (linear_map.direct_sum ℘ (a * x)
--     • linear_map.is_faithful_pos_map.direct_sum.sig h℘ (-1) (star b)) x :
--   by rw inner_smul_left,
-- end

-- noncomputable def qam.symm' (h℘ : Π i, (℘ i).is_faithful_pos_map) :
--   l(l(𝔹)) :=
-- begin
--   letI := λ i, fact.mk (h℘ i),
--   exact { to_fun := λ x, τ ∘ₗ (((η).adjoint ∘ₗ m) ⊗ₘ id) ∘ₗ ((id ⊗ₘ x) ⊗ₘ id) ∘ₗ υ⁻¹
--       ∘ₗ (id ⊗ₘ ((m).adjoint ∘ₗ η)) ∘ₗ ϰ⁻¹ ∘ₗ τ⁻¹,
--     map_add' := λ x y, by { simp only [tensor_product.map_add, tensor_product.add_map,
--       linear_map.comp_add, linear_map.add_comp], },
--     map_smul' := λ x y, by { simp only [tensor_product.map_smul, smul_map,
--       linear_map.comp_smul, linear_map.smul_comp, ring_hom.id_apply], },  },
-- end

-- lemma qam.rank_one.symmetric'_eq [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (a b : 𝔹) :
--   qam.symm' (λ i, (h℘ i).elim) (|a⟩⟨b|) = |star b⟩⟨linear_map.is_faithful_pos_map.direct_sum.sig h℘ (-1) (star a)| :=
-- begin
--   rw [qam.symm', linear_map.coe_mk, linear_map.ext_iff_inner_map],
--   intros x,
--   obtain ⟨α, β, this⟩ := tensor_product.eq_span ((linear_map.mul' ℂ 𝔹).adjoint (1 : 𝔹)),
--   simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, lid_symm_apply, comm_symm_tmul,
--     map_tmul, linear_map.comp_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, one_smul],
--   rw ← this,
--   simp_rw [tmul_sum, _root_.map_sum, assoc_symm_tmul, map_tmul,
--     linear_map.one_apply, lid_tmul, sum_inner, linear_map.comp_apply,
--     continuous_linear_map.coe_coe, rank_one_apply, ← smul_tmul, ← smul_tmul',
--     smul_hom_class.map_smul,
--     nontracial.direct_sum.unit_adjoint_eq, smul_eq_mul, linear_map.mul'_apply],
--   calc ∑ x_1, inner ((inner b (α x_1) * (linear_map.direct_sum ℘) (x * a)) • β x_1) x
--     = star_ring_end ℂ ((linear_map.direct_sum ℘) (x * a))
--       * ∑ x_1, inner (α x_1) b * inner (β x_1) x :
--   by { simp only [inner_smul_left, _root_.map_mul, inner_conj_symm, finset.mul_sum],
--     simp_rw [mul_assoc, mul_rotate', mul_comm], }
--   ... = star_ring_end ℂ ((linear_map.direct_sum ℘) (x * a))
--     * inner (∑ x_1, α x_1 ⊗ₜ[ℂ] β x_1) (b ⊗ₜ[ℂ] x) :
--   by { simp_rw [← inner_tmul, ← sum_inner], }
--   ... = star_ring_end ℂ ((linear_map.direct_sum ℘) (x * a))
--     * inner ((m).adjoint 1) (b ⊗ₜ[ℂ] x) : by rw this
--   ... = star_ring_end ℂ ((linear_map.direct_sum ℘) (x * a)) * inner (star b) x :
--   by { rw [linear_map.adjoint_inner_left, linear_map.mul'_apply,
--     linear_map.is_faithful_pos_map.direct_sum_inner_right_mul, mul_one], }
--   ... = star_ring_end ℂ (inner (star x) a) * inner (star b) x :
--   by { rw [linear_map.is_faithful_pos_map.direct_sum_inner_eq (star x) a, star_star], }
--   ... = star_ring_end ℂ (inner (linear_map.is_faithful_pos_map.direct_sum.sig h℘ (-1) (star a)) x) * inner (star b) x :
--   by { rw [direct_sum.inner_symm, star_star], }
--   ... = inner (inner (linear_map.is_faithful_pos_map.direct_sum.sig h℘ (-1) (star a)) x • (star b)) x :
--   by { rw [inner_smul_left], },
-- end

-- lemma rank_one_lm_eq_rank_one {𝕜 E : Type*} [is_R_or_C 𝕜]
--   [normed_add_comm_group E] [inner_product_space 𝕜 E] (x y : E) :
--   (rank_one_lm x y : E →ₗ[𝕜] E) = (rank_one x y : E →L[𝕜] E) :=
-- rfl

-- lemma qam.symm_adjoint_eq_symm'_of_adjoint [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (x : l(𝔹)) :
--   (qam.symm (λ i, (h℘ i).elim) x).adjoint = qam.symm' (λ i, (h℘ i).elim) (x.adjoint) :=
-- begin
--   obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one x,
--   simp_rw [map_sum, ← rank_one_lm_eq_rank_one, rank_one_lm_adjoint, rank_one_lm_eq_rank_one,
--     qam.rank_one.symmetric_eq, qam.rank_one.symmetric'_eq, ← rank_one_lm_eq_rank_one,
--     rank_one_lm_adjoint],
-- end

-- private lemma commute.adjoint_adjoint {K E : Type*} [is_R_or_C K] [normed_add_comm_group E]
--   [inner_product_space K E] [complete_space E] {f g : E →L[K] E} :
--   commute f.adjoint g.adjoint ↔ commute f g :=
-- begin
--   simp_rw [← continuous_linear_map.star_eq_adjoint],
--   exact commute_star_star,
-- end
-- private lemma commute.adjoint_adjoint_lm {K E : Type*} [is_R_or_C K] [normed_add_comm_group E]
--   [inner_product_space K E] [finite_dimensional K E] {f g : E →ₗ[K] E} :
--   commute f.adjoint g.adjoint ↔ commute f g :=
-- begin
--   have := @commute.adjoint_adjoint K E _ _ _ (finite_dimensional.complete K E)
--     f.to_continuous_linear_map g.to_continuous_linear_map,
--   simp_rw [linear_map.adjoint_eq_to_clm_adjoint],
--   simp_rw [commute, semiconj_by, continuous_linear_map.ext_iff, linear_map.ext_iff,
--     linear_map.mul_apply, continuous_linear_map.mul_apply, continuous_linear_map.coe_coe] at *,
--   simp_rw [this, linear_map.to_continuous_linear_map, linear_equiv.coe_mk,
--     continuous_linear_map.coe_mk'],
-- end

-- lemma linear_map.adjoint_real_eq (f : ℍ →ₗ[ℂ] ℍ) :
--   f.adjoint.real = (hφ.elim.sig 1).to_linear_map ∘ₗ f.real.adjoint ∘ₗ (hφ.elim.sig (-1)).to_linear_map :=
-- begin
--   rw [← ext_inner_map],
--   intros u,
--   nth_rewrite_lhs 0 nontracial.inner_symm,
--   simp_rw [linear_map.real_eq, star_eq_conj_transpose, conj_transpose_conj_transpose,
--     linear_map.adjoint_inner_right],
--   nth_rewrite_lhs 0 nontracial.inner_symm,
--   simp_rw [conj_transpose_conj_transpose, ← linear_map.is_faithful_pos_map.sig_conj_transpose,
--     ← star_eq_conj_transpose, ← linear_map.real_eq f, linear_map.comp_apply],
--   simp_rw [← linear_map.adjoint_inner_left (f.real), ← alg_equiv.to_linear_map_apply,
--     ← linear_map.adjoint_inner_left (hφ.elim.sig 1).to_linear_map,
--     linear_map.is_faithful_pos_map.sig_adjoint],
-- end

-- @[instance] def B.star_module :
--   star_module ℂ 𝔹 :=
-- by {
--   apply @pi.star_module _ _ ℂ _ _ _ _,
--   exact λ i, matrix.star_module,
-- }

-- lemma linear_map.direct_sum.adjoint_real_eq [h℘ : Π i, fact (℘ i).is_faithful_pos_map]
--   (f : 𝔹 →ₗ[ℂ] 𝔹) :
--   (f.adjoint).real
--     = (linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map
--       ∘ₗ (f.real).adjoint
--       ∘ₗ (linear_map.is_faithful_pos_map.direct_sum.sig h℘ (-1)).to_linear_map :=
-- begin
--   rw [← ext_inner_map],
--   intros u,
--   nth_rewrite_lhs 0 direct_sum.inner_symm,
--   simp_rw [linear_map.real_eq, star_star, linear_map.adjoint_inner_right],
--   nth_rewrite_lhs 0 direct_sum.inner_symm,
--   simp_rw [star_star, ← linear_map.is_faithful_pos_map.direct_sum.sig_star,
--     ← linear_map.real_eq f, linear_map.comp_apply, ← linear_map.adjoint_inner_left (f.real),
--     ← alg_equiv.to_linear_map_apply, ← linear_map.adjoint_inner_left
--       (linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map,
--     linear_map.is_faithful_pos_map.direct_sum.sig_adjoint],
-- end


-- lemma linear_map.is_faithful_pos_map.sig_trans_sig (x y : ℝ) :
--   (hφ.elim.sig y).trans (hφ.elim.sig x) = hφ.elim.sig (x + y) :=
-- begin
--   ext1,
--   simp_rw [alg_equiv.trans_apply, linear_map.is_faithful_pos_map.sig_apply_sig],
-- end
-- lemma linear_map.is_faithful_pos_map.direct_sum.sig_trans_sig
--   [h℘ : Π i, fact (℘ i).is_faithful_pos_map]
--   (x y : ℝ) :
--   (linear_map.is_faithful_pos_map.direct_sum.sig h℘ y).trans
--     (linear_map.is_faithful_pos_map.direct_sum.sig h℘ x)
--   = linear_map.is_faithful_pos_map.direct_sum.sig h℘ (x + y) :=
-- begin
--   ext1,
--   simp_rw [alg_equiv.trans_apply, linear_map.is_faithful_pos_map.direct_sum.sig_apply_sig],
-- end

-- lemma linear_map.is_faithful_pos_map.sig_comp_sig (x y : ℝ) :
--   (hφ.elim.sig x).to_linear_map.comp (hφ.elim.sig y).to_linear_map
--     = (hφ.elim.sig (x + y)).to_linear_map :=
-- by ext1; simp_rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply,
--   linear_map.is_faithful_pos_map.sig_apply_sig]
-- lemma linear_map.is_faithful_pos_map.direct_sum.sig_comp_sig
--   [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (x y : ℝ) :
--   (linear_map.is_faithful_pos_map.direct_sum.sig h℘ x).to_linear_map
--     .comp (linear_map.is_faithful_pos_map.direct_sum.sig h℘ y).to_linear_map
--   = (linear_map.is_faithful_pos_map.direct_sum.sig h℘ (x + y)).to_linear_map :=
-- by ext1; simp_rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, linear_map.is_faithful_pos_map.direct_sum.sig_apply_sig]

-- lemma linear_map.is_faithful_pos_map.sig_zero' :
--   hφ.elim.sig 0 = 1 :=
-- begin
--   rw alg_equiv.ext_iff,
--   intros,
--   rw [linear_map.is_faithful_pos_map.sig_zero],
--   refl,
-- end
-- lemma linear_map.is_faithful_pos_map.direct_sum.sig_zero'
--   [h℘ : Π i, fact (℘ i).is_faithful_pos_map] :
--   linear_map.is_faithful_pos_map.direct_sum.sig h℘ 0 = 1 :=
-- begin
--   rw alg_equiv.ext_iff,
--   intros,
--   rw [linear_map.is_faithful_pos_map.direct_sum.sig_zero],
--   refl,
-- end

-- private lemma comp_sig_eq (t : ℝ) (f g : ℍ →ₗ[ℂ] ℍ) :
--   f ∘ₗ (hφ.elim.sig t).to_linear_map = g
--     ↔ f = g ∘ₗ (hφ.elim.sig (-t)).to_linear_map :=
-- begin
--   split; rintros rfl,
--   all_goals
--   { rw [linear_map.comp_assoc, linear_map.is_faithful_pos_map.sig_comp_sig], },
--   work_on_goal 1 { rw add_neg_self },
--   work_on_goal 2 { rw neg_add_self },
--   all_goals
--   { rw [linear_map.is_faithful_pos_map.sig_zero', alg_equiv.one_to_linear_map,
--       linear_map.comp_one], },
-- end
-- private lemma direct_sum.comp_sig_eq [h℘ : Π i, fact (℘ i).is_faithful_pos_map]
--   (t : ℝ) (f g : 𝔹 →ₗ[ℂ] 𝔹) :
--   f ∘ₗ (linear_map.is_faithful_pos_map.direct_sum.sig h℘ t).to_linear_map = g
--     ↔ f = g ∘ₗ (linear_map.is_faithful_pos_map.direct_sum.sig h℘ (-t)).to_linear_map :=
-- begin
--   split; rintros rfl,
--   all_goals
--   { rw [linear_map.comp_assoc, linear_map.is_faithful_pos_map.direct_sum.sig_comp_sig], },
--   work_on_goal 1 { rw add_neg_self },
--   work_on_goal 2 { rw neg_add_self },
--   all_goals { rw [linear_map.is_faithful_pos_map.direct_sum.sig_zero', alg_equiv.one_to_linear_map,
--       linear_map.comp_one], },
-- end

-- local notation `σ_` := linear_map.is_faithful_pos_map.direct_sum.sig
-- local notation `Q_` := linear_map.direct_sum_matrix_block

-- variable [h℘ : Π i, fact (℘ i).is_faithful_pos_map]
-- lemma linear_map.is_real.adjoint_is_real_iff_commute_with_sig
--   {f : 𝔹 →ₗ[ℂ] 𝔹} (hf : f.is_real) :
--   (f.adjoint).is_real ↔
--   commute f (σ_ h℘ 1).to_linear_map :=
-- begin
--   rw linear_map.is_real_iff at hf,
--   have : commute f (σ_ h℘ 1).to_linear_map ↔ commute (f.adjoint) (σ_ h℘ 1).to_linear_map,
--   { simp_rw [σ_ h℘],
--     nth_rewrite_rhs 0 ← linear_map.is_faithful_pos_map.direct_sum.sig_adjoint,
--     rw commute.adjoint_adjoint_lm, },
--   rw this,
--   clear this,
--   rw [linear_map.is_real_iff, linear_map.direct_sum.adjoint_real_eq, hf, ← linear_map.comp_assoc,
--     direct_sum.comp_sig_eq, neg_neg],
--   simp_rw [commute, semiconj_by, linear_map.mul_eq_comp, @eq_comm _ _ ((σ_ h℘ 1).to_linear_map ∘ₗ _)],
-- end

-- lemma sig_apply_pos_def_matrix (t s : ℝ) :
--   hφ.elim.sig t (hφ.elim.matrix_is_pos_def.rpow s)
--   = hφ.elim.matrix_is_pos_def.rpow s :=
-- begin
--   simp_rw [linear_map.is_faithful_pos_map.sig_apply, pos_def.rpow_mul_rpow, neg_add_cancel_comm],
-- end
-- lemma direct_sum.sig_apply_pos_def_matrix [h℘ : Π i, fact (℘ i).is_faithful_pos_map]
--   (t s : ℝ) :
--   (σ_ h℘) t (pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘) s)
--   = pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘) s :=
-- begin
--   rw [linear_map.is_faithful_pos_map.direct_sum.sig_apply h℘],
--   simp_rw [pi.pos_def.rpow_mul_rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘)],
--   rw [@neg_add_cancel_comm ℝ],
-- end

-- lemma sig_apply_pos_def_matrix' (t : ℝ) :
--   hφ.elim.sig t φ.matrix = φ.matrix :=
-- begin
--   nth_rewrite_rhs 0 [← pos_def.rpow_one_eq_self hφ.elim.matrix_is_pos_def],
--   rw [← sig_apply_pos_def_matrix t (1 : ℝ), pos_def.rpow_one_eq_self],
-- end
-- lemma direct_sum.sig_apply_pos_def_matrix' [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (t : ℝ) :
--   (σ_ h℘) t (Q_ ℘) = Q_ ℘ :=
-- begin
--   have : Q_ ℘ = λ i, (℘ i).matrix :=
--   by { ext1 i, simp only [linear_map.direct_sum_matrix_block_apply], },
--   rw [this],
--   nth_rewrite_rhs 0 [← pi.pos_def.rpow_one_eq_self (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘)],
--   rw [← direct_sum.sig_apply_pos_def_matrix t (1 : ℝ)],
--   rw [← this],

-- end

