/-
Copyright (c) 2024 Monica Omar. All rights reserved.
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

/-!
 # Quantum graphs: quantum adjacency matrices

 This file defines the quantum adjacency matrix of a quantum graph.
-/

variables {n : Type*} [fintype n] [decidable_eq n]
  {s : n → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]

open_locale tensor_product big_operators kronecker

local notation `𝔹` := Π i, matrix (s i) (s i) ℂ
local notation `l(`x`)` := x →ₗ[ℂ] x
-- local notation `L(`x`)` := x →L[ℂ] x

-- variables {℘ : Π i, matrix (s i) (s i) ℂ →ₗ[ℂ] ℂ}

open_locale matrix
open matrix

local notation `|` x `⟩⟨` y `|` := (@rank_one ℂ _ _ _ _ x y)
local notation `m` x := linear_map.mul' ℂ x
-- local notation `η` x := algebra.linear_map ℂ x
local notation x ` ⊗ₘ ` y := tensor_product.map x y
-- local notation `υ` B :=
--   ((tensor_product.assoc ℂ B B B) : (B ⊗[ℂ] B ⊗[ℂ] B) →ₗ[ℂ] B ⊗[ℂ] (B ⊗[ℂ] B))
-- local notation `υ⁻¹` B :=
--   ((tensor_product.assoc ℂ B B B).symm : B ⊗[ℂ] (B ⊗[ℂ] B) →ₗ[ℂ] (B ⊗[ℂ] B ⊗[ℂ] B))
-- local notation x`ϰ`y := (↑(tensor_product.comm ℂ x y) : (x ⊗[ℂ] y) →ₗ[ℂ] (y ⊗[ℂ] x))
-- local notation x`ϰ⁻¹`y := ((tensor_product.comm ℂ x y).symm : (y ⊗[ℂ] x) →ₗ[ℂ] (x ⊗[ℂ] y))
-- local notation `τ` x  := ((tensor_product.lid ℂ x) : (ℂ ⊗[ℂ] x) →ₗ[ℂ] x)
-- local notation `τ⁻¹` x := ((tensor_product.lid ℂ x).symm : x →ₗ[ℂ] (ℂ ⊗[ℂ] x))
-- local notation `id` x := (1 : x →ₗ[ℂ] x)

open_locale functional

class normed_add_comm_group_of_ring (B : Type*) extends ring B :=
(to_has_norm : has_norm B)
(to_metric_space : metric_space B)
(dist_eq : ∀ x y : B, dist x y = has_norm.norm (x - y))

instance my_normed_ring.to_normed_add_comm_group {B : Type*} [normed_add_comm_group_of_ring B] :
  normed_add_comm_group B :=
{ to_has_norm := normed_add_comm_group_of_ring.to_has_norm,
  dist_eq := normed_add_comm_group_of_ring.dist_eq,
  ..normed_add_comm_group_of_ring.to_metric_space }

noncomputable instance module.dual.is_normed_add_comm_group_of_ring
  {n : Type*} [fintype n] [decidable_eq n]
  {ψ : module.dual ℂ (matrix n n ℂ)}
  [hψ : fact ψ.is_faithful_pos_map] :
  normed_add_comm_group_of_ring (matrix n n ℂ) :=
{ to_has_norm := normed_add_comm_group.to_has_norm,
  to_metric_space := normed_add_comm_group.to_metric_space,
  dist_eq := normed_add_comm_group.dist_eq }

noncomputable instance pi.module.dual.is_normed_add_comm_group_of_ring
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  normed_add_comm_group_of_ring 𝔹 :=
{ to_has_norm := normed_add_comm_group.to_has_norm,
  to_metric_space := normed_add_comm_group.to_metric_space,
  dist_eq := normed_add_comm_group.dist_eq }

noncomputable def schur_idempotent
  {B : Type*}
  [normed_add_comm_group_of_ring B]
  [inner_product_space ℂ B]
  [smul_comm_class ℂ B B]
  [is_scalar_tower ℂ B B]
  [finite_dimensional ℂ B]
  :
  l(B) →ₗ[ℂ] l(B) →ₗ[ℂ] l(B) :=
begin
  exact { to_fun := λ x,
    { to_fun := λ y,
        (m B) ∘ₗ (x ⊗ₘ y) ∘ₗ (m B).adjoint,
      map_add' := λ x y, by { simp only [tensor_product.map_apply,
        tensor_product.map_add_right, linear_map.add_comp,
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

lemma schur_idempotent.apply_rank_one
  {B : Type*}
  [normed_add_comm_group_of_ring B]
  [inner_product_space ℂ B]
  [smul_comm_class ℂ B B]
  [is_scalar_tower ℂ B B]
  [finite_dimensional ℂ B] 
  (a b c d : B) :
  schur_idempotent (↑|a⟩⟨b|) (↑|c⟩⟨d|) = (|a * c⟩⟨b * d| : B →ₗ[ℂ] B) :=
begin
  rw [schur_idempotent, linear_map.ext_iff_inner_map],
  intros x,
  simp only [continuous_linear_map.coe_coe, linear_map.coe_mk, rank_one_apply,
    linear_map.comp_apply],
  obtain ⟨α, β, h⟩ := tensor_product.eq_span ((linear_map.mul' ℂ B).adjoint x),
  rw ← h,
  simp_rw [map_sum, tensor_product.map_tmul, continuous_linear_map.coe_coe, rank_one_apply,
    linear_map.mul'_apply, smul_mul_smul, ← tensor_product.inner_tmul, ← finset.sum_smul,
    ← inner_sum, h, linear_map.adjoint_inner_right, linear_map.mul'_apply],
end

-- @[elab_as_eliminator]
-- theorem linear_map.induction_on
--   {𝕜 B : Type*} [is_R_or_C 𝕜] [normed_add_comm_group B] [inner_product_space 𝕜 B]
--   [finite_dimensional 𝕜 B] {C : (B →ₗ[𝕜] B) → Prop}
--   (z : B →ₗ[𝕜] B) (C0 : C 0) (C1 : ∀ {x y}, C $ ((rank_one x y : B →L[𝕜] B) : B →ₗ[𝕜] B))
--   (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
-- begin
--   -- let f := std_orthonormal_basis 𝕜 B,
--   let n := finite_dimensional.finrank 𝕜 B * finite_dimensional.finrank 𝕜 B,
--   obtain ⟨α, β, rfl⟩ :
--     ∃ x y : fin n → B, z = ∑ i, ↑(rank_one (x i) (y i) : B →L[𝕜] B) :=
--   begin
--     let n' := finite_dimensional.finrank 𝕜 B,
--     let σ : fin (n' * n') ≃ fin n' × fin n' := fin_prod_fin_equiv.symm,
--     obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one z,
--     refine ⟨λ i, α (σ i), λ i, β (σ i), _⟩,
--     apply fintype.sum_bijective σ.symm,
--     { exact (equiv.symm σ).bijective, },
--     { simp only [equiv.apply_symm_apply, eq_self_iff_true, forall_true_iff], },
--   end,
  
-- end

lemma schur_idempotent_one_one_right {B : Type*}
  [normed_add_comm_group_of_ring B]
  [inner_product_space ℂ B]
  [smul_comm_class ℂ B B]
  [is_scalar_tower ℂ B B]
  [finite_dimensional ℂ B] (A : l(B)) :
  schur_idempotent (A : l(B)) (|(1 : B)⟩⟨(1 : B)| : l(B)) = A :=
begin
  obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one A,
  simp_rw [linear_map.map_sum, linear_map.sum_apply, schur_idempotent.apply_rank_one, mul_one],
end

lemma schur_idempotent_one_one_left {B : Type*}
  [normed_add_comm_group_of_ring B]
  [inner_product_space ℂ B]
  [smul_comm_class ℂ B B]
  [is_scalar_tower ℂ B B]
  [finite_dimensional ℂ B] (A : l(B)) :
  schur_idempotent (|(1 : B)⟩⟨(1 : B)| : l(B)) A = A :=
begin
  obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one A,
  simp_rw [linear_map.map_sum, schur_idempotent.apply_rank_one, one_mul],
end

private lemma schur_idempotent_one_right_aux {B : Type*}
  [normed_add_comm_group_of_ring B]
  [inner_product_space ℂ B]
  [smul_comm_class ℂ B B]
  [is_scalar_tower ℂ B B]
  [finite_dimensional ℂ B]
  [star_semigroup B]
  {ψ : module.dual ℂ B} (hψ : ∀ a b, ⟪a, b⟫_ℂ = ψ (star a * b))
  (a b c : B) :
  ⟪a * b, c⟫_ℂ = ⟪b, star a * c⟫_ℂ :=
begin
  simp_rw [hψ, star_semigroup.star_mul, ← mul_assoc],
end

lemma lmul_adjoint {B : Type*}
  [normed_add_comm_group_of_ring B]
  [inner_product_space ℂ B]
  [smul_comm_class ℂ B B]
  [is_scalar_tower ℂ B B]
  [finite_dimensional ℂ B]
  [star_semigroup B] {ψ : module.dual ℂ B} (hψ : ∀ a b, ⟪a, b⟫_ℂ = ψ (star a * b)) (a : B) :
  (lmul a : l(B)).adjoint = lmul (star a) :=
begin
  rw [linear_map.ext_iff_inner_map],
  intros u,
  simp_rw [linear_map.adjoint_inner_left,
    lmul_apply,
    schur_idempotent_one_right_aux hψ, star_star],
end

lemma pi.pos_def.rpow_one_eq_self {Q : 𝔹} (hQ : Π i, (Q i).pos_def) :
  pi.pos_def.rpow hQ 1 = Q :=
begin
  ext1 i,
  simp only [pi.pos_def.rpow, pos_def.rpow_one_eq_self],
end

lemma pi.pos_def.rpow_neg_one_eq_inv_self {Q : 𝔹} (hQ : Π i, (Q i).pos_def) :
  pi.pos_def.rpow hQ (-1) = Q⁻¹ :=
begin
  ext1 i,
  simp only [pi.pos_def.rpow, pos_def.rpow_neg_one_eq_inv_self, pi.inv_apply],
end

lemma module.dual.pi.is_faithful_pos_map.inner_left_conj'
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] (a b c : Π i, matrix (s i) (s i) ℂ) :
  ⟪a, b * c⟫_ℂ = ⟪a * module.dual.pi.is_faithful_pos_map.sig hψ (-1) (star c), b⟫_ℂ :=
begin
  simp_rw [module.dual.pi.is_faithful_pos_map.sig_apply, neg_neg,
    pi.pos_def.rpow_one_eq_self, pi.pos_def.rpow_neg_one_eq_inv_self,
    ← module.dual.pi.matrix_block_apply, ← module.dual.pi.is_faithful_pos_map.inner_left_conj],
end
lemma module.dual.pi.is_faithful_pos_map.inner_right_conj'
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] (a b c : Π i, matrix (s i) (s i) ℂ) :
  ⟪a * c, b⟫_ℂ = ⟪a, b * module.dual.pi.is_faithful_pos_map.sig hψ (-1) (star c)⟫_ℂ :=
begin
  rw [← inner_conj_symm, module.dual.pi.is_faithful_pos_map.inner_left_conj', inner_conj_symm],
end


lemma rmul_adjoint {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] (a : 𝔹) :
  (rmul a : l(𝔹)).adjoint
    = rmul (module.dual.pi.is_faithful_pos_map.sig hψ (-1) (star a)) :=
begin
  rw [linear_map.ext_iff_inner_map],
  intros u,
  simp_rw [linear_map.adjoint_inner_left,
    rmul_apply, module.dual.pi.is_faithful_pos_map.inner_left_conj'],
end

lemma continuous_linear_map.linear_map_adjoint {𝕜 B C : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group B]
  [normed_add_comm_group C]
  [inner_product_space 𝕜 B]
  [inner_product_space 𝕜 C]
  [finite_dimensional 𝕜 B]
  [finite_dimensional 𝕜 C]
  (x : B →L[𝕜] C) :
  (x : B →ₗ[𝕜] C).adjoint
    = @continuous_linear_map.adjoint 𝕜 _ _ _ _ _ _ _
      (finite_dimensional.complete 𝕜 B) (finite_dimensional.complete 𝕜 C) x :=
rfl

lemma schur_idempotent_adjoint {B : Type*}
  [normed_add_comm_group_of_ring B]
  [inner_product_space ℂ B]
  [smul_comm_class ℂ B B]
  [is_scalar_tower ℂ B B]
  [finite_dimensional ℂ B]
  (x y : l(B)) :
  (schur_idempotent x y).adjoint = schur_idempotent x.adjoint y.adjoint :=
begin
  obtain ⟨α, β, rfl⟩ := linear_map.exists_sum_rank_one x,
  obtain ⟨γ, δ, rfl⟩ := linear_map.exists_sum_rank_one y,
  simp only [map_sum, linear_map.sum_apply],
  repeat { apply finset.sum_congr rfl, intros, },
  simp_rw [schur_idempotent.apply_rank_one, continuous_linear_map.linear_map_adjoint,
    rank_one.adjoint, schur_idempotent.apply_rank_one],
end

lemma rank_one_lm_eq_rank_one {𝕜 E : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [inner_product_space 𝕜 E] (x y : E) :
  (rank_one_lm x y : E →ₗ[𝕜] E) = (rank_one x y : E →L[𝕜] E) :=
rfl

lemma schur_idempotent_real
-- {B : Type*}
--   [normed_add_comm_group_of_ring B]
--   [inner_product_space ℂ B]
--   [smul_comm_class ℂ B B]
--   [is_scalar_tower ℂ B B]
--   [finite_dimensional ℂ B]
--   [star_ring B]
--   [star_module ℂ B]
  -- {ψ : module.dual ℂ B} (hψ : ∀ a b, ⟪a, b⟫_ℂ = ψ (star a * b))
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (x y : l(𝔹)) :
  (schur_idempotent x y : l(𝔹)).real =
    schur_idempotent y.real x.real :=
begin
  obtain ⟨α, β, rfl⟩ := x.exists_sum_rank_one,
  obtain ⟨γ, ζ, rfl⟩ := y.exists_sum_rank_one,
  simp only [map_sum, linear_map.real_sum, linear_map.sum_apply,
    schur_idempotent.apply_rank_one],
  simp_rw [← rank_one_lm_eq_rank_one, pi.rank_one_lm_real_apply,
    rank_one_lm_eq_rank_one, schur_idempotent.apply_rank_one,
    ← _root_.map_mul, ← star_semigroup.star_mul],
  rw finset.sum_comm,
end

lemma schur_idempotent_one_right_rank_one
  {B : Type*}
  [normed_add_comm_group_of_ring B]
  [inner_product_space ℂ B]
  [smul_comm_class ℂ B B]
  [is_scalar_tower ℂ B B]
  [finite_dimensional ℂ B]
  [star_semigroup B]
  {ψ : module.dual ℂ B} (hψ : ∀ a b, ⟪a, b⟫_ℂ = ψ (star a * b))
  (a b : B) :
  schur_idempotent (↑|a⟩⟨b|) 1
    = (lmul a) * (lmul b : l(B)).adjoint :=
begin
  simp_rw [linear_map.ext_iff_inner_map],
  intros u,
  let f := std_orthonormal_basis ℂ B,
  rw [← rank_one.sum_orthonormal_basis_eq_id_lm f],
  simp_rw [map_sum, linear_map.sum_apply, schur_idempotent.apply_rank_one,
    continuous_linear_map.coe_coe, rank_one_apply,
    linear_map.mul_apply,
    lmul_apply, sum_inner,
    inner_smul_left,
    schur_idempotent_one_right_aux hψ,
    inner_conj_symm,
    orthonormal_basis.sum_inner_mul_inner,
    lmul_adjoint hψ, lmul_apply],
end

lemma matrix.cast_apply
  {i j : n} (x : matrix (s i) (s i) ℂ)
  (h : i = j)
  (p q : s j) :
  (by rw [h] : matrix (s i) (s i) ℂ = matrix (s j) (s j) ℂ).mp x p q = x (by rw [h]; exact p) (by rw [h]; exact q) :=
begin
  tidy,
end
lemma matrix.cast_mul
  {i j : n} (x y : matrix (s i) (s i) ℂ)
  (h : i = j) :
  (by rw [h] : matrix (s i) (s i) ℂ = matrix (s j) (s j) ℂ).mp (x * y)
    = (by rw [h] : matrix (s i) (s i) ℂ = matrix (s j) (s j) ℂ).mp x
      * (by rw [h] : matrix (s i) (s i) ℂ = matrix (s j) (s j) ℂ).mp y :=
begin
  tidy,
end
lemma module.dual.pi.is_faithful_pos_map.basis.apply_cast_eq_mp
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] {i j : n}
  (h : i = j)
  (p : s i × s i) :
  (by rw [h] : matrix (s i) (s i) ℂ = matrix (s j) (s j) ℂ).mp ((hψ i).elim.basis p)
  = (hψ j).elim.basis (by rw [← h]; exact p) :=
begin
  tidy,
end

lemma pi_lmul_to_matrix
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] (x : 𝔹) :
  (module.dual.pi.is_faithful_pos_map.to_matrix (λ i, (hψ i).elim) (lmul x : l(𝔹))
    : matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ)
    = block_diagonal' (λ i, (x i) ⊗ₖ 1) :=
begin
  ext1 r l,
  simp_rw [module.dual.pi.is_faithful_pos_map.to_matrix_apply', lmul_apply,
    mul_include_block, include_block_apply, mul_apply,
    dite_apply, dite_mul, pi.zero_apply, zero_mul,
    finset.sum_dite_irrel, ← mul_apply, block_diagonal'_apply, kronecker_map, of_apply,
    @eq_comm _ r.fst, one_apply, mul_boole, matrix.cast_mul,
    module.dual.pi.is_faithful_pos_map.basis.apply_cast_eq_mp,
    mul_eq_mul,
    matrix.mul_assoc, module.dual.is_faithful_pos_map.basis_apply, matrix.mul_assoc,
    pos_def.rpow_mul_rpow, neg_add_self, pos_def.rpow_zero, matrix.mul_one,
    mul_apply, std_basis_matrix, mul_boole, ite_and, finset.sum_ite_eq,
    finset.mem_univ, if_true, @eq_comm _ r.snd.snd, finset.sum_const_zero,
    eq_mpr_eq_cast],
  congr' 2,
  ext1 h,
  tidy,
end
lemma pi_rmul_to_matrix
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] (x : 𝔹) :
  (module.dual.pi.is_faithful_pos_map.to_matrix (λ i, (hψ i).elim) (rmul x : l(𝔹))
    : matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ)
    = block_diagonal' (λ i, 1 ⊗ₖ ((hψ i).elim.sig (1/2) (x i))ᵀ) :=
begin
  ext1 r l,
  simp_rw [module.dual.pi.is_faithful_pos_map.to_matrix_apply', rmul_apply,
    include_block_mul, include_block_apply, mul_apply,
    dite_apply, dite_mul, pi.zero_apply, zero_mul,
    finset.sum_dite_irrel, ← mul_apply, block_diagonal'_apply, kronecker_map, of_apply,
    @eq_comm _ r.fst, one_apply, mul_boole, matrix.cast_mul,
    module.dual.pi.is_faithful_pos_map.basis.apply_cast_eq_mp,
    mul_eq_mul,
    matrix.mul_assoc, module.dual.is_faithful_pos_map.basis_apply, matrix.mul_assoc,
    ← matrix.mul_assoc (pos_def.rpow _ _) _ (pos_def.rpow _ (1/2 : ℝ)),
    ← module.dual.is_faithful_pos_map.sig_apply,
    mul_apply, std_basis_matrix, boole_mul, ite_and,
    finset.sum_ite_irrel, finset.sum_const_zero, finset.sum_ite_eq,
    finset.mem_univ, if_true, transpose_apply, finset.sum_const_zero,
    eq_mpr_eq_cast, @eq_comm _ r.snd.1],
  congr' 2,
  ext1 h,
  tidy,
end
lemma schur_idempotent_one_left_rank_one
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (a b : 𝔹) :
  schur_idempotent (1 : l(𝔹)) (|a⟩⟨b|)
    = (rmul a : l(𝔹)) * (rmul b : l(𝔹)).adjoint :=
begin
  simp_rw [← ext_inner_map],
  intros u,
  let f := std_orthonormal_basis ℂ 𝔹,
  rw [← rank_one.sum_orthonormal_basis_eq_id_lm f, map_sum, linear_map.sum_apply],
  simp_rw [schur_idempotent.apply_rank_one, linear_map.sum_apply,
    continuous_linear_map.coe_coe, rank_one_apply,
    linear_map.mul_apply, rmul_apply, sum_inner,
    inner_smul_left,
    module.dual.pi.is_faithful_pos_map.inner_right_conj',
    inner_conj_symm, orthonormal_basis.sum_inner_mul_inner,
    ← module.dual.pi.is_faithful_pos_map.inner_right_conj',
    rmul_adjoint, rmul_apply],
end

lemma linear_map.pi.adjoint_real_eq
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (f : 𝔹 →ₗ[ℂ] 𝔹) :
  (f.adjoint).real
    = (module.dual.pi.is_faithful_pos_map.sig hψ 1).to_linear_map
      ∘ₗ (f.real).adjoint
      ∘ₗ (module.dual.pi.is_faithful_pos_map.sig hψ (-1)).to_linear_map :=
begin
  rw [← ext_inner_map],
  intros u,
  nth_rewrite_lhs 0 pi.inner_symm,
  simp_rw [linear_map.real_eq, star_star, linear_map.adjoint_inner_right],
  nth_rewrite_lhs 0 pi.inner_symm,
  simp_rw [star_star, ← module.dual.pi.is_faithful_pos_map.sig_star,
    ← linear_map.real_eq f, linear_map.comp_apply, ← linear_map.adjoint_inner_left (f.real),
    ← alg_equiv.to_linear_map_apply, ← linear_map.adjoint_inner_left
      (module.dual.pi.is_faithful_pos_map.sig hψ 1).to_linear_map,
    module.dual.pi.is_faithful_pos_map.sig_adjoint],
end

-- open tensor_product

-- noncomputable def pi.qam.symm
--   {B : Type*}
--   [normed_ring B]
--   [inner_product_space ℂ B]
--   [algebra ℂ B]
--   [smul_comm_class ℂ B B]
--   [is_scalar_tower ℂ B B]
--   [finite_dimensional ℂ B] :
--   --(h℘ : Π i, (℘ i).is_faithful_pos_map) :
--   l(l(B)) :=
-- begin
--   -- letI := λ i, fact.mk (h℘ i),
--   exact { to_fun := λ x,
--     (τ B) ∘ₗ (B ϰ ℂ) ∘ₗ ((id B) ⊗ₘ ((algebra.linear_map ℂ B).adjoint ∘ₗ (m B)))
--       ∘ₗ (υ B) ∘ₗ ((id B ⊗ₘ x) ⊗ₘ id B)
--       ∘ₗ (((m B).adjoint ∘ₗ (algebra.linear_map ℂ B).adjoint) ⊗ₘ id B) ∘ₗ (τ⁻¹ B),
--     map_add' := λ x y, by {
--       simp only [tensor_product.map_add, tensor_product.add_map, linear_map.add_comp,
--         linear_map.comp_add], },
--     map_smul' := λ r x, by {
--       simp only [tensor_product.map_smul, tensor_product.smul_map, linear_map.smul_comp,
--         linear_map.comp_smul, ring_hom.id_apply], } },
-- end

-- lemma pi.qam.rank_one.symmetric_eq [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (a b : 𝔹) :
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

-- noncomputable def pi.qam.symm' (h℘ : Π i, (℘ i).is_faithful_pos_map) :
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

-- lemma pi.qam.rank_one.symmetric'_eq [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (a b : 𝔹) :
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

-- lemma pi.qam.symm_adjoint_eq_symm'_of_adjoint [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (x : l(𝔹)) :
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
-- commute_star_star
-- private lemma commute.adjoint_adjoint_lm {K E : Type*} [is_R_or_C K] [normed_add_comm_group E]
--   [inner_product_space K E] [finite_dimensional K E] {f g : E →ₗ[K] E} :
--   commute f.adjoint g.adjoint ↔ commute f g :=
-- commute_star_star

-- @[instance] def B.star_module :
--   star_module ℂ 𝔹 :=
-- by {
--   apply @pi.star_module _ _ ℂ _ _ _ _,
--   exact λ i, matrix.star_module,
-- }

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

-- lemma linear_map.is_faithful_pos_map.direct_sum.sig_comp_sig
--   [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (x y : ℝ) :
--   (linear_map.is_faithful_pos_map.direct_sum.sig h℘ x).to_linear_map
--     .comp (linear_map.is_faithful_pos_map.direct_sum.sig h℘ y).to_linear_map
--   = (linear_map.is_faithful_pos_map.direct_sum.sig h℘ (x + y)).to_linear_map :=
-- by ext1; simp_rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, linear_map.is_faithful_pos_map.direct_sum.sig_apply_sig]

-- lemma linear_map.is_faithful_pos_map.direct_sum.sig_zero'
--   [h℘ : Π i, fact (℘ i).is_faithful_pos_map] :
--   linear_map.is_faithful_pos_map.direct_sum.sig h℘ 0 = 1 :=
-- begin
--   rw alg_equiv.ext_iff,
--   intros,
--   rw [linear_map.is_faithful_pos_map.direct_sum.sig_zero],
--   refl,
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

-- lemma linear_map.direct_sum.is_real.adjoint_is_real_iff_commute_with_sig
--   [h℘ : Π i, fact (℘ i).is_faithful_pos_map] {f : 𝔹 →ₗ[ℂ] 𝔹} (hf : f.is_real) :
--   (f.adjoint).is_real ↔
--   commute f (linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map :=
-- begin
--   rw linear_map.is_real_iff at hf,
--   have : commute f (linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map
--     ↔ commute (f.adjoint) (linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map,
--   { simp_rw [linear_map.is_faithful_pos_map.direct_sum.sig h℘],
--     nth_rewrite_rhs 0 ← linear_map.is_faithful_pos_map.direct_sum.sig_adjoint,
--     rw commute.adjoint_adjoint_lm, },
--   rw this,
--   clear this,
--   rw [linear_map.is_real_iff, linear_map.direct_sum.adjoint_real_eq, hf, ← linear_map.comp_assoc,
--     direct_sum.comp_sig_eq, neg_neg],
--   simp_rw [commute, semiconj_by, linear_map.mul_eq_comp, @eq_comm _ _ ((linear_map.is_faithful_pos_map.direct_sum.sig h℘ 1).to_linear_map ∘ₗ _)],
-- end

-- lemma direct_sum.sig_apply_pos_def_matrix [h℘ : Π i, fact (℘ i).is_faithful_pos_map]
--   (t s : ℝ) :
--   (linear_map.is_faithful_pos_map.direct_sum.sig h℘) t (pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘) s)
--   = pi.pos_def.rpow (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘) s :=
-- begin
--   simp_rw [linear_map.is_faithful_pos_map.direct_sum.sig_apply h℘, pi.pos_def.rpow_mul_rpow,
--     neg_add_cancel_comm],
-- end

-- -- lemma direct_sum.sig_apply_pos_def_matrix' [h℘ : Π i, fact (℘ i).is_faithful_pos_map] (t : ℝ) :
-- --   (linear_map.is_faithful_pos_map.direct_sum.sig h℘) t (linear_map.direct_sum_matrix_block ℘) = linear_map.direct_sum_matrix_block ℘ :=
-- -- begin
-- --   have : linear_map.direct_sum_matrix_block ℘ = λ i, (℘ i).matrix :=
-- --   by { ext1 i, simp only [linear_map.direct_sum_matrix_block_apply], },
-- --   rw [this],
-- --   nth_rewrite_rhs 0 [← pi.pos_def.rpow_one_eq_self (linear_map.is_faithful_pos_map.direct_sum.matrix_is_pos_def h℘)],
-- --   rw [← direct_sum.sig_apply_pos_def_matrix t (1 : ℝ)],
-- --   rw [← this],
-- -- end

