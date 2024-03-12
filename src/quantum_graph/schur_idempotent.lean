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
import linear_algebra.my_ips.quantum_set

/-!
 # Schur idempotent operator

 In this file we define the Schur idempotent operator and prove some basic properties.
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
example {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map] (x : 𝔹) :
  (module.dual.pi.is_faithful_pos_map.to_matrix (λ i, (hψ i).elim) (lmul x : l(𝔹))
    : matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ)
  = block_diagonal' (λ i, (hψ i).elim.to_matrix (lmul (x i))) :=
begin
  simp_rw [pi_lmul_to_matrix, lmul_eq_mul, linear_map.mul_left_to_matrix],
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
lemma unitary.coe_pi (U : Π i, unitary_group (s i) ℂ) :
  (unitary.pi U : Π i, matrix (s i) (s i) ℂ) = ↑U :=
rfl
lemma unitary.coe_pi_apply (U : Π i, unitary_group (s i) ℂ) (i : n) :
  (↑U : Π i, matrix (s i) (s i) ℂ) i = U i :=
rfl

lemma pi_inner_aut_to_matrix
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (U : Π i, unitary_group (s i) ℂ) :
  (module.dual.pi.is_faithful_pos_map.to_matrix (λ i, (hψ i).elim) ((unitary.inner_aut_star_alg ℂ (unitary.pi U)).to_alg_equiv.to_linear_map : l(𝔹))
    : matrix (Σ i, s i × s i) (Σ i, s i × s i) ℂ)
  =
  block_diagonal' (λ i,
    (U i) ⊗ₖ ((hψ i).elim.sig (- (1/2 : ℝ)) ((U i) : matrix (s i) (s i) ℂ))ᴴᵀ) :=
begin
  have : ((unitary.inner_aut_star_alg ℂ (unitary.pi U)).to_alg_equiv.to_linear_map : l(𝔹))
    =
  (lmul ↑U : l(𝔹)) * (rmul (star ↑U) : l(𝔹)),
  { ext1,
    simp_rw [alg_equiv.to_linear_map_apply, star_alg_equiv.coe_to_alg_equiv,
      linear_map.mul_apply, lmul_apply, rmul_apply, unitary.inner_aut_star_alg_apply,
      mul_assoc, unitary.coe_star, unitary.coe_pi], },
  rw [this, _root_.map_mul, pi_lmul_to_matrix, pi_rmul_to_matrix,
    mul_eq_mul, ← block_diagonal'_mul],
  simp_rw [← mul_kronecker_mul, matrix.mul_one, matrix.one_mul,
    pi.star_apply, star_eq_conj_transpose, block_diagonal'_inj, unitary.coe_pi_apply],
  ext1 i,
  nth_rewrite 0 [← neg_neg (1 / 2 : ℝ)],
  simp_rw [← module.dual.is_faithful_pos_map.sig_conj_transpose],
  refl,
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

lemma Psi.symm_map
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (r₁ r₂ : ℝ)
  (f g : (Π i, matrix (s i) (s i) ℂ) →ₗ[ℂ] (Π i, matrix (s i) (s i) ℂ)) :
  module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (schur_idempotent f g)
  = 
  (module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ f)
  * (module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ g) :=
begin
  suffices : ∀ a b c d : 𝔹,
    module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (schur_idempotent (↑(|a⟩⟨b|) : l(𝔹)) (|c⟩⟨d|))
  = 
  (module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (|a⟩⟨b|))
  * (module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (|c⟩⟨d|)),
  { obtain ⟨α, β, rfl⟩ := f.exists_sum_rank_one,
    obtain ⟨γ, δ, rfl⟩ := g.exists_sum_rank_one,
    simp_rw [map_sum, linear_map.sum_apply, finset.mul_sum, finset.sum_mul, map_sum, this], },
  intros a b c d,
  simp_rw [module.dual.pi.is_faithful_pos_map.Psi_apply, schur_idempotent.apply_rank_one,
    module.dual.pi.is_faithful_pos_map.Psi_to_fun'_apply,
    algebra.tensor_product.tmul_mul_tmul, op_apply, ← mul_opposite.op_mul,
    ← star_semigroup.star_mul, ← _root_.map_mul],
end


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

