import linear_algebra.is_real
import linear_algebra.my_ips.nontracial

@[simps] noncomputable def linear_equiv.symm_map
  (R : Type*) [is_R_or_C R] (M : Type*)
  [normed_add_comm_group M] [inner_product_space R M]
  [star_add_monoid M] [star_module R M]
  [finite_dimensional R M] :
  (M →ₗ[R] M) ≃ₗ[R] (M →ₗ[R] M) :=
{ to_fun := λ f, (linear_map.real f).adjoint,
  inv_fun := λ f, (linear_map.adjoint f).real,
  left_inv := λ f, by { simp only [linear_map.adjoint_adjoint, linear_map.real_real], },
  right_inv := λ f, by { simp only [linear_map.real_real, linear_map.adjoint_adjoint], },
  map_add' := λ f g, by { simp only [linear_map.real_add, map_add], },
  map_smul' := λ c f, by { simp only [linear_map.real_smul, linear_map.adjoint_smul,
    star_ring_end_self_apply, ring_hom.id_apply], } }

lemma linear_equiv.symm_map_real
  {R : Type*} [is_R_or_C R] {M : Type*}
  [normed_add_comm_group M] [inner_product_space R M]
  [star_add_monoid M] [star_module R M]
  [finite_dimensional R M] :
  linear_map.real (linear_equiv.symm_map R M : (M →ₗ[R] M) →ₗ[R] (M →ₗ[R] M))
    = (linear_equiv.symm_map R M).symm :=
begin
  ext1 f,
  simp_rw [linear_map.real_eq, linear_equiv.coe_coe, linear_map.star_eq_adjoint,
    linear_equiv.symm_map_apply, linear_map.adjoint_adjoint],
  refl,
end

open_locale tensor_product kronecker matrix functional

variables {n : Type*} [fintype n] [decidable_eq n]
  {s : n → Type*} [Π i, fintype (s i)] [Π i, decidable_eq (s i)]
  {ψ : Π i, module.dual ℂ (matrix (s i) (s i) ℂ)}
local notation `𝔹` := Π i, matrix (s i) (s i) ℂ

local notation `|` x `⟩⟨` y `|` := (@rank_one ℂ _ _ _ _ x y)
local notation `m` x := linear_map.mul' ℂ x
local notation `η` x := algebra.linear_map ℂ x
local notation x ` ⊗ₘ ` y := tensor_product.map x y
local notation `υ` B :=
  ((tensor_product.assoc ℂ B B B) : (B ⊗[ℂ] B ⊗[ℂ] B) →ₗ[ℂ] B ⊗[ℂ] (B ⊗[ℂ] B))
local notation `υ⁻¹` B :=
  ((tensor_product.assoc ℂ B B B).symm : B ⊗[ℂ] (B ⊗[ℂ] B) →ₗ[ℂ] (B ⊗[ℂ] B ⊗[ℂ] B))
local notation x`ϰ`y := (↑(tensor_product.comm ℂ x y) : (x ⊗[ℂ] y) →ₗ[ℂ] (y ⊗[ℂ] x))
local notation x`ϰ⁻¹`y := ((tensor_product.comm ℂ x y).symm : (y ⊗[ℂ] x) →ₗ[ℂ] (x ⊗[ℂ] y))
local notation `τ` x  := ((tensor_product.lid ℂ x) : (ℂ ⊗[ℂ] x) →ₗ[ℂ] x)
local notation `τ⁻¹` x := ((tensor_product.lid ℂ x).symm : x →ₗ[ℂ] (ℂ ⊗[ℂ] x))
local notation `id` x := (1 : x →ₗ[ℂ] x)

lemma linear_equiv.symm_map_rank_one_apply [hψ : Π i, fact (ψ i).is_faithful_pos_map] (a b : 𝔹) :
  linear_equiv.symm_map _ _ (|a⟩⟨b| : 𝔹 →ₗ[ℂ] 𝔹)
    = |(module.dual.pi.is_faithful_pos_map.sig hψ (-1) (star b))⟩⟨(star a)| :=
begin
  rw [linear_equiv.symm_map_apply, ← rank_one_lm_eq_rank_one, pi.rank_one_lm_real_apply,
    rank_one_lm_adjoint],
  refl,
end
lemma linear_equiv.symm_map_symm_rank_one_apply [hψ : Π i, fact (ψ i).is_faithful_pos_map] (a b : 𝔹) :
  (linear_equiv.symm_map _ _).symm (|a⟩⟨b| : 𝔹 →ₗ[ℂ] 𝔹)
    = |(star b)⟩⟨module.dual.pi.is_faithful_pos_map.sig hψ (-1) (star a)| :=
begin
  rw [linear_equiv.symm_map_symm_apply, ← rank_one_lm_eq_rank_one,
    rank_one_lm_adjoint, pi.rank_one_lm_real_apply],
  refl,
end

open_locale big_operators
open tensor_product

lemma pi.symm_map_eq
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (f : (Π i, matrix (s i) (s i) ℂ) →ₗ[ℂ] (Π i, matrix (s i) (s i) ℂ)) :
  (linear_equiv.symm_map ℂ (Π i, matrix (s i) (s i) ℂ)) f
    =
  (τ 𝔹) ∘ₗ (𝔹 ϰ ℂ) ∘ₗ ((id 𝔹) ⊗ₘ ((algebra.linear_map ℂ 𝔹).adjoint ∘ₗ (m 𝔹)))
      ∘ₗ (υ 𝔹) ∘ₗ ((id 𝔹 ⊗ₘ f) ⊗ₘ id 𝔹)
      ∘ₗ (((m 𝔹).adjoint ∘ₗ (algebra.linear_map ℂ 𝔹)) ⊗ₘ id 𝔹) ∘ₗ (τ⁻¹ 𝔹) :=
begin
  obtain ⟨a, b, rfl⟩ := f.exists_sum_rank_one,
  simp only [map_sum, linear_map.sum_comp, linear_map.comp_sum,
    tensor_product.sum_map, tensor_product.map_sum],
  apply finset.sum_congr rfl,
  intros x hx,
  rw [linear_equiv.symm_map_rank_one_apply, eq_comm, linear_map.ext_iff_inner_map],
  intros a_1,
  obtain ⟨α, β, this⟩ := tensor_product.eq_span ((linear_map.mul' ℂ 𝔹).adjoint (1 : 𝔹)),
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, lid_symm_apply,
    map_tmul, linear_map.comp_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, one_smul],
  rw [← this],
  simp_rw [_root_.map_sum, map_tmul, linear_map.one_apply, sum_tmul, _root_.map_sum, assoc_tmul,
    map_tmul, comm_tmul, lid_tmul, sum_inner, linear_map.comp_apply,
    continuous_linear_map.coe_coe, rank_one_apply, ← smul_tmul', smul_hom_class.map_smul,
    linear_map.one_apply, nontracial.pi.unit_adjoint_eq, smul_eq_mul,
    linear_map.mul'_apply],
  calc ∑ x_1,
    ⟪(⟪(b x), (β x_1)⟫_ℂ * ((module.dual.pi ψ) (a x * a_1 : 𝔹))) • α x_1, a_1⟫_ℂ
    = star_ring_end ℂ ((module.dual.pi ψ) (a x * a_1 : 𝔹))
      * ∑ x_1, ⟪α x_1, a_1⟫_ℂ * ⟪β x_1, b x⟫_ℂ :
  by { simp_rw [inner_smul_left, _root_.map_mul, inner_conj_symm, mul_comm,
      finset.mul_sum, mul_rotate'], }
  ... = star_ring_end ℂ (module.dual.pi ψ (a x * a_1))
    * ⟪∑ x_1, α x_1 ⊗ₜ[ℂ] β x_1, a_1 ⊗ₜ[ℂ] b x⟫_ℂ :
  by { simp_rw [← inner_tmul, ← sum_inner], }
  ... = star_ring_end ℂ (module.dual.pi ψ (a x * a_1))
    * ⟪1, a_1 * b x⟫_ℂ :
  by { simp_rw [this, linear_map.adjoint_inner_left, linear_map.mul'_apply], }
  ... = ⟪⟪star (a x), a_1⟫_ℂ
    • module.dual.pi.is_faithful_pos_map.sig hψ (-1) (star (b x)), a_1⟫_ℂ :
  by { simp_rw [module.dual.pi.is_faithful_pos_map.inner_left_conj', one_mul,
    module.dual.pi.is_faithful_pos_map.inner_eq, star_smul,
    smul_mul_assoc, smul_hom_class.map_smul, star_star, star_ring_end_apply, smul_eq_mul], },
end

lemma pi.symm_map_symm_eq
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (f : (Π i, matrix (s i) (s i) ℂ) →ₗ[ℂ] (Π i, matrix (s i) (s i) ℂ)) :
  (linear_equiv.symm_map ℂ _).symm f =
    (τ 𝔹) ∘ₗ (((η 𝔹).adjoint ∘ₗ m 𝔹) ⊗ₘ id 𝔹) ∘ₗ ((id 𝔹 ⊗ₘ f) ⊗ₘ id 𝔹) ∘ₗ (υ⁻¹ 𝔹)
      ∘ₗ (id 𝔹 ⊗ₘ ((m 𝔹).adjoint ∘ₗ η 𝔹)) ∘ₗ (𝔹 ϰ⁻¹ ℂ) ∘ₗ (τ⁻¹ 𝔹) :=
begin
  symmetry,
  obtain ⟨a, b, rfl⟩ := f.exists_sum_rank_one,
  simp only [map_sum, linear_map.sum_comp, linear_map.comp_sum,
    tensor_product.sum_map, tensor_product.map_sum],
  apply finset.sum_congr rfl,
  intros p hp,
  rw [linear_equiv.symm_map_symm_rank_one_apply, linear_map.ext_iff_inner_map],
  intros x,
  obtain ⟨α, β, this⟩ := tensor_product.eq_span ((linear_map.mul' ℂ 𝔹).adjoint (1 : 𝔹)),
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, lid_symm_apply, comm_symm_tmul,
    map_tmul, linear_map.comp_apply, algebra.linear_map_apply, algebra.algebra_map_eq_smul_one, one_smul],
  rw ← this,
  simp_rw [tmul_sum, _root_.map_sum, assoc_symm_tmul, map_tmul,
    linear_map.one_apply, lid_tmul, sum_inner, linear_map.comp_apply,
    continuous_linear_map.coe_coe, rank_one_apply, ← smul_tmul, ← smul_tmul',
    smul_hom_class.map_smul,
    nontracial.pi.unit_adjoint_eq, smul_eq_mul, linear_map.mul'_apply],
  calc ∑ x_1, inner ((inner (b p) (α x_1) * (module.dual.pi ψ) (x * (a p))) • β x_1) x
    = star_ring_end ℂ ((module.dual.pi ψ) (x * (a p)))
      * ∑ x_1, inner (α x_1) (b p) * inner (β x_1) x :
  by { simp only [inner_smul_left, _root_.map_mul, inner_conj_symm, finset.mul_sum],
    simp_rw [mul_assoc, mul_rotate', mul_comm],
    simp_rw [← mul_assoc, mul_comm], }
  ... = star_ring_end ℂ ((module.dual.pi ψ) (x * a p))
    * inner (∑ x_1, α x_1 ⊗ₜ[ℂ] β x_1) (b p ⊗ₜ[ℂ] x) :
  by { simp_rw [← inner_tmul, ← sum_inner], }
  ... = star_ring_end ℂ ((module.dual.pi ψ) (x * a p))
    * inner 1 (b p * x) : by simp_rw [this, linear_map.adjoint_inner_left, linear_map.mul'_apply]
  ... = star_ring_end ℂ ((module.dual.pi ψ) (x * a p)) * inner (star (b p)) x :
  by { rw [module.dual.pi.is_faithful_pos_map.inner_right_mul, mul_one], }
  ... = star_ring_end ℂ (inner (star x) (a p)) * inner (star (b p)) x :
  by { rw [module.dual.pi.is_faithful_pos_map.inner_eq (star x) (a p), star_star], }
  ... = star_ring_end ℂ (inner (module.dual.pi.is_faithful_pos_map.sig hψ (-1) (star (a p))) x) * inner (star (b p)) x :
  by { rw [pi.inner_symm, star_star], }
  ... = inner (inner (module.dual.pi.is_faithful_pos_map.sig hψ (-1) (star (a p))) x • (star (b p))) x :
  by { rw [inner_smul_left], },
end

lemma pi.symm_map_tfae
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (A : 𝔹 →ₗ[ℂ] 𝔹) :
  tfae [linear_equiv.symm_map _ _ A = A,
    (linear_equiv.symm_map _ _).symm A = A,
    A.real = A.adjoint,
    ∀ x y, module.dual.pi ψ ((A x) * y) = module.dual.pi ψ (x * (A y))] :=
begin
  tfae_have : 1 ↔ 2,
  { rw [← linear_equiv.eq_symm_apply, eq_comm], },
  tfae_have : 2 ↔ 3,
  { rw [linear_equiv.symm_map_symm_apply, linear_map.real_inj_eq,
      linear_map.real_real, eq_comm], },
  tfae_have : 3 → 4,
  { intros h x y,
    calc module.dual.pi ψ (A x * y) = ⟪star (A x), y⟫_ℂ :
    by { rw [module.dual.pi.is_faithful_pos_map.inner_eq, star_star], }
    ... = ⟪A.real (star x), y⟫_ℂ :
    by { simp_rw [linear_map.real_eq, star_star], }
    ... = ⟪A.adjoint (star x), y⟫_ℂ : by rw h
    ... = ⟪star x, A y⟫_ℂ : by rw linear_map.adjoint_inner_left
    ... = module.dual.pi ψ (x * A y) :
    by { rw [module.dual.pi.is_faithful_pos_map.inner_eq, star_star], }, },
  tfae_have : 4 → 3,
  { intros h,
    rw linear_map.ext_iff_inner_map,
    intros u,
    rw [linear_map.adjoint_inner_left],
    nth_rewrite_rhs 0 [module.dual.pi.is_faithful_pos_map.inner_eq],
    rw [← h, linear_map.real_eq, module.dual.pi.is_faithful_pos_map.inner_eq, star_star], },
  tfae_finish,
end

lemma commute_real_real {R A : Type*} [semiring R] [star_ring R]
  [add_comm_monoid A] [module R A] [star_add_monoid A] [star_module R A]
  (f g : A →ₗ[R] A) :
  commute (f.real : A →ₗ[R] A) (g.real : A →ₗ[R] A) ↔ commute f g :=
begin
  simp_rw [commute, semiconj_by, linear_map.mul_eq_comp,
    ← linear_map.real_comp, ← linear_map.real_inj_eq],
end

lemma module.dual.pi.is_faithful_pos_map.sig_real [hψ : Π i, fact (ψ i).is_faithful_pos_map] :
  (module.dual.pi.is_faithful_pos_map.sig hψ 1).to_linear_map.real
  = (module.dual.pi.is_faithful_pos_map.sig hψ (-1)).to_linear_map :=
begin
  ext1,
  simp only [linear_map.real_eq, alg_equiv.to_linear_map_apply,
    module.dual.pi.is_faithful_pos_map.sig_star, star_star],
end

lemma pi.commute_sig_pos_neg [hψ : Π i, fact (ψ i).is_faithful_pos_map] (r : ℝ)
  (x : 𝔹 →ₗ[ℂ] 𝔹) :
  commute x (module.dual.pi.is_faithful_pos_map.sig hψ (r)).to_linear_map
  ↔ commute x (module.dual.pi.is_faithful_pos_map.sig hψ (-r)).to_linear_map :=
begin
  simp_rw [commute, semiconj_by, linear_map.mul_eq_comp],
  rw [pi.comp_sig_eq_iff],
  nth_rewrite_rhs 0 [← pi.sig_comp_eq_iff r],
  rw [eq_comm],
  simp_rw [linear_map.comp_assoc],
end

lemma pi.symm_map_apply_eq_symm_map_symm_apply_iff
  [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (A : 𝔹 →ₗ[ℂ] 𝔹) :
  linear_equiv.symm_map ℂ (Π i, matrix (s i) (s i) ℂ) A
    = (linear_equiv.symm_map ℂ _).symm A ↔
  commute A (module.dual.pi.is_faithful_pos_map.sig hψ 1).to_linear_map :=
begin
  rw [linear_equiv.symm_map_apply, linear_equiv.symm_map_symm_apply, linear_map.pi.adjoint_real_eq,
    ← commute_real_real, ← commute_star_star],
  simp_rw [linear_map.star_eq_adjoint, module.dual.pi.is_faithful_pos_map.sig_real,
    module.dual.pi.is_faithful_pos_map.sig_adjoint, ← pi.commute_sig_pos_neg 1],
  simp_rw [commute, semiconj_by, linear_map.mul_eq_comp,
    pi.comp_sig_eq_iff, linear_map.comp_assoc],
end

lemma Psi.real_apply [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (r₁ r₂ : ℝ) (A : 𝔹 →ₗ[ℂ] 𝔹) :
  module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ A.real
  = ((module.dual.pi.is_faithful_pos_map.sig hψ (2 * r₁)).to_linear_map
    ⊗ₘ (op ∘ₗ (module.dual.pi.is_faithful_pos_map.sig hψ (1 - 2 * r₂)).to_linear_map) ∘ₗ unop)
    (star (module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ A)) :=
begin
  suffices : ∀ a b : 𝔹,
    module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (linear_map.real (|a⟩⟨b|))
  = ((module.dual.pi.is_faithful_pos_map.sig hψ (2 * r₁)).to_linear_map
    ⊗ₘ (op ∘ₗ (module.dual.pi.is_faithful_pos_map.sig hψ (1 - 2 * r₂)).to_linear_map) ∘ₗ unop)
    (star (module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (|a⟩⟨b|))),
  { obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one,
    letI this11 : star_add_monoid 𝔹ᵐᵒᵖ := by apply_instance,
    letI this12 : star_module ℂ 𝔹ᵐᵒᵖ := by apply_instance,
    letI this1 : star_add_monoid (𝔹 ⊗[ℂ] 𝔹ᵐᵒᵖ),
    { apply_instance, },
    simp only [map_sum, linear_map.real_sum, star_sum, this], },
  intros a b,
  simp_rw [← rank_one_lm_eq_rank_one, pi.rank_one_lm_real_apply,
    rank_one_lm_eq_rank_one, module.dual.pi.is_faithful_pos_map.Psi_apply,
    module.dual.pi.is_faithful_pos_map.Psi_to_fun'_apply,
    star_tmul, map_tmul, linear_map.comp_apply,
    alg_equiv.to_linear_map_apply, unop_apply, op_apply,
    ← mul_opposite.op_star, mul_opposite.unop_op, star_star,
    module.dual.pi.is_faithful_pos_map.sig_star,
    module.dual.pi.is_faithful_pos_map.sig_apply_sig,
    star_star, two_mul, neg_neg, sub_eq_add_neg, add_assoc,
    neg_add, add_neg_cancel_comm_assoc, neg_add_cancel_comm, add_comm],
end

lemma Psi.adjoint_apply [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (r₁ r₂ : ℝ) (A : 𝔹 →ₗ[ℂ] 𝔹) :
  module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ A.adjoint
  = ((module.dual.pi.is_faithful_pos_map.sig hψ (r₁ - r₂)).to_linear_map
    ⊗ₘ (op ∘ₗ (module.dual.pi.is_faithful_pos_map.sig hψ (r₁ - r₂)).to_linear_map ∘ₗ unop))
    (ten_swap (star
      (module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ A))) :=
begin
  suffices : ∀ a b : 𝔹,
    module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (linear_map.adjoint ↑(|a⟩⟨b|)) =
    ((module.dual.pi.is_faithful_pos_map.sig hψ (r₁ - r₂)).to_linear_map
      ⊗ₘ (op ∘ₗ (module.dual.pi.is_faithful_pos_map.sig hψ (r₁ - r₂)).to_linear_map ∘ₗ unop))
      (ten_swap (star
        (module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (|a⟩⟨b|)))),
  { obtain ⟨α, β, rfl⟩ := A.exists_sum_rank_one,
    letI this11 : star_add_monoid 𝔹ᵐᵒᵖ := by apply_instance,
    letI this12 : star_module ℂ 𝔹ᵐᵒᵖ := by apply_instance,
    letI this1 : star_add_monoid (𝔹 ⊗[ℂ] 𝔹ᵐᵒᵖ),
    { apply_instance, },
    simp only [map_sum, star_sum, this], },
  intros a b,
  simp_rw [← rank_one_lm_eq_rank_one, rank_one_lm_adjoint,
    rank_one_lm_eq_rank_one,
    module.dual.pi.is_faithful_pos_map.Psi_apply,
    module.dual.pi.is_faithful_pos_map.Psi_to_fun'_apply,
    star_tmul, op_apply, ← mul_opposite.op_star, ten_swap_apply',
    star_star, map_tmul, linear_map.comp_apply, alg_equiv.to_linear_map_apply, unop_apply,
    mul_opposite.unop_op, module.dual.pi.is_faithful_pos_map.sig_star,
    module.dual.pi.is_faithful_pos_map.sig_apply_sig, op_apply,
    sub_eq_add_neg, add_assoc, add_neg_cancel_comm_assoc, neg_add_self, add_zero],
end

lemma Psi.symm_map_apply [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (r₁ r₂ : ℝ) (A : 𝔹 →ₗ[ℂ] 𝔹) :
  module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ (linear_equiv.symm_map _ _ A)
  = ((module.dual.pi.is_faithful_pos_map.sig hψ (r₁ + r₂ - 1)).to_linear_map
    ⊗ₘ (op ∘ₗ (module.dual.pi.is_faithful_pos_map.sig hψ (-r₁ - r₂)).to_linear_map ∘ₗ unop))
  (ten_swap ((module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ A))) :=
begin
  simp_rw [← linear_equiv.coe_coe, ← linear_map.comp_apply],
  revert A,
  simp_rw [← linear_map.ext_iff],
  apply linear_map.ext_of_rank_one',
  intros a b,
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, linear_equiv.symm_map_rank_one_apply,
    module.dual.pi.is_faithful_pos_map.Psi_apply,
    module.dual.pi.is_faithful_pos_map.Psi_to_fun'_apply, op_apply, ten_swap_apply',
    map_tmul, linear_map.comp_apply, alg_equiv.to_linear_map_apply, unop_apply,
    mul_opposite.unop_op, module.dual.pi.is_faithful_pos_map.sig_star,
    module.dual.pi.is_faithful_pos_map.sig_apply_sig, star_star, op_apply,
    sub_eq_add_neg, neg_add_cancel_comm, add_assoc, add_neg_cancel_comm_assoc],
end

lemma Psi.symm_map_symm_apply [hψ : Π i, fact (ψ i).is_faithful_pos_map]
  (r₁ r₂ : ℝ) (A : 𝔹 →ₗ[ℂ] 𝔹) :
  module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ ((linear_equiv.symm_map _ _).symm A)
  = ((module.dual.pi.is_faithful_pos_map.sig hψ (r₁ + r₂)).to_linear_map
    ⊗ₘ (op ∘ₗ (module.dual.pi.is_faithful_pos_map.sig hψ (1 - r₁ - r₂)).to_linear_map ∘ₗ unop))
  (ten_swap ((module.dual.pi.is_faithful_pos_map.Psi hψ r₁ r₂ A))) :=
begin
  simp_rw [← linear_equiv.coe_coe, ← linear_map.comp_apply],
  revert A,
  simp_rw [← linear_map.ext_iff],
  apply linear_map.ext_of_rank_one',
  intros a b,
  simp_rw [linear_map.comp_apply, linear_equiv.coe_coe, linear_equiv.symm_map_symm_rank_one_apply,
    module.dual.pi.is_faithful_pos_map.Psi_apply,
    module.dual.pi.is_faithful_pos_map.Psi_to_fun'_apply, op_apply, ten_swap_apply',
    map_tmul, linear_map.comp_apply, alg_equiv.to_linear_map_apply, unop_apply,
    mul_opposite.unop_op, module.dual.pi.is_faithful_pos_map.sig_star,
    module.dual.pi.is_faithful_pos_map.sig_apply_sig, star_star, op_apply,
    sub_eq_add_neg, add_assoc, neg_add_cancel_comm_assoc, add_neg_self, add_zero, neg_neg,
    add_comm],
end
