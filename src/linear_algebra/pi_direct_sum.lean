/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.direct_sum.basic
import linear_algebra.my_tensor_product
import linear_algebra.direct_sum_from_to

open_locale tensor_product

local notation x ` ⊗ₘ ` y := tensor_product.map x y

lemma direct_sum.tensor_coe_zero {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*}
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] :
  ⇑(0 : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) = 0 :=
rfl
lemma direct_sum.tensor_coe_add {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*}
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)]
  (x y : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) :
  ⇑(x + y : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) = x + y :=
rfl
lemma direct_sum.tensor_coe_smul {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*}
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)]
  (x : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) (r : R) :
  ⇑(r • x : direct_sum (ι₁ × ι₂) (λ (i : ι₁ × ι₂), M₁ i.fst ⊗[R] M₂ i.snd)) = r • x :=
rfl

def pi.tensor_of {R : Type*} [comm_semiring R] {ι₁ ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (i : ι₁ × ι₂) :
  M₁ i.fst ⊗[R] M₂ i.snd →ₗ[R] (Π j, M₁ j) ⊗[R] (Π j, M₂ j) :=
(@linear_map.single R ι₁ _ M₁ _ _ _ i.fst ⊗ₘ @linear_map.single R ι₂ _ M₂ _ _ _ i.snd)

def pi.tensor_proj {R : Type*} [comm_semiring R] {ι₁ ι₂ : Type*}
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (i : ι₁ × ι₂) :
  (Π j, M₁ j) ⊗[R] (Π j, M₂ j) →ₗ[R] M₁ i.fst ⊗[R] M₂ i.snd :=
(@linear_map.proj R ι₁ _ M₁ _ _ i.fst ⊗ₘ @linear_map.proj R ι₂ _ M₂ _ _ i.snd)

def direct_sum_tensor_to_fun
  {R : Type*} [comm_semiring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] :
  (Π i, M₁ i) ⊗[R] (Π i, M₂ i) →ₗ[R] Π i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd :=
{ to_fun :=  λ x i, (pi.tensor_proj i x),
  map_add' := λ x y,
    by { simp only [map_add, direct_sum.tensor_coe_add],
      refl, },
  map_smul' := λ r x,
    by { simp only [smul_hom_class.map_smul, direct_sum.tensor_coe_smul, ring_hom.id_apply],
      refl, } }

lemma direct_sum_tensor_to_fun_apply
  {R : Type*} [comm_semiring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (x : Π i, M₁ i) (y : Π i, M₂ i) (i : ι₁ × ι₂) :
  direct_sum_tensor_to_fun (x ⊗ₜ[R] y) i = x i.1 ⊗ₜ[R] y i.2 :=
rfl

open_locale big_operators

def direct_sum_tensor_inv_fun {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] :
  (Π i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd) →ₗ[R] ((Π i, M₁ i) ⊗[R] (Π i, M₂ i)) :=
{ to_fun :=  λ x, (∑ i : ι₁ × ι₂, pi.tensor_of i (x i)),
  map_add' := λ x y, by { simp only [map_add, pi.add_apply, finset.sum_add_distrib], },
  map_smul' := λ r x, by { simp only [smul_hom_class.map_smul, pi.smul_apply, ring_hom.id_apply],
    rw [← finset.smul_sum], } }

lemma function.sum_update_eq_self {R : Type*} [semiring R] {ι₁ : Type*} [decidable_eq ι₁]
  [fintype ι₁]
  {M₁ : ι₁ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)] (x : Π i, M₁ i) :
  ∑ (x_1 : ι₁), function.update 0 x_1 (x x_1) = x :=
begin
  ext,
  simp only [finset.sum_apply, function.update, finset.sum_dite_eq, finset.mem_univ, if_true,
    pi.zero_apply],
end

lemma direct_sum_tensor_inv_fun_apply_to_fun
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (x : (Π i, M₁ i) ⊗[R] Π i, M₂ i) :
  direct_sum_tensor_inv_fun (direct_sum_tensor_to_fun x) = x :=
begin
  apply x.induction_on,
  { simp only [map_zero], },
  { intros x y,
    simp only [direct_sum_tensor_inv_fun, linear_map.coe_mk, linear_map.comp_apply,
      direct_sum_tensor_to_fun_apply],
    calc ∑ (i : ι₁ × ι₂), (pi.tensor_of i) (x i.fst ⊗ₜ[R] y i.snd)
      = ∑ (i : ι₁) (j : ι₂), (pi.tensor_of (i,j)) (x i ⊗ₜ[R] y j) :
    by { rw ← finset.sum_product',
      simp only [finset.univ_product_univ],
      apply finset.sum_congr rfl,
      intros,
      refl, }
    ... = ∑ (x_1 : ι₁) (x_2 : ι₂), function.update 0 (x_1, x_2).fst (x x_1) ⊗ₜ[R] function.update 0 (x_1, x_2).snd (y x_2) :
    by { simp only [pi.tensor_of, tensor_product.map_tmul],
      refl, }
    ... = ∑ (x_1 : ι₁) (x_2 : ι₂), function.update 0 x_1 (x x_1) ⊗ₜ[R] function.update 0 x_2 (y x_2) : rfl
    ... = (∑ (x_1 : ι₁), function.update 0 x_1 (x x_1)) ⊗ₜ[R]
      (∑ (x_2 : ι₂), function.update 0 x_2 (y x_2)) :
    by { simp only [tensor_product.tmul_sum, tensor_product.sum_tmul], }
    ... = x ⊗ₜ[R] y : _,
    congr;
    exact @function.sum_update_eq_self R _ _ _ _ _ _ _, },
  { intros x y hx hy,
    simp only [map_add, hx, hy], },
end

lemma pi.tensor_proj_apply_pi_tensor_of
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)]
  (i j : ι₁ × ι₂) (x : Π i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2) :
  (pi.tensor_proj i) (pi.tensor_of j (x j)) = ite (i = j) (x i) 0 :=
begin
  have t1 : ∀ i j : ι₁, (linear_map.proj j).comp (linear_map.single i) = (direct_sum_from_to i j : M₁ i →ₗ[R] M₁ j)
  := λ i j, rfl,
  have t2 : ∀ i j : ι₂, (linear_map.proj j).comp (linear_map.single i) = (direct_sum_from_to i j : M₂ i →ₗ[R] M₂ j)
  := λ i j, rfl,
  simp only [pi.tensor_of, pi.tensor_proj, ← linear_map.comp_apply, ← tensor_product.map_comp,
    t1, t2],
  split_ifs,
  { rw h,
    simp only [direct_sum_from_to_apply_same, tensor_product.map_one, linear_map.one_apply], },
  { rw [prod.eq_iff_fst_eq_snd_eq, not_and_distrib] at h,
    rcases h with (h|h),
    { rw [direct_sum_from_to_apply_ne_same h, tensor_product.zero_map, linear_map.zero_apply], },
    { rw [direct_sum_from_to_apply_ne_same h, tensor_product.map_zero, linear_map.zero_apply], }, },
end

lemma direct_sum_tensor_to_fun_apply_inv_fun {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)]
  (x : Π i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2) :
  direct_sum_tensor_to_fun (direct_sum_tensor_inv_fun x) = x :=
begin
  simp only [direct_sum_tensor_to_fun, direct_sum_tensor_inv_fun, linear_map.coe_mk,
    map_sum, pi.tensor_proj_apply_pi_tensor_of],
  ext1,
  simp only [finset.sum_apply, finset.sum_ite_eq, finset.mem_univ, if_true],
end

def direct_sum_tensor
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] :
  (Π i, M₁ i) ⊗[R] (Π i, M₂ i) ≃ₗ[R] Π i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd :=
{ to_fun := direct_sum_tensor_to_fun,
  inv_fun := direct_sum_tensor_inv_fun,
  left_inv := λ x, direct_sum_tensor_inv_fun_apply_to_fun x,
  right_inv := λ x, direct_sum_tensor_to_fun_apply_inv_fun x,
  map_add' := λ x y, map_add _ _ _,
  map_smul' := λ r x, smul_hom_class.map_smul _ _ _ }

lemma direct_sum_tensor_apply
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (x : (Π i, M₁ i)) (y : (Π i, M₂ i)) (i : ι₁ × ι₂) :
  direct_sum_tensor (x ⊗ₜ[R] y) i = x i.1 ⊗ₜ[R] y i.2 :=
rfl

@[ext] lemma pi.tensor_ext_iff
  {R : Type*} [comm_ring R] {ι₁ : Type*} {ι₂ : Type*} [decidable_eq ι₁]
  [decidable_eq ι₂] [fintype ι₁] [fintype ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} [Π (i₁ : ι₁), add_comm_group (M₁ i₁)]
  [Π (i₂ : ι₂), add_comm_group (M₂ i₂)] [Π (i₁ : ι₁), module R (M₁ i₁)]
  [Π (i₂ : ι₂), module R (M₂ i₂)] (x z : (Π i, M₁ i)) (y w : (Π i, M₂ i)) :
  x ⊗ₜ[R] y = z ⊗ₜ[R] w ↔ ∀ i j, x i ⊗ₜ[R] y j = z i ⊗ₜ[R] w j :=
begin
  rw ← function.injective.eq_iff (direct_sum_tensor : (Π i, M₁ i) ⊗[R] (Π i, M₂ i) ≃ₗ[R] Π i : ι₁ × ι₂, M₁ i.fst ⊗[R] M₂ i.snd).injective,
  simp_rw [function.funext_iff, direct_sum_tensor_apply, prod.forall],
end


@[simps] def linear_map.pi_pi_prod (R : Type*) {ι₁ ι₂ : Type*} [semiring R]
  (φ : ι₁ → Type*) (ψ : ι₂ → Type*)
  [Π i, add_comm_monoid (φ i)] [Π i, module R (φ i)]
  [Π i, add_comm_monoid (ψ i)] [Π i, module R (ψ i)]
  (S : Type*) [fintype ι₁] [decidable_eq ι₁]
  [fintype ι₂] [decidable_eq ι₂]
  [semiring S] [Π i, module S (ψ i)] [Π i, smul_comm_class R S (ψ i)] :
    (Π i : ι₁ × ι₂, φ i.1 →ₗ[R] ψ i.2) ≃ₗ[S] (Π i j, φ i →ₗ[R] ψ j) :=
by { refine linear_equiv.of_linear _ _ _ _,
  refine { to_fun := λ f j k, f (j,k),
    map_add' := λ f g, by { simp only [pi.add_apply], ext, refl },
    map_smul' := λ r f, by { simp only [pi.smul_apply], ext, refl, } },
  refine { to_fun := λ f i, f i.1 i.2,
    map_add' := λ f g, by { ext, refl },
    map_smul' := λ r f, by { ext, refl, } },
  refl,
  { rw linear_map.ext_iff,
    intros x,
    simp only [linear_map.coe_comp, linear_map.coe_mk,
      function.comp_app, linear_map.id_coe, id.def],
    ext,
    congr,
    exact prod.mk.eta, } }

@[simps] def linear_map.pi_prod_swap (R : Type*) {ι₁ ι₂ : Type*} [semiring R]
  (φ : ι₁ → Type*) (ψ : ι₂ → Type*)
  [Π i, add_comm_monoid (φ i)] [Π i, module R (φ i)]
  [Π i, add_comm_monoid (ψ i)] [Π i, module R (ψ i)]
  (S : Type*) [fintype ι₁] [decidable_eq ι₁]
  [fintype ι₂] [decidable_eq ι₂]
  [semiring S] [Π i, module S (ψ i)] [Π i, smul_comm_class R S (ψ i)] :
    (Π i j, φ i →ₗ[R] ψ j) ≃ₗ[S] (Π j i, φ i →ₗ[R] ψ j) :=
begin
  refine linear_equiv.of_linear _ _ _ _,
  refine { to_fun := λ f j i, f i j,
    map_add' := λ f g, by { ext, refl },
    map_smul' := λ r f, by { ext, refl, } },
  refine { to_fun := λ f i j, f j i,
    map_add' := λ f g, by { ext, refl },
    map_smul' := λ r f, by { ext, refl, } },
  refl,
  { rw linear_map.ext_iff,
    intros x,
    simp only [linear_map.coe_comp, linear_map.coe_mk,
      function.comp_app, linear_map.id_coe, id.def], },
end

@[simps] def linear_map.rsum (R : Type*) {M : Type*} {ι : Type*}
  [semiring R] (φ : ι → Type*) [Π (i : ι), add_comm_monoid (φ i)]
  [Π (i : ι), module R (φ i)]
  (S : Type*) [add_comm_monoid M] [module R M] [fintype ι] [decidable_eq ι]
  [semiring S] [Π i, module S (φ i)] [Π i, smul_comm_class R S (φ i)] :
  (Π i, M →ₗ[R] φ i) ≃ₗ[S] (M →ₗ[R] (Π i, φ i)) :=
{ to_fun := λ f, linear_map.pi f,
  inv_fun := λ f i, (linear_map.proj i) ∘ₗ f,
  map_add' := λ f g, by { ext, simp only [linear_map.pi_apply, pi.add_apply,
    linear_map.add_apply], },
  map_smul' := λ r f, by { ext, simp only [linear_map.pi_apply, pi.smul_apply,
    linear_map.smul_apply, ring_hom.id_apply], },
  left_inv := λ f, by { ext i x, simp only [linear_map.proj_pi], },
  right_inv := λ f, by { ext, simp only [linear_map.comp_apply, linear_map.pi_apply],
    refl, } }

@[simps] def linear_map.lrsum (R : Type*) {ι₁ ι₂ : Type*} [semiring R]
  (φ : ι₁ → Type*) (ψ : ι₂ → Type*)
  [Π i, add_comm_monoid (φ i)] [Π i, module R (φ i)]
  [Π i, add_comm_monoid (ψ i)] [Π i, module R (ψ i)]
  (S : Type*) [fintype ι₁] [decidable_eq ι₁]
  [fintype ι₂] [decidable_eq ι₂]
  [semiring S] [Π i, module S (ψ i)] [Π i, smul_comm_class R S (ψ i)] :
  (Π i : ι₁ × ι₂, φ i.1 →ₗ[R] ψ i.2)
    ≃ₗ[S] (Π i, φ i) →ₗ[R] (Π i, ψ i) :=
begin
  let h₂ : (Π (j : ι₂) (i : ι₁), φ i →ₗ[R] ψ j)
    ≃ₗ[S] Π j, (Π i, φ i) →ₗ[R] ψ j,
  { apply linear_equiv.Pi_congr_right,
    intros j,
    exact linear_map.lsum R φ S, },
  exact (((linear_map.pi_pi_prod R φ ψ S).trans
    (linear_map.pi_prod_swap R φ ψ S)).trans h₂).trans
    (linear_map.rsum R ψ S),
end
