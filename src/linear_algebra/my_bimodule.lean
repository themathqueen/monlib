/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.my_tensor_product
import algebra.algebra.bilinear
import linear_algebra.End
import ring_theory.tensor_product
import preq.finset
import linear_algebra.lmul_rmul

/-!
 # (A-A)-Bimodules

  We define (A-A)-bimodules, where A is a commutative semiring, and show basic properties of them.
-/

variables {R H₁ H₂ : Type*} [comm_semiring R]
  [semiring H₁] [semiring H₂]
  [algebra R H₁] [algebra R H₂]

open_locale tensor_product

local notation x ` ⊗ₘ ` y := tensor_product.map x y

def bimodule.lsmul (x : H₁) (y : H₁ ⊗[R] H₂) :
  H₁ ⊗[R] H₂ :=
((linear_map.mul_left R x) ⊗ₘ 1) y
def bimodule.rsmul (x : H₁ ⊗[R] H₂) (y : H₂) :
  H₁ ⊗[R] H₂ :=
(1 ⊗ₘ linear_map.mul_right R y) x
localized "infix (name := bimodule.lsmul) ` •ₗ `:72 :=  bimodule.lsmul" in bimodule
localized "infix (name := bimodule.rsmul) ` •ᵣ `:72 := bimodule.rsmul" in bimodule

-- open bimodule
open_locale bimodule big_operators

lemma bimodule.lsmul_apply (x a : H₁) (b : H₂) :
  x •ₗ (a ⊗ₜ b) = (x * a) ⊗ₜ[R] b :=
rfl
lemma bimodule.rsmul_apply (a : H₁) (x b : H₂) :
  (a ⊗ₜ b) •ᵣ x = a ⊗ₜ[R] (b * x) :=
rfl
lemma bimodule.lsmul_rsmul_assoc (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂) :
  (x •ₗ a) •ᵣ y = x •ₗ (a •ᵣ y) :=
begin
  simp_rw [bimodule.lsmul, bimodule.rsmul, ← linear_map.comp_apply,
    ← tensor_product.map_comp, linear_map.one_comp, linear_map.comp_one],
end

lemma bimodule.lsmul_zero (x : H₁) :
  x •ₗ (0 : H₁ ⊗[R] H₂) = 0 :=
rfl
lemma bimodule.zero_lsmul (x : H₁ ⊗[R] H₂) :
  0 •ₗ x = 0 :=
by rw [bimodule.lsmul, linear_map.mul_left_zero_eq_zero,
  tensor_product.zero_map, linear_map.zero_apply]
lemma bimodule.zero_rsmul (x : H₂) :
  (0 : H₁ ⊗[R] H₂) •ᵣ x = 0 :=
rfl
lemma bimodule.rsmul_zero (x : H₁ ⊗[R] H₂) :
  x •ᵣ 0 = 0 :=
by rw [bimodule.rsmul, linear_map.mul_right_zero_eq_zero,
  tensor_product.map_zero, linear_map.zero_apply]
lemma bimodule.lsmul_add (x : H₁) (a b : H₁ ⊗[R] H₂) :
  x •ₗ (a + b) = x •ₗ a + x •ₗ b :=
map_add _ _ _
lemma bimodule.add_rsmul (x : H₂) (a b : H₁ ⊗[R] H₂) :
  (a + b) •ᵣ x = a •ᵣ x + b •ᵣ x :=
map_add _ _ _
lemma bimodule.lsmul_sum (x : H₁) {k : Type*} [fintype k] (a : k → H₁ ⊗[R] H₂) :
  x •ₗ (∑ i, a i) = ∑ i, x •ₗ a i :=
map_sum _ _ _
lemma bimodule.sum_rsmul (x : H₂) {k : Type*} [fintype k] (a : k → H₁ ⊗[R] H₂) :
  (∑ i, a i) •ᵣ x = ∑ i, a i •ᵣ x :=
map_sum _ _ _
lemma bimodule.one_lsmul (x : H₁ ⊗[R] H₂) :
  1 •ₗ x = x :=
by rw [bimodule.lsmul, linear_map.mul_left_one, ← linear_map.one_eq_id,
  tensor_product.map_one, linear_map.one_apply]
lemma bimodule.rsmul_one (x : H₁ ⊗[R] H₂) :
  x •ᵣ 1 = x :=
by rw [bimodule.rsmul, linear_map.mul_right_one, ← linear_map.one_eq_id,
  tensor_product.map_one, linear_map.one_apply]
lemma bimodule.lsmul_one (x : H₁) :
  x •ₗ (1 : H₁ ⊗[R] H₂) = x ⊗ₜ 1 :=
by rw [algebra.tensor_product.one_def, bimodule.lsmul_apply, mul_one]
lemma bimodule.one_rsmul (x : H₂) :
  (1 : H₁ ⊗[R] H₂) •ᵣ x = 1 ⊗ₜ x :=
by rw [algebra.tensor_product.one_def, bimodule.rsmul_apply, one_mul]
lemma bimodule.lsmul_smul (α : R) (x : H₁) (a : H₁ ⊗[R] H₂) :
  x •ₗ (α • a) = α • (x •ₗ a) :=
by simp_rw [bimodule.lsmul, smul_hom_class.map_smul]
lemma bimodule.smul_rsmul (α : R) (x : H₂) (a : H₁ ⊗[R] H₂) :
  (α • a) •ᵣ x = α • (a •ᵣ x) :=
by simp_rw [bimodule.rsmul, smul_hom_class.map_smul]
lemma bimodule.lsmul_lsmul (x y : H₁) (a : H₁ ⊗[R] H₂) :
  x •ₗ (y •ₗ a) = (x * y) •ₗ a :=
by simp_rw [bimodule.lsmul, ← linear_map.comp_apply, ← tensor_product.map_comp,
  ← linear_map.mul_left_mul]; refl
lemma bimodule.rsmul_rsmul (x y : H₂) (a : H₁ ⊗[R] H₂) :
  a •ᵣ x •ᵣ y = a •ᵣ (x * y) :=
by simp_rw [bimodule.rsmul, ← linear_map.comp_apply, ← tensor_product.map_comp,
  ← linear_map.mul_right_mul]; refl

local notation `l(` x `,` y `)` := y →ₗ[x] y

def linear_map.is_bimodule_map (P : l(R, H₁ ⊗[R] H₂)) :
  Prop :=
∀ (x : H₁) (y : H₂) (a : H₁ ⊗[R] H₂),
  P (x •ₗ a •ᵣ y) = x •ₗ (P a) •ᵣ y
lemma linear_map.is_bimodule_map.lsmul {P : l(R, H₁ ⊗[R] H₂)} (hP : P.is_bimodule_map)
  (x : H₁) (a : H₁ ⊗[R] H₂) :
  P (x •ₗ a) = x •ₗ P a :=
begin
  nth_rewrite 0 [← bimodule.rsmul_one a],
  rw [← bimodule.lsmul_rsmul_assoc, hP, bimodule.rsmul_one],
end
lemma linear_map.is_bimodule_map.rsmul {P : l(R, H₁ ⊗[R] H₂)} (hP : P.is_bimodule_map)
  (x : H₂) (a : H₁ ⊗[R] H₂) :
  P (a •ᵣ x) = (P a) •ᵣ x :=
begin
  nth_rewrite 0 [← bimodule.one_lsmul a],
  rw [hP, bimodule.one_lsmul],
end

lemma linear_map.is_bimodule_map.add {P Q : l(R, H₁ ⊗[R] H₂)} (hP : P.is_bimodule_map)
  (hQ : Q.is_bimodule_map) :
  (P + Q).is_bimodule_map :=
begin
  simp_rw [linear_map.is_bimodule_map, linear_map.add_apply, bimodule.lsmul_add,
    bimodule.add_rsmul],
  intros x y a,
  rw [hP, hQ],
end
lemma linear_map.is_bimodule_map_zero :
  (0 : l(R, H₁ ⊗[R] H₂)).is_bimodule_map :=
begin
  intros x y a,
  simp_rw [linear_map.zero_apply, bimodule.lsmul_zero, bimodule.zero_rsmul],
end
lemma linear_map.is_bimodule_map.smul {x : l(R, H₁ ⊗[R] H₂)} (hx : x.is_bimodule_map) (k : R) :
  (k • x).is_bimodule_map :=
begin
  intros x y a,
  simp only [linear_map.smul_apply, bimodule.lsmul_smul, bimodule.smul_rsmul],
  rw hx,
end
lemma linear_map.is_bimodule_map.nsmul {x : l(R, H₁ ⊗[R] H₂)} (hx : x.is_bimodule_map) (k : ℕ) :
  (k • x).is_bimodule_map :=
begin
  intros x y a,
  simp only [linear_map.smul_apply, nsmul_eq_smul_cast R k,
    bimodule.lsmul_smul, bimodule.smul_rsmul],
  rw hx,
end

@[instance] def is_bimodule_map.add_comm_monoid :
  add_comm_monoid { x : l(R, H₁ ⊗[R] H₂) // x.is_bimodule_map } :=
{ add := λ x y, ⟨↑x + ↑y, linear_map.is_bimodule_map.add (subtype.mem x)
    (subtype.mem y)⟩,
  add_assoc := λ x y z, by { simp only [subtype.coe_mk, add_assoc], },
  zero := ⟨0, linear_map.is_bimodule_map_zero⟩,
  zero_add := λ x, by { simp only [subtype.coe_mk, zero_add, subtype.coe_eta], },
  add_zero := λ x, by { simp only [subtype.coe_mk, add_zero, subtype.coe_eta], },
  nsmul := λ k x, ⟨k • ↑x, linear_map.is_bimodule_map.nsmul (subtype.mem x) k⟩,
  nsmul_zero' := λ x, by { simp only [subtype.coe_mk, zero_smul], refl, },
  nsmul_succ' := λ k x, by { simp only [nsmul_eq_mul, nat.cast_succ, add_mul,
    one_mul, add_comm], refl, },
  add_comm := λ x y, by { rw [← subtype.coe_inj],
    unfold_coes,
    simp_rw [subtype.val, add_comm], } }
@[instance] def is_bimodule_map.has_smul :
  has_smul R {x : l(R, H₁ ⊗[R] H₂) // x.is_bimodule_map} :=
{ smul := λ a x, ⟨a • ↑x, linear_map.is_bimodule_map.smul (subtype.mem x) a⟩ }
lemma is_bimodule_map.add_smul (a b : R) (x : { x : l(R, H₁ ⊗[R] H₂) // x.is_bimodule_map }) :
  (a + b) • x = a • x + b • x :=
begin
  rw [← subtype.coe_inj],
  unfold_coes,
  simp_rw [subtype.val, add_smul],
  refl,
end
instance :
  mul_action R {x : l(R, H₁ ⊗[R] H₂) // x.is_bimodule_map} :=
{ one_smul := λ x, by { simp_rw [← subtype.coe_inj],
    unfold_coes,
    simp_rw [subtype.val, one_smul],
    refl, },
  mul_smul := λ x y a, by { simp_rw [← subtype.coe_inj],
    unfold_coes,
    simp_rw [subtype.val, ← smul_smul],
    refl, } }
instance :
  distrib_mul_action R {x : l(R, H₁ ⊗[R] H₂) // x.is_bimodule_map} :=
{ smul_zero := λ x, rfl,
  smul_add := λ x y z, by { simp_rw [← subtype.coe_inj],
    unfold_coes,
    simp_rw [subtype.val],
    unfold_coes,
    simp_rw [subtype.val, ← smul_add], } }
instance is_bimodule_map.module :
  module R { x : l(R, H₁ ⊗[R] H₂) // x.is_bimodule_map } :=
{ add_smul := λ r s x, by { simp_rw [← subtype.coe_inj],
    unfold_coes,
    simp_rw [subtype.val, add_smul],
    refl, },
  zero_smul := λ x, by { simp_rw [← subtype.coe_inj],
    unfold_coes,
    simp_rw [subtype.val, zero_smul], } }
def is_bimodule_map.submodule :
  submodule R l(R, H₁ ⊗[R] H₂) :=
{ carrier := λ x, x.is_bimodule_map,
  add_mem' := λ x y hx hy, hx.add hy,
  zero_mem' := linear_map.is_bimodule_map_zero,
  smul_mem' := λ r x hx, hx.smul r }

lemma is_bimodule_map_iff {T : l(R, H₁ ⊗[R] H₂)} :
  T.is_bimodule_map ↔ ∀ a b x y, T ((a * x) ⊗ₜ[R] (y * b)) = a •ₗ T (x ⊗ₜ[R] y) •ᵣ b :=
begin
  refine ⟨λ h a b x y, by rw [← h]; refl, λ h a b x, _⟩,
  apply x.induction_on,
  { simp only [map_zero, bimodule.lsmul_zero, bimodule.zero_rsmul], },
  { intros c d,
    exact h _ _ _ _, },
  { intros c d hc hd,
    simp only [map_add, bimodule.lsmul_add, bimodule.add_rsmul, hc, hd], },
end

lemma is_bimodule_map_iff_ltensor_lsmul_rtensor_rsmul {R H₁ H₂ : Type*}
  [field R] [ring H₁] [ring H₂] [algebra R H₁] [algebra R H₂]
  {x : l(R, H₁)} {y : l(R, H₂)} :
  (x ⊗ₘ y).is_bimodule_map ↔
    (x ⊗ₘ y) = 0 ∨ (x = linear_map.mul_right R (x 1) ∧ y = linear_map.mul_left R (y 1)) :=
begin
  rw [← left_module_map_iff, ← right_module_map_iff],
  by_cases h : (x ⊗ₘ y) = 0,
  { simp_rw [h, eq_self_iff_true, true_or, iff_true, linear_map.is_bimodule_map_zero], },
  simp_rw [is_bimodule_map_iff, tensor_product.map_tmul, bimodule.lsmul_apply,
    bimodule.rsmul_apply, h, false_or],
  have hy : y ≠ 0,
  { intros hy,
    rw [hy, tensor_product.map_zero] at h,
    contradiction, },
  have hx : x ≠ 0,
  { intros hx,
    rw [hx, tensor_product.zero_map] at h,
    contradiction, },
  simp_rw [ne.def, linear_map.ext_iff, linear_map.zero_apply, not_forall] at hx hy,
  refine ⟨λ hxy, _, λ hxy a b c d, by rw [hxy.1, hxy.2]⟩,
  obtain ⟨a, ha⟩ := hx,
  obtain ⟨b, hb⟩ := hy,
  have H : ∀ x_4 x_2 x_1 x_3, x (x_1 * x_3) ⊗ₜ y (x_4 * x_2) = (x_1 * x x_3) ⊗ₜ (y x_4 * x_2) :=
  λ x_4 x_2 x_1 x_3, hxy x_1 x_2 x_3 x_4,
  rw [forall.rotate] at hxy,
  specialize hxy a 1,
  specialize H b 1,
  simp_rw [mul_one, one_mul, ← @sub_eq_zero _ _ _ (_ ⊗ₜ[R] (_ * _) : H₁ ⊗[R] H₂),
    ← @sub_eq_zero _ _ _ ((_ * _) ⊗ₜ[R] _), ← tensor_product.sub_tmul, ← tensor_product.tmul_sub,
    tensor_product.tmul_eq_zero, sub_eq_zero, ha, hb, false_or, or_false] at H hxy,
  exact ⟨H, λ _ _, hxy _ _⟩,
end

def is_bimodule_map.sum {p : Type*} [fintype p]
  (x : p → {x : l(R, H₁ ⊗[R] H₂) // x.is_bimodule_map}) :
  {x : l(R, H₁ ⊗[R] H₂) // x.is_bimodule_map} :=
⟨∑ i, x i, λ a b c, by { simp_rw [linear_map.sum_apply, bimodule.lsmul_sum, bimodule.sum_rsmul],
  apply finset.sum_congr rfl, intros,
  rw subtype.mem (x _), }⟩

lemma rmul_map_lmul_apply_apply (x : H₁ ⊗[R] H₂) (a : H₁) (b : H₂) :
  rmul_map_lmul x (a ⊗ₜ b) = a •ₗ x •ᵣ b :=
begin
  apply x.induction_on,
  { simp only [map_zero], refl, },
  { intros α β,
    simp_rw [rmul_map_lmul_apply, tensor_product.map_tmul, rmul_apply, lmul_apply],
    refl, },
  { intros α β hα hβ,
    simp_rw [map_add, linear_map.add_apply],
    rw [hα, hβ, bimodule.lsmul_add, bimodule.add_rsmul], },
end

lemma linear_map.is_bimodule_map_iff' {f : l(R, H₁ ⊗[R] H₂)} :
  f.is_bimodule_map ↔ rmul_map_lmul (f 1) = f :=
begin
  simp_rw [tensor_product.ext_iff, rmul_map_lmul_apply_apply],
  refine ⟨λ h x y, by rw [← h, bimodule.lsmul_one, bimodule.rsmul_apply, one_mul], λ h, _⟩,
  rw [is_bimodule_map_iff],
  intros a b c d,
  rw [← h, ← bimodule.lsmul_lsmul, ← bimodule.rsmul_rsmul, bimodule.lsmul_rsmul_assoc, h],
end
