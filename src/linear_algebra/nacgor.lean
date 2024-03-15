/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import analysis.normed.group.basic
import analysis.normed_space.pi_Lp
import analysis.inner_product_space.basic

/-!
 # Normed additive commutative groups of rings

 This file contains the definition of `normed_add_comm_group_of_ring` which is a structure
  combining the ring structure, the norm, and the metric space structure.
-/

/-- `normed_add_comm_group` structure extended by `ring` -/
@[class]
structure normed_add_comm_group_of_ring (B : Type*) extends
  has_norm B, ring B, metric_space B :=
(dist := λ x y, ‖x - y‖)
(dist_eq : ∀ x y, dist x y = ‖x - y‖ . obviously)

open_locale big_operators
instance normed_add_comm_group_of_ring.to_normed_add_comm_group {B : Type*}
  [h : normed_add_comm_group_of_ring B] :
  normed_add_comm_group B :=
{ dist_eq := normed_add_comm_group_of_ring.dist_eq }

def algebra.of_is_scalar_tower_smul_comm_class
  {R A : Type*} [comm_semiring R] [semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A] :
  algebra R A :=
algebra.of_module smul_mul_assoc mul_smul_comm
local attribute [instance] algebra.of_is_scalar_tower_smul_comm_class

noncomputable instance pi.normed_add_comm_group_of_ring
  {ι : Type*} [fintype ι] {B : ι → Type*} [Π i, normed_add_comm_group_of_ring (B i)] :
  normed_add_comm_group_of_ring (Π i, B i) :=
{ to_has_norm := pi_Lp.has_norm 2 B,
  to_ring := pi.ring,
  to_metric_space := pi_Lp.metric_space 2 B,
  dist_eq := λ x y, by {
    have : 0 < (2 : ennreal).to_real := by norm_num,
    simp_rw [pi_Lp.norm_eq_sum this, pi_Lp.dist_eq_sum this, dist_eq_norm],
    refl, }, }

example {ι : Type*} [fintype ι] {E : ι → Type*} [h : Π i, normed_add_comm_group_of_ring (E i)] :
  @add_comm_group.to_add_comm_monoid _
    ((normed_add_comm_group_of_ring.to_normed_add_comm_group
      : normed_add_comm_group (Π i, E i)).to_add_comm_group)
    =
  (non_unital_non_assoc_semiring.to_add_comm_monoid _) :=
rfl
-- set_option old_structure_cmd true
lemma pi.normed_add_comm_group_of_ring.norm_eq_sum
  {ι : Type*} [fintype ι] {B : ι → Type*} [Π i, normed_add_comm_group_of_ring (B i)]
  (x : Π i, B i) :
  ‖x‖ = real.sqrt (∑ i, ‖x i‖ ^ 2) :=
by { have : 0 < (2 : ennreal).to_real := by norm_num,
  simp_rw [pi_Lp.norm_eq_sum this, ennreal.to_real_bit0,
    ennreal.one_to_real, real.rpow_two, real.sqrt_eq_rpow], }

example {E : Type*} [h : normed_add_comm_group_of_ring E] :
  @add_comm_group_with_one.to_add_comm_group E (ring.to_add_comm_group_with_one E)
    = normed_add_comm_group.to_add_comm_group :=
rfl
example {E : Type*} [h : normed_add_comm_group_of_ring E] :
  (@add_comm_group.to_add_comm_monoid E normed_add_comm_group.to_add_comm_group : add_comm_monoid E)
    = (non_unital_non_assoc_semiring.to_add_comm_monoid E : add_comm_monoid E) :=
rfl
example {E : Type*} [ring E] :
  @add_comm_group.to_add_comm_monoid E
  (@add_comm_group_with_one.to_add_comm_group E (ring.to_add_comm_group_with_one E))
  = non_unital_non_assoc_semiring.to_add_comm_monoid E :=
rfl

/-- `module` given by `algebra` is equal to that given by
  `inner_product_space`, but they are not definitionally equal.
  So this may cause some problems in the future.
  In Lean 4, they are definitionally equal. -/
example
  {E : Type*} [normed_add_comm_group_of_ring E]
  [h : inner_product_space ℂ E] [smul_comm_class ℂ E E]
  [is_scalar_tower ℂ E E] :
  h.to_module = (algebra.to_module : module ℂ E) :=
by ext; refl
