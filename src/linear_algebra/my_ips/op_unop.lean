/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.tensor_product
import algebra.algebra.basic
import algebra.module.opposites

/-!

# The multiplicative opposite linear equivalence

This file defines the multiplicative opposite linear equivalence as linear maps `op` and `unop`. This is essentially `mul_opposite.op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ` but defined as linear maps rather than `linear_equiv`.

We also define `ten_swap` which is the linear automorphisms on `A ⊗[R] Aᵐᵒᵖ` given by swapping the tensor factors while keeping the `ᵒᵖ` in place, i.e., `ten_swap (x ⊗ₜ op y) = y ⊗ₜ op x`.

-/

variables {R A : Type*} [comm_semiring R] [add_comm_monoid A] [module R A]

def op :
  A →ₗ[R] Aᵐᵒᵖ :=
((mul_opposite.op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ)

lemma op_apply (x : A) :
  (op : A →ₗ[R] Aᵐᵒᵖ) x = mul_opposite.op x :=
rfl

def unop :
  Aᵐᵒᵖ →ₗ[R] A :=
((mul_opposite.op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A)

lemma unop_apply (x : Aᵐᵒᵖ) :
  (unop : Aᵐᵒᵖ →ₗ[R] A) x = mul_opposite.unop x :=
rfl

lemma unop_op (x : A) :
  (unop : Aᵐᵒᵖ →ₗ[R] A) ((op : A →ₗ[R] Aᵐᵒᵖ) x) = x :=
rfl

lemma op_unop (x : Aᵐᵒᵖ) :
  (op : A →ₗ[R] Aᵐᵒᵖ) ((unop : Aᵐᵒᵖ →ₗ[R] A) x) = x :=
rfl

lemma unop_comp_op :
  unop ∘ₗ op = (1 : A →ₗ[R] A) :=
rfl

lemma op_comp_unop :
  op ∘ₗ unop = (1 : Aᵐᵒᵖ →ₗ[R] Aᵐᵒᵖ) :=
rfl

lemma op_star_apply [has_star A] (a : A) :
  (op : A →ₗ[R] Aᵐᵒᵖ) (star a) = star ((op : A →ₗ[R] Aᵐᵒᵖ) a) :=
rfl

lemma unop_star_apply [has_star A] (a : Aᵐᵒᵖ) :
  (unop : Aᵐᵒᵖ →ₗ[R] A) (star a) = star ((unop : Aᵐᵒᵖ →ₗ[R] A) a) :=
rfl

open_locale tensor_product
def ten_swap :
  (A ⊗[R] Aᵐᵒᵖ) →ₗ[R] A ⊗[R] Aᵐᵒᵖ :=
(tensor_product.map
  (unop : Aᵐᵒᵖ →ₗ[R] A)
  (op : A →ₗ[R] Aᵐᵒᵖ)) ∘ₗ
    (tensor_product.comm R A Aᵐᵒᵖ).to_linear_map

lemma ten_swap_apply (x : A) (y : Aᵐᵒᵖ) :
  ten_swap (x ⊗ₜ[R] y) = mul_opposite.unop y ⊗ₜ[R] mul_opposite.op x :=
rfl

lemma ten_swap_apply' (x y : A) :
  ten_swap (x ⊗ₜ mul_opposite.op y) = y ⊗ₜ[R] mul_opposite.op x :=
rfl

lemma ten_swap_ten_swap :
  ten_swap ∘ₗ ten_swap = (1 : (A ⊗[R] Aᵐᵒᵖ →ₗ[R] A ⊗[R] Aᵐᵒᵖ)) :=
begin
  apply tensor_product.ext',
  intros,
  simp only [linear_map.comp_apply, ten_swap_apply, mul_opposite.unop_op, mul_opposite.op_unop,
    linear_map.one_apply],
end

lemma ten_swap_apply_ten_swap (x : A ⊗[R] Aᵐᵒᵖ) :
  ten_swap (ten_swap x) = x :=
by rw [← linear_map.comp_apply, ten_swap_ten_swap, linear_map.one_apply]

def ten_swap_injective :
  function.injective (ten_swap : A ⊗[R] Aᵐᵒᵖ →ₗ[R] A ⊗[R] Aᵐᵒᵖ) :=
begin
  intros a b h,
  rw [← ten_swap_apply_ten_swap a, h, ten_swap_apply_ten_swap],
end
