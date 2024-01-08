/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import algebra.group.defs
import data.finset.basic
import algebra.big_operators.basic

/-!

# finset

In this file we provide some elementary results for summations

-/

namespace finset

open_locale big_operators

@[simp] lemma sum_rotate {α β γ ζ : Type*} [add_comm_monoid β]
  {s : finset α} {t : finset γ} {u : finset ζ} {f : α → γ → ζ → β} :
  ∑ (x : α) in s, ∑ (y : γ) in t, ∑ (z : ζ) in u, f x y z
    = ∑ (z : ζ) in u, ∑ (x : α) in s, ∑ (y : γ) in t, f x y z :=
begin
  nth_rewrite_rhs 0 finset.sum_comm,
  congr,
  ext x,
  rw finset.sum_comm,
end

@[simp] lemma sum_3_comm {α β γ ζ : Type*} [add_comm_monoid β]
  {s : finset α} {t : finset γ} {u : finset ζ} {f : α → γ → ζ → β} :
  ∑ (x : α) in s, ∑ (y : γ) in t, ∑ (z : ζ) in u, f x y z
    = ∑ (z : ζ) in u, ∑ (y : γ) in t, ∑ (x : α) in s, f x y z :=
begin
  rw finset.sum_rotate,
  congr,
  ext,
  rw finset.sum_comm,
end

@[simp] lemma sum_4_rotate {α β γ ζ ε : Type*} [add_comm_monoid β]
  {s : finset α} {t : finset γ} {u : finset ζ} {v : finset ε} {f : α → γ → ζ → ε → β} :
  ∑ (x : α) in s, ∑ (y : γ) in t, ∑ (z : ζ) in u, ∑ (w : ε) in v, f x y z w
    = ∑ (w : ε) in v, ∑ (x : α) in s, ∑ (y : γ) in t, ∑ (z : ζ) in u, f x y z w :=
begin
  nth_rewrite_rhs 0 finset.sum_comm,
  congr,
  ext x,
  rw finset.sum_rotate,
end

@[simp] lemma sum_sum_comm_sum {α β γ ζ ε : Type*} [add_comm_monoid β]
  {s : finset α} {t : finset γ} {u : finset ζ} {v : finset ε} {f : α → γ → ζ → ε → β} :
  ∑ (x : α) in s, ∑ (y : γ) in t, ∑ (z : ζ) in u, ∑ (w : ε) in v, f x y z w
    = ∑ (x : α) in s, ∑ (y : γ) in t, ∑ (w : ε) in v, ∑ (z : ζ) in u, f x y z w :=
begin
  congr,
  ext x,
  congr,
  ext y,
  nth_rewrite_rhs 0 finset.sum_comm,
end

@[simp] lemma sum_sum_sum {β α γ ζ : Type*}
  [add_comm_monoid β] {s : finset γ} {t : finset α} {g : finset ζ}
  {f : γ → α → ζ → β} :
  ∑ (x : γ) in s, ∑ (y : α) in t, ∑ (z : ζ) in g, f x y z
    = ∑ (z : ζ) in g, ∑ (x : γ) in s, ∑ (y : α) in t, f x y z :=
begin
  symmetry,
  rw finset.sum_comm,
  congr,
  ext,
  rw finset.sum_comm,
end

lemma sum_4_swap_2 {β α γ ζ ε : Type*} [add_comm_monoid β] {s : finset γ}
  {t : finset α} {u : finset ζ} {v : finset ε} {f : γ → α → ζ → ε → β} :
  ∑ (x : γ) in s, ∑ (y : α) in t, ∑ (z : ζ) in u, ∑ (w : ε) in v, f x y z w
    = ∑ (z : ζ) in u, ∑ (w : ε) in v, ∑ (x : γ) in s, ∑ (y : α) in t, f x y z w :=
begin
  rw finset.sum_rotate,
  congr,
  ext,
  rw sum_rotate,
end

lemma sum_5_rotate {α β γ ζ ε κ : Type*}
  [add_comm_monoid β] {s : finset α} {t : finset γ} {u : finset ζ} {v : finset ε} {k : finset κ}
  {f : α → γ → ζ → ε → κ → β} :
  ∑ (x : α) in s, ∑ (y : γ) in t, ∑ (z : ζ) in u, ∑ (w : ε) in v, ∑ (vz : κ) in k, f x y z w vz
    = ∑ (vz : κ) in k, ∑ (x : α) in s, ∑ (y : γ) in t, ∑ (z : ζ) in u, ∑ (w : ε) in v,
      f x y z w vz :=
begin
  nth_rewrite_rhs 0 finset.sum_comm,
  congr,
  ext x,
  rw finset.sum_4_rotate,
end

end finset

@[simp] lemma forall.rotate {α β γ : Sort*} {p : α → β → γ → Prop} :
  (∀ (x : α) (y : β) (z : γ), p x y z) ↔ ∀ (z : γ) (x : α) (y : β), p x y z :=
⟨λ h _ _ _, h _ _ _, λ h _ _ _, h _ _ _⟩

@[simp] lemma forall_forall_comm {α β γ ζ : Sort*} {p : α → β → γ → ζ → Prop} :
  (∀ (x : α) (y : β) (z : γ) (w : ζ), p x y z w) ↔ ∀ (x : α) (z : γ) (y : β) (w : ζ), p x y z w :=
⟨λ h _ _ _ _, h _ _ _ _, λ h _ _ _ _, h _ _ _ _⟩
