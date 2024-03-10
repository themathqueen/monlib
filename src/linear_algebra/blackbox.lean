/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.inner_aut
import linear_algebra.my_matrix.spectra
import preq.equiv

/-!

# Some stuff on almost-Hermitian matrices

This file contains a blackbox theorem that says that two almost-Hermitian matrices have the same spectrum if and only if they are almost similar. This is a generalization of the fact that two Hermitian matrices have the same spectrum if and only if they are unitarily similar.

-/

open_locale big_operators

lemma ite_eq_ite_iff {α : Type*} (a b c : α) :
  (∀ {p : Prop} [decidable p], @ite α p _inst_1 a c = @ite α p _inst_1 b c)
    ↔ a = b := by
{ split; intros h,
  { specialize @h true _,
    simp_rw [if_true] at h,
    exact h, },
  { simp_rw [h, eq_self_iff_true, forall_2_true_iff], }, }

lemma ite_eq_ite_iff_of_pi {n α : Type*} [decidable_eq n] (a b c :  n → α) :
  (∀ (i j : n), ite (i = j) (a i) (c i) = ite (i = j) (b i) (c i))
    ↔ a = b :=
begin
  rw [← ite_eq_ite_iff _ _ c],
  simp_rw [function.funext_iff, ite_apply],
  split; rintros h _ _,
  { intros i,
    specialize h i i,
    simp_rw [eq_self_iff_true, if_true] at h,
    rw h, },
  { exact h _, },
end

namespace matrix

open_locale matrix

variables {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]

lemma is_almost_hermitian.spectra_ext [decidable_eq 𝕜]
  {A B : n → 𝕜} (hA : (diagonal A).is_almost_hermitian)
  (hB : (diagonal B).is_almost_hermitian) :
  hA.spectra = hB.spectra
  ↔ ∃ σ : equiv.perm n, ∀ i, A i = B (σ i) :=
begin
  sorry
end

lemma is_diagonal.spectrum_eq_iff_rotation [decidable_eq 𝕜]
  (A₁ A₂ : n → 𝕜) (hA₁ : (diagonal A₁).is_almost_hermitian) (hA₂ : (diagonal A₂).is_almost_hermitian) :
  hA₁.spectra = hA₂.spectra
    ↔ ∃ (U : equiv.perm n), diagonal A₂ = inner_aut
      ⟨(equiv.to_pequiv U).to_matrix, equiv.perm.to_pequiv.to_matrix_mem_unitary_group U⟩⁻¹
      (diagonal A₁) :=
begin
  simp_rw [inner_aut_apply', unitary_group.inv_apply, ← matrix.ext_iff,
    mul_apply, star_apply, ← unitary_group.star_coe_eq_coe_star,
    unitary_group.inv_apply, star_star, unitary_group.coe_mk, pequiv.equiv_to_pequiv_to_matrix,
    diagonal_apply, mul_ite, mul_zero, finset.sum_ite_eq', finset.mem_univ, if_true,
    one_apply, mul_boole, star_ite, star_one, star_zero, boole_mul],
  simp_rw [← ite_and, and_comm, ite_and, ← equiv.eq_symm_apply, finset.sum_ite_eq',
    finset.mem_univ, if_true, (equiv.injective _).eq_iff],
  rw [is_almost_hermitian.spectra_ext hA₁ hA₂],
  simp_rw [ite_eq_ite_iff_of_pi, function.funext_iff],
  split,
  { rintros ⟨σ, hσ⟩,
    use σ,
    intros i,
    rw [hσ, equiv.apply_symm_apply], },
  { rintros ⟨U, hU⟩,
    use U,
    intros i,
    rw [hU, equiv.symm_apply_apply], },
end

lemma is_almost_hermitian.spectra_of_inner_aut [decidable_eq 𝕜]
  {A : matrix n n 𝕜} (hA : A.is_almost_hermitian) (U : unitary_group n 𝕜) :
  (hA.of_inner_aut U).spectra = hA.spectra :=
begin
  sorry
end
lemma is_almost_hermitian.inner_aut_spectra [decidable_eq 𝕜]
  {A : matrix n n 𝕜}
  (U : unitary_group n 𝕜)
  (hA : (inner_aut U A).is_almost_hermitian) :
  hA.spectra = ((is_almost_hermitian_iff_of_inner_aut _).mpr hA).spectra :=
begin
  rw ← is_almost_hermitian.spectra_of_inner_aut _ U⁻¹,
  simp_rw [inner_aut_inv_apply_inner_aut_self],
end


lemma is_almost_hermitian.spectrum_eq_iff [decidable_eq 𝕜] {A₁ A₂ : matrix n n 𝕜}
  (hA₁ : A₁.is_almost_hermitian) (hA₂ : A₂.is_almost_hermitian) :
  hA₁.spectra = hA₂.spectra ↔ ∃ (U : unitary_group n 𝕜), A₂ = inner_aut U⁻¹ A₁ :=
begin
  split,
  { rcases hA₁.schur_decomp with ⟨D₁, U₁, h₁⟩,
    rcases hA₂.schur_decomp with ⟨D₂, U₂, h₂⟩,
    have hA₁' : is_almost_hermitian (inner_aut U₁ (diagonal D₁)) :=
    by rw [h₁]; exact hA₁,
    have hA₂' : is_almost_hermitian (inner_aut U₂ (diagonal D₂)) :=
    by rw [h₂]; exact hA₂,
    have h₁' : hA₁.spectra = hA₁'.spectra :=
    by { simp_rw [h₁], },
    have h₂' : hA₂.spectra = hA₂'.spectra :=
    by { simp_rw [h₂], },
    rw [h₁', h₂'],
    simp_rw [is_almost_hermitian.inner_aut_spectra, is_diagonal.spectrum_eq_iff_rotation],
    rcases hA₁ with ⟨α₁, N₁, hA₁⟩,
    rcases hA₂ with ⟨α₂, N₂, hA₂⟩,
    simp_rw [← h₁, ← h₂],
    rw [inner_aut_eq_iff] at h₁ h₂,
    rintros ⟨U, hU⟩,
    simp_rw [hU, inner_aut_apply_inner_aut_inv, inner_aut_eq_iff,
      inner_aut_apply_inner_aut, _root_.mul_inv_rev, inv_inv],
    use U₁ * (⟨(equiv.to_pequiv U).to_matrix,
      equiv.perm.to_pequiv.to_matrix_mem_unitary_group _⟩ : unitary_group n 𝕜) * U₂⁻¹,
    simp_rw [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_self, mul_one,
      inv_mul_cancel_left, mul_inv_self, inner_aut_one, linear_map.one_apply], },
  { rintros ⟨U, rfl⟩,
    simp_rw [is_almost_hermitian.inner_aut_spectra], },
end

/-- two matrices are _almost similar_ if there exists some
  $0\neq\beta\in\mathbb{C}$ such that $x$ and $\beta y$ are similar -/
def is_almost_similar_to [fintype n] [decidable_eq n] [is_R_or_C 𝕜] (x y : matrix n n 𝕜) : Prop :=
∃ (β : 𝕜ˣ) (U : unitary_group n 𝕜), (β : 𝕜) • y = inner_aut U⁻¹ x

/-- an immediate corollary to `matrix.is_almost_hermitian.spectrum_eq_iff` using
  `matrix.is_almost_similar_to` and `matrix.has_almost_equal_spectra_to` -/
lemma is_almost_hermitian.has_almost_equal_spectra_to_iff_is_almost_similar_to
  [linear_order n] {x y : matrix n n ℂ} (hx : x.is_almost_hermitian) (hy : y.is_almost_hermitian) :
  hx.has_almost_equal_spectra_to hy ↔ x.is_almost_similar_to y :=
begin
  simp_rw [is_almost_hermitian.has_almost_equal_spectra_to,
    is_almost_hermitian.spectrum_eq_iff, matrix.is_almost_similar_to],
end


end matrix
