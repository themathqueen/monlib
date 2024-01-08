/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import linear_algebra.inner_aut

/-!

# Some stuff on almost-Hermitian matrices

This file contains a blackbox theorem that says that two almost-Hermitian matrices have the same spectrum if and only if they are almost similar. This is a generalization of the fact that two Hermitian matrices have the same spectrum if and only if they are unitarily similar.

-/

open_locale big_operators
lemma equiv.perm.to_pequiv.to_matrix_mem_unitary_group {n : Type*} [decidable_eq n]
  [fintype n] {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜] (σ : equiv.perm n) :
  (equiv.to_pequiv σ).to_matrix ∈ matrix.unitary_group n 𝕜 :=
begin
  simp_rw [matrix.mem_unitary_group_iff, ← matrix.ext_iff, matrix.mul_eq_mul,
    matrix.mul_apply, pequiv.to_matrix_apply, boole_mul, equiv.to_pequiv_apply,
    matrix.one_apply, option.mem_def, matrix.star_apply, pequiv.to_matrix_apply,
    star_ite, is_R_or_C.star_def, map_one, map_zero, finset.sum_ite_eq,
    finset.mem_univ, if_true],
  intros i j,
  simp_rw [equiv.to_pequiv_apply, option.mem_def, eq_comm, function.injective.eq_iff
    (equiv.injective _)],
end

namespace matrix

variables {n 𝕜 : Type*} [is_R_or_C 𝕜] [fintype n] [decidable_eq n]

lemma is_diagonal.spectrum_eq_iff_rotation [decidable_eq 𝕜]
  (A₁ A₂ : n → 𝕜) :
  spectrum 𝕜 (diagonal A₁ : matrix n n 𝕜).to_lin'
    = spectrum 𝕜 (diagonal A₂ : matrix n n 𝕜).to_lin'
    ↔ ∃ (U : equiv.perm n), diagonal A₂ = inner_aut
      ⟨(equiv.to_pequiv U).to_matrix, equiv.perm.to_pequiv.to_matrix_mem_unitary_group U⟩⁻¹
      (diagonal A₁) :=
begin
  split,
  { simp_rw [inner_aut_apply', unitary_group.inv_apply, ← matrix.ext_iff,
      mul_apply, star_apply, ← unitary_group.star_coe_eq_coe_star,
      unitary_group.inv_apply, star_star, unitary_group.coe_mk, pequiv.equiv_to_pequiv_to_matrix,
      diagonal_apply, mul_ite, mul_zero, finset.sum_ite_eq', finset.mem_univ, if_true,
      one_apply, mul_boole, star_ite, star_one, star_zero, boole_mul],
    simp_rw [← ite_and, and_comm, ite_and, ← equiv.eq_symm_apply, finset.sum_ite_eq',
      finset.mem_univ, if_true, (equiv.injective _).eq_iff, diagonal.spectrum, set.ext_iff,
      set.mem_set_of_eq],
    intros h,
    simp_rw [ite_eq_iff', @eq_comm _ _ (ite _ _ _), ite_eq_iff', eq_self_iff_true,
      imp_true_iff, and_true],
    sorry, },
  { rintros ⟨U, hU⟩,
    simp_rw [hU, inner_aut.spectrum_eq], },
end

lemma is_almost_hermitian.spectrum_eq_iff [decidable_eq 𝕜] [linear_order n] {A₁ A₂ : matrix n n 𝕜}
  (hA₁ : A₁.is_almost_hermitian) (hA₂ : A₂.is_almost_hermitian) :
  spectrum 𝕜 A₁.to_lin' = spectrum 𝕜 A₂.to_lin'
    ↔ ∃ (U : unitary_group n 𝕜), A₂ = inner_aut U⁻¹ A₁ :=
begin
  rcases hA₁.schur_decomp with ⟨D₁, U₁, h₁⟩,
  rcases hA₂.schur_decomp with ⟨D₂, U₂, h₂⟩,
  rcases hA₁ with ⟨α₁, N₁, hA₁⟩,
  rcases hA₂ with ⟨α₂, N₂, hA₂⟩,
  rw [← h₁, ← h₂],
  rw [inner_aut_eq_iff] at h₁ h₂,
  split,
  { intros h,
    simp_rw inner_aut.spectrum_eq at h,
    obtain ⟨σ, hσ⟩ : ∃ σ : equiv.perm n, diagonal D₂
      = inner_aut ⟨(equiv.to_pequiv σ).to_matrix, _⟩⁻¹ (diagonal D₁) :=
    (is_diagonal.spectrum_eq_iff_rotation D₁ D₂).mp h,
    let P : unitary_group n 𝕜 := ⟨(equiv.to_pequiv σ).to_matrix,
      equiv.perm.to_pequiv.to_matrix_mem_unitary_group σ⟩,
    existsi U₁ * P * U₂⁻¹,
    simp_rw [← linear_map.comp_apply, inner_aut_comp_inner_aut, h₁,
      _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_self, mul_one, hσ, ← h₁,
      ← linear_map.comp_apply, inner_aut_comp_inner_aut], },
  { rintros ⟨U, hU⟩,
    simp_rw [hU, ← linear_map.comp_apply, inner_aut_comp_inner_aut, inner_aut.spectrum_eq], },
end

/-- two matrices are _almost similar_ if there exists some
  $0\neq\beta\in\mathbb{C}$ such that $x$ and $\beta y$ are similar -/
def is_almost_similar_to [fintype n] [decidable_eq n] [is_R_or_C 𝕜] (x y : matrix n n 𝕜) : Prop :=
∃ (β : 𝕜ˣ) (U : unitary_group n 𝕜), (β : 𝕜) • y = inner_aut U⁻¹ x

/-- an immediate corollary to `matrix.is_almost_hermitian.spectrum_eq_iff` using
  `matrix.is_almost_similar_to` and `matrix.has_almost_equal_spectra_to` -/
lemma is_almost_hermitian.has_almost_equal_spectra_to_iff_is_almost_similar_to
  [linear_order n] {x y : matrix n n ℂ} (hx : x.is_almost_hermitian) (hy : y.is_almost_hermitian) :
  x.has_almost_equal_spectra_to y ↔ x.is_almost_similar_to y :=
begin
  have : (∃ (β : ℂˣ), spectrum ℂ (to_lin' x) = spectrum ℂ (to_lin' ((β : ℂ) • y)))
    ↔ (∃ β : ℂ, β ≠ 0 ∧ spectrum ℂ (to_lin' x) = spectrum ℂ (to_lin' (β • y))) :=
  ⟨λ ⟨β, hβ⟩, ⟨(β : ℂ), ⟨units.ne_zero _, hβ⟩⟩, λ ⟨β, ⟨hβ, h⟩⟩, ⟨units.mk0 β hβ, h⟩⟩,
  simp_rw [matrix.has_almost_equal_spectra_to, this, is_almost_hermitian.spectrum_eq_iff hx
    (almost_hermitian_iff_smul.mp hy _), matrix.is_almost_similar_to],
  split,
  { rintros ⟨β, ⟨hβ, ⟨U, hU⟩⟩⟩,
    exact ⟨units.mk0 β hβ, U, hU⟩, },
  { rintros ⟨β, U, hU⟩,
    exact ⟨β, ⟨units.ne_zero _, ⟨U, hU⟩⟩⟩, },
end


end matrix
