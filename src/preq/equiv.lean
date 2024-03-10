import linear_algebra.my_matrix.basic

lemma equiv.perm.to_pequiv.to_matrix_mem_unitary_group {n : Type*} [decidable_eq n]
  [fintype n] {𝕜 : Type*} [comm_ring 𝕜] [star_ring 𝕜] (σ : equiv.perm n) :
  (equiv.to_pequiv σ).to_matrix ∈ matrix.unitary_group n 𝕜 :=
begin
  simp_rw [matrix.mem_unitary_group_iff, ← matrix.ext_iff, matrix.mul_eq_mul,
    matrix.mul_apply, pequiv.to_matrix_apply, boole_mul, equiv.to_pequiv_apply,
    matrix.one_apply, option.mem_def, matrix.star_apply, pequiv.to_matrix_apply,
    star_ite, star_one, star_zero, finset.sum_ite_eq,
    finset.mem_univ, if_true],
  intros i j,
  simp_rw [equiv.to_pequiv_apply, option.mem_def, eq_comm, function.injective.eq_iff
    (equiv.injective _)],
end