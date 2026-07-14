import AverageHarperStability.Interface

namespace AverageHarperStability

theorem uniformMass_isLaw {n : ℕ} (A : Finset (Cube n)) (hA : A.Nonempty) :
    IsLaw (uniformMass A) := by
  constructor
  · intro x
    dsimp [uniformMass]
    split_ifs
    · exact div_nonneg zero_le_one (by positivity)
    · rfl
  · dsimp [uniformMass]
    rw [Finset.sum_ite]
    have hF : (Finset.univ : Finset (Cube n)).filter (· ∈ A) = A := by
      ext x
      simp
    rw [hF]
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : (A.card : ℝ) ≠ 0 := by
      intro h_eq
      have h1 : A.card = 0 := by exact_mod_cast h_eq
      rw [Finset.card_eq_zero] at h1
      subst h1
      exact Finset.not_nonempty_empty hA
    exact mul_one_div_cancel hcard

theorem entropy_uniformMass {n : ℕ} (A : Finset (Cube n)) (hA : A.Nonempty) :
    entropy (uniformMass A) = Real.log (A.card : ℝ) := by
  dsimp [entropy, uniformMass]
  have h_log : ∀ x, Real.negMulLog (if x ∈ A then 1 / (A.card : ℝ) else 0) =
      if x ∈ A then Real.negMulLog (1 / (A.card : ℝ)) else 0 := by
    intro x
    split_ifs
    · rfl
    · exact Real.negMulLog_zero
  simp_rw [h_log, Finset.sum_ite]
  have hF : (Finset.univ : Finset (Cube n)).filter (· ∈ A) = A := by
    ext x
    simp
  rw [hF]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (A.card : ℝ) ≠ 0 := by
    intro h_eq
    have h1 : A.card = 0 := by exact_mod_cast h_eq
    rw [Finset.card_eq_zero] at h1
    subst h1
    exact Finset.not_nonempty_empty hA
  dsimp [Real.negMulLog]
  have h_alg2 : ∀ c L : ℝ, c ≠ 0 → c * (- c⁻¹ * -L) = L := by
    intro c L hc
    calc
      c * (- c⁻¹ * -L) = (c * c⁻¹) * L := by ring
      _ = 1 * L := by rw [mul_inv_cancel₀ hc]
      _ = L := by ring
  rw [one_div, Real.log_inv]
  exact h_alg2 _ _ hcard

theorem noiseMass_isLaw {n : ℕ} {tau : ℝ} (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (mu : Cube n → ℝ) (hmu : IsLaw mu) : IsLaw (noiseMass tau mu) := by
  constructor
  · intro y
    dsimp [noiseMass]
    apply Finset.sum_nonneg
    intro x _hx
    apply mul_nonneg
    · exact hmu.1 x
    · dsimp [noiseKernel]
      apply mul_nonneg
      · exact pow_nonneg ht0 _
      · exact pow_nonneg (sub_nonneg.mpr ht1) _
  · dsimp [noiseMass]
    rw [Finset.sum_comm]
    have h_sum_kernel : ∀ x, ∑ y : Cube n, noiseKernel tau x y = 1 := by
      intro x
      dsimp [noiseKernel, hDist]
      let e : Cube n ≃ Cube n := {
        toFun := fun y => symmDiff x y
        invFun := fun y => symmDiff x y
        left_inv := fun y => by simp [symmDiff_symmDiff_cancel_left]
        right_inv := fun y => by simp [symmDiff_symmDiff_cancel_left]
      }
      have h_shift := Equiv.sum_comp e (fun z => tau ^ z.card * (1 - tau) ^ (n - z.card))
      dsimp [e] at h_shift
      rw [h_shift]
      have h_univ : (Finset.univ : Finset (Cube n)) = Finset.powerset (Finset.univ : Finset (Fin n)) := by
        ext a
        simp
      rw [h_univ]
      have h_binomial := Finset.sum_pow_mul_eq_add_pow tau (1 - tau) (Finset.univ : Finset (Fin n))
      have h_card : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
      rw [h_card] at h_binomial
      have h_one : tau + (1 - tau) = 1 := by ring
      rw [h_one, one_pow] at h_binomial
      exact h_binomial
    simp_rw [← Finset.mul_sum, h_sum_kernel, mul_one]
    exact hmu.2

end AverageHarperStability
