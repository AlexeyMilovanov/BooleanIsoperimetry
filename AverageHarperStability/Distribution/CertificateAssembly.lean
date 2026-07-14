import AverageHarperStability.Distribution.Azuma

open scoped BigOperators

namespace AverageHarperStability

/-!
# Tracking-certificate assembly

This is the elementary final layer: Markov on the nonnegative `off` field,
the Azuma event, and a finite union bound.
-/

lemma eventMass_union_le {n : ℕ} (mu : Cube n → ℝ) (hmu : ∀ x, 0 ≤ mu x)
    (E1 E2 : Cube n → Prop) :
    eventMass mu (fun x => E1 x ∨ E2 x) ≤ eventMass mu E1 + eventMass mu E2 := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases h1 : E1 x <;> by_cases h2 : E2 x <;> simp [h1, h2, hmu x]

lemma eventMass_le_of_imp {n : ℕ} (mu : Cube n → ℝ) (hmu : ∀ x, 0 ≤ mu x)
    (E1 E2 : Cube n → Prop) (h : ∀ x, E1 x → E2 x) :
    eventMass mu E1 ≤ eventMass mu E2 := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum
  intro x _
  by_cases h1 : E1 x
  · simp [h1, h x h1]
  · by_cases h2 : E2 x <;> simp [h1, h2, hmu x]

lemma markov_ineq {n : ℕ} (mu : Cube n → ℝ) (hmu : ∀ x, 0 ≤ mu x)
    (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) (t : ℝ) (ht : 0 < t) :
    eventMass mu (fun x => t < f x) ≤ (∑ x, mu x * f x) / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : t < f x
  · simp only [hx, if_true]
    exact mul_le_mul_of_nonneg_left hx.le (hmu x)
  · simp only [hx, if_false, zero_mul]
    exact mul_nonneg (hmu x) (hf x)

/-- A tracking certificate plus its generic Azuma tail implies the frozen
distribution-stability conclusion. -/
theorem tracking_certificate_to_conclusion
    {n : ℕ} {mu : Cube n → ℝ} {err : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (herr : 0 < err)
    (C : TrackingCertificate mu (hbInv (entropyRate n mu)) err)
    (hAzuma : eventMass mu (fun x =>
      Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) <
        (hDist x (C.D x) : ℝ) - predictableDistance C.q x) ≤
      1 / (n : ℝ)) :
    distributionStabilityConclusion err mu := by
  let p := hbInv (entropyRate n mu)
  let S := Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ)
  use C.D
  refine ⟨C.label_entropy, ?_⟩
  let E_A := fun x => S < (hDist x (C.D x) : ℝ) - predictableDistance C.q x
  let E_M := fun x => (err / 2) * (n : ℝ) < C.off x
  have H_imp : ∀ x,
    (p + err + Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ) < (hDist x (C.D x) : ℝ) →
    E_A x ∨ E_M x := by
    intro x hx
    by_contra! h
    rcases h with ⟨hA, hM⟩
    have hA' : (hDist x (C.D x) : ℝ) - predictableDistance C.q x ≤ S := not_lt.mp hA
    have hM' : C.off x ≤ (err / 2) * (n : ℝ) := not_lt.mp hM
    have H1 : (hDist x (C.D x) : ℝ) ≤ predictableDistance C.q x + S := sub_le_iff_le_add'.mp hA'
    have H2 : predictableDistance C.q x ≤ (p + err / 2) * (n : ℝ) + C.off x := C.predictable_bound x
    have H3 : S = Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) := rfl
    linarith
  have H_prob1 : eventMass mu (fun x => E_A x ∨ E_M x) ≤ eventMass mu E_A + eventMass mu E_M :=
    eventMass_union_le mu hmu.1 E_A E_M
  have H_prob2 : eventMass mu E_M ≤ err / 2 := by
    have hm : eventMass mu E_M ≤ (∑ x, mu x * C.off x) / ((err / 2) * (n : ℝ)) := by
      apply markov_ineq mu hmu.1 _ C.off_nonneg
      positivity
    have hm2 : (∑ x, mu x * C.off x) / ((err / 2) * (n : ℝ)) ≤ err / 2 := by
      have h1 : ∑ x, mu x * C.off x ≤ (err ^ 2 / 4) * (n : ℝ) := C.off_mean
      have hc : 0 < (err / 2) * (n : ℝ) := by positivity
      have h2 : (∑ x, mu x * C.off x) / ((err / 2) * (n : ℝ)) ≤ ((err ^ 2 / 4) * (n : ℝ)) / ((err / 2) * (n : ℝ)) := div_le_div_of_nonneg_right h1 hc.le
      have h3 : (err ^ 2 / 4) * (n : ℝ) / ((err / 2) * (n : ℝ)) = err / 2 := by
        calc (err ^ 2 / 4) * (n : ℝ) / ((err / 2) * (n : ℝ))
          _ = (err / 2) * ((err / 2) * (n : ℝ)) / ((err / 2) * (n : ℝ)) := by ring
          _ = err / 2 := by
            rw [mul_div_cancel_right₀]
            positivity
      linarith
    linarith
  have H_prob3 : eventMass mu (fun x => (p + err + Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ) < (hDist x (C.D x) : ℝ)) ≤ eventMass mu (fun x => E_A x ∨ E_M x) :=
    eventMass_le_of_imp mu hmu.1 _ _ H_imp
  linarith

end AverageHarperStability
