import AverageHarperStability.Interface

namespace AverageHarperStability

/-! Entropy pigeonhole and conversion of probability mass to set cardinality. -/

open scoped Topology
open Filter Set Finset Classical

private lemma uniformMass_nonneg {n : ℕ} (A : Finset (Cube n)) (x : Cube n) :
    0 ≤ uniformMass A x := by
  simp only [uniformMass]
  split_ifs <;> positivity

private lemma mapMass_uniform_nonneg {n : ℕ} (A : Finset (Cube n))
    (D : Cube n → Cube n) (d : Cube n) :
    0 ≤ mapMass (uniformMass A) D d := by
  simp only [mapMass]
  exact Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact uniformMass_nonneg A x
    · exact le_rfl

private lemma uniformMass_sum_le_one {n : ℕ} (A : Finset (Cube n)) :
    ∑ x, uniformMass A x ≤ 1 := by
  by_cases hA : A.Nonempty
  · rw [show ∑ x, uniformMass A x = 1 by
      simp only [uniformMass]
      rw [← Finset.sum_filter]
      simp [hA.card_ne_zero]]
  · have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [this, uniformMass]

private lemma sum_mapMass {n : ℕ} (mu : Cube n → ℝ) (D : Cube n → Cube n) :
    ∑ d, mapMass mu D d = ∑ x, mu x := by
  simp only [mapMass]
  rw [Finset.sum_comm]
  simp

private lemma eventMass_map {n : ℕ} (mu : Cube n → ℝ) (D : Cube n → Cube n)
    (P : Cube n → Prop) [DecidablePred P] :
    eventMass mu (fun x => P (D x)) =
      ∑ d, if P d then mapMass mu D d else 0 := by
  simp only [eventMass]
  rw [← Finset.sum_filter]
  simp only [mapMass]
  rw [Finset.sum_comm]
  simp
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : P (D x) <;> simp [h]

private lemma mapMass_uniform_le_one {n : ℕ} (A : Finset (Cube n))
    (D : Cube n → Cube n) (d : Cube n) :
    mapMass (uniformMass A) D d ≤ 1 := by
  calc
    mapMass (uniformMass A) D d ≤ ∑ e, mapMass (uniformMass A) D e := by
      apply Finset.single_le_sum (fun e _ => mapMass_uniform_nonneg A D e)
      simp
    _ = ∑ x, uniformMass A x := sum_mapMass (uniformMass A) D
    _ ≤ 1 := uniformMass_sum_le_one A

private lemma mul_le_negMulLog_of_lt_exp_neg {q t : ℝ} (hq : 0 ≤ q)
    (hqt : q < Real.exp (-t)) : t * q ≤ Real.negMulLog q := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hlog : Real.log q < -t := (Real.log_lt_iff_lt_exp hqpos).2 hqt
    rw [Real.negMulLog_eq_neg]
    have hm := mul_lt_mul_of_pos_left hlog hqpos
    nlinarith

private lemma eventMass_mono_uniform {n : ℕ} (A : Finset (Cube n))
    (P Q : Cube n → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q x) :
    eventMass (uniformMass A) P ≤ eventMass (uniformMass A) Q := by
  simp only [eventMass]
  apply Finset.sum_le_sum
  intro x _
  by_cases hP : P x <;> by_cases hQ : Q x <;>
    simp_all [uniformMass_nonneg A x]

private lemma eventMass_union_le {n : ℕ} (A : Finset (Cube n))
    (P Q : Cube n → Prop) [DecidablePred P] [DecidablePred Q] :
    eventMass (uniformMass A) (fun x => P x ∨ Q x) ≤
      eventMass (uniformMass A) P + eventMass (uniformMass A) Q := by
  simp only [eventMass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hP : P x <;> by_cases hQ : Q x <;>
    simp_all [uniformMass_nonneg A x]

private lemma eventMass_uniform_eq_card_div {n : ℕ} (A : Finset (Cube n))
    (E : Cube n → Prop) [DecidablePred E] :
    eventMass (uniformMass A) E = ((A.filter E).card : ℝ) / (A.card : ℝ) := by
  simp only [eventMass, uniformMass]
  rw [show (∑ x, if E x then (if x ∈ A then 1 / (A.card : ℝ) else 0) else 0) =
      ∑ x, if x ∈ A.filter E then 1 / (A.card : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hE : E x <;> by_cases hx : x ∈ A <;> simp_all]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun x => x ∈ A.filter E)).card =
      (A.filter E).card := by
    have hs : Finset.univ.filter (fun x => x ∈ A.filter E) = A.filter E := by
      ext x
      simp
    exact congrArg Finset.card hs
  rw [hc]
  simp [div_eq_mul_inv]

lemma centers_card_bound {n : ℕ} (A : Finset (Cube n)) (D : Cube n → Cube n) (a : ℝ)
    (centers : Finset (Cube n))
    (h_centers : centers = Finset.univ.filter (fun d => Real.exp (- (Real.sqrt a * (n : ℝ))) ≤ mapMass (uniformMass A) D d)) :
    (centers.card : ℝ) ≤ Real.exp (Real.sqrt a * (n : ℝ)) := by
  let s : ℝ := Real.sqrt a * (n : ℝ)
  have hmul : (centers.card : ℝ) * Real.exp (-s) ≤ 1 := by
    calc
      (centers.card : ℝ) * Real.exp (-s) = ∑ d ∈ centers, Real.exp (-s) := by simp
      _ ≤ ∑ d ∈ centers, mapMass (uniformMass A) D d := by
        apply Finset.sum_le_sum
        intro d hd
        rw [h_centers] at hd
        simpa [s] using (Finset.mem_filter.mp hd).2
      _ ≤ ∑ d, mapMass (uniformMass A) D d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ centers)
        intro d _ _
        exact mapMass_uniform_nonneg A D d
      _ = ∑ x, uniformMass A x := sum_mapMass (uniformMass A) D
      _ ≤ 1 := uniformMass_sum_le_one A
  calc
    (centers.card : ℝ) = ((centers.card : ℝ) * Real.exp (-s)) * Real.exp s := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ 1 * Real.exp s := mul_le_mul_of_nonneg_right hmul (Real.exp_pos s).le
    _ = Real.exp (Real.sqrt a * (n : ℝ)) := by simp [s]

lemma uncentered_mass_bound {n : ℕ} (A : Finset (Cube n)) (D : Cube n → Cube n) (a : ℝ)
    (ha : 0 < a) (hn : 1 ≤ n)
    (centers : Finset (Cube n))
    (h_centers : centers = Finset.univ.filter (fun d => Real.exp (- (Real.sqrt a * (n : ℝ))) ≤ mapMass (uniformMass A) D d))
    (h_ent : entropy (mapMass (uniformMass A) D) ≤ a * (n : ℝ)) :
    eventMass (uniformMass A) (fun x => D x ∉ centers) ≤ Real.sqrt a := by
  let q : Cube n → ℝ := mapMass (uniformMass A) D
  let t : ℝ := Real.sqrt a * (n : ℝ)
  let low : Cube n → Prop := fun d => q d < Real.exp (-t)
  have ht : 0 < t := mul_pos (Real.sqrt_pos.2 ha) (by exact_mod_cast hn)
  have hnotmem : ∀ d, d ∉ centers ↔ low d := by
    intro d
    rw [h_centers]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    rfl
  have hevent : eventMass (uniformMass A) (fun x => D x ∉ centers) =
      ∑ d, if low d then q d else 0 := by
    rw [eventMass_map (uniformMass A) D (fun d => d ∉ centers)]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∉ centers
    · have hl := (hnotmem d).1 hd
      simp [hd, hl, q]
    · have hl : ¬ low d := mt (hnotmem d).2 hd
      simp [hd, hl]
  have htail : t * eventMass (uniformMass A) (fun x => D x ∉ centers) ≤
      entropy q := by
    rw [hevent]
    simp only [entropy]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    by_cases hd : low d
    · simp only [hd, if_true]
      exact mul_le_negMulLog_of_lt_exp_neg (mapMass_uniform_nonneg A D d) hd
    · simp only [hd, if_false, mul_zero]
      simpa [q] using
        Real.negMulLog_nonneg (mapMass_uniform_nonneg A D d) (mapMass_uniform_le_one A D d)
  have hmain : t * eventMass (uniformMass A) (fun x => D x ∉ centers) ≤
      a * (n : ℝ) := htail.trans h_ent
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  by_contra hgoal
  have hlt : Real.sqrt a < eventMass (uniformMass A) (fun x => D x ∉ centers) :=
    lt_of_not_ge hgoal
  have hmul := mul_lt_mul_of_pos_left hlt ht
  dsimp [t] at hmain hmul
  nlinarith

lemma uncovered_mass_bound {n : ℕ} (A centers : Finset (Cube n)) (D : Cube n → Cube n) (radius : ℝ)
    (b a_sqrt : ℝ)
    (h_uncentered : eventMass (uniformMass A) (fun x => D x ∉ centers) ≤ a_sqrt)
    (h_dist : eventMass (uniformMass A) (fun x => radius < (hDist x (D x) : ℝ)) ≤ b) :
    ((A \ coveredByBalls A centers radius).card : ℝ) ≤ (a_sqrt + b) * (A.card : ℝ) := by
  by_cases hA : A.Nonempty
  · let bad : Cube n → Prop := fun x => x ∈ A ∧ x ∉ coveredByBalls A centers radius
    let uncentered : Cube n → Prop := fun x => D x ∉ centers
    let far : Cube n → Prop := fun x => radius < (hDist x (D x) : ℝ)
    have hbad : ∀ x, bad x → uncentered x ∨ far x := by
      intro x hx
      by_contra h
      push_neg at h
      apply hx.2
      simp only [coveredByBalls, Finset.mem_filter]
      refine ⟨hx.1, D x, ?_, ?_⟩
      · simpa [uncentered] using h.1
      · exact le_of_not_gt (by simpa [far] using h.2)
    have hfilter : A.filter bad = A \ coveredByBalls A centers radius := by
      ext x
      simp [bad]
    have hevent_bad : eventMass (uniformMass A) bad =
        (((A \ coveredByBalls A centers radius).card : ℝ) / (A.card : ℝ)) := by
      rw [eventMass_uniform_eq_card_div A bad, hfilter]
    have hevent : eventMass (uniformMass A) bad ≤ a_sqrt + b := by
      calc
        eventMass (uniformMass A) bad ≤
            eventMass (uniformMass A) (fun x => uncentered x ∨ far x) :=
          eventMass_mono_uniform A bad (fun x => uncentered x ∨ far x) hbad
        _ ≤ eventMass (uniformMass A) uncentered + eventMass (uniformMass A) far :=
          eventMass_union_le A uncentered far
        _ ≤ a_sqrt + b := add_le_add h_uncentered h_dist
    have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
    calc
      ((A \ coveredByBalls A centers radius).card : ℝ) =
          (((A \ coveredByBalls A centers radius).card : ℝ) / (A.card : ℝ)) *
            (A.card : ℝ) := by
        field_simp
      _ = eventMass (uniformMass A) bad * (A.card : ℝ) := by rw [hevent_bad]
      _ ≤ (a_sqrt + b) * (A.card : ℝ) :=
        mul_le_mul_of_nonneg_right hevent (Nat.cast_nonneg A.card)
  · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [hAe]

theorem entropy_labels_to_cover : EntropyLabelsToCoverStatement := by
  intro n A D a b radius hn hA ha hb h_ent h_mass
  let centers := Finset.univ.filter (fun d => Real.exp (- (Real.sqrt a * (n : ℝ))) ≤ mapMass (uniformMass A) D d)
  have hc : centers = Finset.univ.filter (fun d => Real.exp (- (Real.sqrt a * (n : ℝ))) ≤ mapMass (uniformMass A) D d) := rfl
  use centers
  constructor
  · have h1 := centers_card_bound A D a centers hc
    have h2 : Real.exp (Real.sqrt a * (n : ℝ)) ≤ Real.exp ((Real.sqrt a + a + b) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact Nat.cast_nonneg n
    exact le_trans h1 h2
  · have h1 := uncentered_mass_bound A D a ha hn centers hc h_ent
    have h2 := uncovered_mass_bound A centers D radius b (Real.sqrt a) h1 h_mass
    have h3 : (Real.sqrt a + b) * (A.card : ℝ) ≤ (Real.sqrt a + a + b) * (A.card : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact Nat.cast_nonneg A.card
    exact le_trans h2 h3

end AverageHarperStability
