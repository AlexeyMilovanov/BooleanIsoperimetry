import AverageHarperStability.Distribution.Certificate

open scoped BigOperators
open Classical

namespace AverageHarperStability

/-!
# Finite Azuma for calibrated cube innovations

This statement is independent of MGL and entropy stability. It is a finite
probability theorem about a calibrated predictable Bernoulli process.
-/

noncomputable def prefixMismatchSum {n : ℕ} (D : Cube n → Cube n)
    (q : Fin n → Cube n → ℝ) (k : ℕ) (x : Cube n) : ℝ :=
  ∑ t ∈ Finset.filter (·.val < k) Finset.univ,
    ((if mismatchAt D t x then (1 : ℝ) else 0) - q t x)

theorem prefixMismatchSum_n {n : ℕ} (D : Cube n → Cube n)
    (q : Fin n → Cube n → ℝ) (x : Cube n) :
    prefixMismatchSum D q n x = (hDist x (D x) : ℝ) - predictableDistance q x := by
  simp only [prefixMismatchSum, Fin.is_lt, Finset.filter_true, predictableDistance]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_boole]
  norm_cast
  unfold hDist
  congr 1
  ext t
  simp [mismatchAt, symmDiff, Finset.mem_union]
  tauto

theorem finite_centered_mgf_bound
    {ι : Type*} (s : Finset ι) (w Y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmean : ∑ i ∈ s, w i * Y i = 0)
    (hY : ∀ i ∈ s, Y i ∈ Set.Icc (-1 : ℝ) 1) (lambda : ℝ) :
    ∑ i ∈ s, w i * Real.exp (lambda * Y i) ≤
      Real.exp (lambda^2 / 2) * ∑ i ∈ s, w i := by
  have hchord : ∀ i ∈ s, Real.exp (lambda * Y i) ≤
      ((1 + Y i) / 2) * Real.exp lambda +
        ((1 - Y i) / 2) * Real.exp (-lambda) := by
    intro i hi
    have hconv := convexOn_exp.2 (Set.mem_univ lambda) (Set.mem_univ (-lambda))
      (show 0 ≤ (1 + Y i) / 2 by linarith [(hY i hi).1])
      (show 0 ≤ (1 - Y i) / 2 by linarith [(hY i hi).2])
      (show (1 + Y i) / 2 + (1 - Y i) / 2 = 1 by ring)
    convert hconv using 1; simp only [smul_eq_mul]; ring_nf
  calc
    ∑ i ∈ s, w i * Real.exp (lambda * Y i) ≤
        ∑ i ∈ s, w i * (((1 + Y i) / 2) * Real.exp lambda +
          ((1 - Y i) / 2) * Real.exp (-lambda)) := by
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hchord i hi) (hw i hi)
    _ = ∑ i ∈ s, (w i * ((Real.exp lambda + Real.exp (-lambda)) / 2) +
        (w i * Y i) * ((Real.exp lambda - Real.exp (-lambda)) / 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, w i) *
        ((Real.exp lambda + Real.exp (-lambda)) / 2) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hmean]
      ring
    _ = (∑ i ∈ s, w i) * Real.cosh lambda := by rw [Real.cosh_eq]
    _ ≤ (∑ i ∈ s, w i) * Real.exp (lambda^2 / 2) := by
      exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq lambda)
        (Finset.sum_nonneg hw)
    _ = Real.exp (lambda^2 / 2) * ∑ i ∈ s, w i := by ring

theorem prefixAt_eq_of_prefixAt_eq {n : ℕ} {s t : Fin n} {x y : Cube n}
    (hst : s < t) (hxy : prefixAt t x = prefixAt t y) :
    prefixAt s x = prefixAt s y := by
  ext i
  have hmem := Finset.ext_iff.mp hxy i
  simp only [prefixAt, Finset.mem_filter] at hmem ⊢
  constructor
  · rintro ⟨hix, his⟩
    exact ⟨(hmem.mp ⟨hix, lt_trans his hst⟩).1, his⟩
  · rintro ⟨hiy, his⟩
    exact ⟨(hmem.mpr ⟨hiy, lt_trans his hst⟩).1, his⟩

theorem prefixMismatchSum_eq_of_prefixAt_eq
    {n : ℕ} {mu : Cube n → ℝ} {p err : ℝ}
    (C : TrackingCertificate mu p err) (t : Fin n) (x y : Cube n)
    (hxy : prefixAt t x = prefixAt t y) :
    prefixMismatchSum C.D C.q t.val x = prefixMismatchSum C.D C.q t.val y := by
  unfold prefixMismatchSum
  apply Finset.sum_congr rfl
  intro s hs
  have hst : s < t := by simpa using (Finset.mem_filter.mp hs).2
  have hprefix : prefixAt s x = prefixAt s y :=
    prefixAt_eq_of_prefixAt_eq hst hxy
  have hq : C.q s x = C.q s y := C.calibrated.1 s x y hprefix
  have hD : s ∈ C.D x ↔ s ∈ C.D y := C.adapted s x y hprefix
  have hbit : s ∈ x ↔ s ∈ y := by
    have hmem := Finset.ext_iff.mp hxy s
    simpa [prefixAt, hst] using hmem
  rw [hq]
  congr 1
  have hm : mismatchAt C.D s x ↔ mismatchAt C.D s y := by
    unfold mismatchAt
    tauto
  by_cases hmx : mismatchAt C.D s x
  · rw [if_pos hmx, if_pos (hm.mp hmx)]
  · rw [if_neg hmx, if_neg (fun h => hmx (hm.mpr h))]

theorem calibrated_mismatch_centered_on_fiber
    {n : ℕ} {mu : Cube n → ℝ} {p err : ℝ}
    (C : TrackingCertificate mu p err) (t : Fin n) (z : Cube n) :
    ∑ x ∈ Finset.filter (fun x => prefixAt t x = prefixAt t z) Finset.univ,
        mu x * ((if mismatchAt C.D t x then (1 : ℝ) else 0) - C.q t x) = 0 := by
  let s := Finset.filter (fun x => prefixAt t x = prefixAt t z) Finset.univ
  have hq : ∀ x ∈ s, C.q t x = C.q t z := by
    intro x hx
    exact C.calibrated.1 t x z (Finset.mem_filter.mp hx).2
  have hprefix : (∑ x ∈ s, mu x) =
      eventMass mu (fun x => prefixAt t x = prefixAt t z) := by
    unfold eventMass s
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hpref : prefixAt t x = prefixAt t z <;> simp [hpref]
  have hmismatch :
      (∑ x ∈ s, mu x * (if mismatchAt C.D t x then (1 : ℝ) else 0)) =
        eventMass mu (fun x => prefixAt t x = prefixAt t z ∧ mismatchAt C.D t x) := by
    unfold eventMass s
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hpref : prefixAt t x = prefixAt t z <;>
      by_cases hmis : mismatchAt C.D t x <;> simp [hpref, hmis]
  rw [show (∑ x ∈ s, mu x *
      ((if mismatchAt C.D t x then (1 : ℝ) else 0) - C.q t x)) =
      (∑ x ∈ s, mu x * (if mismatchAt C.D t x then (1 : ℝ) else 0)) -
        C.q t z * ∑ x ∈ s, mu x by
      rw [Finset.sum_congr rfl fun x hx => show
        mu x * ((if mismatchAt C.D t x then (1 : ℝ) else 0) - C.q t x) =
          mu x * (if mismatchAt C.D t x then (1 : ℝ) else 0) - C.q t z * mu x by
            rw [hq x hx]; ring,
        Finset.sum_sub_distrib, Finset.mul_sum]]
  rw [hmismatch, hprefix, C.calibrated.2 t z]
  ring

theorem prefixMismatchSum_succ {n : ℕ} (D : Cube n → Cube n)
    (q : Fin n → Cube n → ℝ) (k : ℕ) (hk : k < n) (x : Cube n) :
    prefixMismatchSum D q (k + 1) x = prefixMismatchSum D q k x +
      ((if mismatchAt D ⟨k, hk⟩ x then (1 : ℝ) else 0) - q ⟨k, hk⟩ x) := by
  let t : Fin n := ⟨k, hk⟩
  have hfilter : Finset.filter (fun s : Fin n => s.val < k + 1) Finset.univ =
      insert t (Finset.filter (fun s : Fin n => s.val < k) Finset.univ) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hs
      by_cases hsk : s.val < k
      · exact Or.inr hsk
      · left
        apply Fin.ext
        simp only [t]
        omega
    · rintro (rfl | hs)
      · simp only [t]
        omega
      · omega
  have ht_not : t ∉ Finset.filter (fun s : Fin n => s.val < k) Finset.univ := by
    simp [t]
  unfold prefixMismatchSum
  rw [hfilter, Finset.sum_insert ht_not]
  simp only [t]
  ring

theorem azuma_mgf_step {n : ℕ} {mu : Cube n → ℝ} {p err : ℝ}
    (hmu : IsLaw mu) (C : TrackingCertificate mu p err)
    (lambda : ℝ) (k : ℕ) (hk : k < n) :
    ∑ x, mu x * Real.exp (lambda * prefixMismatchSum C.D C.q (k + 1) x) ≤
      Real.exp (lambda^2 / 2) *
        ∑ x, mu x * Real.exp (lambda * prefixMismatchSum C.D C.q k x) := by
  let t : Fin n := ⟨k, hk⟩
  let Y : Cube n → ℝ := fun x =>
    (if mismatchAt C.D t x then (1 : ℝ) else 0) - C.q t x
  let w : Cube n → ℝ := fun x =>
    mu x * Real.exp (lambda * prefixMismatchSum C.D C.q k x)
  calc
    ∑ x, mu x * Real.exp (lambda * prefixMismatchSum C.D C.q (k + 1) x) =
        ∑ j : Cube n, ∑ x ∈ Finset.univ with prefixAt t x = j,
          w x * Real.exp (lambda * Y x) := by
      rw [Finset.sum_fiberwise]
      apply Finset.sum_congr rfl
      intro x hx
      rw [prefixMismatchSum_succ C.D C.q k hk x]
      simp only [w, Y, t]
      rw [show lambda * (prefixMismatchSum C.D C.q k x +
          ((if mismatchAt C.D ⟨k, hk⟩ x then (1 : ℝ) else 0) - C.q ⟨k, hk⟩ x)) =
          lambda * prefixMismatchSum C.D C.q k x +
            lambda * ((if mismatchAt C.D ⟨k, hk⟩ x then (1 : ℝ) else 0) -
              C.q ⟨k, hk⟩ x) by ring, Real.exp_add]
      ring
    _ ≤ ∑ j : Cube n, Real.exp (lambda^2 / 2) *
          ∑ x ∈ Finset.univ with prefixAt t x = j, w x := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hex : ∃ z : Cube n, prefixAt t z = j
      · obtain ⟨z, hz⟩ := hex
        let s := Finset.filter (fun x => prefixAt t x = j) Finset.univ
        apply finite_centered_mgf_bound s w Y
        · intro x hx
          exact mul_nonneg (hmu.1 x) (Real.exp_nonneg _)
        · have hprefix : ∀ x ∈ s,
              prefixMismatchSum C.D C.q k x = prefixMismatchSum C.D C.q k z := by
            intro x hx
            apply prefixMismatchSum_eq_of_prefixAt_eq C t
            exact (Finset.mem_filter.mp hx).2.trans hz.symm
          rw [show (∑ x ∈ s, w x * Y x) =
              Real.exp (lambda * prefixMismatchSum C.D C.q k z) *
                ∑ x ∈ s, mu x * Y x by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            simp only [w]
            rw [hprefix x hx]
            ring]
          have hcenter := calibrated_mismatch_centered_on_fiber C t z
          simp only [Y, s, hz] at hcenter ⊢
          rw [hcenter, mul_zero]
        · intro x hx
          simp only [Y]
          by_cases hm : mismatchAt C.D t x
          · rw [if_pos hm]
            constructor <;> linarith [C.q_nonneg t x, C.q_le_one t x]
          · rw [if_neg hm]
            constructor <;> linarith [C.q_nonneg t x, C.q_le_one t x]
      · have hs : Finset.filter (fun x => prefixAt t x = j) Finset.univ = ∅ := by
          ext x
          constructor
          · intro hx
            exact (hex ⟨x, (Finset.mem_filter.mp hx).2⟩).elim
          · intro hx
            simp at hx
        simp only [hs, Finset.sum_empty, mul_zero, le_refl]
    _ = Real.exp (lambda^2 / 2) *
        ∑ x, mu x * Real.exp (lambda * prefixMismatchSum C.D C.q k x) := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise]

theorem azuma_mgf_bound {n : ℕ} {mu : Cube n → ℝ} {p err : ℝ}
    (hmu : IsLaw mu) (C : TrackingCertificate mu p err) (lambda : ℝ) (k : ℕ) (hk : k ≤ n) :
    ∑ x, mu x * Real.exp (lambda * prefixMismatchSum C.D C.q k x) ≤
      Real.exp (k * lambda^2 / 2) := by
  induction k with
  | zero =>
      simpa [prefixMismatchSum] using hmu.2.le
  | succ k ih =>
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hprev := ih (Nat.le_of_lt hkn)
      calc
        ∑ x, mu x * Real.exp
            (lambda * prefixMismatchSum C.D C.q (k + 1) x) ≤
            Real.exp (lambda^2 / 2) *
              ∑ x, mu x * Real.exp
                (lambda * prefixMismatchSum C.D C.q k x) :=
          azuma_mgf_step hmu C lambda k hkn
        _ ≤ Real.exp (lambda^2 / 2) * Real.exp (k * lambda^2 / 2) :=
          mul_le_mul_of_nonneg_left hprev (Real.exp_nonneg _)
        _ = Real.exp (((k : ℝ) + 1) * lambda^2 / 2) := by
          rw [← Real.exp_add]
          apply le_antisymm
          · apply Real.exp_le_exp.mpr
            ring_nf
            rfl
          · apply Real.exp_le_exp.mpr
            ring_nf
            rfl
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * lambda^2 / 2) := by norm_num

theorem azuma_exp_markov {n : ℕ} {mu : Cube n → ℝ} {Z : Cube n → ℝ}
    {t lambda : ℝ} [DecidablePred fun x => t < Z x]
    (hmu : IsLaw mu) (hlambda : 0 ≤ lambda) :
    eventMass mu (fun x => t < Z x) ≤
      Real.exp (-lambda * t) * ∑ x, mu x * Real.exp (lambda * Z x) := by
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · have hexp : 1 ≤ Real.exp (lambda * (Z x - t)) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ Z x - t := sub_nonneg.mpr (le_of_lt hx)
      positivity
    calc
      mu x = mu x * 1 := by ring
      _ ≤ mu x * Real.exp (lambda * (Z x - t)) :=
        mul_le_mul_of_nonneg_left hexp (hmu.1 x)
      _ = Real.exp (-lambda * t) * (mu x * Real.exp (lambda * Z x)) := by
        rw [show lambda * (Z x - t) = -lambda * t + lambda * Z x by ring,
          Real.exp_add]
        ring
  · exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hmu.1 x) (Real.exp_nonneg _))

/-- A calibrated tracking certificate has the corrected finite-`n` innovation
tail. The normalization is intentionally the looser `exp(-lambda^2 n / 2)`
form used in the mathematical proof, giving exactly `1/n` at the displayed
threshold. -/
theorem tracking_certificate_azuma
    {n : ℕ} {mu : Cube n → ℝ} {p err : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (C : TrackingCertificate mu p err) :
    eventMass mu (fun x =>
      Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) <
        (hDist x (C.D x) : ℝ) - predictableDistance C.q x) ≤
      1 / (n : ℝ) := by
  set lambda := Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))
  set t := lambda * (n : ℝ)
  have hlambda : 0 ≤ lambda := Real.sqrt_nonneg _
  have h_markov := azuma_exp_markov (Z := fun x => (hDist x (C.D x) : ℝ) - predictableDistance C.q x) (t := t) hmu hlambda
  have h_mgf := azuma_mgf_bound hmu C lambda n (le_refl n)
  have h_sum_eq : (∑ x, mu x * Real.exp (lambda * ((hDist x (C.D x) : ℝ) - predictableDistance C.q x))) =
    ∑ x, mu x * Real.exp (lambda * prefixMismatchSum C.D C.q n x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [prefixMismatchSum_n]
  rw [h_sum_eq] at h_markov
  have h_bound : eventMass mu (fun x => t < (hDist x (C.D x) : ℝ) - predictableDistance C.q x) ≤
    Real.exp (-lambda * t) * Real.exp ((n : ℝ) * lambda^2 / 2) := by
    apply le_trans h_markov
    apply mul_le_mul_of_nonneg_left h_mgf (Real.exp_nonneg _)
  have h_exp_add : Real.exp (-lambda * t) * Real.exp ((n : ℝ) * lambda^2 / 2) = Real.exp (-lambda * t + (n : ℝ) * lambda^2 / 2) := by
    rw [← Real.exp_add]
  rw [h_exp_add] at h_bound
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn
  have h_lambda_sq : lambda ^ 2 = 2 * Real.log (n : ℝ) / (n : ℝ) := by
    apply Real.sq_sqrt
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    positivity
  have h_algebra : -lambda * t + (n : ℝ) * lambda^2 / 2 = - Real.log (n : ℝ) := by
    calc
      -lambda * t + (n : ℝ) * lambda^2 / 2 = -lambda * (lambda * (n : ℝ)) + (n : ℝ) * lambda^2 / 2 := rfl
      _ = - (lambda^2 * (n : ℝ)) / 2 := by ring
      _ = - ((2 * Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ)) / 2 := by rw [h_lambda_sq]
      _ = - (2 * Real.log (n : ℝ)) / 2 := by rw [div_mul_cancel₀ _ (ne_of_gt hn_pos)]
      _ = - Real.log (n : ℝ) := by ring
  rw [h_algebra] at h_bound
  have h_final : Real.exp (- Real.log (n : ℝ)) = 1 / (n : ℝ) := by
    rw [Real.exp_neg, Real.exp_log hn_pos]
    exact inv_eq_one_div _
  exact le_trans h_bound (le_of_eq h_final)

end AverageHarperStability
