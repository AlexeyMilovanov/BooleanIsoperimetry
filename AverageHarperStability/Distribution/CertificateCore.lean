import AverageHarperStability.Distribution.Slack
import AverageHarperStability.Distribution.EntropyChain
import AverageHarperStability.Interface.Statements

open scoped BigOperators
open Filter Topology Set Classical

namespace AverageHarperStability

attribute [local instance] Classical.propDecidable

/-!
# Predictable tracking certificate

This file isolates the entropy/MGL/tracking part of the distribution theorem.
It deliberately stops before martingale concentration and final tail assembly.
-/


/-- A center is adapted when its coordinate `t` depends only on the prefix
strictly before `t`. -/
def IsAdaptedCenter {n : ℕ} (D : Cube n → Cube n) : Prop :=
  ∀ (t : Fin n) (x y : Cube n), prefixAt t x = prefixAt t y →
    (t ∈ D x ↔ t ∈ D y)

/-- The input bit and center bit disagree at coordinate `t`. -/
def mismatchAt {n : ℕ} (D : Cube n → Cube n) (t : Fin n) (x : Cube n) : Prop :=
  (t ∈ x ∧ t ∉ D x) ∨ (t ∉ x ∧ t ∈ D x)

/-- Sum of the predictable conditional mismatch probabilities. -/
noncomputable def predictableDistance {n : ℕ} (q : Fin n → Cube n → ℝ)
    (x : Cube n) : ℝ :=
  ∑ t, q t x

/-- `q t` is prefix-measurable and is the exact conditional mismatch
probability on every prefix fiber (including the totalized zero-mass fibers). -/
def CalibratesMismatch {n : ℕ} (mu : Cube n → ℝ) (D : Cube n → Cube n)
    (q : Fin n → Cube n → ℝ) : Prop :=
  (∀ (t : Fin n) (x y : Cube n), prefixAt t x = prefixAt t y → q t x = q t y) ∧
  ∀ (t : Fin n) (x : Cube n),
    q t x * eventMass mu (fun y => prefixAt t y = prefixAt t x) =
      eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ mismatchAt D t y)

/-- The exact output needed from L0--L9 before applying Azuma.

`off` is a nonnegative off-flat budget. Its expectation is quadratic in the
final error, so Markov at threshold `(err/2)n` costs at most `err/2` mass.
-/
structure TrackingCertificate {n : ℕ} (mu : Cube n → ℝ) (p err : ℝ) where
  D : Cube n → Cube n
  q : Fin n → Cube n → ℝ
  off : Cube n → ℝ
  adapted : IsAdaptedCenter D
  calibrated : CalibratesMismatch mu D q
  q_nonneg : ∀ t x, 0 ≤ q t x
  q_le_one : ∀ t x, q t x ≤ 1
  off_nonneg : ∀ x, 0 ≤ off x
  label_entropy : entropy (mapMass mu D) ≤ err * (n : ℝ)
  predictable_bound : ∀ x,
    predictableDistance q x ≤ (p + err / 2) * (n : ℝ) + off x
  off_mean : ∑ x, mu x * off x ≤ (err ^ 2 / 4) * (n : ℝ)


/-- The adapted center sets coordinate `t` to 1 if `condProbOne > 1/2`. -/
noncomputable def adaptedCenter {n : ℕ} (mu : Cube n → ℝ) (x : Cube n) : Cube n :=
  (Finset.univ : Finset (Fin n)).filter (fun t => 1 / 2 < condProbOne mu t x)

/-- The conditional probability of mismatch at step `t`. -/
noncomputable def conditionalMismatch {n : ℕ} (mu : Cube n → ℝ) (t : Fin n) (x : Cube n) : ℝ :=
  if 1 / 2 < condProbOne mu t x then 1 - condProbOne mu t x else condProbOne mu t x

/-- Conditional entropy `F_t = Hb(p_t)`. -/
noncomputable def condEntropy {n : ℕ} (mu : Cube n → ℝ) (t : Fin n) (x : Cube n) : ℝ :=
  Hb (condProbOne mu t x)

/-- The nonnegative excess of the predictable mismatch sum over its target.

The entropy/Jensen argument is used only to bound the mean of this quantity;
the certificate's pointwise predictable bound then holds by construction. -/
noncomputable def offFlatBudget {n : ℕ} (err : ℝ) (mu : Cube n → ℝ) (x : Cube n) : ℝ :=
  max 0 (predictableDistance (conditionalMismatch mu) x -
    (hbInv (entropyRate n mu) + err / 2) * (n : ℝ))


lemma adaptedCenter_isAdapted {n : ℕ} (mu : Cube n → ℝ) :
    IsAdaptedCenter (adaptedCenter mu) := by
  unfold IsAdaptedCenter
  intro t x y h_pref
  unfold adaptedCenter
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [condProbOne_depends_only_on_prefix mu t x y h_pref]

lemma eventMass_nonneg {n : ℕ} {mu : Cube n → ℝ} (hmu : IsLaw mu) (E : Cube n → Prop) :
    0 ≤ eventMass mu E := by
  unfold eventMass
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hmu.1 x
  · exact le_refl 0

lemma eventMass_split {n : ℕ} (mu : Cube n → ℝ) (t : Fin n) (x : Cube n) :
    prefixMass mu t x = eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) +
      eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∉ y) := by
  unfold prefixMass eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h1 : prefixAt t y = prefixAt t x
  · by_cases h2 : t ∈ y
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

lemma eventMass_le_eventMass {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) (E F : Cube n → Prop) (h : ∀ x, E x → F x) :
    eventMass mu E ≤ eventMass mu F := by
  unfold eventMass
  apply Finset.sum_le_sum
  intro x _
  by_cases hE : E x
  · by_cases hF : F x
    · simp [hE, hF]
    · exfalso; exact hF (h x hE)
  · by_cases hF : F x
    · simp [hE, hF]; exact hmu.1 x
    · simp [hE, hF]

lemma conditionalMismatch_calibrates {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    CalibratesMismatch mu (adaptedCenter mu) (conditionalMismatch mu) := by
  unfold CalibratesMismatch
  apply And.intro
  · intro t x y h_pref
    unfold conditionalMismatch
    rw [condProbOne_depends_only_on_prefix mu t x y h_pref]
  · intro t x
    unfold conditionalMismatch
    have hd : IsAdaptedCenter (adaptedCenter mu) := adaptedCenter_isAdapted mu
    by_cases h_cond : 1 / 2 < condProbOne mu t x
    · rw [if_pos h_cond]
      have htD : t ∈ adaptedCenter mu x := by
        unfold adaptedCenter
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_cond
      have h_cpo : condProbOne mu t x * prefixMass mu t x = eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) := by
        unfold condProbOne
        by_cases h_pm : prefixMass mu t x = 0
        · rw [if_pos h_pm, zero_mul]
          have h_le : eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) ≤ prefixMass mu t x := by
            apply eventMass_le_eventMass mu hmu
            intro y hy; exact hy.1
          have h_ge : 0 ≤ eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) := eventMass_nonneg hmu _
          rw [h_pm] at h_le
          linarith
        · rw [if_neg h_pm, div_mul_cancel₀ _ h_pm]
      have h_LHS : (1 - condProbOne mu t x) * prefixMass mu t x = eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∉ y) := by
        rw [sub_mul, one_mul, h_cpo]
        have h_split := eventMass_split mu t x
        linarith
      have h_rewrite_LHS : (1 - condProbOne mu t x) * eventMass mu (fun y => prefixAt t y = prefixAt t x) = (1 - condProbOne mu t x) * prefixMass mu t x := rfl
      rw [h_rewrite_LHS, h_LHS]
      unfold eventMass
      apply Finset.sum_congr rfl
      intro y _
      by_cases h1 : prefixAt t y = prefixAt t x
      · have h_ty : t ∈ adaptedCenter mu y ↔ t ∈ adaptedCenter mu x := hd t y x h1
        have htDy : t ∈ adaptedCenter mu y := h_ty.mpr htD
        unfold mismatchAt
        by_cases h2 : t ∈ y
        · simp [h1, h2, htDy]
        · simp [h1, h2, htDy]
      · simp [h1]
    · rw [if_neg h_cond]
      have htD : t ∉ adaptedCenter mu x := by
        unfold adaptedCenter
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_cond
      have h_cpo : condProbOne mu t x * prefixMass mu t x = eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) := by
        unfold condProbOne
        by_cases h_pm : prefixMass mu t x = 0
        · rw [if_pos h_pm, zero_mul]
          have h_le : eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) ≤ prefixMass mu t x := by
            apply eventMass_le_eventMass mu hmu
            intro y hy; exact hy.1
          have h_ge : 0 ≤ eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) := eventMass_nonneg hmu _
          rw [h_pm] at h_le
          linarith
        · rw [if_neg h_pm, div_mul_cancel₀ _ h_pm]
      have h_rewrite_LHS : condProbOne mu t x * eventMass mu (fun y => prefixAt t y = prefixAt t x) = condProbOne mu t x * prefixMass mu t x := rfl
      rw [h_rewrite_LHS, h_cpo]
      unfold eventMass
      apply Finset.sum_congr rfl
      intro y _
      by_cases h1 : prefixAt t y = prefixAt t x
      · have h_ty : t ∈ adaptedCenter mu y ↔ t ∈ adaptedCenter mu x := hd t y x h1
        have htDy : t ∉ adaptedCenter mu y := mt h_ty.mp htD
        unfold mismatchAt
        by_cases h2 : t ∈ y
        · simp [h1, h2, htDy]
        · simp [h1, h2, htDy]
      · simp [h1]

lemma conditionalMismatch_nonneg {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) (t : Fin n) (x : Cube n) :
    0 ≤ conditionalMismatch mu t x := by
  unfold conditionalMismatch
  split_ifs with h
  · linarith [condProbOne_le_one mu hmu t x]
  · exact condProbOne_nonneg mu hmu t x

lemma conditionalMismatch_le_one {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) (t : Fin n) (x : Cube n) :
    conditionalMismatch mu t x ≤ 1 := by
  have _ := hmu
  unfold conditionalMismatch
  split_ifs with h
  · linarith [condProbOne_nonneg mu hmu t x]
  · linarith [condProbOne_le_one mu hmu t x]

lemma offFlatBudget_nonneg {n : ℕ} (err : ℝ) (mu : Cube n → ℝ) (x : Cube n) :
    0 ≤ offFlatBudget err mu x := by
  unfold offFlatBudget
  exact le_max_left _ _

/-- The per-step conditional entropy equals binary entropy of the conditional
mismatch probability. Since `Hb` is symmetric about `1/2`
(`Real.binEntropy_one_sub`), folding the conditional probability to its
mismatch branch (`1 - p` when `p > 1/2`, else `p`) leaves the entropy
unchanged. -/
lemma condEntropy_eq_Hb_conditionalMismatch {n : ℕ} (mu : Cube n → ℝ)
    (t : Fin n) (x : Cube n) :
    condEntropy mu t x = Hb (conditionalMismatch mu t x) := by
  unfold condEntropy conditionalMismatch
  split_ifs with h
  · rw [Hb, Hb, Real.binEntropy_one_sub]
  · rfl


noncomputable def delta0_val (tau zeta : ℝ) : ℝ :=
  (zeta * tau * (1 - 2 * tau))^2

theorem delta0_val_pos {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) :
    0 < delta0_val tau zeta := by
  have _ := hz1
  have hchannel : 0 < 1 - 2 * tau := by
    nlinarith
  unfold delta0_val
  positivity

/-- A deliberately conservative modulus for the assembled distribution theorem.
The eighth root absorbs the quarter-root tail and the logarithmic label-entropy
losses in the corrected Corollary 10; the channel/window factor is fixed once
`tau` and `zeta` are fixed. -/
noncomputable def err_val (tau zeta delta : ℝ) : ℝ :=
  (1 + 1 / (zeta * tau * (1 - 2 * tau)) ^ 2) *
    Real.sqrt (Real.sqrt (Real.sqrt delta))

theorem err_val_tendsto {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) :
    Tendsto (err_val tau zeta) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have _ := ht0
  have _ := ht1
  have _ := hz0
  have _ := hz1
  have hsqrt : Tendsto (fun delta : ℝ =>
      Real.sqrt (Real.sqrt (Real.sqrt delta)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hcontinuous : Continuous (fun delta : ℝ =>
        Real.sqrt (Real.sqrt (Real.sqrt delta))) :=
      Real.continuous_sqrt.comp
        (Real.continuous_sqrt.comp Real.continuous_sqrt)
    have hsqrt' : Tendsto (fun delta : ℝ =>
        Real.sqrt (Real.sqrt (Real.sqrt delta))) (nhds 0) (nhds 0) := by
      simpa using (hcontinuous.continuousAt (x := (0 : ℝ))).tendsto
    exact hsqrt'.mono_left inf_le_left
  unfold err_val
  (convert tendsto_const_nhds.mul hsqrt using 1; norm_num)

theorem err_val_pos {tau zeta delta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) (hd0 : 0 < delta) :
    0 < err_val tau zeta delta := by
  have _ := ht0
  have _ := ht1
  have _ := hz0
  have _ := hz1
  unfold err_val
  positivity

theorem quarterRoot_le_err_val {tau zeta delta : ℝ}
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    (hd0 : 0 < delta) (hd1 : delta ≤ delta0_val tau zeta) :
    Real.sqrt (Real.sqrt delta) ≤ err_val tau zeta delta := by
  have _ := hd0
  have htau : 0 < 1 - 2 * tau := by linarith
  have hX : 0 < zeta * tau * (1 - 2 * tau) := by positivity
  have hX1 : zeta * tau * (1 - 2 * tau) ≤ 1 := by
    calc
      zeta * tau * (1 - 2 * tau) ≤ (1 / 4) * (1 / 2) * 1 := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact hz1
          · exact le_of_lt ht1
          · exact le_of_lt ht0
          · norm_num
        · linarith
        · positivity
        · positivity
      _ ≤ 1 := by norm_num
  unfold err_val
  have hd : Real.sqrt (Real.sqrt (Real.sqrt delta)) ≤ 1 := by
    have hd1' : delta ≤ 1 := by
      calc
        delta ≤ delta0_val tau zeta := hd1
        _ = (zeta * tau * (1 - 2 * tau))^2 := rfl
        _ ≤ 1^2 := by gcongr
        _ = 1 := by norm_num
    have h1 : Real.sqrt delta ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hd1'
    rw [Real.sqrt_one] at h1
    have h2 : Real.sqrt (Real.sqrt delta) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_one] at h2
    have h3 : Real.sqrt (Real.sqrt (Real.sqrt delta)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_one] at h3
    exact h3
  have hd_pos : 0 ≤ Real.sqrt (Real.sqrt (Real.sqrt delta)) := Real.sqrt_nonneg _
  have hd_pos_inner : 0 ≤ Real.sqrt (Real.sqrt delta) := Real.sqrt_nonneg _
  have h_bound : Real.sqrt (Real.sqrt (Real.sqrt delta)) ≤ 1 + 1 / (zeta * tau * (1 - 2 * tau))^2 := by
    have hp : 0 ≤ 1 / (zeta * tau * (1 - 2 * tau))^2 := by positivity
    linarith
  have h_mul := mul_le_mul_of_nonneg_right h_bound hd_pos
  have h_lhs : Real.sqrt (Real.sqrt (Real.sqrt delta)) * Real.sqrt (Real.sqrt (Real.sqrt delta)) = Real.sqrt (Real.sqrt delta) := by
    exact Real.mul_self_sqrt hd_pos_inner
  rw [h_lhs] at h_mul
  exact h_mul

theorem delta_le_delta0_of_err_val_lt_log_two
    {tau zeta delta err : ℝ}
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    (hd0 : 0 < delta)
    (herr : err_val tau zeta delta ≤ err)
    (hsmall : err < Real.log 2) :
    delta ≤ delta0_val tau zeta := by
  have herr_bound : err_val tau zeta delta < Real.log 2 := herr.trans_lt hsmall
  have hlog2 : Real.log 2 ≤ 1 := by
    apply Real.log_le_sub_one_of_pos (by norm_num) |>.trans
    norm_num
  have herr_le_one : err_val tau zeta delta < 1 := herr_bound.trans_le hlog2
  have hX : 0 < zeta * tau * (1 - 2 * tau) := by
    have h1 : 0 < 1 - 2 * tau := by linarith
    positivity
  have hX1 : zeta * tau * (1 - 2 * tau) ≤ 1 := by
    calc
      zeta * tau * (1 - 2 * tau) ≤ (1 / 4) * (1 / 2) * 1 := by
        have h1 : 0 ≤ 1 - 2 * tau := by linarith
        apply mul_le_mul
        · apply mul_le_mul hz1 ht1.le ht0.le (by norm_num)
        · linarith
        · linarith
        · norm_num
      _ ≤ 1 := by norm_num
  unfold err_val at herr_le_one
  unfold delta0_val
  have hpos : 0 ≤ Real.sqrt (Real.sqrt (Real.sqrt delta)) := Real.sqrt_nonneg _
  have hp : 0 < 1 / (zeta * tau * (1 - 2 * tau))^2 := by positivity
  have h_add : 1 / (zeta * tau * (1 - 2 * tau))^2 < 1 + 1 / (zeta * tau * (1 - 2 * tau))^2 := by linarith
  have h1 : 1 / (zeta * tau * (1 - 2 * tau))^2 * Real.sqrt (Real.sqrt (Real.sqrt delta)) ≤
    (1 + 1 / (zeta * tau * (1 - 2 * tau))^2) * Real.sqrt (Real.sqrt (Real.sqrt delta)) := by
    apply mul_le_mul_of_nonneg_right h_add.le hpos
  have h2 : 1 / (zeta * tau * (1 - 2 * tau))^2 * Real.sqrt (Real.sqrt (Real.sqrt delta)) < 1 := h1.trans_lt herr_le_one
  have h3 : Real.sqrt (Real.sqrt (Real.sqrt delta)) < (zeta * tau * (1 - 2 * tau))^2 := by
    have hX_pos : 0 < (zeta * tau * (1 - 2 * tau))^2 := by positivity
    have heq : 1 / (zeta * tau * (1 - 2 * tau))^2 * Real.sqrt (Real.sqrt (Real.sqrt delta)) = Real.sqrt (Real.sqrt (Real.sqrt delta)) / (zeta * tau * (1 - 2 * tau))^2 := by ring
    rw [heq] at h2
    rwa [div_lt_one₀ hX_pos] at h2
  have h4 : Real.sqrt (Real.sqrt (Real.sqrt delta)) ≤ (zeta * tau * (1 - 2 * tau))^2 := h3.le
  have h5 : (zeta * tau * (1 - 2 * tau))^2 ≤ 1 := by
    nlinarith
  have h6 : Real.sqrt (Real.sqrt (Real.sqrt delta)) ≤ 1 := h4.trans h5
  have h7 : Real.sqrt (Real.sqrt delta) ≤ 1 := by
    calc
      Real.sqrt (Real.sqrt delta) = Real.sqrt (Real.sqrt (Real.sqrt delta)) * Real.sqrt (Real.sqrt (Real.sqrt delta)) := (Real.mul_self_sqrt (Real.sqrt_nonneg (Real.sqrt delta))).symm
      _ ≤ 1 * 1 := mul_le_mul h6 h6 hpos (by norm_num)
      _ = 1 := mul_one 1
  have h8 : Real.sqrt delta ≤ 1 := by
    calc
      Real.sqrt delta = Real.sqrt (Real.sqrt delta) * Real.sqrt (Real.sqrt delta) := (Real.mul_self_sqrt (Real.sqrt_nonneg delta)).symm
      _ ≤ 1 * 1 := mul_le_mul h7 h7 (Real.sqrt_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  have h9 : delta ≤ 1 := by
    calc
      delta = Real.sqrt delta * Real.sqrt delta := (Real.mul_self_sqrt hd0.le).symm
      _ ≤ 1 * 1 := mul_le_mul h8 h8 (Real.sqrt_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  have hd : delta ≤ Real.sqrt (Real.sqrt (Real.sqrt delta)) := by
    have h_le1 : delta ≤ Real.sqrt delta := by
      calc
        delta = Real.sqrt delta * Real.sqrt delta := (Real.mul_self_sqrt hd0.le).symm
        _ ≤ Real.sqrt delta * 1 := mul_le_mul_of_nonneg_left h8 (Real.sqrt_nonneg _)
        _ = Real.sqrt delta := mul_one _
    have h_le2 : Real.sqrt delta ≤ Real.sqrt (Real.sqrt delta) := by
      calc
        Real.sqrt delta = Real.sqrt (Real.sqrt delta) * Real.sqrt (Real.sqrt delta) := (Real.mul_self_sqrt (Real.sqrt_nonneg delta)).symm
        _ ≤ Real.sqrt (Real.sqrt delta) * 1 := mul_le_mul_of_nonneg_left h7 (Real.sqrt_nonneg _)
        _ = Real.sqrt (Real.sqrt delta) := mul_one _
    have h_le3 : Real.sqrt (Real.sqrt delta) ≤ Real.sqrt (Real.sqrt (Real.sqrt delta)) := by
      calc
        Real.sqrt (Real.sqrt delta) = Real.sqrt (Real.sqrt (Real.sqrt delta)) * Real.sqrt (Real.sqrt (Real.sqrt delta)) := (Real.mul_self_sqrt (Real.sqrt_nonneg (Real.sqrt delta))).symm
        _ ≤ Real.sqrt (Real.sqrt (Real.sqrt delta)) * 1 := mul_le_mul_of_nonneg_left h6 hpos
        _ = Real.sqrt (Real.sqrt (Real.sqrt delta)) := mul_one _
    linarith
  exact hd.trans h4

/-- The predictable mismatch distance never exceeds its `(p + err/2) n` target
plus the off-flat budget. Immediate from the definition of `offFlatBudget` as the
positive part of exactly that excess (`a ≤ b + max 0 (a - b)`); this discharges
the certificate's `predictable_bound` field by construction, so `off_mean` carries
the entire quantitative content of the mismatch cap. -/
lemma predictableDistance_le_target_add_offFlatBudget {n : ℕ} (err : ℝ)
    (mu : Cube n → ℝ) (x : Cube n) :
    predictableDistance (conditionalMismatch mu) x ≤
      (hbInv (entropyRate n mu) + err / 2) * (n : ℝ) + offFlatBudget err mu x := by
  have h : predictableDistance (conditionalMismatch mu) x
      - (hbInv (entropyRate n mu) + err / 2) * (n : ℝ) ≤ offFlatBudget err mu x := by
    unfold offFlatBudget
    exact le_max_right _ _
  linarith

/-- Entropy of a pushforward label law is nonnegative. Proved locally because the
general `entropy_nonneg` / `mapMass_isLaw` lemmas live downstream in `Tracking.lean`.
Each pushforward mass `mapMass mu D d = ∑_{x : D x = d} mu x` lies in `[0,1]`, so its
`negMulLog` is nonnegative. -/
lemma entropy_mapMass_nonneg {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (D : Cube n → Cube n) :
    0 ≤ entropy (mapMass mu D) := by
  unfold entropy
  apply Finset.sum_nonneg
  intro d _
  apply Real.negMulLog_nonneg
  · unfold mapMass
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hmu.1 x
    · exact le_refl 0
  · unfold mapMass
    calc (∑ x, if D x = d then mu x else 0) ≤ ∑ x, mu x := by
          apply Finset.sum_le_sum
          intro x _
          split_ifs
          · exact le_refl _
          · exact hmu.1 x
      _ = 1 := hmu.2

/-- `hbInv x = 0` for nonpositive `x`: the defining set is all of `[0,1/2]`. -/
lemma hbInv_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : hbInv x = 0 := by
  unfold hbInv
  have hset : {p : ℝ | p ∈ Icc (0:ℝ) (1/2) ∧ x ≤ Hb p} = Icc 0 (1/2) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hp, _⟩; exact hp
    · intro hp
      refine ⟨hp, ?_⟩
      have hnn : 0 ≤ Hb p := by
        simp only [Hb]
        exact Real.binEntropy_nonneg hp.1 (le_trans hp.2 (by norm_num))
      linarith
  rw [hset]
  exact (isGLB_Icc (by norm_num : (0:ℝ) ≤ 1/2)).csInf_eq (Set.nonempty_Icc.mpr (by norm_num))

/-- `hbInv x = 0` for `x` above `log 2`: the defining set is empty. -/
lemma hbInv_eq_zero_of_gt_log2 {x : ℝ} (hx : Real.log 2 < x) : hbInv x = 0 := by
  unfold hbInv
  have hset : {p : ℝ | p ∈ Icc (0:ℝ) (1/2) ∧ x ≤ Hb p} = (∅ : Set ℝ) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hxp
    have hHb_le : Hb p ≤ Real.log 2 := by
      simp only [Hb]; exact Real.binEntropy_le_log_two
    linarith
  rw [hset, Real.sInf_empty]

lemma hbInv_mem_Icc_all (x : ℝ) : hbInv x ∈ Icc (0:ℝ) (1/2) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [hbInv_eq_zero_of_nonpos hx]; constructor <;> norm_num
  · rcases le_or_gt x (Real.log 2) with hx2 | hx2
    · exact hbInv_mapsTo ⟨le_of_lt hx, hx2⟩
    · rw [hbInv_eq_zero_of_gt_log2 hx2]; constructor <;> norm_num

lemma mglCurve_eq_base_of_nonpos {tau x : ℝ} (hx : x ≤ 0) :
    mglCurve tau x = mglCurve tau 0 := by
  unfold mglCurve
  rw [hbInv_eq_zero_of_nonpos hx, hbInv_eq_zero_of_nonpos (le_refl (0:ℝ))]

lemma mglCurve_eq_base_of_gt {tau x : ℝ} (hx : Real.log 2 < x) :
    mglCurve tau x = mglCurve tau 0 := by
  unfold mglCurve
  rw [hbInv_eq_zero_of_gt_log2 hx, hbInv_eq_zero_of_nonpos (le_refl (0:ℝ))]

lemma mglCurve_ge_base {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1/2) (x : ℝ) :
    mglCurve tau 0 ≤ mglCurve tau x := by
  have hbase : mglCurve tau 0 = Hb tau := by
    unfold mglCurve
    rw [hbInv_eq_zero_of_nonpos (le_refl (0:ℝ))]
    congr 1; ring
  rw [hbase]
  unfold mglCurve
  have hpx := hbInv_mem_Icc_all x
  have h1 : 0 ≤ 1 - 2*tau := by linarith
  have h_inner_ge : tau ≤ tau + (1 - 2*tau) * hbInv x := by nlinarith [hpx.1]
  have h_inner_le : tau + (1 - 2*tau) * hbInv x ≤ 1/2 := by nlinarith [hpx.2]
  have hmono : MonotoneOn Hb (Icc 0 (1/2)) := by
    have heq : Icc (0:ℝ) (1/2) = Icc (0:ℝ) 2⁻¹ := by norm_num
    rw [heq]
    exact Real.binEntropy_strictMonoOn.monotoneOn
  apply hmono
  · exact ⟨le_of_lt ht0, by linarith⟩
  · exact ⟨by linarith, h_inner_le⟩
  · exact h_inner_ge

/-- Core slope inequality: `L(q) ≤ (1-2τ)·L(p)` where `L y = log(1-y)-log y`,
`q = τ+(1-2τ)p`, from convexity of `L` on `[p,1/2]`, `L(1/2)=0`, and the fact that
`q = (1-A)·(1/2) + A·p` is a convex combination (`A = 1-2τ`). No limit is needed:
the slope cap is pure convexity. -/
lemma mgl_slope_core {tau p : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1/2)
    (hp : p ∈ Set.Ioo (0:ℝ) (1/2)) :
    Real.log (1 - (tau + (1 - 2*tau)*p)) - Real.log (tau + (1 - 2*tau)*p)
      ≤ (1 - 2*tau) * (Real.log (1 - p) - Real.log p) := by
  set A := 1 - 2*tau with hAdef
  have hA0 : 0 < A := by rw [hAdef]; linarith
  have hA1 : A < 1 := by rw [hAdef]; linarith
  have hp0 : 0 < p := hp.1
  have hp1 : p < 1/2 := hp.2
  set L : ℝ → ℝ := fun y => Real.log (1 - y) - Real.log y with hLdef
  have hLcont : ContinuousOn L (Set.Icc p (1/2)) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.log (continuousOn_const.sub continuousOn_id)
      intro y hy; simp only [Set.mem_Icc] at hy
      exact ne_of_gt (by linarith [hy.2] : (0:ℝ) < 1 - y)
    · apply ContinuousOn.log continuousOn_id
      intro y hy; simp only [Set.mem_Icc, id_eq] at hy ⊢
      exact ne_of_gt (lt_of_lt_of_le hp0 hy.1)
  have hstrict : StrictConvexOn ℝ (Set.Icc p (1/2)) L := by
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc p (1/2)) hLcont
    rw [interior_Icc]
    have hderiv_eqOn : Set.EqOn (deriv L) (fun y => -1/(y*(1-y))) (Set.Ioo p (1/2)) := by
      intro y hy
      simp only [Set.mem_Ioo] at hy
      have hy0 : (0:ℝ) < y := lt_trans hp0 hy.1
      have hy1 : y < 1 := lt_trans hy.2 (by norm_num)
      have hd : HasDerivAt L (-1 / (y * (1 - y))) y := by
        have h1 := (Real.hasDerivAt_log (ne_of_gt (by linarith : (0:ℝ) < 1 - y))).comp y
          ((hasDerivAt_const y 1).sub (hasDerivAt_id y))
        have h2 := Real.hasDerivAt_log (ne_of_gt hy0)
        rw [hLdef]
        (convert h1.sub h2 using 1;
          field_simp [ne_of_gt hy0, ne_of_gt (sub_pos.mpr hy1)]; ring)
      exact hd.deriv
    apply StrictMonoOn.congr _ hderiv_eqOn.symm
    intro y hy z hz hyz
    simp only [Set.mem_Ioo] at hy hz
    show -1 / (y * (1 - y)) < -1 / (z * (1 - z))
    have hy0 : 0 < y := lt_trans hp0 hy.1
    have hz0 : 0 < z := lt_trans hp0 hz.1
    have hyp : 0 < y*(1-y) := mul_pos hy0 (by linarith [hy.2])
    have hzp : 0 < z*(1-z) := mul_pos hz0 (by linarith [hz.2])
    have hlt : y*(1-y) < z*(1-z) := by nlinarith [hy.2, hz.2, hyz]
    have h := one_div_lt_one_div_of_lt hyp hlt
    rw [neg_div, neg_div, neg_lt_neg_iff]
    exact h
  have hconv := hstrict.convexOn
  have hmem_half : (1/2 : ℝ) ∈ Set.Icc p (1/2) := ⟨le_of_lt hp1, le_refl _⟩
  have hmem_p : p ∈ Set.Icc p (1/2) := ⟨le_refl _, le_of_lt hp1⟩
  have hcombo : L ((1 - A) * (1/2) + A * p) ≤ (1 - A) * L (1/2) + A * L p := by
    have hh := hconv.2 hmem_half hmem_p (by linarith : (0:ℝ) ≤ 1 - A) (le_of_lt hA0)
      (by ring : (1 - A) + A = 1)
    simpa using hh
  have hLhalf : L (1/2) = 0 := by rw [hLdef]; norm_num
  have hq_eq : (1 - A) * (1/2) + A * p = tau + A * p := by rw [hAdef]; ring
  rw [hq_eq, hLhalf, mul_zero, zero_add] at hcombo
  rw [hLdef] at hcombo
  simp only at hcombo
  calc Real.log (1 - (tau + (1 - 2*tau)*p)) - Real.log (tau + (1 - 2*tau)*p)
      = Real.log (1 - (tau + A*p)) - Real.log (tau + A*p) := by rw [hAdef]
    _ ≤ A * (Real.log (1 - p) - Real.log p) := hcombo
    _ = (1 - 2*tau) * (Real.log (1 - p) - Real.log p) := by rw [hAdef]

/-- Slope cap: `deriv (mglCurve tau) u ≤ (1-2τ)²` on `(0, log 2)`. -/
lemma mglCurve_deriv_le {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1/2)
    {u : ℝ} (hu : u ∈ Ioo 0 (Real.log 2)) :
    deriv (mglCurve tau) u ≤ (1 - 2*tau)^2 := by
  rw [(mglCurve_hasDerivAt ht0 ht1 hu).deriv]
  have hp : hbInv u ∈ Ioo (0:ℝ) (1/2) := hbInv_mem_Ioo hu
  have hLp_pos : 0 < Real.log (1 - hbInv u) - Real.log (hbInv u) := by
    rw [sub_pos]; exact Real.log_lt_log hp.1 (by linarith [hp.2])
  have hcore := mgl_slope_core ht0 ht1 hp
  have hA0 : 0 ≤ 1 - 2*tau := by linarith
  rw [div_le_iff₀ hLp_pos]
  nlinarith [mul_le_mul_of_nonneg_left hcore hA0]

/-- Secant bound on the domain `[0, log 2]`, from the slope cap and monotonicity of
`x ↦ (1-2τ)²·x - mglCurve tau x`. -/
lemma mglCurve_secant_on_domain {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1/2)
    {w v : ℝ} (hw : w ∈ Icc 0 (Real.log 2)) (hv : v ∈ Icc 0 (Real.log 2)) (hwv : w ≤ v) :
    mglCurve tau v - mglCurve tau w ≤ (1 - 2*tau)^2 * (v - w) := by
  have hmglcont : ContinuousOn (mglCurve tau) (Icc 0 (Real.log 2)) := by
    unfold mglCurve
    have hi : ContinuousOn (fun u => tau + (1 - 2 * tau) * hbInv u) (Icc (0 : ℝ) (Real.log 2)) :=
      continuousOn_const.add (continuousOn_const.mul hbInv_continuousOn)
    apply Real.binEntropy_continuous.continuousOn.comp
    · exact hi
    · exact fun _ _ => mem_univ _
  have hmono : MonotoneOn (fun x => (1 - 2*tau)^2 * x - mglCurve tau x) (Icc 0 (Real.log 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (continuousOn_const.mul continuousOn_id).sub hmglcont
    · intro x hx
      rw [interior_Icc] at hx
      have hmgl := mglCurve_hasDerivAt ht0 ht1 hx
      have hlin : HasDerivAt (fun x => (1 - 2*tau)^2 * x) ((1 - 2*tau)^2) x := by
        simpa using (hasDerivAt_id x).const_mul ((1 - 2*tau)^2)
      exact (hlin.sub hmgl).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hmgl : HasDerivAt (mglCurve tau) (deriv (mglCurve tau) x) x :=
        (mglCurve_hasDerivAt ht0 ht1 hx).differentiableAt.hasDerivAt
      have hlin : HasDerivAt (fun x => (1 - 2*tau)^2 * x) ((1 - 2*tau)^2) x := by
        simpa using (hasDerivAt_id x).const_mul ((1 - 2*tau)^2)
      have hderiv : deriv (fun x => (1 - 2*tau)^2 * x - mglCurve tau x) x
          = (1 - 2*tau)^2 - deriv (mglCurve tau) x := (hlin.sub hmgl).deriv
      rw [hderiv]
      have := mglCurve_deriv_le ht0 ht1 hx
      linarith
  have hkey : (1 - 2*tau)^2 * w - mglCurve tau w ≤ (1 - 2*tau)^2 * v - mglCurve tau v :=
    hmono hw hv hwv
  linarith

/-- **Secant/slope cap for the MGL curve (note 04 §0, Lemma 0'').** For every real
`u` and `theta ≥ 0`, `g(u) - g(u - theta) ≤ (1-2τ)²·theta`. This is the analytic
`g' ≤ (1-2τ)²` slope cap in integrated (secant) form, valid for all `u` because the
curve is constant (`= Hb τ`, its minimum) outside `[0, log 2]`. Used by
`label_entropy_bound` to turn the Wyner–Ziv sandwich into `H(D) ≤ err·n`. -/
lemma mglCurve_secant_bound
    {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (u theta : ℝ) (htheta : 0 ≤ theta) :
    mglCurve tau u - mglCurve tau (u - theta) ≤ (1 - 2 * tau)^2 * theta := by
  have hA2 : 0 ≤ (1 - 2*tau)^2 := by positivity
  have hL2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt u 0 with hu0 | hu0
  · rw [mglCurve_eq_base_of_nonpos hu0,
      mglCurve_eq_base_of_nonpos (show u - theta ≤ 0 by linarith)]
    linarith [mul_nonneg hA2 htheta]
  · rcases lt_or_ge (Real.log 2) u with huL | huL
    · rw [mglCurve_eq_base_of_gt huL]
      have hge := mglCurve_ge_base ht0 ht1 (u - theta)
      linarith [hge, mul_nonneg hA2 htheta]
    · rcases lt_or_ge (u - theta) 0 with hw0 | hw0
      · rw [mglCurve_eq_base_of_nonpos (le_of_lt hw0)]
        have hdom := mglCurve_secant_on_domain ht0 ht1
          (show (0:ℝ) ∈ Icc 0 (Real.log 2) from ⟨le_refl 0, le_of_lt hL2⟩)
          (show u ∈ Icc 0 (Real.log 2) from ⟨le_of_lt hu0, huL⟩) (le_of_lt hu0)
        simp only [sub_zero] at hdom
        have hu_le : u ≤ theta := by linarith
        nlinarith [hdom, mul_le_mul_of_nonneg_left hu_le hA2]
      · have hdom := mglCurve_secant_on_domain ht0 ht1
          (show (u - theta) ∈ Icc 0 (Real.log 2) from ⟨hw0, by linarith⟩)
          (show u ∈ Icc 0 (Real.log 2) from ⟨le_of_lt hu0, huL⟩) (by linarith)
        have heq : u - (u - theta) = theta := by ring
        rw [heq] at hdom
        exact hdom

end AverageHarperStability
