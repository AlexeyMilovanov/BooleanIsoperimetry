import AverageHarperStability.Distribution.CertificateCore
import AverageHarperStability.Distribution.Flatness

open scoped BigOperators
open Filter Topology Set Classical

namespace AverageHarperStability

attribute [local instance] Classical.propDecidable

/-!
# Conditional MGL and the Wyner--Ziv label sandwich

The worker contract below includes the entropy-rate window already present at
its unique caller.  This is the authorized repair of the old, false unwindowed
contract: near the endpoint `hbInv u = 1/2`, the adapted label can have fixed
entropy while the MGL slack tends to zero.

This file separates the remaining argument into two pieces:

* `conditional_mgl_label_sandwich` proves the finite conditional Mrs. Gerber
  inequality for an arbitrary deterministic label, including all normalization,
  zero-mass fibers, entropy chain rules, and Jensen bookkeeping.
* `adaptedCenter_conditionalLabelEntropy_bound` is the remaining tracking leaf:
  near equality and the entropy window must make the adapted label decodable
  from the noisy output, hence bound `H(D | Q)`.
-/

/-- The law of `X` conditioned on `D X = d`.  A zero-mass fiber is totalized by
the point mass at `∅`; its value is immaterial after multiplication by the
fiber mass. -/
noncomputable def wzFiberLaw {n : ℕ} (mu : Cube n → ℝ)
    (D : Cube n → Cube n) (d x : Cube n) : ℝ :=
  if mapMass mu D d = 0 then
    if x = ∅ then 1 else 0
  else if D x = d then mu x / mapMass mu D d else 0

private lemma mapMass_nonneg' {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (D : Cube n → Cube n) (d : Cube n) :
    0 ≤ mapMass mu D d := by
  unfold mapMass
  exact Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact hmu.1 x
    · exact le_rfl

private lemma mass_le_mapMass {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (D : Cube n → Cube n) {x d : Cube n} (hDx : D x = d) :
    mu x ≤ mapMass mu D d := by
  unfold mapMass
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (Cube n)))
    (f := fun z => if D z = d then mu z else 0)
    (fun z _ => by by_cases hz : D z = d <;> simp [hz, hmu.1 z])
    (Finset.mem_univ x)
  simpa [hDx] using hsingle

lemma wzFiberLaw_isLaw {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (D : Cube n → Cube n) (d : Cube n) :
    IsLaw (wzFiberLaw mu D d) := by
  constructor
  · intro x
    unfold wzFiberLaw
    split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact div_nonneg (hmu.1 x) (mapMass_nonneg' mu hmu D d)
    · exact le_rfl
  · unfold wzFiberLaw
    by_cases hw : mapMass mu D d = 0
    · simp [hw]
    · simp only [hw, if_false]
      rw [show (∑ x, if D x = d then mu x / mapMass mu D d else 0) =
          ∑ x, (if D x = d then mu x else 0) / mapMass mu D d by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : D x = d <;> simp [hx]]
      rw [← Finset.sum_div]
      change mapMass mu D d / mapMass mu D d = 1
      exact div_self hw

lemma mapMass_mul_wzFiberLaw {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (D : Cube n → Cube n) (d x : Cube n) :
    mapMass mu D d * wzFiberLaw mu D d x =
      if D x = d then mu x else 0 := by
  by_cases hw : mapMass mu D d = 0
  · rw [hw, zero_mul]
    by_cases hDx : D x = d
    · rw [if_pos hDx]
      have hle := mass_le_mapMass mu hmu D hDx
      rw [hw] at hle
      exact (le_antisymm hle (hmu.1 x)).symm
    · rw [if_neg hDx]
  · unfold wzFiberLaw
    rw [if_neg hw]
    by_cases hDx : D x = d
    · rw [if_pos hDx, if_pos hDx]
      exact mul_div_cancel₀ _ hw
    · rw [if_neg hDx, if_neg hDx, mul_zero]

/-- Joint mass of the deterministic label `D X` and the noisy output `Q`. -/
noncomputable def wzLabelNoiseJoint {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D : Cube n → Cube n) (d y : Cube n) : ℝ :=
  ∑ x, if D x = d then mu x * noiseKernel tau x y else 0

lemma wzLabelNoiseJoint_eq {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (D : Cube n → Cube n) (d y : Cube n) :
    wzLabelNoiseJoint tau mu D d y =
      mapMass mu D d * noiseMass tau (wzFiberLaw mu D d) y := by
  unfold wzLabelNoiseJoint noiseMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, mapMass_mul_wzFiberLaw mu hmu D d x]
  split_ifs <;> ring

lemma sum_wzLabelNoiseJoint_label {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D : Cube n → Cube n) (d : Cube n) :
    ∑ y, wzLabelNoiseJoint tau mu D d y = mapMass mu D d := by
  simp_rw [wzLabelNoiseJoint_eq tau mu hmu D]
  rw [← Finset.mul_sum,
    (noiseMass_isLaw ht0 ht1 _ (wzFiberLaw_isLaw mu hmu D d)).2, mul_one]

lemma sum_wzLabelNoiseJoint_noise {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D : Cube n → Cube n) (y : Cube n) :
    ∑ d, wzLabelNoiseJoint tau mu D d y = noiseMass tau mu y := by
  unfold wzLabelNoiseJoint noiseMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

noncomputable def wzLabelNoiseEntropy {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D : Cube n → Cube n) : ℝ :=
  ∑ d, ∑ y, Real.negMulLog (wzLabelNoiseJoint tau mu D d y)

/-- The entropy of the deterministic label conditioned on the noisy output,
represented as `H(D,Q) - H(Q)`. -/
noncomputable def wzConditionalLabelEntropy {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (D : Cube n → Cube n) : ℝ :=
  wzLabelNoiseEntropy tau mu D - entropy (noiseMass tau mu)

lemma wzLabelNoiseEntropy_eq {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D : Cube n → Cube n) :
    wzLabelNoiseEntropy tau mu D =
      entropy (mapMass mu D) +
        ∑ d, mapMass mu D d * entropy (noiseMass tau (wzFiberLaw mu D d)) := by
  unfold wzLabelNoiseEntropy
  calc
    (∑ d, ∑ y, Real.negMulLog (wzLabelNoiseJoint tau mu D d y)) =
        ∑ d, (Real.negMulLog (mapMass mu D d) +
          mapMass mu D d * entropy (noiseMass tau (wzFiberLaw mu D d))) := by
      apply Finset.sum_congr rfl
      intro d _
      simp_rw [wzLabelNoiseJoint_eq tau mu hmu D d]
      simp_rw [Real.negMulLog_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      rw [(noiseMass_isLaw ht0 ht1 _ (wzFiberLaw_isLaw mu hmu D d)).2]
      unfold entropy
      ring
    _ = entropy (mapMass mu D) +
        ∑ d, mapMass mu D d * entropy (noiseMass tau (wzFiberLaw mu D d)) := by
      rw [Finset.sum_add_distrib]
      rfl

/-- Entropy chain rule for a deterministic label, proved directly for the
finite mass representation. -/
lemma entropy_eq_label_add_fibers {n : ℕ} (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (D : Cube n → Cube n) :
    entropy mu = entropy (mapMass mu D) +
      ∑ d, mapMass mu D d * entropy (wzFiberLaw mu D d) := by
  calc
    entropy mu = ∑ x, ∑ d,
        Real.negMulLog (if D x = d then mu x else 0) := by
      unfold entropy
      apply Finset.sum_congr rfl
      intro x _
      rw [show (∑ d, Real.negMulLog (if D x = d then mu x else 0)) =
          ∑ d, if D x = d then Real.negMulLog (mu x) else 0 by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : D x = d <;> simp [hd]]
      simp
    _ = ∑ d, ∑ x,
        Real.negMulLog (if D x = d then mu x else 0) := Finset.sum_comm
    _ = ∑ d, (Real.negMulLog (mapMass mu D d) +
        mapMass mu D d * entropy (wzFiberLaw mu D d)) := by
      apply Finset.sum_congr rfl
      intro d _
      calc
        (∑ x, Real.negMulLog (if D x = d then mu x else 0)) =
            ∑ x, Real.negMulLog (mapMass mu D d * wzFiberLaw mu D d x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [mapMass_mul_wzFiberLaw mu hmu D d x]
        _ = Real.negMulLog (mapMass mu D d) +
            mapMass mu D d * entropy (wzFiberLaw mu D d) := by
          simp_rw [Real.negMulLog_mul]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
          rw [(wzFiberLaw_isLaw mu hmu D d).2]
          unfold entropy
          ring
    _ = entropy (mapMass mu D) +
        ∑ d, mapMass mu D d * entropy (wzFiberLaw mu D d) := by
      rw [Finset.sum_add_distrib]
      rfl

private lemma mapMass_isLaw' {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (D : Cube n → Cube n) : IsLaw (mapMass mu D) := by
  constructor
  · exact mapMass_nonneg' mu hmu D
  · unfold mapMass
    rw [Finset.sum_comm]
    calc
      (∑ x, ∑ d, if D x = d then mu x else 0) = ∑ x, mu x := by
        apply Finset.sum_congr rfl
        intro x _
        simp
      _ = 1 := hmu.2

private lemma entropyRate_mem_Icc' {n : ℕ} (hn : 1 ≤ n)
    (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    entropyRate n mu ∈ Icc (0 : ℝ) (Real.log 2) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hent_eq := entropy_eq_sum_stepEntropy mu hmu
  have hent0 : 0 ≤ entropy mu := by
    rw [hent_eq]
    exact Finset.sum_nonneg fun t _ => stepEntropy_nonneg mu hmu t
  have hent_le : entropy mu ≤ (n : ℝ) * Real.log 2 := by
    rw [hent_eq]
    calc
      (∑ t, stepEntropy mu t) ≤ ∑ _t : Fin n, Real.log 2 := by
        apply Finset.sum_le_sum
        intro t _
        exact stepEntropy_le_log2 mu hmu t
      _ = (n : ℝ) * Real.log 2 := by simp
  unfold entropyRate
  constructor
  · exact div_nonneg hent0 hnpos.le
  · rw [div_le_iff₀ hnpos]
    nlinarith

private lemma entropy_noise_ge_mgl' {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (hn : 1 ≤ n) :
    (n : ℝ) * mglCurve tau (entropyRate n mu) ≤
      entropy (noiseMass tau mu) := by
  have hmem := S_mem_nonneg tau mu hmu ht0 ht1
  have kjen := S_jen_nonneg tau mu hmu ht0 ht1 hn
  have hsplit := slack_split tau mu
  linarith

/-- Conditional Mrs. Gerber for an arbitrary deterministic label:
`H(Q) ≥ H(D) - H(D|Q) + n g((H(X)-H(D))/n)`.

This is proved by applying the already-checked MGL theorem to every normalized
label fiber and then applying convexity of `mglCurve` across the fibers. -/
lemma conditional_mgl_label_sandwich {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (hn : 1 ≤ n)
    (D : Cube n → Cube n) :
    entropy (noiseMass tau mu) ≥
      entropy (mapMass mu D) - wzConditionalLabelEntropy tau mu D +
        (n : ℝ) * mglCurve tau
          ((entropy mu - entropy (mapMass mu D)) / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmap := mapMass_isLaw' mu hmu D
  have hweights0 : ∀ d ∈ (Finset.univ : Finset (Cube n)),
      0 ≤ mapMass mu D d := fun d _ => hmap.1 d
  have hweights1 : ∑ d, mapMass mu D d = 1 := hmap.2
  have hargs : ∀ d ∈ (Finset.univ : Finset (Cube n)),
      entropyRate n (wzFiberLaw mu D d) ∈ Icc (0 : ℝ) (Real.log 2) := by
    intro d _
    exact entropyRate_mem_Icc' hn _ (wzFiberLaw_isLaw mu hmu D d)
  have hjensen := (mglCurve_strictConvex ht0 ht1).convexOn.map_sum_le
    hweights0 hweights1 hargs
  have hfiber_mgl :
      ∑ d, mapMass mu D d *
          ((n : ℝ) * mglCurve tau (entropyRate n (wzFiberLaw mu D d))) ≤
        ∑ d, mapMass mu D d *
          entropy (noiseMass tau (wzFiberLaw mu D d)) := by
    apply Finset.sum_le_sum
    intro d _
    exact mul_le_mul_of_nonneg_left
      (entropy_noise_ge_mgl' tau _ (wzFiberLaw_isLaw mu hmu D d)
        ht0 ht1 hn)
      (hmap.1 d)
  have havg :
      ∑ d, mapMass mu D d * entropyRate n (wzFiberLaw mu D d) =
        (entropy mu - entropy (mapMass mu D)) / (n : ℝ) := by
    rw [entropy_eq_label_add_fibers mu hmu D]
    unfold entropyRate
    ring_nf
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hjensen_scaled :
      (n : ℝ) * mglCurve tau
          ((entropy mu - entropy (mapMass mu D)) / (n : ℝ)) ≤
        ∑ d, mapMass mu D d *
          ((n : ℝ) * mglCurve tau (entropyRate n (wzFiberLaw mu D d))) := by
    rw [← havg]
    calc
      (n : ℝ) * mglCurve tau
          (∑ d, mapMass mu D d * entropyRate n (wzFiberLaw mu D d)) ≤
        (n : ℝ) *
          (∑ d, mapMass mu D d *
            mglCurve tau (entropyRate n (wzFiberLaw mu D d))) :=
        mul_le_mul_of_nonneg_left hjensen hnpos.le
      _ = ∑ d, mapMass mu D d *
          ((n : ℝ) * mglCurve tau (entropyRate n (wzFiberLaw mu D d))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
  have hconditional :
      (n : ℝ) * mglCurve tau
          ((entropy mu - entropy (mapMass mu D)) / (n : ℝ)) ≤
        ∑ d, mapMass mu D d *
          entropy (noiseMass tau (wzFiberLaw mu D d)) :=
    hjensen_scaled.trans hfiber_mgl
  have hjoint := wzLabelNoiseEntropy_eq tau mu hmu ht0.le (by linarith) D
  unfold wzConditionalLabelEntropy
  linarith

private lemma entropy_nonneg' {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    0 ≤ entropy mu := by
  rw [entropy_eq_sum_stepEntropy mu hmu]
  exact Finset.sum_nonneg fun t _ => stepEntropy_nonneg mu hmu t

private lemma entropy_le_dim_log2' {n : ℕ} (hn : 1 ≤ n)
    (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    entropy mu ≤ (n : ℝ) * Real.log 2 := by
  have h := (entropyRate_mem_Icc' hn mu hmu).2
  unfold entropyRate at h
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [div_le_iff₀ hnpos] at h
  simpa [mul_comm] using h

private lemma entropy_mapMass_le' {n : ℕ} (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (D : Cube n → Cube n) :
    entropy (mapMass mu D) ≤ entropy mu := by
  rw [entropy_eq_label_add_fibers mu hmu D]
  have hsum : 0 ≤ ∑ d, mapMass mu D d * entropy (wzFiberLaw mu D d) := by
    apply Finset.sum_nonneg
    intro d _
    exact mul_nonneg (mapMass_nonneg' mu hmu D d)
      (entropy_nonneg' _ (wzFiberLaw_isLaw mu hmu D d))
  linarith

/-- In the nontrivial branch, the eighth-root error budget has enough numeric
room to absorb the original MGL slack twice.  This leaves the tracking leaf a
clean positive half-budget instead of a subtraction by `delta`. -/
lemma two_delta_le_wz_budget
    {tau zeta delta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) (hd0 : 0 < delta)
    (hsmall : err_val tau zeta delta * (4 * tau * (1 - tau)) < Real.log 2) :
    2 * delta ≤ err_val tau zeta delta * (4 * tau * (1 - tau)) := by
  let a := zeta * tau * (1 - 2 * tau)
  let c := 4 * tau * (1 - tau)
  let s := Real.sqrt (Real.sqrt (Real.sqrt delta))
  have hchannel0 : 0 < 1 - 2 * tau := by linarith
  have hchannel1 : 1 - 2 * tau ≤ 1 := by linarith
  have hz1' : zeta ≤ 1 := hz1.trans (by norm_num)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hc0 : 0 < c := by dsimp [c]; nlinarith
  have ha_le_tau : a ≤ tau := by
    dsimp [a]
    calc
      zeta * tau * (1 - 2 * tau) ≤ 1 * tau * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hz1' ht0.le
        · exact hchannel1
        · positivity
        · positivity
      _ = tau := by ring
  have ha_sq_le : a ^ 2 ≤ tau ^ 2 := by nlinarith
  have htau_sq : tau ^ 2 ≤ 2 * tau * (1 - tau) := by nlinarith
  have hac : 2 * a ^ 2 ≤ c := by dsimp [c]; nlinarith
  have hrecip : 2 ≤ 1 / a ^ 2 * c := by
    rw [show 1 / a ^ 2 * c = c / a ^ 2 by ring]
    rw [le_div_iff₀ (sq_pos_of_pos ha0)]
    exact hac
  have hcoef : 2 ≤ (1 + 1 / a ^ 2) * c := by
    calc
      2 ≤ 1 / a ^ 2 * c := hrecip
      _ ≤ (1 + 1 / a ^ 2) * c := by nlinarith
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have herr : err_val tau zeta delta * (4 * tau * (1 - tau)) =
      ((1 + 1 / a ^ 2) * c) * s := by
    dsimp [a, c, s]
    unfold err_val
    ring
  have h2s : 2 * s ≤ err_val tau zeta delta * (4 * tau * (1 - tau)) := by
    rw [herr]
    nlinarith [mul_le_mul_of_nonneg_right hcoef hs0]
  have hlog2 : Real.log 2 ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans
      (by norm_num)
  have hs1 : s ≤ 1 := by linarith
  have hr2 : Real.sqrt (Real.sqrt delta) ≤ 1 := by
    calc
      Real.sqrt (Real.sqrt delta) = s * s := by
        dsimp [s]
        exact (Real.mul_self_sqrt (Real.sqrt_nonneg (Real.sqrt delta))).symm
      _ ≤ 1 * 1 := mul_le_mul hs1 hs1 hs0 (by norm_num)
      _ = 1 := by norm_num
  have hr1 : Real.sqrt delta ≤ 1 := by
    calc
      Real.sqrt delta = Real.sqrt (Real.sqrt delta) * Real.sqrt (Real.sqrt delta) :=
        (Real.mul_self_sqrt (Real.sqrt_nonneg delta)).symm
      _ ≤ 1 * 1 := mul_le_mul hr2 hr2 (Real.sqrt_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hdelta_s : delta ≤ s := by
    have hle1 : delta ≤ Real.sqrt delta := by
      calc
        delta = Real.sqrt delta * Real.sqrt delta :=
          (Real.mul_self_sqrt hd0.le).symm
        _ ≤ Real.sqrt delta * 1 :=
          mul_le_mul_of_nonneg_left hr1 (Real.sqrt_nonneg _)
        _ = Real.sqrt delta := mul_one _
    have hle2 : Real.sqrt delta ≤ Real.sqrt (Real.sqrt delta) := by
      calc
        Real.sqrt delta = Real.sqrt (Real.sqrt delta) * Real.sqrt (Real.sqrt delta) :=
          (Real.mul_self_sqrt (Real.sqrt_nonneg delta)).symm
        _ ≤ Real.sqrt (Real.sqrt delta) * 1 :=
          mul_le_mul_of_nonneg_left hr2 (Real.sqrt_nonneg _)
        _ = Real.sqrt (Real.sqrt delta) := mul_one _
    have hle3 : Real.sqrt (Real.sqrt delta) ≤ s := by
      calc
        Real.sqrt (Real.sqrt delta) = s * s := by
          dsimp [s]
          exact (Real.mul_self_sqrt (Real.sqrt_nonneg (Real.sqrt delta))).symm
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left hs1 hs0
        _ = s := mul_one _
    linarith
  linarith

private def fanoXorEquiv {n : ℕ} (d : Cube n) : Cube n ≃ Cube n where
  toFun e := symmDiff e d
  invFun e := symmDiff e d
  left_inv e := by simp
  right_inv e := by simp

private noncomputable def fanoErrorJoint {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D Dhat : Cube n → Cube n) (e y : Cube n) : ℝ :=
  ∑ x, if symmDiff (D x) (Dhat y) = e then
    mu x * noiseKernel tau x y else 0

private lemma fanoErrorJoint_nonneg {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) (e y : Cube n) :
    0 ≤ fanoErrorJoint tau mu D Dhat e y := by
  unfold fanoErrorJoint
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact mul_nonneg (hmu.1 x) ((noiseKernel_isLaw ht0 ht1 x).1 y)
  · exact le_rfl

lemma sum_fanoErrorJoint {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D Dhat : Cube n → Cube n) (y : Cube n) :
    ∑ e, fanoErrorJoint tau mu D Dhat e y = noiseMass tau mu y := by
  unfold fanoErrorJoint noiseMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

private lemma fanoErrorJoint_eq_labelJoint {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D Dhat : Cube n → Cube n) (e y : Cube n) :
    fanoErrorJoint tau mu D Dhat e y =
      wzLabelNoiseJoint tau mu D (symmDiff e (Dhat y)) y := by
  unfold fanoErrorJoint wzLabelNoiseJoint
  apply Finset.sum_congr rfl
  intro x _
  have heq : symmDiff (D x) (Dhat y) = e ↔
      D x = symmDiff e (Dhat y) := by
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      rw [symmDiff_comm e (Dhat y)]
      simp
  rw [if_congr heq rfl rfl]

private lemma fanoLabelNoiseEntropy_eq_errorJoint {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (D Dhat : Cube n → Cube n) :
    wzLabelNoiseEntropy tau mu D =
      ∑ y, ∑ e, Real.negMulLog (fanoErrorJoint tau mu D Dhat e y) := by
  unfold wzLabelNoiseEntropy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hshift := Equiv.sum_comp (fanoXorEquiv (Dhat y))
    (fun d => Real.negMulLog (wzLabelNoiseJoint tau mu D d y))
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro e _
  rw [fanoErrorJoint_eq_labelJoint]
  rfl

private noncomputable def fanoErrorFiberLaw {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D Dhat : Cube n → Cube n) (y e : Cube n) : ℝ :=
  if noiseMass tau mu y = 0 then
    if e = ∅ then 1 else 0
  else fanoErrorJoint tau mu D Dhat e y / noiseMass tau mu y

private lemma fanoErrorFiberLaw_isLaw {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) (y : Cube n) :
    IsLaw (fanoErrorFiberLaw tau mu D Dhat y) := by
  constructor
  · intro e
    unfold fanoErrorFiberLaw
    split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact div_nonneg (fanoErrorJoint_nonneg tau mu hmu ht0 ht1 D Dhat e y)
        ((noiseMass_isLaw ht0 ht1 mu hmu).1 y)
  · unfold fanoErrorFiberLaw
    by_cases hy : noiseMass tau mu y = 0
    · simp [hy]
    · simp only [hy, if_false]
      rw [← Finset.sum_div, sum_fanoErrorJoint]
      exact div_self hy

lemma noiseMass_mul_fanoErrorFiberLaw {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) (y e : Cube n) :
    noiseMass tau mu y * fanoErrorFiberLaw tau mu D Dhat y e =
      fanoErrorJoint tau mu D Dhat e y := by
  by_cases hy : noiseMass tau mu y = 0
  · rw [hy, zero_mul]
    have he0 := fanoErrorJoint_nonneg tau mu hmu ht0 ht1 D Dhat e y
    have hele : fanoErrorJoint tau mu D Dhat e y ≤
        ∑ e', fanoErrorJoint tau mu D Dhat e' y :=
      Finset.single_le_sum
        (fun e' _ => fanoErrorJoint_nonneg tau mu hmu ht0 ht1 D Dhat e' y)
        (Finset.mem_univ e)
    rw [sum_fanoErrorJoint, hy] at hele
    linarith
  · unfold fanoErrorFiberLaw
    rw [if_neg hy, mul_div_cancel₀ _ hy]

private noncomputable def fanoErrorMass {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D Dhat : Cube n → Cube n) (e : Cube n) : ℝ :=
  ∑ y, fanoErrorJoint tau mu D Dhat e y

private lemma fanoErrorMass_isLaw {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) :
    IsLaw (fanoErrorMass tau mu D Dhat) := by
  constructor
  · intro e
    unfold fanoErrorMass
    exact Finset.sum_nonneg fun y _ =>
      fanoErrorJoint_nonneg tau mu hmu ht0 ht1 D Dhat e y
  · unfold fanoErrorMass
    rw [Finset.sum_comm]
    simp_rw [sum_fanoErrorJoint]
    exact (noiseMass_isLaw ht0 ht1 mu hmu).2

private lemma fanoErrorMass_eq_mixture {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) (e : Cube n) :
    fanoErrorMass tau mu D Dhat e =
      ∑ y, noiseMass tau mu y * fanoErrorFiberLaw tau mu D Dhat y e := by
  unfold fanoErrorMass
  apply Finset.sum_congr rfl
  intro y _
  exact (noiseMass_mul_fanoErrorFiberLaw tau mu hmu ht0 ht1 D Dhat y e).symm

lemma sum_negMulLog_fanoErrorJoint {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) (y : Cube n) :
    ∑ e, Real.negMulLog (fanoErrorJoint tau mu D Dhat e y) =
      Real.negMulLog (noiseMass tau mu y) +
        noiseMass tau mu y * entropy (fanoErrorFiberLaw tau mu D Dhat y) := by
  have hfiber := fanoErrorFiberLaw_isLaw tau mu hmu ht0 ht1 D Dhat y
  calc
    (∑ e, Real.negMulLog (fanoErrorJoint tau mu D Dhat e y)) =
        ∑ e, Real.negMulLog
          (noiseMass tau mu y * fanoErrorFiberLaw tau mu D Dhat y e) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [noiseMass_mul_fanoErrorFiberLaw tau mu hmu ht0 ht1 D Dhat]
    _ = ∑ e, (Real.negMulLog (noiseMass tau mu y) *
          fanoErrorFiberLaw tau mu D Dhat y e +
        noiseMass tau mu y *
          Real.negMulLog (fanoErrorFiberLaw tau mu D Dhat y e)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Real.negMulLog_mul]
      ring
    _ = Real.negMulLog (noiseMass tau mu y) +
        noiseMass tau mu y * entropy (fanoErrorFiberLaw tau mu D Dhat y) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hfiber.2, mul_one]
      rfl

private lemma fanoConditionalLabelEntropy_eq {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) :
    wzConditionalLabelEntropy tau mu D =
      ∑ y, noiseMass tau mu y *
        entropy (fanoErrorFiberLaw tau mu D Dhat y) := by
  rw [wzConditionalLabelEntropy, fanoLabelNoiseEntropy_eq_errorJoint]
  have hsum :
      (∑ y, ∑ e, Real.negMulLog (fanoErrorJoint tau mu D Dhat e y)) =
        ∑ y, (Real.negMulLog (noiseMass tau mu y) +
          noiseMass tau mu y * entropy (fanoErrorFiberLaw tau mu D Dhat y)) := by
    apply Finset.sum_congr rfl
    intro y _
    exact sum_negMulLog_fanoErrorJoint tau mu hmu ht0 ht1 D Dhat y
  rw [hsum]
  rw [Finset.sum_add_distrib]
  unfold entropy
  ring

private lemma fanoConditionalLabelEntropy_le_errorMass {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) :
    wzConditionalLabelEntropy tau mu D ≤ entropy (fanoErrorMass tau mu D Dhat) := by
  rw [fanoConditionalLabelEntropy_eq tau mu hmu ht0 ht1 D Dhat]
  have hnoise := noiseMass_isLaw ht0 ht1 mu hmu
  have hpoint (e : Cube n) :
      ∑ y, noiseMass tau mu y *
          Real.negMulLog (fanoErrorFiberLaw tau mu D Dhat y e) ≤
        Real.negMulLog (fanoErrorMass tau mu D Dhat e) := by
    have hjensen := Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset (Cube n)))
      (w := fun y => noiseMass tau mu y)
      (p := fun y => fanoErrorFiberLaw tau mu D Dhat y e)
      (fun y _ => hnoise.1 y)
      hnoise.2
      (fun y _ => (fanoErrorFiberLaw_isLaw tau mu hmu ht0 ht1 D Dhat y).1 e)
    simp only [smul_eq_mul] at hjensen
    rw [← fanoErrorMass_eq_mixture tau mu hmu ht0 ht1 D Dhat e] at hjensen
    exact hjensen
  unfold entropy
  calc
    (∑ y, noiseMass tau mu y *
        ∑ e, Real.negMulLog (fanoErrorFiberLaw tau mu D Dhat y e)) =
        ∑ e, ∑ y, noiseMass tau mu y *
          Real.negMulLog (fanoErrorFiberLaw tau mu D Dhat y e) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
    _ ≤ ∑ e, Real.negMulLog (fanoErrorMass tau mu D Dhat e) := by
      apply Finset.sum_le_sum
      intro e _
      exact hpoint e

private lemma fanoErrorMass_mean {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (D Dhat : Cube n → Cube n) :
    ∑ e, fanoErrorMass tau mu D Dhat e * (e.card : ℝ) =
      ∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (D x) (Dhat y) : ℝ) := by
  unfold fanoErrorMass fanoErrorJoint
  simp_rw [Finset.sum_mul]
  calc
    (∑ e, ∑ y, ∑ x,
        (if symmDiff (D x) (Dhat y) = e then
          mu x * noiseKernel tau x y else 0) * (e.card : ℝ)) =
        ∑ y, ∑ x, ∑ e,
          (if symmDiff (D x) (Dhat y) = e then
            mu x * noiseKernel tau x y else 0) * (e.card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, mu x * noiseKernel tau x y *
          (hDist (D x) (Dhat y) : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      unfold hDist
      simp

private lemma fanoCondProbOne_mul_prefixMass {n : ℕ} (nu : Cube n → ℝ)
    (hnu : IsLaw nu) (t : Fin n) (x : Cube n) :
    condProbOne nu t x * prefixMass nu t x =
      eventMass nu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) := by
  unfold condProbOne
  by_cases hzero : prefixMass nu t x = 0
  · rw [if_pos hzero, zero_mul]
    have hle : eventMass nu
        (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) ≤
        prefixMass nu t x := by
      apply eventMass_le_eventMass nu hnu
      intro y hy
      exact hy.1
    have hnonneg := eventMass_nonneg hnu
      (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y)
    rw [hzero] at hle
    linarith
  · rw [if_neg hzero, div_mul_cancel₀ _ hzero]

private lemma fanoMean_condProbOne {n : ℕ} (nu : Cube n → ℝ) (hnu : IsLaw nu)
    (t : Fin n) :
    ∑ x, nu x * condProbOne nu t x = eventMass nu (fun x => t ∈ x) := by
  have hfiber : ∀ c : Cube n,
      ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
          nu x * condProbOne nu t x =
        ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
          (if t ∈ x then nu x else 0) := by
    intro c
    by_cases hne : (Finset.univ.filter (fun x => prefixAt t x = c)).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      rw [Finset.mem_filter] at hx0
      have hx0c : prefixAt t x0 = c := hx0.2
      have hleft :
          ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
              nu x * condProbOne nu t x =
            eventMass nu
              (fun y => prefixAt t y = prefixAt t x0 ∧ t ∈ y) := by
        calc
          (∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
              nu x * condProbOne nu t x) =
              (∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c), nu x) *
                condProbOne nu t x0 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mem_filter] at hx
            have hpref : prefixAt t x = prefixAt t x0 := by rw [hx.2, hx0c]
            rw [condProbOne_depends_only_on_prefix nu t x x0 hpref]
          _ = prefixMass nu t x0 * condProbOne nu t x0 := by
            congr 1
            unfold prefixMass eventMass
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : prefixAt t x = c <;> simp [hx, hx0c]
          _ = _ := by
            rw [mul_comm]
            exact fanoCondProbOne_mul_prefixMass nu hnu t x0
      have hright :
          ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
              (if t ∈ x then nu x else 0) =
            eventMass nu
              (fun y => prefixAt t y = prefixAt t x0 ∧ t ∈ y) := by
        rw [Finset.sum_filter]
        unfold eventMass
        apply Finset.sum_congr rfl
        intro x _
        by_cases hp : prefixAt t x = c <;> by_cases ht : t ∈ x <;>
          simp [hp, ht, hx0c]
      rw [hleft, hright]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty, Finset.sum_empty]
  calc
    (∑ x, nu x * condProbOne nu t x) =
        ∑ c, ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
          nu x * condProbOne nu t x :=
      (Finset.sum_fiberwise Finset.univ (prefixAt t)
        (fun x => nu x * condProbOne nu t x)).symm
    _ = ∑ c, ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
          (if t ∈ x then nu x else 0) :=
      Finset.sum_congr rfl (fun c _ => hfiber c)
    _ = eventMass nu (fun x => t ∈ x) :=
      by
        unfold eventMass
        calc
          (∑ c, ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
              (if t ∈ x then nu x else 0)) =
              ∑ x, (if t ∈ x then nu x else 0) :=
            Finset.sum_fiberwise Finset.univ (prefixAt t)
              (fun x => if t ∈ x then nu x else 0)
          _ = ∑ x, @ite ℝ (t ∈ x) (Classical.propDecidable _) (nu x) 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : t ∈ x <;> simp [hx]

private lemma fanoStepEntropy_le_marginal {n : ℕ} (nu : Cube n → ℝ)
    (hnu : IsLaw nu) (t : Fin n) :
    stepEntropy nu t ≤ Hb (eventMass nu (fun x => t ∈ x)) := by
  have hjensen := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    (t := (Finset.univ : Finset (Cube n)))
    (w := nu)
    (p := fun x => condProbOne nu t x)
    (fun x _ => hnu.1 x)
    hnu.2
    (fun x _ => ⟨condProbOne_nonneg nu hnu t x,
      condProbOne_le_one nu hnu t x⟩)
  simp only [smul_eq_mul] at hjensen
  unfold stepEntropy
  rw [fanoMean_condProbOne nu hnu t] at hjensen
  exact hjensen

private lemma fanoSum_bit_marginals {n : ℕ} (nu : Cube n → ℝ) :
    ∑ t, eventMass nu (fun x => t ∈ x) =
      ∑ x, nu x * (x.card : ℝ) := by
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    (∑ t : Fin n,
        @ite ℝ ((fun x => t ∈ x) x) (Classical.propDecidable _) (nu x) 0) =
        ∑ t ∈ x, nu x := by
      calc
        (∑ t : Fin n,
            @ite ℝ ((fun x => t ∈ x) x) (Classical.propDecidable _) (nu x) 0) =
            ∑ t ∈ x,
              @ite ℝ ((fun x => t ∈ x) x) (Classical.propDecidable _) (nu x) 0 := by
          symm
          apply Finset.sum_subset (Finset.subset_univ x)
          intro t _ ht
          simp [ht]
        _ = ∑ t ∈ x, nu x := by
          apply Finset.sum_congr rfl
          intro t ht
          simp [ht]
    _ = nu x * (x.card : ℝ) := by simp; ring

private lemma fanoEntropy_le_Hb_mean {n : ℕ} (hn : 1 ≤ n)
    (nu : Cube n → ℝ) (hnu : IsLaw nu) :
    entropy nu ≤ (n : ℝ) *
      Hb ((∑ x, nu x * (x.card : ℝ)) / (n : ℝ)) := by
  let p : Fin n → ℝ := fun t => eventMass nu (fun x => t ∈ x)
  have hp : ∀ t ∈ (Finset.univ : Finset (Fin n)), p t ∈ Icc (0 : ℝ) 1 := by
    intro t _
    constructor
    · exact eventMass_nonneg hnu _
    · calc
        eventMass nu (fun x => t ∈ x) ≤ eventMass nu (fun _ => True) := by
          apply eventMass_le_eventMass nu hnu
          intro x _
          trivial
        _ = 1 := by unfold eventMass; simpa using hnu.2
  have hscaled := Hb_weighted_average_ge
    (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℝ)) p
    (fun _ _ => by norm_num)
    (show 0 ≤ (n : ℝ) by positivity)
    (by simp)
    hp
  simp only [one_mul] at hscaled
  have hsteps :
      ∑ t, stepEntropy nu t ≤ ∑ t, Hb (p t) := by
    apply Finset.sum_le_sum
    intro t _
    exact fanoStepEntropy_le_marginal nu hnu t
  rw [entropy_eq_sum_stepEntropy nu hnu]
  calc
    (∑ t, stepEntropy nu t) ≤ ∑ t, Hb (p t) := hsteps
    _ ≤ (n : ℝ) * Hb ((∑ t, p t) / (n : ℝ)) := hscaled
    _ = (n : ℝ) * Hb ((∑ x, nu x * (x.card : ℝ)) / (n : ℝ)) := by
      rw [show (∑ t, p t) = ∑ x, nu x * (x.card : ℝ) by
        dsimp [p]
        exact fanoSum_bit_marginals nu]

private lemma fanoEntropy_le_Hb_min_mean {n : ℕ} (nu : Cube n → ℝ) (hnu : IsLaw nu) :
    entropy nu ≤ (n : ℝ) *
      Hb (min ((∑ x, nu x * (x.card : ℝ)) / (n : ℝ)) (1 / 2)) := by
  by_cases hn : n = 0
  · subst n
    rw [entropy_eq_sum_stepEntropy nu hnu]
    simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    let r := (∑ x, nu x * (x.card : ℝ)) / (n : ℝ)
    rcases le_or_gt r (1 / 2) with hr | hr
    · rw [min_eq_left hr]
      exact fanoEntropy_le_Hb_mean hn1 nu hnu
    · rw [min_eq_right (le_of_lt hr)]
      rw [entropy_eq_sum_stepEntropy nu hnu]
      calc
        (∑ t, stepEntropy nu t) ≤ ∑ _t : Fin n, Real.log 2 := by
          apply Finset.sum_le_sum
          intro t _
          exact stepEntropy_le_log2 nu hnu t
        _ = (n : ℝ) * Real.log 2 := by simp
        _ = (n : ℝ) * Hb (1 / 2) := by
          congr 1
          simpa only [Hb, one_div] using Real.binEntropy_two_inv.symm


lemma fano_mismatch_bound {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D : Cube n → Cube n) (Dhat : Cube n → Cube n) :
    wzConditionalLabelEntropy tau mu D ≤
      (n : ℝ) * Hb (min ((∑ x, ∑ y, mu x * noiseKernel tau x y * (hDist (D x) (Dhat y) : ℝ)) / (n : ℝ)) (1/2)) := by
  calc
    wzConditionalLabelEntropy tau mu D ≤
        entropy (fanoErrorMass tau mu D Dhat) :=
      fanoConditionalLabelEntropy_le_errorMass tau mu hmu ht0 ht1 D Dhat
    _ ≤ (n : ℝ) * Hb
        (min ((∑ e, fanoErrorMass tau mu D Dhat e * (e.card : ℝ)) /
          (n : ℝ)) (1 / 2)) :=
      fanoEntropy_le_Hb_min_mean _ (fanoErrorMass_isLaw tau mu hmu ht0 ht1 D Dhat)
    _ = (n : ℝ) * Hb (min ((∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (D x) (Dhat y) : ℝ)) / (n : ℝ)) (1 / 2)) := by
      rw [fanoErrorMass_mean]

/-- Joint mass of `Q = y` and the event that coordinate `t` of the adapted
label is one. -/
noncomputable def wzDirectionOneMass {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (t : Fin n) (y : Cube n) : ℝ :=
  ∑ x, if t ∈ adaptedCenter mu x then mu x * noiseKernel tau x y else 0

/-- Joint mass of `Q = y` and the event that coordinate `t` of the adapted
label is zero. -/
noncomputable def wzDirectionZeroMass {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (t : Fin n) (y : Cube n) : ℝ :=
  ∑ x, if t ∉ adaptedCenter mu x then mu x * noiseKernel tau x y else 0

/-- Coordinatewise Bayes decoder of the adapted label from the full noisy
output.  Ties are resolved toward zero. -/
noncomputable def wzMAPCenter {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (y : Cube n) : Cube n :=
  Finset.univ.filter fun t =>
    wzDirectionZeroMass tau mu t y < wzDirectionOneMass tau mu t y

private lemma wz_hDist_as_sum {n : ℕ} (a b : Cube n) :
    (hDist a b : ℝ) = ∑ t : Fin n,
      if (t ∈ a ∧ t ∉ b) ∨ (t ∉ a ∧ t ∈ b) then 1 else 0 := by
  rw [Finset.sum_boole]
  norm_cast
  unfold hDist
  congr 1
  ext t
  simp [symmDiff, Finset.mem_union]
  tauto

/-- Exact Bayes-risk identity for `wzMAPCenter`: at each output and coordinate,
the mismatch mass is the smaller of the two posterior (unnormalized) direction
masses.  This isolates the predictor construction and calibration part of the
tracking argument from the remaining memory-charge estimate. -/
lemma wzMAPCenter_expected_mismatch_eq {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) :
    ∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (adaptedCenter mu x) (wzMAPCenter tau mu y) : ℝ) =
      ∑ t, ∑ y, min (wzDirectionOneMass tau mu t y)
        (wzDirectionZeroMass tau mu t y) := by
  simp_rw [wz_hDist_as_sum, Finset.mul_sum]
  rw [show (∑ x, ∑ y, ∑ t, mu x * noiseKernel tau x y *
        (if (t ∈ adaptedCenter mu x ∧ t ∉ wzMAPCenter tau mu y) ∨
          (t ∉ adaptedCenter mu x ∧ t ∈ wzMAPCenter tau mu y) then 1 else 0)) =
      ∑ t, ∑ y, ∑ x, mu x * noiseKernel tau x y *
        (if (t ∈ adaptedCenter mu x ∧ t ∉ wzMAPCenter tau mu y) ∨
          (t ∉ adaptedCenter mu x ∧ t ∈ wzMAPCenter tau mu y) then 1 else 0) by
    calc
      _ = ∑ y, ∑ t, ∑ x, mu x * noiseKernel tau x y *
          (if (t ∈ adaptedCenter mu x ∧ t ∉ wzMAPCenter tau mu y) ∨
            (t ∉ adaptedCenter mu x ∧ t ∈ wzMAPCenter tau mu y) then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro y _
  unfold wzMAPCenter
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hmap : wzDirectionZeroMass tau mu t y <
      wzDirectionOneMass tau mu t y
  · simp only [hmap, not_true_eq_false, and_false, and_true, false_or]
    rw [min_eq_right hmap.le]
    unfold wzDirectionZeroMass
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : t ∈ adaptedCenter mu x <;> simp [hx]
  · simp only [hmap, not_false_eq_true, and_true, and_false, or_false]
    rw [min_eq_left (le_of_not_gt hmap)]
    unfold wzDirectionOneMass
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : t ∈ adaptedCenter mu x <;> simp [hx]

/-- The coordinatewise posterior-majority decoder minimizes expected Hamming
loss among all cube-valued decoders of the noisy output. -/
lemma wzMAPCenter_expected_mismatch_le {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (Dhat : Cube n → Cube n) :
    ∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (adaptedCenter mu x) (wzMAPCenter tau mu y) : ℝ) ≤
      ∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (adaptedCenter mu x) (Dhat y) : ℝ) := by
  rw [wzMAPCenter_expected_mismatch_eq]
  simp_rw [wz_hDist_as_sum, Finset.mul_sum]
  rw [show (∑ x, ∑ y, ∑ t, mu x * noiseKernel tau x y *
        (if (t ∈ adaptedCenter mu x ∧ t ∉ Dhat y) ∨
          (t ∉ adaptedCenter mu x ∧ t ∈ Dhat y) then 1 else 0)) =
      ∑ t, ∑ y, ∑ x, mu x * noiseKernel tau x y *
        (if (t ∈ adaptedCenter mu x ∧ t ∉ Dhat y) ∨
          (t ∉ adaptedCenter mu x ∧ t ∈ Dhat y) then 1 else 0) by
    calc
      _ = ∑ y, ∑ t, ∑ x, mu x * noiseKernel tau x y *
          (if (t ∈ adaptedCenter mu x ∧ t ∉ Dhat y) ∨
            (t ∉ adaptedCenter mu x ∧ t ∈ Dhat y) then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro y _
  by_cases hhat : t ∈ Dhat y
  · calc
      min (wzDirectionOneMass tau mu t y)
          (wzDirectionZeroMass tau mu t y) ≤
          wzDirectionZeroMass tau mu t y := min_le_right _ _
      _ = ∑ x, mu x * noiseKernel tau x y *
          (if (t ∈ adaptedCenter mu x ∧ t ∉ Dhat y) ∨
            (t ∉ adaptedCenter mu x ∧ t ∈ Dhat y) then 1 else 0) := by
        unfold wzDirectionZeroMass
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : t ∈ adaptedCenter mu x <;> simp [hhat, hx]
  · calc
      min (wzDirectionOneMass tau mu t y)
          (wzDirectionZeroMass tau mu t y) ≤
          wzDirectionOneMass tau mu t y := min_le_left _ _
      _ = ∑ x, mu x * noiseKernel tau x y *
          (if (t ∈ adaptedCenter mu x ∧ t ∉ Dhat y) ∨
            (t ∉ adaptedCenter mu x ∧ t ∈ Dhat y) then 1 else 0) := by
        unfold wzDirectionOneMass
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : t ∈ adaptedCenter mu x <;> simp [hhat, hx]

/-- Joint mass of an output prefix `c` and the event that coordinate `t` of
the adapted label is one. -/
noncomputable def wzPrefixDirectionOneMass {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (t : Fin n) (c : Cube n) : ℝ :=
  ∑ x, if t ∈ adaptedCenter mu x then
    mu x * prefixMarginal (noiseKernel tau x) t.1 c else 0

/-- Joint mass of an output prefix `c` and the event that coordinate `t` of
the adapted label is zero. -/
noncomputable def wzPrefixDirectionZeroMass {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (t : Fin n) (c : Cube n) : ℝ :=
  ∑ x, if t ∉ adaptedCenter mu x then
    mu x * prefixMarginal (noiseKernel tau x) t.1 c else 0

/-- Posterior-majority decoder using only the noisy prefix strictly before the
coordinate being predicted. -/
noncomputable def wzPrefixMAPCenter {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (y : Cube n) : Cube n :=
  Finset.univ.filter fun t =>
    wzPrefixDirectionZeroMass tau mu t (prefixNat t.1 y) <
      wzPrefixDirectionOneMass tau mu t (prefixNat t.1 y)

lemma wzPrefixDirectionOneMass_eq_sum_output {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (t : Fin n) (c : Cube n) :
    (∑ y, if prefixNat t.1 y = c then wzDirectionOneMass tau mu t y else 0) =
      wzPrefixDirectionOneMass tau mu t c := by
  unfold wzDirectionOneMass wzPrefixDirectionOneMass prefixMarginal eventMass
  calc
    (∑ y, if prefixNat t.1 y = c then
        (∑ x, if t ∈ adaptedCenter mu x then mu x * noiseKernel tau x y else 0)
      else 0) =
        ∑ y, ∑ x, if prefixNat t.1 y = c then
          (if t ∈ adaptedCenter mu x then mu x * noiseKernel tau x y else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : prefixNat t.1 y = c <;> simp [hy]
    _ = ∑ x, ∑ y, if prefixNat t.1 y = c then
          (if t ∈ adaptedCenter mu x then mu x * noiseKernel tau x y else 0)
        else 0 := Finset.sum_comm
    _ = ∑ x, if t ∈ adaptedCenter mu x then
          mu x * (∑ y, if prefixNat t.1 y = c then noiseKernel tau x y else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : t ∈ adaptedCenter mu x
      · simp only [hx, if_true, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : prefixNat t.1 y = c <;> simp [hy]
      · simp [hx]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : t ∈ adaptedCenter mu x
      · simp only [hx, if_true]
        apply congrArg (fun z : ℝ => mu x * z)
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : prefixNat t.1 y = c <;> simp [hy]
      · simp [hx]

lemma wzPrefixDirectionZeroMass_eq_sum_output {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (t : Fin n) (c : Cube n) :
    (∑ y, if prefixNat t.1 y = c then wzDirectionZeroMass tau mu t y else 0) =
      wzPrefixDirectionZeroMass tau mu t c := by
  unfold wzDirectionZeroMass wzPrefixDirectionZeroMass prefixMarginal eventMass
  calc
    (∑ y, if prefixNat t.1 y = c then
        (∑ x, if t ∉ adaptedCenter mu x then mu x * noiseKernel tau x y else 0)
      else 0) =
        ∑ y, ∑ x, if prefixNat t.1 y = c then
          (if t ∉ adaptedCenter mu x then mu x * noiseKernel tau x y else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : prefixNat t.1 y = c <;> simp [hy]
    _ = ∑ x, ∑ y, if prefixNat t.1 y = c then
          (if t ∉ adaptedCenter mu x then mu x * noiseKernel tau x y else 0)
        else 0 := Finset.sum_comm
    _ = ∑ x, if t ∉ adaptedCenter mu x then
          mu x * (∑ y, if prefixNat t.1 y = c then noiseKernel tau x y else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : t ∉ adaptedCenter mu x
      · simp only [hx, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : prefixNat t.1 y = c <;> simp [hy]
      · simp [hx]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : t ∉ adaptedCenter mu x
      · simp only [hx]
        apply congrArg (fun z : ℝ => mu x * z)
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : prefixNat t.1 y = c <;> simp [hy]
      · simp [hx]

/-- Exact risk identity for the noisy-prefix MAP decoder.  It is the finite
calibration equality in Proposition 7: expected tracking errors equal the sum,
over coordinates and noisy-prefix fibers, of the minority direction masses. -/
lemma wzPrefixMAPCenter_expected_mismatch_eq {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) :
    ∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (adaptedCenter mu x) (wzPrefixMAPCenter tau mu y) : ℝ) =
      ∑ t, ∑ c, min (wzPrefixDirectionOneMass tau mu t c)
        (wzPrefixDirectionZeroMass tau mu t c) := by
  have hdecoder :
      (∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (adaptedCenter mu x) (wzPrefixMAPCenter tau mu y) : ℝ)) =
      ∑ t, ∑ y, if t ∈ wzPrefixMAPCenter tau mu y then
        wzDirectionZeroMass tau mu t y else wzDirectionOneMass tau mu t y := by
    simp_rw [wz_hDist_as_sum, Finset.mul_sum]
    rw [show (∑ x, ∑ y, ∑ t, mu x * noiseKernel tau x y *
          (if (t ∈ adaptedCenter mu x ∧ t ∉ wzPrefixMAPCenter tau mu y) ∨
            (t ∉ adaptedCenter mu x ∧ t ∈ wzPrefixMAPCenter tau mu y) then 1 else 0)) =
        ∑ t, ∑ y, ∑ x, mu x * noiseKernel tau x y *
          (if (t ∈ adaptedCenter mu x ∧ t ∉ wzPrefixMAPCenter tau mu y) ∨
            (t ∉ adaptedCenter mu x ∧ t ∈ wzPrefixMAPCenter tau mu y) then 1 else 0) by
      calc
        _ = ∑ y, ∑ t, ∑ x, mu x * noiseKernel tau x y *
            (if (t ∈ adaptedCenter mu x ∧ t ∉ wzPrefixMAPCenter tau mu y) ∨
              (t ∉ adaptedCenter mu x ∧ t ∈ wzPrefixMAPCenter tau mu y) then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hhat : t ∈ wzPrefixMAPCenter tau mu y
    · rw [if_pos hhat]
      unfold wzDirectionZeroMass
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : t ∈ adaptedCenter mu x <;> simp [hhat, hx]
    · rw [if_neg hhat]
      unfold wzDirectionOneMass
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : t ∈ adaptedCenter mu x <;> simp [hhat, hx]
  rw [hdecoder]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_fiberwise Finset.univ (prefixNat t.1)
    (fun y => if t ∈ wzPrefixMAPCenter tau mu y then
      wzDirectionZeroMass tau mu t y else wzDirectionOneMass tau mu t y)]
  apply Finset.sum_congr rfl
  intro c _
  unfold wzPrefixMAPCenter
  by_cases hmap : wzPrefixDirectionZeroMass tau mu t c <
      wzPrefixDirectionOneMass tau mu t c
  · rw [min_eq_right hmap.le]
    rw [← wzPrefixDirectionZeroMass_eq_sum_output]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mem_filter] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hy.2, hmap, if_true]
  · rw [min_eq_left (le_of_not_gt hmap)]
    rw [← wzPrefixDirectionOneMass_eq_sum_output]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mem_filter] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hy.2, hmap, if_false]

/-- Posterior law of the clean input conditioned on a noisy prefix.  A
zero-mass prefix is totalized by the point mass at `∅`. -/
noncomputable def wzPrefixPosteriorLaw {n : ℕ} (tau : ℝ)
    (mu : Cube n → ℝ) (t : Fin n) (c x : Cube n) : ℝ :=
  if prefixMarginal (noiseMass tau mu) t.1 c = 0 then
    if x = ∅ then 1 else 0
  else
    mu x * prefixMarginal (noiseKernel tau x) t.1 c /
      prefixMarginal (noiseMass tau mu) t.1 c

lemma wzPrefixPosteriorLaw_isLaw {n : ℕ} {tau : ℝ}
    (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (c : Cube n) :
    IsLaw (wzPrefixPosteriorLaw tau mu t c) := by
  constructor
  · intro x
    unfold wzPrefixPosteriorLaw
    split_ifs
    · norm_num
    · norm_num
    · apply div_nonneg
      · exact mul_nonneg (hmu.1 x)
          (eventMass_nonneg_of_isLaw (noiseKernel_isLaw ht0 ht1 x) _)
      · exact eventMass_nonneg_of_isLaw (noiseMass_isLaw ht0 ht1 mu hmu) _
  · unfold wzPrefixPosteriorLaw
    by_cases hc : prefixMarginal (noiseMass tau mu) t.1 c = 0
    · simp [hc]
    · simp only [hc, if_false]
      rw [← Finset.sum_div]
      rw [show (∑ x, mu x * prefixMarginal (noiseKernel tau x) t.1 c) =
          prefixMarginal (noiseMass tau mu) t.1 c by
        exact (prefixMarginal_noiseMass tau mu c).symm]
      exact div_self hc

lemma prefixMass_mul_wzPrefixPosteriorLaw {n : ℕ} {tau : ℝ}
    (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (c x : Cube n) :
    prefixMarginal (noiseMass tau mu) t.1 c * wzPrefixPosteriorLaw tau mu t c x =
      mu x * prefixMarginal (noiseKernel tau x) t.1 c := by
  by_cases hc : prefixMarginal (noiseMass tau mu) t.1 c = 0
  · rw [hc, zero_mul]
    have hterm : 0 ≤ mu x * prefixMarginal (noiseKernel tau x) t.1 c :=
      mul_nonneg (hmu.1 x)
        (eventMass_nonneg_of_isLaw (noiseKernel_isLaw ht0 ht1 x) _)
    have hle : mu x * prefixMarginal (noiseKernel tau x) t.1 c ≤
        ∑ z, mu z * prefixMarginal (noiseKernel tau z) t.1 c :=
      Finset.single_le_sum
        (fun z _ => mul_nonneg (hmu.1 z)
          (eventMass_nonneg_of_isLaw (noiseKernel_isLaw ht0 ht1 z) _))
        (Finset.mem_univ x)
    rw [← prefixMarginal_noiseMass, hc] at hle
    linarith
  · unfold wzPrefixPosteriorLaw
    rw [if_neg hc, mul_div_cancel₀ _ hc]

lemma wzPrefixDirectionOneMass_eq_posterior {n : ℕ} {tau : ℝ}
    (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (c : Cube n) :
    prefixMarginal (noiseMass tau mu) t.1 c *
        (∑ x, if t ∈ adaptedCenter mu x then
          wzPrefixPosteriorLaw tau mu t c x else 0) =
      wzPrefixDirectionOneMass tau mu t c := by
  unfold wzPrefixDirectionOneMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : t ∈ adaptedCenter mu x
  · simp only [hx, if_true]
    exact prefixMass_mul_wzPrefixPosteriorLaw ht0 ht1 mu hmu t c x
  · simp [hx]

lemma wzPrefixDirectionZeroMass_eq_posterior {n : ℕ} {tau : ℝ}
    (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (c : Cube n) :
    prefixMarginal (noiseMass tau mu) t.1 c *
        (∑ x, if t ∉ adaptedCenter mu x then
          wzPrefixPosteriorLaw tau mu t c x else 0) =
      wzPrefixDirectionZeroMass tau mu t c := by
  unfold wzPrefixDirectionZeroMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : t ∈ adaptedCenter mu x
  · simp [hx]
  · simp only [hx, not_false_eq_true, if_true]
    exact prefixMass_mul_wzPrefixPosteriorLaw ht0 ht1 mu hmu t c x

/-- Per-prefix memory charge.  Strong concavity of binary entropy controls
the posterior variance of the current clean bias, and the affine BSC bias
contributes the exact factor `(1-2τ)²`. -/
lemma wzPrefixPosterior_memory_charge {n : ℕ} {tau : ℝ}
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (c : Cube n) :
    2 * (1 - 2 * tau)^2 * prefixMarginal (noiseMass tau mu) t.1 c *
        (∑ x, wzPrefixPosteriorLaw tau mu t c x *
          (condProbOne mu t x -
            ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z)^2) ≤
      prefixMarginal (noiseMass tau mu) t.1 c *
          Hb (∑ x, wzPrefixPosteriorLaw tau mu t c x *
            (tau + (1 - 2 * tau) * condProbOne mu t x)) -
        ∑ x, mu x * prefixMarginal (noiseKernel tau x) t.1 c *
          Hb (tau + (1 - 2 * tau) * condProbOne mu t x) := by
  let w : Cube n → ℝ := wzPrefixPosteriorLaw tau mu t c
  let p : Cube n → ℝ := fun x => condProbOne mu t x
  let b : Cube n → ℝ := fun x => tau + (1 - 2 * tau) * p x
  let M : ℝ := prefixMarginal (noiseMass tau mu) t.1 c
  have hwlaw : IsLaw w :=
    wzPrefixPosteriorLaw_isLaw ht0.le (ht1.le.trans (by norm_num)) mu hmu t c
  have hp : ∀ x ∈ (Finset.univ : Finset (Cube n)), p x ∈ Icc (0 : ℝ) 1 := by
    intro x _
    exact ⟨condProbOne_nonneg mu hmu t x, condProbOne_le_one mu hmu t x⟩
  have hb : ∀ x ∈ (Finset.univ : Finset (Cube n)), b x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    exact noiseBias_mem_Icc ht0.le ht1.le (hp x hx)
  have hj := Hb_jensen_gap_ge_two_variance
    (Finset.univ : Finset (Cube n)) w b
    (fun x _ => hwlaw.1 x) hwlaw.2 hb
  have hvar := var_linear_transform
    (Finset.univ : Finset (Cube n)) w p
    (fun x _ => hwlaw.1 x) hwlaw.2 tau
  have hM0 : 0 ≤ M :=
    eventMass_nonneg_of_isLaw
      (noiseMass_isLaw ht0.le (ht1.le.trans (by norm_num)) mu hmu) _
  have hmul := mul_le_mul_of_nonneg_left hj hM0
  dsimp only [b] at hvar hj hmul
  rw [hvar] at hmul
  calc
    2 * (1 - 2 * tau) ^ 2 * prefixMarginal (noiseMass tau mu) (↑t) c *
          ∑ x, wzPrefixPosteriorLaw tau mu t c x *
            (condProbOne mu t x -
                ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z) ^ 2 =
        prefixMarginal (noiseMass tau mu) t.1 c *
          (2 * ((1 - 2 * tau) ^ 2 *
            ∑ x, wzPrefixPosteriorLaw tau mu t c x *
              (condProbOne mu t x -
                ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z) ^ 2)) := by
      ring
    _ ≤ prefixMarginal (noiseMass tau mu) t.1 c *
        (Hb (∑ x, wzPrefixPosteriorLaw tau mu t c x *
              (tau + (1 - 2 * tau) * condProbOne mu t x)) -
          ∑ x, wzPrefixPosteriorLaw tau mu t c x *
            Hb (tau + (1 - 2 * tau) * condProbOne mu t x)) := hmul
    _ = prefixMarginal (noiseMass tau mu) t.1 c *
          Hb (∑ x, wzPrefixPosteriorLaw tau mu t c x *
            (tau + (1 - 2 * tau) * condProbOne mu t x)) -
        ∑ x, mu x * prefixMarginal (noiseKernel tau x) t.1 c *
          Hb (tau + (1 - 2 * tau) * condProbOne mu t x) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [← mul_assoc]
      rw [prefixMass_mul_wzPrefixPosteriorLaw ht0.le
        (ht1.le.trans (by norm_num)) mu hmu t c x]

/-- On a canonical noisy-prefix fiber, the posterior mean BSC bias is the
current noisy-bit conditional probability.  This is the Bayes normalization
needed to identify the first term in the aggregate memory charge. -/
lemma wzPrefixPosterior_bias_entropy_term {n : ℕ} {tau : ℝ}
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (c : Cube n) (hc : c ∈ prefixSupport t.1) :
    prefixMarginal (noiseMass tau mu) t.1 c *
        Hb (∑ x, wzPrefixPosteriorLaw tau mu t c x *
          (tau + (1 - 2 * tau) * condProbOne mu t x)) =
      prefixMarginal (noiseMass tau mu) t.1 c *
        Hb (eventMass (noiseMass tau mu)
          (fun y => prefixNat t.1 y = c ∧ t ∈ y) /
            prefixMarginal (noiseMass tau mu) t.1 c) := by
  have _ := hc
  let M := prefixMarginal (noiseMass tau mu) t.1 c
  by_cases hM : M = 0
  · simp [M, hM]
  · have hweighted :
        M * (∑ x, wzPrefixPosteriorLaw tau mu t c x *
          (tau + (1 - 2 * tau) * condProbOne mu t x)) =
        eventMass (noiseMass tau mu)
          (fun y => prefixNat t.1 y = c ∧ t ∈ y) := by
      rw [Finset.mul_sum]
      calc
        (∑ x, M * (wzPrefixPosteriorLaw tau mu t c x *
            (tau + (1 - 2 * tau) * condProbOne mu t x))) =
            ∑ x, (mu x * prefixMarginal (noiseKernel tau x) t.1 c) *
              (tau + (1 - 2 * tau) * condProbOne mu t x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [show M * (wzPrefixPosteriorLaw tau mu t c x *
              (tau + (1 - 2 * tau) * condProbOne mu t x)) =
              (M * wzPrefixPosteriorLaw tau mu t c x) *
                (tau + (1 - 2 * tau) * condProbOne mu t x) by ring]
          rw [show M = prefixMarginal (noiseMass tau mu) t.1 c from rfl,
            prefixMass_mul_wzPrefixPosteriorLaw ht0.le
              (ht1.le.trans (by norm_num)) mu hmu t c x]
        _ = ∑ x, mu x * prefixMarginal (noiseKernel tau x) t.1 c *
              (tau + (1 - 2 * tau) * condProbOne mu t x) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := noisePrefix_one_mass_eq tau mu hmu t c
    have havg : (∑ x, wzPrefixPosteriorLaw tau mu t c x *
          (tau + (1 - 2 * tau) * condProbOne mu t x)) =
        eventMass (noiseMass tau mu)
          (fun y => prefixNat t.1 y = c ∧ t ∈ y) / M := by
      apply (eq_div_iff hM).2
      simpa only [mul_comm] using hweighted
    rw [havg]

/-- The clean BSC-bias entropy average dominates the MGL curve at the clean
step entropy.  This is the within-step Jensen component complementary to the
posterior memory charge. -/
lemma mglCurve_stepEntropy_le_cleanNoiseBias {n : ℕ} {tau : ℝ}
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) :
    mglCurve tau (stepEntropy mu t) ≤
      ∑ x, mu x * Hb (tau + (1 - 2 * tau) * condProbOne mu t x) := by
  have hconv := (mglCurve_strictConvex ht0 ht1).convexOn
  have hp : ∀ x ∈ (Finset.univ : Finset (Cube n)),
      Hb (condProbOne mu t x) ∈ Icc (0 : ℝ) (Real.log 2) := by
    intro x _
    exact ⟨Real.binEntropy_nonneg (condProbOne_nonneg mu hmu t x)
      (condProbOne_le_one mu hmu t x), Real.binEntropy_le_log_two⟩
  have hj := hconv.map_sum_le (fun x _ => hmu.1 x) hmu.2 hp
  unfold stepEntropy
  calc
    mglCurve tau (∑ x, mu x * Hb (condProbOne mu t x)) ≤
        ∑ x, mu x * mglCurve tau (Hb (condProbOne mu t x)) := hj
    _ = ∑ x, mu x * Hb (tau + (1 - 2 * tau) * condProbOne mu t x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [mglCurve_Hb_eq_all ht0 ht1
        ⟨condProbOne_nonneg mu hmu t x, condProbOne_le_one mu hmu t x⟩]

/-- Aggregate memory charge (Lemma 4): the total posterior variance of the
clean current-bit biases over noisy-prefix fibers is bounded by `S_mem`, with
the exact strong-concavity and channel factors. -/
lemma wzPrefixPosterior_memory_charge_sum {n : ℕ} {tau : ℝ}
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    2 * (1 - 2 * tau)^2 *
        (∑ t, ∑ c ∈ prefixSupport t.1,
          prefixMarginal (noiseMass tau mu) t.1 c *
            (∑ x, wzPrefixPosteriorLaw tau mu t c x *
              (condProbOne mu t x -
                ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z)^2)) ≤
      S_mem tau mu := by
  have hnoise := noiseMass_isLaw ht0.le (ht1.le.trans (by norm_num)) mu hmu
  have hper (t : Fin n) :
      2 * (1 - 2 * tau)^2 *
          (∑ c ∈ prefixSupport t.1,
            prefixMarginal (noiseMass tau mu) t.1 c *
              (∑ x, wzPrefixPosteriorLaw tau mu t c x *
                (condProbOne mu t x -
                  ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z)^2)) ≤
        stepEntropy (noiseMass tau mu) t -
          mglCurve tau (stepEntropy mu t) := by
    have hcharges :
        ∑ c ∈ prefixSupport t.1,
          (2 * (1 - 2 * tau)^2 * prefixMarginal (noiseMass tau mu) t.1 c *
            (∑ x, wzPrefixPosteriorLaw tau mu t c x *
              (condProbOne mu t x -
                ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z)^2)) ≤
        ∑ c ∈ prefixSupport t.1,
          (prefixMarginal (noiseMass tau mu) t.1 c *
              Hb (∑ x, wzPrefixPosteriorLaw tau mu t c x *
                (tau + (1 - 2 * tau) * condProbOne mu t x)) -
            ∑ x, mu x * prefixMarginal (noiseKernel tau x) t.1 c *
              Hb (tau + (1 - 2 * tau) * condProbOne mu t x)) := by
      apply Finset.sum_le_sum
      intro c _
      exact wzPrefixPosterior_memory_charge ht0 ht1 mu hmu t c
    have hfirst :
        ∑ c ∈ prefixSupport t.1,
          prefixMarginal (noiseMass tau mu) t.1 c *
            Hb (∑ x, wzPrefixPosteriorLaw tau mu t c x *
              (tau + (1 - 2 * tau) * condProbOne mu t x)) =
        stepEntropy (noiseMass tau mu) t := by
      rw [show t = (⟨t.1, t.isLt⟩ : Fin n) from Fin.ext rfl]
      rw [stepEntropy_eq_prefix_sum (noiseMass tau mu) t.isLt]
      apply Finset.sum_congr rfl
      intro c hc
      exact wzPrefixPosterior_bias_entropy_term ht0 ht1 mu hmu t c hc
    have hsecond :
        ∑ c ∈ prefixSupport t.1,
          ∑ x, mu x * prefixMarginal (noiseKernel tau x) t.1 c *
            Hb (tau + (1 - 2 * tau) * condProbOne mu t x) =
        ∑ x, mu x * Hb (tau + (1 - 2 * tau) * condProbOne mu t x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      have hh :
          (∑ c ∈ prefixSupport t.1,
            mu x * prefixMarginal (noiseKernel tau x) t.1 c *
              Hb (tau + (1 - 2 * tau) * condProbOne mu t x)) =
          (mu x * Hb (tau + (1 - 2 * tau) * condProbOne mu t x)) *
            ∑ c ∈ prefixSupport t.1,
              prefixMarginal (noiseKernel tau x) t.1 c := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      rw [hh]
      rw [show (∑ c ∈ prefixSupport t.1,
          prefixMarginal (noiseKernel tau x) t.1 c) = 1 by
        exact sum_prefixMarginal_eq_one (noiseKernel tau x)
          (noiseKernel_isLaw ht0.le (ht1.le.trans (by norm_num)) x)]
      ring
    rw [Finset.sum_sub_distrib, hfirst, hsecond] at hcharges
    have hclean := mglCurve_stepEntropy_le_cleanNoiseBias ht0 ht1 mu hmu t
    have hfactor :
        2 * (1 - 2 * tau)^2 *
          (∑ c ∈ prefixSupport t.1,
            prefixMarginal (noiseMass tau mu) t.1 c *
              (∑ x, wzPrefixPosteriorLaw tau mu t c x *
                (condProbOne mu t x -
                  ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z)^2)) =
        ∑ c ∈ prefixSupport t.1,
          (2 * (1 - 2 * tau)^2 * prefixMarginal (noiseMass tau mu) t.1 c *
            (∑ x, wzPrefixPosteriorLaw tau mu t c x *
              (condProbOne mu t x -
                ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z)^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hfactor]
    linarith
  rw [Finset.mul_sum]
  have hsum := Finset.sum_le_sum
    (fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) => hper t)
  rw [Finset.sum_sub_distrib] at hsum
  unfold S_mem
  rw [entropy_eq_sum_stepEntropy (noiseMass tau mu) hnoise]
  exact hsum

/-- Arithmetic form of the direction-error estimate.  Here `m1,m0` are the
two separated on-flat clusters and `beta` is the off-flat mass.  The factor
two (slightly sharper than the factor four in the proof note) follows by
using whichever on-flat cluster has mass at least `1/2`, with the remaining
case paid entirely by `beta`. -/
lemma direction_minority_bound
    {pi m1 m0 beta : ℝ}
    (hm1 : 0 ≤ m1) (hm0 : 0 ≤ m0) (hbeta : 0 ≤ beta)
    (hmass : m1 + m0 + beta = 1)
    (hone : pi ≤ m1 + beta) (hzero : 1 - pi ≤ m0 + beta) :
    min pi (1 - pi) ≤ 2 * m1 * m0 + 2 * beta := by
  by_cases hm0half : 1 / 2 ≤ m0
  · have hmin : min pi (1 - pi) ≤ pi := min_le_left _ _
    have hm : m1 ≤ 2 * m1 * m0 := by nlinarith
    linarith
  · by_cases hm1half : 1 / 2 ≤ m1
    · have hmin : min pi (1 - pi) ≤ 1 - pi := min_le_right _ _
      have hm : m0 ≤ 2 * m1 * m0 := by nlinarith
      linarith
    · have hm0le : m0 ≤ 1 / 2 := le_of_not_ge hm0half
      have hm1le : m1 ≤ 1 / 2 := le_of_not_ge hm1half
      have hmin : min pi (1 - pi) ≤ 1 / 2 := by
        rcases le_total pi (1 / 2) with hpi | hpi
        · exact (min_le_left _ _).trans hpi
        · exact (min_le_right _ _).trans (by linarith)
      have hprod : 0 ≤ (1 / 2 - m1) * (1 / 2 - m0) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hprod]

lemma wzPrefix_fiber_direction_bound {n : ℕ} {tau zeta : ℝ}
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    (mu : Cube n → ℝ) (hmu : IsLaw mu) (t : Fin n) (c : Cube n) :
    min (wzPrefixDirectionOneMass tau mu t c)
        (wzPrefixDirectionZeroMass tau mu t c) ≤
      (2 / zeta ^ 2) * prefixMarginal (noiseMass tau mu) t.1 c *
        (∑ x, wzPrefixPosteriorLaw tau mu t c x *
          (condProbOne mu t x -
            ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z) ^ 2) +
      2 * (∑ x, if
        (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
          ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
        then mu x * prefixMarginal (noiseKernel tau x) t.1 c else 0) := by
  have _ := hz1
  let w : Cube n → ℝ := wzPrefixPosteriorLaw tau mu t c
  let p : Cube n → ℝ := fun x => condProbOne mu t x
  let M : ℝ := prefixMarginal (noiseMass tau mu) t.1 c
  let s1 : Finset (Cube n) := Finset.univ.filter fun x => (2 : ℝ)⁻¹ + zeta / 2 ≤ p x
  let s0 : Finset (Cube n) := Finset.univ.filter fun x => p x ≤ (2 : ℝ)⁻¹ - zeta / 2
  let beta : ℝ := ∑ x, if
    (¬ ((2 : ℝ)⁻¹ + zeta / 2 ≤ p x) ∧ ¬ (p x ≤ (2 : ℝ)⁻¹ - zeta / 2))
    then w x else 0
  let pi : ℝ := ∑ x, if (2 : ℝ)⁻¹ < p x then w x else 0
  have hwlaw : IsLaw w :=
    wzPrefixPosteriorLaw_isLaw ht0.le (ht1.le.trans (by norm_num)) mu hmu t c
  have hM0 : 0 ≤ M := eventMass_nonneg_of_isLaw
    (noiseMass_isLaw ht0.le (ht1.le.trans (by norm_num)) mu hmu) _
  have hs1 : s1 ⊆ (Finset.univ : Finset (Cube n)) := Finset.subset_univ _
  have hs0 : s0 ⊆ (Finset.univ : Finset (Cube n)) := Finset.subset_univ _
  have hdisj : Disjoint s1 s0 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx0
    simp only [s1, s0, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx0
    linarith
  have hp1 : ∀ x ∈ s1, 1 / 2 + zeta / 2 ≤ p x := by
    intro x hx
    simpa only [one_div] using (Finset.mem_filter.mp hx).2
  have hp0 : ∀ x ∈ s0, p x ≤ 1 / 2 - zeta / 2 := by
    intro x hx
    simpa only [one_div] using (Finset.mem_filter.mp hx).2
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hwlaw.1 x
    · exact le_rfl
  have hmass : (∑ x ∈ s1, w x) + (∑ x ∈ s0, w x) + beta = 1 := by
    dsimp [s1, s0, beta]
    rw [Finset.sum_filter, Finset.sum_filter]
    have hpartition :
        ((∑ x, if (2 : ℝ)⁻¹ + zeta / 2 ≤ p x then w x else 0) +
          (∑ x, if p x ≤ (2 : ℝ)⁻¹ - zeta / 2 then w x else 0)) +
          (∑ x, if ¬((2 : ℝ)⁻¹ + zeta / 2 ≤ p x) ∧
              ¬(p x ≤ (2 : ℝ)⁻¹ - zeta / 2) then w x else 0) =
        ∑ x, w x := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hhi : (2 : ℝ)⁻¹ + zeta / 2 ≤ p x
      · have hnlo : ¬p x ≤ (2 : ℝ)⁻¹ - zeta / 2 := by linarith
        simp [hhi, hnlo]
      · by_cases hlo : p x ≤ (2 : ℝ)⁻¹ - zeta / 2
        · simp [hhi, hlo]
        · simp [hhi, hlo]
    rw [hpartition, hwlaw.2]
  have hone : pi ≤ (∑ x ∈ s1, w x) + beta := by
    dsimp [pi, s1, beta]
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases hd : (2 : ℝ)⁻¹ < p x
    · by_cases hhi : (2 : ℝ)⁻¹ + zeta / 2 ≤ p x
      · simp [hd, hhi]
      · have hnlo : ¬p x ≤ (2 : ℝ)⁻¹ - zeta / 2 := by linarith
        simp [hd, hhi, hnlo]
    · rw [if_neg hd]
      exact add_nonneg (by split_ifs <;> simp_all [hwlaw.1 x]) (by
        split_ifs <;> simp_all [hwlaw.1 x])
  have hpi_zero : 1 - pi = ∑ x, if ¬ (2 : ℝ)⁻¹ < p x then w x else 0 := by
    dsimp [pi]
    have hsplit :
        (∑ x, w x) - (∑ x, if (2 : ℝ)⁻¹ < p x then w x else 0) =
          ∑ x, if ¬(2 : ℝ)⁻¹ < p x then w x else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hd : (2 : ℝ)⁻¹ < p x <;> simp [hd]
    calc
      1 - (∑ x, if (2 : ℝ)⁻¹ < p x then w x else 0) =
          (∑ x, w x) - (∑ x, if (2 : ℝ)⁻¹ < p x then w x else 0) := by
        congr 1
        exact hwlaw.2.symm
      _ = _ := hsplit
  have hzero : 1 - pi ≤ (∑ x ∈ s0, w x) + beta := by
    rw [hpi_zero]
    dsimp [s0, beta]
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases hd : (2 : ℝ)⁻¹ < p x
    · rw [if_neg (not_not_intro hd)]
      exact add_nonneg (by split_ifs <;> simp_all [hwlaw.1 x]) (by
        split_ifs <;> simp_all [hwlaw.1 x])
    · by_cases hlo : p x ≤ (2 : ℝ)⁻¹ - zeta / 2
      · simp [hd, hlo]
      · have hnhi : ¬(2 : ℝ)⁻¹ + zeta / 2 ≤ p x := by linarith
        simp [hd, hlo, hnhi]
  have hdir := normalized_two_cluster_direction_bound
    (Finset.univ : Finset (Cube n)) s1 s0 w p
    (fun x _ => hwlaw.1 x) hwlaw.2 hz0
    (by norm_num)
    hs1 hs0 hdisj hp1 hp0 hbeta hmass hone hzero
  have hmul := mul_le_mul_of_nonneg_left hdir hM0
  have honeMass : M * pi = wzPrefixDirectionOneMass tau mu t c := by
    dsimp [M, pi, p, w]
    simpa only [one_div, adaptedCenter, Finset.mem_filter, Finset.mem_univ, true_and] using
      (wzPrefixDirectionOneMass_eq_posterior
        ht0.le (ht1.le.trans (by norm_num)) mu hmu t c)
  have hzeroMass : M * (1 - pi) = wzPrefixDirectionZeroMass tau mu t c := by
    rw [hpi_zero]
    dsimp [M, p, w]
    simpa only [one_div, adaptedCenter, Finset.mem_filter, Finset.mem_univ, true_and] using
      (wzPrefixDirectionZeroMass_eq_posterior
        ht0.le (ht1.le.trans (by norm_num)) mu hmu t c)
  have hoffMass : M * beta = ∑ x, if
      (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
        ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
      then mu x * prefixMarginal (noiseKernel tau x) t.1 c else 0 := by
    dsimp [M, beta, p, w]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
        ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
    · have hxi : (¬ ((2 : ℝ)⁻¹ + zeta / 2 ≤ condProbOne mu t x) ∧
          ¬ (condProbOne mu t x ≤ (2 : ℝ)⁻¹ - zeta / 2)) := by
        simpa only [one_div] using hx
      rw [if_pos hxi, if_pos hx]
      rw [prefixMass_mul_wzPrefixPosteriorLaw ht0.le
        (ht1.le.trans (by norm_num)) mu hmu t c x]
    · have hxi : ¬ (¬ ((2 : ℝ)⁻¹ + zeta / 2 ≤ condProbOne mu t x) ∧
          ¬ (condProbOne mu t x ≤ (2 : ℝ)⁻¹ - zeta / 2)) := by
        simpa only [one_div] using hx
      rw [if_neg hxi, if_neg hx, mul_zero]
  rw [mul_min_of_nonneg pi (1 - pi) hM0, honeMass, hzeroMass] at hmul
  dsimp only [w, p, M] at hmul hoffMass
  nlinarith [hoffMass]

lemma tracking_bound_of_offFlat
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ))
    (hoff : ∑ t : Fin n, ∑ x, (if
        (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
          ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
        then mu x else 0) ≤ Real.sqrt delta * (n : ℝ)) :
    (∑ x, ∑ y, mu x * noiseKernel tau x y *
      (hDist (adaptedCenter mu x) (wzPrefixMAPCenter tau mu y) : ℝ)) / (n : ℝ) ≤
      2 * Real.log 2 / (zeta^2 * (1 - 2*tau)^2) * delta +
        2 * Real.sqrt delta := by
  let V : ℝ := ∑ t, ∑ c ∈ prefixSupport t.1,
    prefixMarginal (noiseMass tau mu) t.1 c *
      (∑ x, wzPrefixPosteriorLaw tau mu t c x *
        (condProbOne mu t x -
          ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z) ^ 2)
  let O : ℝ := ∑ t, ∑ c ∈ prefixSupport t.1, ∑ x, if
    (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
      ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
    then mu x * prefixMarginal (noiseKernel tau x) t.1 c else 0
  have hriskSupport :
      (∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (adaptedCenter mu x) (wzPrefixMAPCenter tau mu y) : ℝ)) =
      ∑ t, ∑ c ∈ prefixSupport t.1,
        min (wzPrefixDirectionOneMass tau mu t c)
          (wzPrefixDirectionZeroMass tau mu t c) := by
    rw [wzPrefixMAPCenter_expected_mismatch_eq]
    apply Finset.sum_congr rfl
    intro t _
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    have hone0 : wzPrefixDirectionOneMass tau mu t c = 0 := by
      unfold wzPrefixDirectionOneMass
      apply Finset.sum_eq_zero
      intro x _
      rw [prefixMarginal_eq_zero_of_not_mem_prefixSupport
        (noiseKernel tau x) hc]
      simp
    have hzero0 : wzPrefixDirectionZeroMass tau mu t c = 0 := by
      unfold wzPrefixDirectionZeroMass
      apply Finset.sum_eq_zero
      intro x _
      rw [prefixMarginal_eq_zero_of_not_mem_prefixSupport
        (noiseKernel tau x) hc]
      simp
    rw [hone0, hzero0, min_self]
  have hrisk :
      (∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (adaptedCenter mu x) (wzPrefixMAPCenter tau mu y) : ℝ)) ≤
      (2 / zeta ^ 2) * V + 2 * O := by
    rw [hriskSupport]
    calc
      (∑ t, ∑ c ∈ prefixSupport t.1,
          min (wzPrefixDirectionOneMass tau mu t c)
            (wzPrefixDirectionZeroMass tau mu t c)) ≤
        ∑ t, ∑ c ∈ prefixSupport t.1,
          ((2 / zeta ^ 2) * prefixMarginal (noiseMass tau mu) t.1 c *
            (∑ x, wzPrefixPosteriorLaw tau mu t c x *
              (condProbOne mu t x -
                ∑ z, wzPrefixPosteriorLaw tau mu t c z * condProbOne mu t z) ^ 2) +
          2 * (∑ x, if
            (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
              ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
            then mu x * prefixMarginal (noiseKernel tau x) t.1 c else 0)) := by
          apply Finset.sum_le_sum
          intro t _
          apply Finset.sum_le_sum
          intro c _
          exact wzPrefix_fiber_direction_bound ht0 ht1 hz0 hz1 mu hmu t c
      _ = (2 / zeta ^ 2) * V + 2 * O := by
        dsimp [V, O]
        simp_rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
  have hoffEq : O = ∑ t : Fin n, ∑ x, (if
      (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
        ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
      then mu x else 0) := by
    dsimp [O]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
        ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
    · simp_rw [if_pos hx]
      have hh :
          (∑ c ∈ prefixSupport t.1,
            mu x * prefixMarginal (noiseKernel tau x) t.1 c) =
          mu x * ∑ c ∈ prefixSupport t.1,
            prefixMarginal (noiseKernel tau x) t.1 c := by
        rw [Finset.mul_sum]
      rw [hh]
      rw [sum_prefixMarginal_eq_one (noiseKernel tau x)
        (noiseKernel_isLaw ht0.le (ht1.le.trans (by norm_num)) x), mul_one]
    · simp_rw [if_neg hx]
      simp
  have hO : O ≤ Real.sqrt delta * (n : ℝ) := by
    rw [hoffEq]
    exact hoff
  have hcharge : 2 * (1 - 2 * tau) ^ 2 * V ≤ delta * (n : ℝ) := by
    exact (wzPrefixPosterior_memory_charge_sum ht0 ht1 mu hmu).trans
      (S_mem_le_delta_n tau mu delta hmu ht0 ht1 hn h_ent)
  have hchannel : 0 < 1 - 2 * tau := by linarith
  have hden : 0 < zeta ^ 2 * (1 - 2 * tau) ^ 2 := by positivity
  have hmem : (2 / zeta ^ 2) * V ≤
      (1 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) * delta * (n : ℝ) := by
    have hexp : (2 / zeta ^ 2) * V =
        (1 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) *
          (2 * (1 - 2 * tau) ^ 2 * V) := by
      field_simp [hz0.ne', hchannel.ne']
    rw [hexp]
    calc
      (1 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) *
          (2 * (1 - 2 * tau) ^ 2 * V) ≤
          (1 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) *
            (delta * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hcharge (by positivity)
      _ = (1 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) * delta * (n : ℝ) := by ring
  have hlog : (1 : ℝ) ≤ 2 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hcoef : 1 / (zeta ^ 2 * (1 - 2 * tau) ^ 2) ≤
      2 * Real.log 2 / (zeta ^ 2 * (1 - 2 * tau) ^ 2) := by
    exact div_le_div_of_nonneg_right hlog hden.le
  have hdeltaN : 0 ≤ delta * (n : ℝ) := mul_nonneg hd0.le (Nat.cast_nonneg n)
  have hmem' : (2 / zeta ^ 2) * V ≤
      (2 * Real.log 2 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) *
        delta * (n : ℝ) := by
    apply hmem.trans
    calc
      (1 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) * delta * (n : ℝ) =
          (1 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) * (delta * (n : ℝ)) := by ring
      _ ≤ (2 * Real.log 2 / (zeta ^ 2 * (1 - 2 * tau) ^ 2)) *
          (delta * (n : ℝ)) := mul_le_mul_of_nonneg_right hcoef hdeltaN
      _ = _ := by ring
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [div_le_iff₀ hnpos]
  nlinarith [hrisk, hmem', hO]

lemma wz_expected_mismatch_rate_le_one {n : ℕ} {tau : ℝ}
    {mu : Cube n → ℝ} (hmu : IsLaw mu) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (D Dhat : Cube n → Cube n) (hn : 1 ≤ n) :
    (∑ x, ∑ y, mu x * noiseKernel tau x y *
      (hDist (D x) (Dhat y) : ℝ)) / (n : ℝ) ≤ 1 := by
  have hdist (x y : Cube n) :
      (hDist (D x) (Dhat y) : ℝ) ≤ (n : ℝ) := by
    norm_cast
    unfold hDist
    simpa using Finset.card_le_univ (symmDiff (D x) (Dhat y))
  have hrisk :
      (∑ x, ∑ y, mu x * noiseKernel tau x y *
        (hDist (D x) (Dhat y) : ℝ)) ≤ (n : ℝ) := by
    calc
      (∑ x, ∑ y, mu x * noiseKernel tau x y *
          (hDist (D x) (Dhat y) : ℝ)) ≤
          ∑ x, ∑ y, mu x * noiseKernel tau x y * (n : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hdist x y)
          (mul_nonneg (hmu.1 x)
            ((noiseKernel_isLaw ht0 ht1 x).1 y))
      _ = (n : ℝ) := by
        calc
          (∑ x, ∑ y, mu x * noiseKernel tau x y * (n : ℝ)) =
              (∑ x, ∑ y, mu x * noiseKernel tau x y) * (n : ℝ) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_mul]
          _ = (n : ℝ) := by
            have hk (x : Cube n) : ∑ y, noiseKernel tau x y = 1 :=
              (noiseKernel_isLaw ht0 ht1 x).2
            simp_rw [← Finset.mul_sum, hk, mul_one, hmu.2, one_mul]
  rw [div_le_iff₀ (Nat.cast_pos.mpr (by omega))]
  simpa using hrisk

set_option maxHeartbeats 800000 in
/-- Under the caller's smallness budget `err_val · 4τ(1-τ) < log 2`, the MGL
slack `delta` is far below the fixed channel/window threshold that the
middle-band Chebyshev estimate needs.  The eighth-root structure of `err_val`
gives an enormous margin: from `s = δ^{1/8} ≤ a²/(4τ(1-τ))` (with
`a = ζτ(1-2τ)`), the required `2√δ = 2s⁴ ≤ (τ(1-2τ))²ζ⁴ = a²ζ²` reduces to
the crude constant inequality `2a⁶ ≤ ζ²(4τ(1-τ))⁴`. -/
lemma wz_two_sqrt_delta_le_channel_window
    {tau zeta delta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) (hd0 : 0 < delta)
    (hsmall : err_val tau zeta delta * (4 * tau * (1 - tau)) < Real.log 2) :
    2 * Real.sqrt delta ≤ (tau * (1 - 2 * tau)) ^ 2 * zeta ^ 4 := by
  have h2t : 0 < 1 - 2 * tau := by linarith
  have h1t : 0 < 1 - tau := by linarith
  set a := zeta * tau * (1 - 2 * tau) with ha_def
  set c := 4 * tau * (1 - tau) with hc_def
  set s := Real.sqrt (Real.sqrt (Real.sqrt delta)) with hs_def
  clear_value a c s
  have hs0 : 0 ≤ s := by rw [hs_def]; positivity
  have hs4 : s ^ 4 = Real.sqrt delta := by
    rw [hs_def,
      show (Real.sqrt (Real.sqrt (Real.sqrt delta))) ^ 4
        = ((Real.sqrt (Real.sqrt (Real.sqrt delta))) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _)]
  have herr : err_val tau zeta delta * c = (1 + 1 / a ^ 2) * c * s := by
    rw [ha_def, hc_def, hs_def]; unfold err_val; ring
  rw [← hs4]
  clear hs_def hs4
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have hc0 : 0 < c := by rw [hc_def]; positivity
  have ha2 : 0 < a ^ 2 := pow_pos ha0 2
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  -- Step 1: `s·c ≤ a²` from the budget.
  have hkey1 : s * c ≤ a ^ 2 := by
    have hsc : 0 ≤ s * c := mul_nonneg hs0 hc0.le
    have h2 : (1 + 1 / a ^ 2) * c * s < 1 := by
      calc (1 + 1 / a ^ 2) * c * s
          = err_val tau zeta delta * c := herr.symm
        _ < Real.log 2 := hsmall
        _ ≤ 1 := hlog2
    have hfrac : (0:ℝ) ≤ 1 / a ^ 2 := by positivity
    have h1 : (1 / a ^ 2) * (s * c) ≤ (1 + 1 / a ^ 2) * c * s := by
      nlinarith [hsc]
    have h3 : (1 / a ^ 2) * (s * c) < 1 := lt_of_le_of_lt h1 h2
    have h4 := mul_lt_mul_of_pos_right h3 ha2
    rw [one_mul] at h4
    have h5 : (1 / a ^ 2) * (s * c) * a ^ 2 = s * c := by
      field_simp
    rw [h5] at h4
    exact h4.le
  -- Step 2: raise to the fourth power.
  have hkey4 : (s * c) ^ 4 ≤ (a ^ 2) ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg hs0 hc0.le) hkey1 4
  -- Step 3: the crude constant inequality `2a⁶ ≤ ζ²c⁴`.
  have haz : a ≤ zeta * tau := by
    rw [ha_def]
    nlinarith [mul_pos (mul_pos hz0 ht0) ht0]
  have ha6 : a ^ 6 ≤ (zeta * tau) ^ 6 := pow_le_pow_left₀ ha0.le haz 6
  have hz4 : zeta ^ 4 ≤ 1 / 256 := by
    have h := pow_le_pow_left₀ hz0.le hz1 4
    norm_num at h
    linarith
  have ht2 : tau ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_pos (show (0:ℝ) < 1 / 2 - tau by linarith)
      (show (0:ℝ) < 1 / 2 + tau by linarith)]
  have hz4t2 : zeta ^ 4 * tau ^ 2 ≤ 1 / 1024 := by
    have h := mul_le_mul hz4 ht2 (pow_nonneg ht0.le 2) (by norm_num)
    linarith [h]
  have hc4 : 16 * tau ^ 4 ≤ c ^ 4 := by
    rw [hc_def]
    have h1τ : (1:ℝ) / 2 ≤ 1 - tau := by linarith
    have h16 : (1/2:ℝ) ^ 4 ≤ (1 - tau) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) h1τ 4
    nlinarith [mul_nonneg (pow_nonneg ht0.le 4) (sub_nonneg.mpr h16)]
  have hmain6 : 2 * a ^ 6 ≤ zeta ^ 2 * c ^ 4 := by
    have hsplit : (zeta * tau) ^ 6 = (zeta ^ 2 * tau ^ 4) * (zeta ^ 4 * tau ^ 2) := by
      ring
    have hzt40 : (0:ℝ) ≤ zeta ^ 2 * tau ^ 4 :=
      mul_nonneg (sq_nonneg _) (pow_nonneg ht0.le 4)
    have h6 : (zeta * tau) ^ 6 ≤ (zeta ^ 2 * tau ^ 4) * (1 / 1024) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hz4t2 hzt40
    have h7 : 2 * ((zeta ^ 2 * tau ^ 4) * (1 / 1024)) ≤ zeta ^ 2 * (16 * tau ^ 4) := by
      nlinarith [hzt40]
    have h8 : zeta ^ 2 * (16 * tau ^ 4) ≤ zeta ^ 2 * c ^ 4 :=
      mul_le_mul_of_nonneg_left hc4 (sq_nonneg zeta)
    linarith [ha6, h6, h7, h8]
  -- Step 4: combine and cancel `c⁴`.
  have hmain : 2 * (a ^ 2) ^ 4 ≤ (a ^ 2 * zeta ^ 2) * c ^ 4 := by
    have h9 := mul_le_mul_of_nonneg_left hmain6 (sq_nonneg a)
    nlinarith [h9]
  have hc40 : 0 < c ^ 4 := pow_pos hc0 4
  have hfin : 2 * s ^ 4 ≤ a ^ 2 * zeta ^ 2 := by
    have h1 : (2 * s ^ 4) * c ^ 4 ≤ (a ^ 2 * zeta ^ 2) * c ^ 4 := by
      have hlhs : (2 * s ^ 4) * c ^ 4 = 2 * (s * c) ^ 4 := by ring
      rw [hlhs]
      calc 2 * (s * c) ^ 4 ≤ 2 * (a ^ 2) ^ 4 := by linarith [hkey4]
        _ ≤ (a ^ 2 * zeta ^ 2) * c ^ 4 := hmain
    exact le_of_mul_le_mul_right h1 hc40
  have hid : a ^ 2 * zeta ^ 2 = (tau * (1 - 2 * tau)) ^ 2 * zeta ^ 4 := by
    rw [ha_def]; ring
  linarith [hfin, hid.le, hid.ge]

set_option maxHeartbeats 800000 in
/-- The middle band `condProbOne ∈ (½-ζ/2, ½+ζ/2)` carries at most `√δ·n`
mass once `2√δ ≤ (τ(1-2τ))²ζ⁴`.  Each middle-band step has conditional
entropy at least `Hb(½-ζ/2)`, which exceeds the entropy rate (at most
`Hb(½-ζ)` on the window) by the fixed gap `ζ²`; Chebyshev against the
quantitative flatness estimate `condEntropy_sq_deviation_bound` finishes. -/
lemma wz_middle_band_mass_le_sqrt_delta
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ))
    (hdsmall : 2 * Real.sqrt delta ≤ (tau * (1 - 2 * tau)) ^ 2 * zeta ^ 4) :
    ∑ t : Fin n, ∑ x, (if
        (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
          ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
        then mu x else 0) ≤ Real.sqrt delta * (n : ℝ) := by
  have h2t : 0 < 1 - 2 * tau := by linarith
  set u := entropyRate n mu with hu_def
  -- The fixed entropy gap of the middle band over the window.
  have hderiv : 2 * zeta ≤ deriv Hb (1 / 2 - zeta / 2) :=
    deriv_Hb_window_ge_two_zeta hz0 hz1
  have hgrow : deriv Hb (1 / 2 - zeta / 2) * ((1 / 2 - zeta / 2) - (1 / 2 - zeta)) ≤
      Hb (1 / 2 - zeta / 2) - Hb (1 / 2 - zeta) :=
    Hb_growth_ge_terminal_deriv (by linarith) (by linarith) le_rfl (by linarith)
  have hgap : zeta ^ 2 ≤ Hb (1 / 2 - zeta / 2) - Hb (1 / 2 - zeta) := by
    nlinarith [hderiv, hgrow, hz0.le]
  -- The entropy rate sits below `Hb(½-ζ)`.
  have hu_mem : u ∈ Ioo (0 : ℝ) (Real.log 2) :=
    entropyRate_mem_Ioo_of_hbInv_window hz0 hzeta1 hzeta2
  have hspec := hbInv_spec ⟨hu_mem.1.le, hu_mem.2.le⟩
  have hu_le : u ≤ Hb (1 / 2 - zeta) := by
    have hmem1 : hbInv u ∈ Icc (0 : ℝ) 2⁻¹ := by
      simpa [one_div] using hspec.1
    have hmem2 : (1 / 2 - zeta : ℝ) ∈ Icc (0 : ℝ) 2⁻¹ := by
      constructor
      · linarith
      · rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num]; linarith
    have hmono : Hb (hbInv u) ≤ Hb (1 / 2 - zeta) :=
      Real.binEntropy_strictMonoOn.monotoneOn hmem1 hmem2 hzeta2
    rw [hspec.2] at hmono
    exact hmono
  -- Pointwise: on the middle band the conditional entropy exceeds `u` by `ζ²`.
  have hpoint : ∀ (t : Fin n) (x : Cube n),
      (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
        ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2)) →
      zeta ^ 2 ≤ condEntropy mu t x - u := by
    intro t x hmid
    obtain ⟨h1, h2⟩ := hmid
    push_neg at h1 h2
    have hmm := conditionalMismatch_mem_Icc_half mu hmu t x
    have hmlow : 1 / 2 - zeta / 2 ≤ conditionalMismatch mu t x := by
      unfold conditionalMismatch
      split_ifs with h
      · linarith
      · linarith
    have hmemA : (1 / 2 - zeta / 2 : ℝ) ∈ Icc (0 : ℝ) 2⁻¹ := by
      constructor
      · linarith
      · rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num]; linarith
    have hmemB : conditionalMismatch mu t x ∈ Icc (0 : ℝ) 2⁻¹ := by
      simpa [one_div] using hmm
    have hHbmono : Hb (1 / 2 - zeta / 2) ≤ Hb (conditionalMismatch mu t x) :=
      Real.binEntropy_strictMonoOn.monotoneOn hmemA hmemB hmlow
    have hce : condEntropy mu t x = Hb (conditionalMismatch mu t x) :=
      condEntropy_eq_Hb_conditionalMismatch mu t x
    rw [hce]
    linarith [hgap, hu_le, hHbmono]
  -- Chebyshev against the quantitative flatness bound.
  set M := ∑ t : Fin n, ∑ x, (if
      (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
        ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
      then mu x else 0) with hM_def
  have hcheb : M * zeta ^ 4 ≤
      ∑ t, ∑ x, mu x * (condEntropy mu t x - u) ^ 2 := by
    rw [hM_def, Finset.sum_mul]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with hmid
    · have hdd : zeta ^ 2 ≤ condEntropy mu t x - u := hpoint t x hmid
      have hz2 : (0:ℝ) ≤ zeta ^ 2 := sq_nonneg _
      have h4 : zeta ^ 4 ≤ (condEntropy mu t x - u) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h4 (hmu.1 x)
    · rw [zero_mul]
      exact mul_nonneg (hmu.1 x) (sq_nonneg _)
  have hV := condEntropy_sq_deviation_bound ht0 ht1 hz0 hmu hzeta1 hzeta2 h_ent
  rw [← hu_def] at hV
  set c2 := (tau * (1 - 2 * tau)) ^ 2 / 2 with hc2_def
  have hc2 : 0 < c2 := by
    rw [hc2_def]
    exact div_pos (pow_pos (mul_pos ht0 h2t) 2) two_pos
  have hK : 0 < c2 * zeta ^ 4 := mul_pos hc2 (pow_pos hz0 4)
  -- `√δ ≤ c₂ζ⁴` and `δ ≤ √δ·c₂ζ⁴`.
  have hsd : Real.sqrt delta ≤ c2 * zeta ^ 4 := by
    rw [hc2_def]
    linarith [hdsmall]
  have hδle : delta ≤ Real.sqrt delta * (c2 * zeta ^ 4) := by
    calc delta = Real.sqrt delta * Real.sqrt delta :=
        (Real.mul_self_sqrt hd0.le).symm
      _ ≤ Real.sqrt delta * (c2 * zeta ^ 4) :=
        mul_le_mul_of_nonneg_left hsd (Real.sqrt_nonneg delta)
  -- Chain everything and cancel the positive factor `c₂ζ⁴`.
  have h1 : c2 * (M * zeta ^ 4) ≤
      c2 * (∑ t, ∑ x, mu x * (condEntropy mu t x - u) ^ 2) :=
    mul_le_mul_of_nonneg_left hcheb hc2.le
  have h2 : c2 * (∑ t, ∑ x, mu x * (condEntropy mu t x - u) ^ 2) ≤
      delta * (n : ℝ) := by
    calc c2 * (∑ t, ∑ x, mu x * (condEntropy mu t x - u) ^ 2)
        = (tau * (1 - 2 * tau)) ^ 2 / 2 *
          (∑ t, ∑ x, mu x * (condEntropy mu t x - u) ^ 2) := by rw [hc2_def]
      _ ≤ delta * (n : ℝ) := hV
  have h3 : delta * (n : ℝ) ≤ (Real.sqrt delta * (c2 * zeta ^ 4)) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hδle (Nat.cast_nonneg n)
  have h5 : M * (c2 * zeta ^ 4) ≤ (Real.sqrt delta * (n : ℝ)) * (c2 * zeta ^ 4) := by
    calc M * (c2 * zeta ^ 4) = c2 * (M * zeta ^ 4) := by ring
      _ ≤ delta * (n : ℝ) := h1.trans h2
      _ ≤ (Real.sqrt delta * (c2 * zeta ^ 4)) * (n : ℝ) := h3
      _ = (Real.sqrt delta * (n : ℝ)) * (c2 * zeta ^ 4) := by ring
  exact le_of_mul_le_mul_right h5 hK

lemma tracking_expected_mismatch_bound
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ))
    (hsmall : err_val tau zeta delta * (4 * tau * (1 - tau)) < Real.log 2) :
    ∃ Dhat : Cube n → Cube n,
      (∑ x, ∑ y, mu x * noiseKernel tau x y * (hDist (adaptedCenter mu x) (Dhat y) : ℝ)) / (n : ℝ) ≤
        2 * Real.log 2 / (zeta^2 * (1 - 2*tau)^2) * delta + 2 * Real.sqrt delta := by
  have hdsmall : 2 * Real.sqrt delta ≤ (tau * (1 - 2 * tau)) ^ 2 * zeta ^ 4 :=
    wz_two_sqrt_delta_le_channel_window ht0 ht1 hz0 hz1 hd0 hsmall
  have hoff : ∑ t : Fin n, ∑ x, (if
      (¬ (1 / 2 + zeta / 2 ≤ condProbOne mu t x) ∧
        ¬ (condProbOne mu t x ≤ 1 / 2 - zeta / 2))
      then mu x else 0) ≤ Real.sqrt delta * (n : ℝ) :=
    wz_middle_band_mass_le_sqrt_delta ht0 ht1 hz0 hz1 hmu hd0 hzeta1 hzeta2 h_ent hdsmall
  exact ⟨wzPrefixMAPCenter tau mu,
    tracking_bound_of_offFlat ht0 ht1 hz0 hz1 hn hmu hd0 h_ent hoff⟩

/-- Binary entropy is bounded by `2√q` on `[0,1)`.  Both `negMulLog` terms are
controlled by `log x ≤ x - 1`: writing `q = (√q)²` gives
`negMulLog q = 2q·log (√q)⁻¹ ≤ 2√q - 2q`, while `negMulLog (1-q) ≤ q`. -/
private lemma Hb_le_two_sqrt {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Hb q ≤ 2 * Real.sqrt q := by
  have hbranch2 : Real.negMulLog (1 - q) ≤ q := by
    have h1q : 0 < 1 - q := by linarith
    have heq : Real.negMulLog (1 - q) = (1 - q) * Real.log ((1 - q)⁻¹) := by
      show -(1 - q) * Real.log (1 - q) = (1 - q) * Real.log ((1 - q)⁻¹)
      rw [Real.log_inv]; ring
    rw [heq]
    have hlog : Real.log ((1 - q)⁻¹) ≤ (1 - q)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    calc (1 - q) * Real.log ((1 - q)⁻¹)
        ≤ (1 - q) * ((1 - q)⁻¹ - 1) := mul_le_mul_of_nonneg_left hlog (le_of_lt h1q)
      _ = (1 - q) * (1 - q)⁻¹ - (1 - q) := by ring
      _ = 1 - (1 - q) := by rw [mul_inv_cancel₀ (ne_of_gt h1q)]
      _ = q := by ring
  have hbranch1 : Real.negMulLog q ≤ 2 * Real.sqrt q - 2 * q := by
    rcases eq_or_lt_of_le hq0 with hq | hq
    · rw [← hq]; simp
    · have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
      have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
      have hlogq : Real.log q = 2 * Real.log (Real.sqrt q) := by
        rw [Real.log_sqrt hq0]; ring
      have heq : Real.negMulLog q = 2 * q * Real.log ((Real.sqrt q)⁻¹) := by
        show -q * Real.log q = 2 * q * Real.log ((Real.sqrt q)⁻¹)
        rw [Real.log_inv, hlogq]; ring
      rw [heq]
      have hlog : Real.log ((Real.sqrt q)⁻¹) ≤ (Real.sqrt q)⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hqinv : q * (Real.sqrt q)⁻¹ = Real.sqrt q := by
        rw [← div_eq_mul_inv, div_eq_iff (ne_of_gt hs)]; linarith [hsq]
      calc 2 * q * Real.log ((Real.sqrt q)⁻¹)
          ≤ 2 * q * ((Real.sqrt q)⁻¹ - 1) :=
            mul_le_mul_of_nonneg_left hlog (by linarith [hq0])
        _ = 2 * (q * (Real.sqrt q)⁻¹) - 2 * q := by ring
        _ = 2 * Real.sqrt q - 2 * q := by rw [hqinv]
  have hsum : Hb q = Real.negMulLog q + Real.negMulLog (1 - q) := by
    unfold Hb
    exact Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub q
  rw [hsum]; linarith

/-- Sqrt-free form of the entropy bound: if `q ≤ B²` with `0 ≤ B` then
`Hb q ≤ 2B`.  Keeping the `Real.sqrt` inside this helper (rather than in
`fano_to_err_val`) matters for performance: a lingering `Real.sqrt` atom makes
`linarith`/`positivity` whnf it on every call. -/
private lemma Hb_le_two_mul_of_le_sq {q B : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hB : 0 ≤ B) (hqB : q ≤ B ^ 2) :
    Hb q ≤ 2 * B := by
  calc Hb q ≤ 2 * Real.sqrt q := Hb_le_two_sqrt hq0 hq1
    _ ≤ 2 * Real.sqrt (B ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqB) (by norm_num)
    _ = 2 * B := by rw [Real.sqrt_sq hB]

/-- `4τ/a ≤ (1+1/a²)·c/2` where `a = ζτ(1-2τ)`, `c = 4τ(1-τ)`.  Extracted so its
`field_simp` cost does not count against `fano_to_err_val`'s heartbeat budget. -/
private lemma wz_hcore_bound {tau a c : ℝ} (ht0 : 0 < tau) (ha0 : 0 < a)
    (hc_def : c = 4 * tau * (1 - tau)) (h2a : 2 * a ≤ 1 - tau) :
    4 * tau / a ≤ (1 + 1 / a ^ 2) * c / 2 := by
  have hane : a ≠ 0 := ha0.ne'
  rw [← sub_nonneg]
  have key : (1 + 1 / a ^ 2) * c / 2 - 4 * tau / a
      = ((a ^ 2 + 1) * c - 8 * tau * a) / (2 * a ^ 2) := by
    field_simp; ring
  rw [key]
  apply div_nonneg _ (by positivity)
  rw [hc_def]
  nlinarith [mul_nonneg (mul_nonneg ht0.le (show (0:ℝ) ≤ 1 - tau by linarith)) (sq_nonneg a),
    mul_nonneg ht0.le (show (0:ℝ) ≤ (1 - tau) - 2 * a by linarith [h2a])]

/-- `1 ≤ (1+1/a²)·c/2` where `c = 4τ(1-τ)` and `a² ≤ 2τ(1-τ)`.  Extracted for the
same heartbeat reason as `wz_hcore_bound`. -/
private lemma wz_hge1_bound {tau a c : ℝ} (ha0 : 0 < a)
    (hc_def : c = 4 * tau * (1 - tau)) (ha2_le : a ^ 2 ≤ 2 * tau * (1 - tau)) :
    (1:ℝ) ≤ (1 + 1 / a ^ 2) * c / 2 := by
  have hane : a ≠ 0 := ha0.ne'
  rw [← sub_nonneg]
  have key : (1 + 1 / a ^ 2) * c / 2 - 1 = ((a ^ 2 + 1) * c - 2 * a ^ 2) / (2 * a ^ 2) := by
    field_simp
  rw [key]
  apply div_nonneg _ (by positivity)
  have hc0' : 0 ≤ c := by rw [hc_def]; nlinarith [ha2_le, sq_nonneg a]
  have h2a2c : 2 * a ^ 2 ≤ c := by rw [hc_def]; nlinarith [ha2_le]
  nlinarith [h2a2c, mul_nonneg (sq_nonneg a) hc0']

-- The `err_val`/`Hb` arithmetic below is long and every automation step must
-- `whnf` the pervasive `Real.log 2` / `Real.sqrt` atoms, so a finite heartbeat
-- bump keeps it in one declaration.  (`maxHeartbeats 0` is the only value the
-- audit forbids; this is a bounded increase.)
set_option maxHeartbeats 400000 in
lemma fano_to_err_val
    {tau zeta delta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) (hd0 : 0 < delta)
    {m : ℝ} (hm0 : 0 ≤ m)
    (hm_bound : m ≤ 2 * Real.log 2 / (zeta^2 * (1 - 2*tau)^2) * delta + 2 * Real.sqrt delta) :
    Hb (min m (1/2)) ≤ err_val tau zeta delta * (4 * tau * (1 - tau)) / 2 := by
  set a := zeta * tau * (1 - 2 * tau) with ha_def
  set c := 4 * tau * (1 - tau) with hc_def
  set s := Real.sqrt (Real.sqrt (Real.sqrt delta)) with hs_def
  clear_value a c s
  have hchannel : 0 < 1 - 2 * tau := by linarith
  -- Establish `δ = s⁸`, `√δ = s⁴` and the `err_val` identity while the nested
  -- `Real.sqrt` definition of `s` is available, then drop `hs_def`: leaving it in
  -- context makes every later `linarith`/`positivity` whnf the triple `Real.sqrt`,
  -- which blows the heartbeat budget.
  have hs0 : 0 ≤ s := by rw [hs_def]; positivity
  have hs4 : s ^ 4 = Real.sqrt delta := by
    rw [hs_def,
      show (Real.sqrt (Real.sqrt (Real.sqrt delta))) ^ 4
        = ((Real.sqrt (Real.sqrt (Real.sqrt delta))) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hs8 : s ^ 8 = delta := by
    rw [show s ^ 8 = (s ^ 4) ^ 2 by ring, hs4, Real.sq_sqrt hd0.le]
  have herr : err_val tau zeta delta * c = (1 + 1 / a ^ 2) * c * s := by
    rw [ha_def, hc_def, hs_def]; unfold err_val; ring
  rw [show Real.sqrt delta = s ^ 4 from hs4.symm] at hm_bound
  clear hs_def hs4
  have hane : a ≠ 0 := by rw [ha_def]; positivity
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have ha2pos : 0 < a ^ 2 := pow_pos ha0 2
  have hc0 : 0 < c := by
    rw [hc_def]; nlinarith [mul_pos ht0 (show (0:ℝ) < 1 - tau by linarith)]
  have hlog2 : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
  have ha_sq : a ^ 2 = zeta ^ 2 * tau ^ 2 * (1 - 2 * tau) ^ 2 := by rw [ha_def]; ring
  -- a-bounds (all with room; these are the constant-dependence checks).
  have hzc1 : zeta * (1 - 2 * tau) ≤ 1 := by
    have := mul_le_mul hz1 (show 1 - 2 * tau ≤ 1 by linarith) hchannel.le
      (by norm_num : (0:ℝ) ≤ 1 / 4)
    linarith
  have ha_le_tau : a ≤ tau := by
    rw [ha_def, show zeta * tau * (1 - 2 * tau) = tau * (zeta * (1 - 2 * tau)) by ring]
    calc tau * (zeta * (1 - 2 * tau)) ≤ tau * 1 := mul_le_mul_of_nonneg_left hzc1 ht0.le
      _ = tau := mul_one tau
  have ha2_le_tau2 : a ^ 2 ≤ tau ^ 2 := by nlinarith [ha_le_tau, ha0, ht0]
  have h2a : 2 * a ≤ 1 - tau := by
    rw [ha_def]
    nlinarith [mul_le_mul_of_nonneg_right hz1 (mul_nonneg ht0.le hchannel.le),
      sq_nonneg (4 * tau - 3), mul_nonneg ht0.le hchannel.le]
  have ha2_le : a ^ 2 ≤ 2 * tau * (1 - tau) := by
    have h1 : tau ^ 2 ≤ tau := by nlinarith [ht0, ht1]
    have h2 : tau ≤ 2 * tau * (1 - tau) := by nlinarith [mul_nonneg ht0.le hchannel.le]
    linarith [ha2_le_tau2]
  -- Core numeric bounds on the target coefficient (extracted helpers).
  have hcore : 4 * tau / a ≤ (1 + 1 / a ^ 2) * c / 2 := wz_hcore_bound ht0 ha0 hc_def h2a
  have hge1 : (1:ℝ) ≤ (1 + 1 / a ^ 2) * c / 2 := wz_hge1_bound ha0 hc_def ha2_le
  have hRnn : 0 ≤ (1 + 1 / a ^ 2) * c / 2 := by linarith [hge1]
  -- q = min m (1/2) facts.
  have hq_nonneg : 0 ≤ min m (1 / 2) := le_min hm0 (by norm_num)
  have hq_le_half : min m (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hq_lt_one : min m (1 / 2) < 1 := lt_of_le_of_lt hq_le_half (by norm_num)
  rw [herr]
  rcases le_or_gt delta 1 with hd1 | hd1
  · -- Small delta: m = O(√δ); δ = s⁸, √δ = s⁴, and Hb(q) ≤ 2√q.
    have hs_le1 : s ≤ 1 :=
      (pow_le_one_iff_of_nonneg hs0 (by norm_num : (8:ℕ) ≠ 0)).mp (by rw [hs8]; exact hd1)
    have hs2_le1 : s ^ 2 ≤ 1 := by nlinarith [hs_le1, hs0]
    have hs4_le1 : s ^ 4 ≤ 1 := by nlinarith [hs2_le1, sq_nonneg s]
    have hKle : 2 * Real.log 2 / (zeta ^ 2 * (1 - 2 * tau) ^ 2) ≤ 2 * tau ^ 2 / a ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos (pow_pos hz0 2) (pow_pos hchannel 2)) ha2pos, ha_sq]
      have hP : (0:ℝ) ≤ zeta ^ 2 * tau ^ 2 * (1 - 2 * tau) ^ 2 := by positivity
      calc 2 * Real.log 2 * (zeta ^ 2 * tau ^ 2 * (1 - 2 * tau) ^ 2)
          ≤ 2 * 1 * (zeta ^ 2 * tau ^ 2 * (1 - 2 * tau) ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith [hlog2]) hP
        _ = 2 * tau ^ 2 * (zeta ^ 2 * (1 - 2 * tau) ^ 2) := by ring
    have hm_r : m ≤ (4 * tau ^ 2 / a ^ 2) * s ^ 4 := by
      have h1 : 2 * Real.log 2 / (zeta ^ 2 * (1 - 2 * tau) ^ 2) * delta
          ≤ (2 * tau ^ 2 / a ^ 2) * s ^ 4 := by
        rw [← hs8]
        calc 2 * Real.log 2 / (zeta ^ 2 * (1 - 2 * tau) ^ 2) * s ^ 8
            ≤ (2 * tau ^ 2 / a ^ 2) * s ^ 8 :=
              mul_le_mul_of_nonneg_right hKle (by positivity)
          _ ≤ (2 * tau ^ 2 / a ^ 2) * s ^ 4 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [hs4_le1, pow_nonneg hs0 4]
      have hle : (2 : ℝ) ≤ 2 * tau ^ 2 / a ^ 2 := by
        rw [le_div_iff₀ ha2pos]; nlinarith [ha2_le_tau2]
      have hb : 4 * tau ^ 2 / a ^ 2 = 2 * tau ^ 2 / a ^ 2 + 2 * tau ^ 2 / a ^ 2 := by ring
      calc m ≤ 2 * Real.log 2 / (zeta ^ 2 * (1 - 2 * tau) ^ 2) * delta + 2 * s ^ 4 := hm_bound
        _ ≤ (2 * tau ^ 2 / a ^ 2) * s ^ 4 + 2 * s ^ 4 := by linarith [h1]
        _ = (2 * tau ^ 2 / a ^ 2 + 2) * s ^ 4 := by ring
        _ ≤ (4 * tau ^ 2 / a ^ 2) * s ^ 4 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith [hle, hb]
    have hs2_le_s : s ^ 2 ≤ s := by
      nlinarith [mul_nonneg hs0 (show (0:ℝ) ≤ 1 - s by linarith [hs_le1])]
    have hB2 : 0 ≤ 2 * tau / a := div_nonneg (mul_nonneg (by norm_num) ht0.le) ha0.le
    have hB4 : 0 ≤ 4 * tau / a := div_nonneg (mul_nonneg (by norm_num) ht0.le) ha0.le
    -- Package the entropy bound sqrt-free: `q ≤ ((2τ/a)s²)²`.
    have hq_le : min m (1 / 2) ≤ ((2 * tau / a) * s ^ 2) ^ 2 := by
      calc min m (1 / 2) ≤ (4 * tau ^ 2 / a ^ 2) * s ^ 4 := le_trans (min_le_left _ _) hm_r
        _ = ((2 * tau / a) * s ^ 2) ^ 2 := by ring
    calc Hb (min m (1 / 2))
        ≤ 2 * ((2 * tau / a) * s ^ 2) :=
          Hb_le_two_mul_of_le_sq hq_nonneg hq_lt_one (mul_nonneg hB2 (sq_nonneg s)) hq_le
      _ = (4 * tau / a) * s ^ 2 := by ring
      _ ≤ (4 * tau / a) * s := mul_le_mul_of_nonneg_left hs2_le_s hB4
      _ ≤ ((1 + 1 / a ^ 2) * c / 2) * s := mul_le_mul_of_nonneg_right hcore hs0
      _ = (1 + 1 / a ^ 2) * c * s / 2 := by ring
  · -- Large delta: constant `1/a²` alone dominates `Hb ≤ log 2 ≤ 1`.
    have hs1 : 1 ≤ s :=
      (one_le_pow_iff_of_nonneg hs0 (by norm_num : (8:ℕ) ≠ 0)).mp (by rw [hs8]; linarith [hd1])
    have hHb_le : Hb (min m (1 / 2)) ≤ Real.log 2 := by
      unfold Hb; exact Real.binEntropy_le_log_two
    calc Hb (min m (1 / 2))
        ≤ Real.log 2 := hHb_le
      _ ≤ 1 := hlog2
      _ ≤ (1 + 1 / a ^ 2) * c / 2 := hge1
      _ = ((1 + 1 / a ^ 2) * c / 2) * 1 := by ring
      _ ≤ ((1 + 1 / a ^ 2) * c / 2) * s := mul_le_mul_of_nonneg_left hs1 hRnn
      _ = (1 + 1 / a ^ 2) * c * s / 2 := by ring

/-- Remaining tracking leaf.  In the nontrivial small-error branch, near-MGL
equality and the entropy window must make the adapted label predictable from
the noisy output.  This is precisely the `H(D | Q)` estimate (Corollary 8 in
the proof note); no conditional-MGL or final sandwich algebra remains here. -/
lemma adaptedCenter_conditionalLabelEntropy_bound
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ))
    (hsmall : err_val tau zeta delta * (4 * tau * (1 - tau)) < Real.log 2) :
    wzConditionalLabelEntropy tau mu (adaptedCenter mu) ≤
      (err_val tau zeta delta * (4 * tau * (1 - tau)) / 2) * (n : ℝ) := by
  obtain ⟨Dhat, hDhat⟩ := tracking_expected_mismatch_bound ht0 ht1 hz0 hz1 hn hmu hd0 hzeta1 hzeta2 h_ent hsmall
  have htau0_le : 0 ≤ tau := ht0.le
  have htau1_le : tau ≤ 1 := ht1.le.trans (by norm_num)
  have hfano := fano_mismatch_bound tau mu hmu htau0_le htau1_le (adaptedCenter mu) Dhat
  have hm_nonneg : 0 ≤ (∑ x, ∑ y, mu x * noiseKernel tau x y * (hDist (adaptedCenter mu x) (Dhat y) : ℝ)) / (n : ℝ) := by
    apply div_nonneg
    · apply Finset.sum_nonneg; intro x _
      apply Finset.sum_nonneg; intro y _
      have h1 := hmu.1 x
      have h2 := (noiseKernel_isLaw (n := n) htau0_le htau1_le x).1 y
      positivity
    · positivity
  have h_calc := fano_to_err_val ht0 ht1 hz0 hz1 hd0 hm_nonneg hDhat
  have h_n_pos : 0 ≤ (n : ℝ) := by positivity
  calc
    wzConditionalLabelEntropy tau mu (adaptedCenter mu) ≤ (n : ℝ) * Hb (min ((∑ x, ∑ y, mu x * noiseKernel tau x y * (hDist (adaptedCenter mu x) (Dhat y) : ℝ)) / (n : ℝ)) (1/2)) := hfano
    _ ≤ (n : ℝ) * (err_val tau zeta delta * (4 * tau * (1 - tau)) / 2) := mul_le_mul_of_nonneg_left h_calc h_n_pos
    _ = (err_val tau zeta delta * (4 * tau * (1 - tau)) / 2) * (n : ℝ) := by ring

lemma wyner_ziv_sandwich
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ)) :
    (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ) ≥
      entropy (mapMass mu (adaptedCenter mu)) -
      ((err_val tau zeta delta * (4 * tau * (1 - tau)) - delta) * (n : ℝ)) +
      (n : ℝ) * mglCurve tau
        ((entropy mu - entropy (mapMass mu (adaptedCenter mu))) / (n : ℝ)) := by
  by_cases hlarge : Real.log 2 ≤
      err_val tau zeta delta * (4 * tau * (1 - tau))
  · let H_D := entropy (mapMass mu (adaptedCenter mu))
    let u := entropyRate n mu
    let theta := H_D / (n : ℝ)
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hDlaw := mapMass_isLaw' mu hmu (adaptedCenter mu)
    have hHDdim : H_D ≤ (n : ℝ) * Real.log 2 :=
      entropy_le_dim_log2' hn _ hDlaw
    have hbudget : H_D ≤
        err_val tau zeta delta * (4 * tau * (1 - tau)) * (n : ℝ) := by
      calc
        H_D ≤ (n : ℝ) * Real.log 2 := hHDdim
        _ ≤ (n : ℝ) *
            (err_val tau zeta delta * (4 * tau * (1 - tau))) :=
          mul_le_mul_of_nonneg_left hlarge hnpos.le
        _ = _ := by ring
    have hH0 : 0 ≤ H_D := entropy_nonneg' _ hDlaw
    have htheta0 : 0 ≤ theta := div_nonneg hH0 hnpos.le
    have hmaple : H_D ≤ entropy mu := entropy_mapMass_le' mu hmu _
    have hu : u ∈ Icc (0 : ℝ) (Real.log 2) := entropyRate_mem_Icc' hn mu hmu
    have huw : u - theta ∈ Icc (0 : ℝ) (Real.log 2) := by
      constructor
      · dsimp [u, theta, H_D, entropyRate]
        rw [← sub_div]
        exact div_nonneg (sub_nonneg.mpr hmaple) hnpos.le
      · linarith [hu.2, htheta0]
    have hgmono : mglCurve tau (u - theta) ≤ mglCurve tau u :=
      mglCurve_mono ht0 ht1 huw hu (by linarith)
    have hgmono_n : (n : ℝ) * mglCurve tau (u - theta) ≤
        (n : ℝ) * mglCurve tau u :=
      mul_le_mul_of_nonneg_left hgmono hnpos.le
    have harg :
        (entropy mu - entropy (mapMass mu (adaptedCenter mu))) / (n : ℝ) =
          u - theta := by
      dsimp [u, theta, H_D, entropyRate]
      ring
    rw [harg]
    dsimp only [u] at hgmono_n ⊢
    dsimp only [H_D] at hbudget
    linarith [hgmono_n]
  · have hsmall : err_val tau zeta delta * (4 * tau * (1 - tau)) <
        Real.log 2 := lt_of_not_ge hlarge
    have hcond := adaptedCenter_conditionalLabelEntropy_bound
      ht0 ht1 hz0 hz1 hn hmu hd0 hzeta1 hzeta2 h_ent hsmall
    have hdelta := two_delta_le_wz_budget ht0 ht1 hz0 hz1 hd0 hsmall
    have hhalf : err_val tau zeta delta * (4 * tau * (1 - tau)) / 2 ≤
        err_val tau zeta delta * (4 * tau * (1 - tau)) - delta := by
      linarith
    have hcond' := hcond.trans
      (mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg n))
    have hmgl := conditional_mgl_label_sandwich tau mu hmu ht0 ht1 hn
      (adaptedCenter mu)
    linarith [hcond']


end AverageHarperStability
