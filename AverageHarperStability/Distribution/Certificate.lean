import AverageHarperStability.Distribution.WynerZiv
import AverageHarperStability.Distribution.Flatness

open scoped BigOperators
open Filter Topology Set Classical

namespace AverageHarperStability

attribute [local instance] Classical.propDecidable

lemma label_entropy_bound
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta err : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ))
    (herr0 : 0 < err) (hsmall : err < Real.log 2)
    (herr_val : err_val tau zeta delta ≤ err) :
    entropy (mapMass mu (adaptedCenter mu)) ≤ err * (n : ℝ) := by
  have _ := herr0
  have _ := hsmall
  have h_sandwich :=
    wyner_ziv_sandwich ht0 ht1 hz0 hz1 hn hmu hd0 hzeta1 hzeta2 h_ent
  set H_D := entropy (mapMass mu (adaptedCenter mu))
  set u := entropyRate n mu
  set theta := H_D / (n : ℝ)
  have h_theta_nonneg : 0 ≤ theta :=
    div_nonneg (entropy_mapMass_nonneg mu hmu (adaptedCenter mu)) (by positivity)
  have h_secant := mglCurve_secant_bound ht0 ht1 u theta h_theta_nonneg
  have h_n_pos : 0 < (n : ℝ) := by positivity
  have h_secant_n : (n : ℝ) * mglCurve tau u - (n : ℝ) * mglCurve tau (u - theta) ≤ (n : ℝ) * ((1 - 2 * tau)^2 * theta) := by
    calc
      (n : ℝ) * mglCurve tau u - (n : ℝ) * mglCurve tau (u - theta) = (n : ℝ) * (mglCurve tau u - mglCurve tau (u - theta)) := by ring
      _ ≤ (n : ℝ) * ((1 - 2 * tau)^2 * theta) := mul_le_mul_of_nonneg_left h_secant (by positivity)
  have h_alg : H_D * (4 * tau * (1 - tau)) ≤ err_val tau zeta delta * (4 * tau * (1 - tau)) * (n : ℝ) := by
    have h_sandwich2 : (n : ℝ) * mglCurve tau u ≥ H_D - err_val tau zeta delta * (4 * tau * (1 - tau)) * (n : ℝ) + (n : ℝ) * mglCurve tau (u - theta) := by
      calc
        (n : ℝ) * mglCurve tau u = (n : ℝ) * mglCurve tau u + delta * (n : ℝ) - delta * (n : ℝ) := by ring
        _ ≥ H_D - ((err_val tau zeta delta * (4 * tau * (1 - tau)) - delta) * (n : ℝ)) + (n : ℝ) * mglCurve tau (u - theta) - delta * (n : ℝ) := by
          have : (entropy mu - H_D) / (n : ℝ) = u - theta := by
            dsimp [u, theta, entropyRate]
            ring
          rw [this] at h_sandwich
          linarith [h_sandwich]
        _ = H_D - err_val tau zeta delta * (4 * tau * (1 - tau)) * (n : ℝ) + (n : ℝ) * mglCurve tau (u - theta) := by ring
    calc
      H_D * (4 * tau * (1 - tau)) = H_D * (1 - (1 - 2 * tau)^2) := by ring
      _ = H_D - (1 - 2 * tau)^2 * H_D := by ring
      _ = theta * (n : ℝ) - (1 - 2 * tau)^2 * (theta * (n : ℝ)) := by
        have : H_D = theta * (n : ℝ) := by
          dsimp [theta]
          rw [div_mul_cancel₀ _ (ne_of_gt h_n_pos)]
        rw [this]
      _ = (n : ℝ) * theta - (n : ℝ) * ((1 - 2 * tau)^2 * theta) := by ring
      _ ≤ (n : ℝ) * theta - ((n : ℝ) * mglCurve tau u - (n : ℝ) * mglCurve tau (u - theta)) := by linarith [h_secant_n]
      _ ≤ err_val tau zeta delta * (4 * tau * (1 - tau)) * (n : ℝ) := by
        have h_theta_eq : H_D = theta * (n : ℝ) := by
          dsimp [theta]
          rw [div_mul_cancel₀ _ (ne_of_gt h_n_pos)]
        linarith [h_sandwich2, h_theta_eq]
  have h_cancel : H_D ≤ err_val tau zeta delta * (n : ℝ) := by
    have h_factor : 0 < 4 * tau * (1 - tau) := by
      have : 0 < 1 - tau := by linarith
      positivity
    have h_div : H_D * (4 * tau * (1 - tau)) / (4 * tau * (1 - tau)) ≤ err_val tau zeta delta * (4 * tau * (1 - tau)) * (n : ℝ) / (4 * tau * (1 - tau)) :=
      div_le_div_of_nonneg_right h_alg (le_of_lt h_factor)
    rwa [mul_div_cancel_right₀ _ (ne_of_gt h_factor), mul_right_comm, mul_div_cancel_right₀ _ (ne_of_gt h_factor)] at h_div
  exact h_cancel.trans (mul_le_mul_of_nonneg_right herr_val (by positivity))

/-- **Off-flat budget mean bound (note 04 §2–4, Theorem (i),(ii),(iv)).** The
mean positive excess of the predictable mismatch sum over its `(p + err/2) · n`
target is at most `(err² / 4) · n`, where `p = hbInv (entropyRate n mu)`.

By `predictableDistance_mean_eq_mismatch_sum` this is equivalent to bounding the
total adapted mismatch mass
`∑ₜ eventMass mu (mismatchAt (adaptedCenter mu) t) ≤ (p + err/2 + err²/4) · n`.
The mechanism (note 04): Jensen-flatness (`Hb_jensen_gap_ge_two_variance`,
already available) caps the off-flat coordinate count `N_off` in mean by
`√delta · n`, and branch geometry caps each flat innovation at `p + O(err/ζ)`.
Pointwise `offFlatBudget err mu x ≤ ½ · N_off x` once the flat window bias is
`≤ err/2`, so the mean is controlled by `E[N_off]`; the `err_val` exponent makes
`err² ≥ 2√delta` for every admitted `delta`. It carries no Azuma content.

Isolated leaf obligation: the exact nonnegative slack split is now available
through `S_jen_le_delta_n` and `S_mem_le_delta_n`.  The proof uses
a quantitative convexity modulus for `mglCurve` (strict convexity alone is
already available as `mglCurve_strictConvex`), together with the
branch-geometry Lipschitz bound on `hbInv`. -/

lemma offFlatBudget_mean_bound
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta err : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ))
    (herr0 : 0 < err) (hsmall : err < Real.log 2)
    (herr_val : err_val tau zeta delta ≤ err) :
    ∑ x, mu x * offFlatBudget err mu x ≤ (err ^ 2 / 4) * (n : ℝ) := by
  have _ := hsmall
  have h_core := flatness_off_flat_budget_bound ht0 ht1 hz0 hz1 hn hmu hd0 hzeta1 hzeta2 h_ent
  have h_le : ∑ x, mu x * offFlatBudget err mu x ≤ ∑ x, mu x * offFlatBudget (err_val tau zeta delta) mu x := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left (offFlatBudget_mono mu x herr_val) (hmu.1 x)
  have herr_sq : err_val tau zeta delta ^ 2 ≤ err ^ 2 := by
    have hpos : 0 < err_val tau zeta delta := err_val_pos ht0 ht1 hz0 hz1 hd0
    nlinarith
  have h_rhs : (err_val tau zeta delta ^ 2 / 4) * (n : ℝ) ≤ (err ^ 2 / 4) * (n : ℝ) := by
    apply mul_le_mul_of_nonneg_right
    · linarith
    · positivity
  exact h_le.trans (h_core.trans h_rhs)

/-- Near equality in MGL yields a predictable tracking certificate.

This is the entropy-specific obligation: exact slack/Jensen flatness, branch
geometry, memory charge, posterior tracking, and the label law. It contains no
Azuma argument and no final event union bound.

The certificate is assembled from the canonical adapted center `adaptedCenter mu`
(coordinate `t` set to `1` iff `Pr[Xₜ = 1 | X_{<t}] > 1/2`), its exact calibrated
conditional mismatch `conditionalMismatch mu`, and the `offFlatBudget`.
Adaptedness, calibration, the probability bounds, and the pointwise predictable
bound hold by construction (the latter because `offFlatBudget` is exactly the
positive part of the predictable-distance excess). The two genuinely
entropy-theoretic facts are isolated as `label_entropy_bound` and
`offFlatBudget_mean_bound`. -/
theorem near_mgl_to_tracking_certificate
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta err : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ))
    (herr0 : 0 < err) (hsmall : err < Real.log 2)
    (herr_val : err_val tau zeta delta ≤ err) :
    Nonempty (TrackingCertificate mu (hbInv (entropyRate n mu)) err) :=
  ⟨{ D := adaptedCenter mu
     q := conditionalMismatch mu
     off := offFlatBudget err mu
     adapted := adaptedCenter_isAdapted mu
     calibrated := conditionalMismatch_calibrates mu hmu
     q_nonneg := conditionalMismatch_nonneg mu hmu
     q_le_one := conditionalMismatch_le_one mu hmu
     off_nonneg := offFlatBudget_nonneg err mu
     label_entropy :=
       label_entropy_bound ht0 ht1 hz0 hz1 hn hmu hd0 hzeta1 hzeta2 h_ent herr0 hsmall herr_val
     predictable_bound := predictableDistance_le_target_add_offFlatBudget err mu
     off_mean :=
       offFlatBudget_mean_bound ht0 ht1 hz0 hz1 hn hmu hd0 hzeta1 hzeta2 h_ent herr0 hsmall herr_val }⟩

lemma trackingCertificate_mean_bound
    {n : ℕ} {mu : Cube n → ℝ} {p err : ℝ}
    (hmu : IsLaw mu) (C : TrackingCertificate mu p err) :
    ∑ x, mu x * predictableDistance C.q x ≤
      (p + err / 2) * (n : ℝ) + (err ^ 2 / 4) * (n : ℝ) := by
  have h1 : ∑ x, mu x * predictableDistance C.q x ≤ ∑ x, mu x * ((p + err / 2) * (n : ℝ) + C.off x) := by
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (C.predictable_bound x) (hmu.1 x)
  have h2 : (∑ x, mu x * ((p + err / 2) * (n : ℝ) + C.off x)) = (p + err / 2) * (n : ℝ) + ∑ x, mu x * C.off x := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hmu.2, one_mul]
  linarith [C.off_mean]

/-- Calibration turns the mean predictable distance into the total
per-coordinate mismatch mass. Grouping by the prefix fiber, on each fiber `q t`
is the constant conditional-mismatch probability, so its `mu`-weighted sum
recovers the fiber's mismatch mass; summing the fibers gives the coordinate's
mismatch mass. -/
lemma predictableDistance_mean_eq_mismatch_sum {n : ℕ} {mu : Cube n → ℝ}
    {D : Cube n → Cube n} {q : Fin n → Cube n → ℝ}
    (hcal : CalibratesMismatch mu D q) :
    ∑ x, mu x * predictableDistance q x = ∑ t, eventMass mu (mismatchAt D t) := by
  obtain ⟨hpref, hcalib⟩ := hcal
  have key : ∀ t : Fin n, ∑ x, mu x * q t x = eventMass mu (mismatchAt D t) := by
    intro t
    have hfiber : ∀ c : Cube n,
        ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c), mu x * q t x
          = ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
              (if mismatchAt D t x then mu x else 0) := by
      intro c
      by_cases hne : (Finset.univ.filter (fun x => prefixAt t x = c)).Nonempty
      · obtain ⟨x₀, hx₀⟩ := hne
        rw [Finset.mem_filter] at hx₀
        have hx₀c : prefixAt t x₀ = c := hx₀.2
        have eqL : ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c), mu x * q t x
            = eventMass mu (fun y => prefixAt t y = prefixAt t x₀ ∧ mismatchAt D t y) := by
          have hconst : ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c), mu x * q t x
              = (∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c), mu x) * q t x₀ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun x hx => ?_)
            rw [Finset.mem_filter] at hx
            have hxx : prefixAt t x = prefixAt t x₀ := by rw [hx.2, hx₀c]
            rw [hpref t x x₀ hxx]
          have hsum : ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c), mu x
              = eventMass mu (fun y => prefixAt t y = prefixAt t x₀) := by
            rw [Finset.sum_filter]
            simp only [eventMass, hx₀c]
          rw [hconst, hsum, mul_comm]
          exact hcalib t x₀
        have eqR : ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
              (if mismatchAt D t x then mu x else 0)
            = eventMass mu (fun y => prefixAt t y = prefixAt t x₀ ∧ mismatchAt D t y) := by
          rw [Finset.sum_filter]
          simp only [eventMass]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          by_cases h1 : prefixAt t x = c <;> by_cases h2 : mismatchAt D t x <;>
            simp [h1, h2, hx₀c]
        rw [eqL, eqR]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.sum_empty, Finset.sum_empty]
    calc ∑ x, mu x * q t x
        = ∑ c, ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c), mu x * q t x :=
          (Finset.sum_fiberwise Finset.univ (prefixAt t) (fun x => mu x * q t x)).symm
      _ = ∑ c, ∑ x ∈ Finset.univ.filter (fun x => prefixAt t x = c),
            (if mismatchAt D t x then mu x else 0) :=
          Finset.sum_congr rfl (fun c _ => hfiber c)
      _ = eventMass mu (mismatchAt D t) :=
          Finset.sum_fiberwise Finset.univ (prefixAt t)
            (fun x => if mismatchAt D t x then mu x else 0)
  calc ∑ x, mu x * predictableDistance q x
      = ∑ x, ∑ t, mu x * q t x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [predictableDistance, Finset.mul_sum]
    _ = ∑ t, ∑ x, mu x * q t x := Finset.sum_comm
    _ = ∑ t, eventMass mu (mismatchAt D t) := Finset.sum_congr rfl (fun t _ => key t)

/-- Any tracking certificate caps the total per-coordinate mismatch mass at
`(p + err/2 + err²/4)·n`. This is the sharp obstruction behind the original
unconstrained worker theorem: the summed mismatch mass
`∑ₜ eventMass mu (mismatchAt C.D t)` is an
intrinsic property of `mu` and the adapted center — for a product law it is
`≥ ∑ₜ min(biasₜ, 1-biasₜ)`, which can strictly exceed `p·n` (a two-bias
product has it `= n/4 > p·n` since `p < 1/4` by strict concavity). Thus an
error lower bound with the correct channel/window dependence is necessary. -/
lemma trackingCertificate_mismatch_bound {n : ℕ} {mu : Cube n → ℝ} {p err : ℝ}
    (hmu : IsLaw mu) (C : TrackingCertificate mu p err) :
    ∑ t, eventMass mu (mismatchAt C.D t) ≤
      (p + err / 2) * (n : ℝ) + (err ^ 2 / 4) * (n : ℝ) := by
  rw [← predictableDistance_mean_eq_mismatch_sum C.calibrated]
  exact trackingCertificate_mean_bound hmu C

/-- Logical core of the interface counterexample. If a law `mu` has an intrinsic
adapted-center mismatch floor `floor` (a lower bound on `∑ₜ eventMass mu (mismatchAt D t)`
holding for *every* adapted center `D`) that strictly exceeds the certificate cap
`(p + err/2 + err²/4)·n`, then no `TrackingCertificate mu p err` can exist.

Without a lower bound tying `err` to the entropy slack and channel parameters,
one may send `err → 0`, dropping the cap below any fixed floor `> p·n`; a
two-bias product law has `floor = n/4` while `p < 1/4`. -/
lemma not_nonempty_trackingCertificate_of_floor {n : ℕ} {mu : Cube n → ℝ}
    {p err floor : ℝ} (hmu : IsLaw mu)
    (hfloor : ∀ D : Cube n → Cube n, IsAdaptedCenter D →
      floor ≤ ∑ t, eventMass mu (mismatchAt D t))
    (hgt : (p + err / 2) * (n : ℝ) + (err ^ 2 / 4) * (n : ℝ) < floor) :
    ¬ Nonempty (TrackingCertificate mu p err) := by
  rintro ⟨C⟩
  have h1 := hfloor C.D C.adapted
  have h2 := trackingCertificate_mismatch_bound hmu C
  linarith

/-- Distribution-independent numeric fact behind the counterexample: the
lower-branch entropy inverse of the *averaged* binary entropy of biases `1/8`
and `3/8` is strictly below `1/4`. Strict concavity of `Hb` gives
`(Hb(1/8)+Hb(3/8))/2 < Hb(1/4)`, and monotone inversion (`hbInv_strictMonoOn`,
`hbInv (Hb (1/4)) = 1/4`) carries this to the claim. For the independent
product law with these biases one has `entropyRate 2 mu = (Hb(1/8)+Hb(3/8))/2`,
so `p := hbInv (entropyRate 2 mu) < 1/4`, while every adapted center has
mismatch mass `≥ 1/8 + 3/8 = 1/2 = (1/4)·2 > p·2`. -/
lemma two_bias_p_lt_quarter :
    hbInv ((Hb (1 / 8) + Hb (3 / 8)) / 2) < 1 / 4 := by
  -- Strict concavity: `(Hb(1/8)+Hb(3/8))/2 < Hb(1/4)`.
  have hlt : (Hb (1 / 8) + Hb (3 / 8)) / 2 < Hb (1 / 4) := by
    have h := Real.strictConcave_binEntropy.2
      (show (1 / 8 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
      (show (3 / 8 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
      (show (1 / 8 : ℝ) ≠ 3 / 8 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul] at h
    rw [show (1 : ℝ) / 2 * (1 / 8) + 1 / 2 * (3 / 8) = 1 / 4 by norm_num] at h
    simp only [Hb]
    linarith
  have hu0 : 0 ≤ (Hb (1 / 8) + Hb (3 / 8)) / 2 := by
    have h1 := Real.binEntropy_nonneg (show (0 : ℝ) ≤ 1 / 8 by norm_num) (by norm_num)
    have h2 := Real.binEntropy_nonneg (show (0 : ℝ) ≤ 3 / 8 by norm_num) (by norm_num)
    simp only [Hb]; linarith
  have hHb14_le : Hb (1 / 4) ≤ Real.log 2 := by
    simp only [Hb]; exact Real.binEntropy_le_log_two
  have hu_mem : (Hb (1 / 8) + Hb (3 / 8)) / 2 ∈ Icc 0 (Real.log 2) :=
    ⟨hu0, le_of_lt (lt_of_lt_of_le hlt hHb14_le)⟩
  have h14_mem : Hb (1 / 4) ∈ Icc 0 (Real.log 2) := by
    refine ⟨?_, hHb14_le⟩
    simp only [Hb]; exact Real.binEntropy_nonneg (by norm_num) (by norm_num)
  -- `hbInv (Hb (1/4)) = 1/4` by injectivity of `Hb` on `[0,1/2]`.
  have hinv14 : hbInv (Hb (1 / 4)) = 1 / 4 := by
    have hspec := hbInv_spec h14_mem
    have hmem_half : hbInv (Hb (1 / 4)) ∈ Icc (0 : ℝ) (2⁻¹) := by
      have h := hspec.1; rwa [show (1 : ℝ) / 2 = 2⁻¹ by norm_num] at h
    have h14_half : (1 / 4 : ℝ) ∈ Icc (0 : ℝ) (2⁻¹) := by constructor <;> norm_num
    apply Real.binEntropy_strictMonoOn.injOn hmem_half h14_half
    exact hspec.2
  have hmono := hbInv_strictMonoOn hu_mem h14_mem hlt
  rw [hinv14] at hmono
  exact hmono

/-- Two-bias product counterexample law on `Cube 2`: independent coordinates
with `Pr[bit0 = 1] = 1/8` and `Pr[bit1 = 1] = 3/8`. -/
noncomputable def muCounter (x : Cube 2) : ℝ :=
  (if (0 : Fin 2) ∈ x then 1 / 8 else 7 / 8) *
  (if (1 : Fin 2) ∈ x then 3 / 8 else 5 / 8)

lemma muCounter_isLaw :
    IsLaw muCounter := by
  constructor;
  · intro x; unfold muCounter; split_ifs <;> norm_num;
  · unfold muCounter; norm_num;
    rw [ show ( Finset.univ : Finset ( Finset ( Fin 2 ) ) ) = { { 0 }, { 1 }, { 0, 1 }, ∅ } by decide ] ; simp +decide ; norm_num

lemma muCounter_entropyRate :
    entropyRate 2 muCounter =
      (Hb (1 / 8) + Hb (3 / 8)) / 2 := by
  unfold entropyRate Hb;
  unfold entropy muCounter;
  rw [ show ( Finset.univ : Finset ( Finset ( Fin 2 ) ) ) = { { 0, 1 }, { 0 }, { 1 }, { } } by decide ] ; simp +decide [ Finset.sum ] ; ring_nf;
  norm_num [ Real.binEntropy, Real.negMulLog ] ; ring_nf;
  norm_num [ Real.log_div ] ; ring_nf;
  rw [ show ( 64 : ℝ ) = 2 ^ 6 by norm_num, Real.log_pow ] ; rw [ show ( 8 : ℝ ) = 2 ^ 3 by norm_num, Real.log_pow ] ; rw [ show ( 21 : ℝ ) = 3 * 7 by norm_num, Real.log_mul ] <;> norm_num ; rw [ show ( 35 : ℝ ) = 5 * 7 by norm_num, Real.log_mul ] <;> norm_num ; ring;

lemma muCounter_adapted_floor :
    ∀ D : Cube 2 → Cube 2, IsAdaptedCenter D →
      (1 / 2 : ℝ) ≤
        ∑ t : Fin 2, eventMass muCounter (mismatchAt D t) := by
  unfold eventMass;
  intro D hD;
  have h0 : ∀ x : Cube 2, (0 ∈ D x ↔ 0 ∈ D ∅) := by
    intro x; exact hD 0 x ∅ (by
    fin_cases x <;> rfl)
  have h1 : ∀ x : Cube 2, (1 ∈ D x ↔ if 0 ∈ x then 1 ∈ D {0} else 1 ∈ D ∅) := by
    intro x; specialize hD 1 x;
    split_ifs <;> simp_all +decide [ prefixAt ];
    · exact hD { 0 } ( by fin_cases x <;> trivial );
    · exact hD ∅ ( by ext i; fin_cases i <;> aesop );
  simp +decide [ mismatchAt ];
  rw [ show ( Finset.univ : Finset ( Cube 2 ) ) = { ∅, { 0 }, { 1 }, { 0, 1 } } by decide ] ; simp +decide [ Finset.sum ] ; ring_nf ; norm_num [ muCounter ] ;
  grind

/-- A fully checked counterexample to the premises/conclusion pattern obtained
by omitting the error lower bound from `near_mgl_to_tracking_certificate`.
The slack parameter `delta` can always be chosen large enough to satisfy the
entropy inequality, while an independent `err` can be chosen below the
intrinsic adapted-center mismatch floor of `muCounter`. -/
theorem near_mgl_tracking_certificate_counterexample :
    ∃ (tau zeta : ℝ) (n : ℕ) (mu : Cube n → ℝ) (delta err : ℝ),
      0 < tau ∧ tau < 1 / 2 ∧ 0 < zeta ∧ zeta ≤ 1 / 4 ∧
      1 ≤ n ∧ IsLaw mu ∧ 0 < delta ∧
      zeta ≤ hbInv (entropyRate n mu) ∧
      hbInv (entropyRate n mu) ≤ 1 / 2 - zeta ∧
      entropy (noiseMass tau mu) ≤
        (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ) ∧
      0 < err ∧ err < Real.log 2 ∧
      ¬ Nonempty (TrackingCertificate mu (hbInv (entropyRate n mu)) err) := by
  let u : ℝ := (Hb (1 / 8) + Hb (3 / 8)) / 2
  let p : ℝ := hbInv u
  let zeta : ℝ := p / 2
  let tau : ℝ := 1 / 4
  let A : ℝ := entropy (noiseMass tau muCounter)
  let B : ℝ := mglCurve tau (entropyRate 2 muCounter)
  let delta : ℝ := |A| + |B| + 1
  let err : ℝ := min ((1 / 4 - p) / 4) (Real.log 2 / 2)
  have hu_pos : 0 < u := by
    dsimp [u, Hb]
    have h1 := Real.binEntropy_pos (show (0 : ℝ) < 1 / 8 by norm_num)
      (show (1 / 8 : ℝ) < 1 by norm_num)
    have h2 := Real.binEntropy_pos (show (0 : ℝ) < 3 / 8 by norm_num)
      (show (3 / 8 : ℝ) < 1 by norm_num)
    linarith
  have hu_lt : u < Real.log 2 := by
    dsimp [u, Hb]
    have h1 := Real.binEntropy_lt_log_two.mpr
      (show (1 / 8 : ℝ) ≠ 2⁻¹ by norm_num)
    have h2 := Real.binEntropy_lt_log_two.mpr
      (show (3 / 8 : ℝ) ≠ 2⁻¹ by norm_num)
    linarith
  have hp_pos : 0 < p := (hbInv_mem_Ioo ⟨hu_pos, hu_lt⟩).1
  have hp_quarter : p < 1 / 4 := by
    dsimp [p]
    exact two_bias_p_lt_quarter
  have hz0 : 0 < zeta := by dsimp [zeta]; positivity
  have hz1 : zeta ≤ 1 / 4 := by dsimp [zeta]; linarith
  have hzeta1 : zeta ≤ hbInv (entropyRate 2 muCounter) := by
    rw [muCounter_entropyRate]
    dsimp [zeta, p, u]
    linarith
  have hzeta2 : hbInv (entropyRate 2 muCounter) ≤ 1 / 2 - zeta := by
    rw [muCounter_entropyRate]
    dsimp [zeta, p, u]
    linarith
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    have hA : 0 ≤ |A| := abs_nonneg _
    have hB : 0 ≤ |B| := abs_nonneg _
    linarith
  have hent : entropy (noiseMass tau muCounter) ≤
      (2 : ℝ) * mglCurve tau (entropyRate 2 muCounter) + delta * (2 : ℝ) := by
    change A ≤ 2 * B + delta * 2
    dsimp [delta]
    calc
      A ≤ |A| := le_abs_self A
      _ ≤ 2 * B + (|A| + |B| + 1) * 2 := by
        have hB := neg_abs_le B
        have hA0 := abs_nonneg A
        linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have herr0 : 0 < err := by
    dsimp [err]
    exact lt_min (by linarith) (by linarith)
  have herr_small : err < Real.log 2 := by
    have hle : err ≤ Real.log 2 / 2 := by dsimp [err]; exact min_le_right _ _
    linarith
  have hcap :
      (p + err / 2) * (2 : ℝ) + (err ^ 2 / 4) * (2 : ℝ) < 1 / 2 := by
    have herr_le : err ≤ (1 / 4 - p) / 4 := by
      dsimp [err]
      exact min_le_left _ _
    have herr_one : err ≤ 1 := by linarith
    nlinarith [mul_nonneg (le_of_lt herr0) (sub_nonneg.mpr herr_one)]
  have hnot : ¬ Nonempty (TrackingCertificate muCounter p err) := by
    apply not_nonempty_trackingCertificate_of_floor muCounter_isLaw muCounter_adapted_floor
    exact hcap
  refine ⟨tau, zeta, 2, muCounter, delta, err, ?_⟩
  have ht0 : 0 < tau := by norm_num [tau]
  have ht1 : tau < 1 / 2 := by norm_num [tau]
  refine ⟨ht0, ht1, hz0, hz1, by norm_num, muCounter_isLaw, hdelta_pos,
    hzeta1, hzeta2, hent, herr0, herr_small, ?_⟩
  simpa [p, u, muCounter_entropyRate] using hnot

end AverageHarperStability
