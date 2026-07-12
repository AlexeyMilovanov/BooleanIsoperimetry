import HarperStability.Core.S5
import HarperStability.Interface.EffectiveUniform

/-!
# Effective S5 (v0.3): pointwise flatness at grade 8

Target: `S5Eff` — `averageBadStepsLE A q eps ((K/eps^4) * (effEnv 8 Q.sigma m + 1))`, v0.3.1: `K` uniform over `eps` (`∃ K` before `∀ eps`); the v0.2 chain gives `epsCoeff·sepCoeff ~ 1/eps^3`, padded to `1/eps^4`
for fat+pinned `A`.

Route: mirror `Core/S5.lean` replacing every `Classical.choose`-based
slack by its effective counterpart (the three analytic leaves
`s5_kl_tilt`, `s5_step_entropy_transfer`, `s5_same_bin_separation` and
the counting glue are PROVED and reused verbatim):
* `base := Q.sigma + S4-envelope` — grade 5 from `hS4` (`S4Eff`);
* heavy-atom threshold `T ≤ G1 := effGeo base` — grade 6;
* atom class `Q' := Q with sigma := Q.sigma + G1` — grade-6 base;
  `R3Eff` at `Q'` gives the atom block-regularity slack
  `effEnv 2 Q'.sigma ≤ C·(effEnv 8 Q.sigma + 1)` (toolkit
  `effEnv_comp` with `i = 5, j = 2`);
* tilt/Markov count `G2 := effGeo G1` — grade 7; S1-on-the-atom count
  `24*s/Δ + 4` with `s` of grade 8 and the explicit class constant
  `Δ = eps*mu0/2`;
* total: grade 8 with `K` collecting `sepCoeff`-style constants and the
  `m < 30` bump.
Do NOT modify `Interface/Effective.lean` (hash-frozen).
-/

namespace HarperStability

namespace S5U

lemma s5_effGeo_sublinear {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (effGeo s) := by
  refine core_Sublinear_of_le (fun n => effGeo_nonneg s n) (fun n => ?_)
    (core_Sublinear_add hs (core_Sublinear_geomMean hs))
  exact max_le_add_of_nonneg (hs.1 n) (Real.sqrt_nonneg _)

lemma s5_effEnv_sublinear (k : ℕ) {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (effEnv k s) := by
  induction k with
  | zero => exact hs
  | succ k ih => exact s5_effGeo_sublinear ih

noncomputable def s5_K4_raw_class (hS4 : S4EffU)
    (qMin qMax s0 mu0 : ℝ)
    (hqMin : 0 < qMin) (hqMinMax : qMin ≤ qMax) (hqMax : qMax < 1 / 2)
    (hs0 : 0 < s0) (hmu0 : 0 < mu0) (hreg : qMax + s0 ≤ 1 / 2 - mu0) : ℝ :=
  Classical.choose
    (hS4 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg)

lemma s5_K4_raw_class_ge_one (hS4 : S4EffU)
    (qMin qMax s0 mu0 : ℝ)
    (hqMin : 0 < qMin) (hqMinMax : qMin ≤ qMax) (hqMax : qMax < 1 / 2)
    (hs0 : 0 < s0) (hmu0 : 0 < mu0) (hreg : qMax + s0 ≤ 1 / 2 - mu0) :
    1 ≤ s5_K4_raw_class hS4 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg := by
  unfold s5_K4_raw_class
  exact
    (Classical.choose_spec
      (hS4 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg)).1

noncomputable def s5_K4_raw (hS4 : S4EffU) (Q : QData) (hQ : validQData Q) : ℝ :=
  s5_K4_raw_class hS4 Q.qMin Q.qMax Q.s0 Q.mu0
    hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2.1

lemma s5_K4_raw_ge_one (hS4 : S4EffU) (Q : QData) (hQ : validQData Q) :
    1 ≤ s5_K4_raw hS4 Q hQ := by
  exact s5_K4_raw_class_ge_one hS4 Q.qMin Q.qMax Q.s0 Q.mu0
    hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2.1

noncomputable def s5_K4 (hS4 : S4EffU) (Q : QData) (hQ : validQData Q) (eps : ℝ) : ℝ :=
  max 1 (s5_K4_raw hS4 Q hQ / eps ^ 4)

lemma s5_K4_ge_one (hS4 : S4EffU) (Q : QData) (hQ : validQData Q) (eps : ℝ) :
    1 ≤ s5_K4 hS4 Q hQ eps := by
  unfold s5_K4
  exact le_max_left _ _

noncomputable def s5_foldEnv_eff (_hR3 : R3Eff) (hS4 : S4EffU) (_hS1 : S1Statement) (_hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) : ℝ :=
  s5_K4 hS4 Q hQ eps * (effEnv 5 Q.sigma m + 1)

lemma s5_foldEnv_eff_sublinear (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (_heps : 0 < eps) :
    Sublinear (s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps) := by
  have hSigma : Sublinear Q.sigma := hQ.2.2.2.2.2.2.1
  have hEnv : Sublinear (effEnv 5 Q.sigma) :=
    s5_effEnv_sublinear 5 hSigma
  have hEnvOne : Sublinear (fun m => effEnv 5 Q.sigma m + 1) :=
    core_Sublinear_add hEnv
      (core_Sublinear_const (show 0 ≤ (1 : ℝ) by norm_num))
  have hK0 : 0 ≤ s5_K4 hS4 Q hQ eps := by
    linarith [s5_K4_ge_one hS4 Q hQ eps]
  simpa [s5_foldEnv_eff] using core_Sublinear_smul hK0 hEnvOne

lemma s5_foldEnv_eff_nonneg (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) :
    ∀ m, 0 ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
  intro m
  unfold s5_foldEnv_eff
  have hk : 0 ≤ s5_K4 hS4 Q hQ eps := by linarith [s5_K4_ge_one hS4 Q hQ eps]
  have henv : 0 ≤ effEnv 5 Q.sigma m :=
    effEnv_nonneg 5 Q.sigma hQ.2.2.2.2.2.2.1.1 m
  nlinarith

lemma s5_foldEnv_eff_spec (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      ∃ o : ℝ, 0 ≤ o ∧ o < eps / 4 ∧
        uH A (binnedFoldField A (eps / 4) o) ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
  intro m A q hA hFat hPinned
  obtain ⟨o, ho0, hoLt, h⟩ :=
    (Classical.choose_spec
      (hS4 Q.qMin Q.qMax Q.s0 Q.mu0 hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1
        hQ.2.2.2.2.1 hQ.2.2.2.2.2.1)).2
      Q.sigma hQ.2.2.2.2.2.2.1 hQ.2.2.2.2.2.2.2 eps heps
      m A q hA hFat hPinned
  unfold s5_foldEnv_eff s5_K4
  have hCoeff :
      s5_K4_raw hS4 Q hQ / eps ^ 4 ≤
        max 1 (s5_K4_raw hS4 Q hQ / eps ^ 4) := le_max_right _ _
  have hEnvNonneg : 0 ≤ effEnv 5 Q.sigma m + 1 := by
    have henv : 0 ≤ effEnv 5 Q.sigma m :=
      effEnv_nonneg 5 Q.sigma hQ.2.2.2.2.2.2.1.1 m
    linarith
  exact ⟨o, ho0, hoLt, h.trans (mul_le_mul_of_nonneg_right hCoeff hEnvNonneg)⟩

noncomputable def s5_baseSlack_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) : ℝ :=
  Q.sigma m + s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m

lemma s5_baseSlack_eff_sublinear (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps) := by
  have hSigma : Sublinear Q.sigma := hQ.2.2.2.2.2.2.1
  unfold s5_baseSlack_eff
  exact core_Sublinear_add hSigma (s5_foldEnv_eff_sublinear hR3 hS4 hS1 hS2 Q hQ eps heps)

lemma s5_baseSlack_eff_nonneg (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) :
    ∀ m, 0 ≤ s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
  intro m
  unfold s5_baseSlack_eff
  have hSigma : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
  have hEnv := s5_foldEnv_eff_nonneg hR3 hS4 hS1 hS2 Q hQ eps m
  linarith

noncomputable def s5_atomQ_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) : QData :=
  { qMin := Q.qMin, qMax := Q.qMax, s0 := Q.s0, mu0 := Q.mu0,
    sigma := fun m =>
      Q.sigma m + Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) }

lemma s5_atomQ_eff_valid (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    validQData (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps) := by
  refine ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1, hQ.2.2.2.2.1, hQ.2.2.2.2.2.1, ?_, ?_⟩
  · dsimp only [s5_atomQ_eff]
    exact core_Sublinear_add hQ.2.2.2.2.2.2.1
      (core_Sublinear_geomMean (s5_baseSlack_eff_sublinear hR3 hS4 hS1 hS2 Q hQ eps heps))
  · intro m hm
    dsimp only [s5_atomQ_eff]
    have hlog := hQ.2.2.2.2.2.2.2 m hm
    have hsqrt : 0 ≤ Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    linarith

noncomputable def s5_K3_raw_class (hR3 : R3Eff)
    (qMin qMax s0 mu0 : ℝ)
    (hqMin : 0 < qMin) (hqMinMax : qMin ≤ qMax) (hqMax : qMax < 1 / 2)
    (hs0 : 0 < s0) (hmu0 : 0 < mu0) (hreg : qMax + s0 ≤ 1 / 2 - mu0) : ℝ :=
  Classical.choose (hR3 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg) /
    (1 / 6 : ℝ)

lemma s5_K3_raw_class_ge_one (hR3 : R3Eff)
    (qMin qMax s0 mu0 : ℝ)
    (hqMin : 0 < qMin) (hqMinMax : qMin ≤ qMax) (hqMax : qMax < 1 / 2)
    (hs0 : 0 < s0) (hmu0 : 0 < mu0) (hreg : qMax + s0 ≤ 1 / 2 - mu0) :
    1 ≤ s5_K3_raw_class hR3 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg := by
  unfold s5_K3_raw_class
  have hK :=
    (Classical.choose_spec
      (hR3 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg)).1
  norm_num
  nlinarith

noncomputable def s5_K3 (hR3 : R3Eff) (_hS4 : S4EffU) (_hS1 : S1Statement) (_hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (_eps : ℝ) : ℝ :=
  s5_K3_raw_class hR3 Q.qMin Q.qMax Q.s0 Q.mu0
    hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2.1

lemma s5_K3_ge_one (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) :
    1 ≤ s5_K3 hR3 hS4 hS1 hS2 Q hQ eps := by
  exact s5_K3_raw_class_ge_one hR3 Q.qMin Q.qMax Q.s0 Q.mu0
    hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2.1

noncomputable def s5_atomSigmaStar_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) : ℝ :=
  s5_K3 hR3 hS4 hS1 hS2 Q hQ eps * (effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m + 1)

lemma s5_atomSigmaStar_eff_sublinear (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps) := by
  have hAtomValid := s5_atomQ_eff_valid hR3 hS4 hS1 hS2 Q hQ eps heps
  have hSigma : Sublinear (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma :=
    hAtomValid.2.2.2.2.2.2.1
  have hEnv : Sublinear (effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma) :=
    s5_effEnv_sublinear 2 hSigma
  have hEnvOne :
      Sublinear (fun m =>
        effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m + 1) :=
    core_Sublinear_add hEnv
      (core_Sublinear_const (show 0 ≤ (1 : ℝ) by norm_num))
  have hK0 : 0 ≤ s5_K3 hR3 hS4 hS1 hS2 Q hQ eps := by
    linarith [s5_K3_ge_one hR3 hS4 hS1 hS2 Q hQ eps]
  simpa [s5_atomSigmaStar_eff] using core_Sublinear_smul hK0 hEnvOne

lemma s5_atomSigmaStar_eff_nonneg (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) :
    ∀ m, 0 ≤ s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
  intro m
  unfold s5_atomSigmaStar_eff
  have hk : 0 ≤ s5_K3 hR3 hS4 hS1 hS2 Q hQ eps := by linarith [s5_K3_ge_one hR3 hS4 hS1 hS2 Q hQ eps]
  have henv : 0 ≤ effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m :=
    effEnv_nonneg 2 _ (by
      intro n
      dsimp [s5_atomQ_eff]
      have h1 : 0 ≤ Q.sigma n := hQ.2.2.2.2.2.2.1.1 n
      have h2 : 0 ≤ Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps n + 1) * ((n : ℝ) + 1)) := Real.sqrt_nonneg _
      linarith) m
  nlinarith

lemma s5_atomSigmaStar_eff_spec (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps) m A q → pinned (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps) m A q →
      blockRegular m A q (1 / 6) (s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m) := by
  intro m A q hA hFat hPinned
  have hR3spec :=
    (Classical.choose_spec
      (hR3 Q.qMin Q.qMax Q.s0 Q.mu0 hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1
        hQ.2.2.2.2.1 hQ.2.2.2.2.2.1)).2
  have hAtomValid := s5_atomQ_eff_valid hR3 hS4 hS1 hS2 Q hQ eps heps
  have h := hR3spec (1 / 6) (by norm_num) (by norm_num)
    (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma
    hAtomValid.2.2.2.2.2.2.1 hAtomValid.2.2.2.2.2.2.2
    m A q hA hFat hPinned
  unfold s5_atomSigmaStar_eff s5_K3 s5_K3_raw_class
  simpa [div_mul_eq_mul_div, mul_assoc] using h

noncomputable def s5_atomSlack_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) : ℝ :=
  s5_sepCoeff eps Q.mu0 *
      (Real.sqrt
          ((Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) +
        s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m +
        Q.sigma m +
        Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) + 40

lemma s5_atomSlack_eff_nonneg (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) :
    0 ≤ s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
  unfold s5_atomSlack_eff
  have hInner :
      0 ≤ Real.sqrt ((Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) +
        s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m +
        Q.sigma m +
        Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1 := by
    have h1 : 0 ≤
        Real.sqrt
          ((Real.sqrt
              ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
                ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    have h2 := s5_atomSigmaStar_eff_nonneg hR3 hS4 hS1 hS2 Q hQ eps m
    have h3 : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
    have h4 : 0 ≤
        Real.sqrt
          ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
            ((m : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    linarith
  have hCoeff := s5_sepCoeff_nonneg eps Q.mu0
  nlinarith [mul_nonneg hCoeff hInner]

lemma s5_atomSlack_eff_ge_40 (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) :
    (40 : ℝ) ≤ s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
  unfold s5_atomSlack_eff
  have hInner :
      0 ≤ Real.sqrt ((Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) +
        s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m +
        Q.sigma m +
        Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1 := by
    have h1 : 0 ≤
        Real.sqrt
          ((Real.sqrt
              ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
                ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    have h2 := s5_atomSigmaStar_eff_nonneg hR3 hS4 hS1 hS2 Q hQ eps m
    have h3 : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
    have h4 : 0 ≤
        Real.sqrt
          ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
            ((m : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    linarith
  have hCoeff := s5_sepCoeff_nonneg eps Q.mu0
  nlinarith [mul_nonneg hCoeff hInner]

lemma s5_atomSlack_eff_sublinear (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps) := by
  have hBase :
      Sublinear (s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps) :=
    s5_baseSlack_eff_sublinear hR3 hS4 hS1 hS2 Q hQ eps heps
  have hG1 :
      Sublinear (fun m =>
        Real.sqrt
          ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
            ((m : ℝ) + 1))) :=
    core_Sublinear_geomMean hBase
  have hG2 :
      Sublinear (fun m =>
        Real.sqrt
          ((Real.sqrt
              ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
                ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1))) :=
    core_Sublinear_geomMean hG1
  have hStar :
      Sublinear (s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps) :=
    s5_atomSigmaStar_eff_sublinear hR3 hS4 hS1 hS2 Q hQ eps heps
  have hSigma : Sublinear Q.sigma := hQ.2.2.2.2.2.2.1
  have hInner : Sublinear (fun m =>
      Real.sqrt
          ((Real.sqrt
              ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
                ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) +
        s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m +
        Q.sigma m +
        Real.sqrt
          ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
            ((m : ℝ) + 1)) +
        1) :=
    core_Sublinear_add
      (core_Sublinear_add
        (core_Sublinear_add
          (core_Sublinear_add hG2 hStar)
          hSigma)
        hG1)
      (core_Sublinear_const (show 0 ≤ (1 : ℝ) by norm_num))
  have hSmul : Sublinear (fun m =>
      s5_sepCoeff eps Q.mu0 *
        (Real.sqrt
            ((Real.sqrt
                ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
                  ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) +
          s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m +
          Q.sigma m +
          Real.sqrt
            ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
              ((m : ℝ) + 1)) +
          1)) :=
    core_Sublinear_smul (s5_sepCoeff_nonneg eps Q.mu0) hInner
  simpa [s5_atomSlack_eff] using
    core_Sublinear_add hSmul
      (core_Sublinear_const (show 0 ≤ (40 : ℝ) by norm_num))

noncomputable def s5_massSlack_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt ((s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
    s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1

lemma s5_massSlack_eff_sublinear (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_massSlack_eff hR3 hS4 hS1 hS2 Q hQ eps) := by
  have hFold :
      Sublinear (s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps) :=
    s5_foldEnv_eff_sublinear hR3 hS4 hS1 hS2 Q hQ eps heps
  have hGeom :
      Sublinear (fun m =>
        Real.sqrt
          ((s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
            ((m : ℝ) + 1))) :=
    core_Sublinear_geomMean hFold
  have hAtom :=
    s5_atomSlack_eff_sublinear hR3 hS4 hS1 hS2 Q hQ eps heps
  unfold s5_massSlack_eff
  simpa [add_assoc] using core_Sublinear_add hGeom
    (core_Sublinear_add hAtom
      (core_Sublinear_const (show 0 ≤ (1 : ℝ) by norm_num)))

lemma s5_effEnv_four_le_seven (Q : QData) (m : ℕ) :
    effEnv 5 Q.sigma m ≤ effEnv 8 Q.sigma m := by
  simpa [effEnv] using le_effEnv 3 (effEnv 5 Q.sigma) m

lemma s5_effEnv_five_le_seven (Q : QData) (m : ℕ) :
    effEnv 6 Q.sigma m ≤ effEnv 8 Q.sigma m := by
  simpa [effEnv] using le_effEnv 2 (effEnv 6 Q.sigma) m

lemma s5_effEnv_six_le_seven (Q : QData) (m : ℕ) :
    effEnv 7 Q.sigma m ≤ effEnv 8 Q.sigma m := by
  simpa [effEnv] using le_effEnv 1 (effEnv 7 Q.sigma) m

lemma s5_baseSlack_eff_le_grade5 (hR3 : R3Eff) (hS4 : S4EffU)
    (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) :
    s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m ≤
      (s5_K4 hS4 Q hQ eps + 1) * (effEnv 5 Q.sigma m + 1) := by
  unfold s5_baseSlack_eff s5_foldEnv_eff
  have hSigma_le : Q.sigma m ≤ effEnv 5 Q.sigma m := le_effEnv 5 Q.sigma m
  have hK4_nonneg : 0 ≤ s5_K4 hS4 Q hQ eps := by
    linarith [s5_K4_ge_one hS4 Q hQ eps]
  have hE4_nonneg : 0 ≤ effEnv 5 Q.sigma m :=
    effEnv_nonneg 5 Q.sigma hQ.2.2.2.2.2.2.1.1 m
  nlinarith

lemma s5_geom_base_eff_le_grade6 (hR3 : R3Eff) (hS4 : S4EffU)
    (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) :
    Real.sqrt
        ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
          ((m : ℝ) + 1)) ≤
      2 * (s5_K4 hS4 Q hQ eps + 1) * (effEnv 6 Q.sigma m + 1) := by
  let C : ℝ := s5_K4 hS4 Q hQ eps + 1
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [s5_K4_ge_one hS4 Q hQ eps]
  have hE4_nonneg : ∀ n, 0 ≤ effEnv 5 Q.sigma n :=
    fun n => effEnv_nonneg 5 Q.sigma hQ.2.2.2.2.2.2.1.1 n
  have hbase_le : ∀ n,
      s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps n ≤
        C * (effEnv 5 Q.sigma n + 1) := by
    intro n
    simpa [C] using
      s5_baseSlack_eff_le_grade5 hR3 hS4 hS1 hS2 Q hQ eps n
  have h1 :
      Real.sqrt
          ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
            ((m : ℝ) + 1)) ≤
        effGeo (s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps) m := by
    unfold effGeo
    exact le_max_right _ _
  have h2 :
      effGeo (s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps) m ≤
        effGeo (fun n => C * (effEnv 5 Q.sigma n + 1)) m :=
    effGeo_mono hbase_le m
  have h3 :
      effGeo (fun n => C * (effEnv 5 Q.sigma n + 1)) m ≤
        2 * C * (effEnv 6 Q.sigma m + 1) := by
    simpa [C, effEnv_succ] using
      effGeo_scale hC hE4_nonneg m
  exact h1.trans (h2.trans (by simpa [C] using h3))

lemma s5_geom2_base_eff_le_grade7 (hR3 : R3Eff) (hS4 : S4EffU)
    (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) :
    Real.sqrt
        ((Real.sqrt
            ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
              ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) ≤
      4 * (s5_K4 hS4 Q hQ eps + 1) * (effEnv 7 Q.sigma m + 1) := by
  let C : ℝ := 2 * (s5_K4 hS4 Q hQ eps + 1)
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [s5_K4_ge_one hS4 Q hQ eps]
  have hE5_nonneg : ∀ n, 0 ≤ effEnv 6 Q.sigma n :=
    fun n => effEnv_nonneg 6 Q.sigma hQ.2.2.2.2.2.2.1.1 n
  have hG1_le : ∀ n,
      Real.sqrt
          ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps n + 1) *
            ((n : ℝ) + 1)) ≤
        C * (effEnv 6 Q.sigma n + 1) := by
    intro n
    simpa [C, mul_assoc] using
      s5_geom_base_eff_le_grade6 hR3 hS4 hS1 hS2 Q hQ eps n
  have h1 :
      Real.sqrt
          ((Real.sqrt
              ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
                ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) ≤
        effGeo
          (fun n =>
            Real.sqrt
              ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps n + 1) *
                ((n : ℝ) + 1))) m := by
    unfold effGeo
    exact le_max_right _ _
  have h2 :
      effGeo
          (fun n =>
            Real.sqrt
              ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps n + 1) *
                ((n : ℝ) + 1))) m ≤
        effGeo (fun n => C * (effEnv 6 Q.sigma n + 1)) m :=
    effGeo_mono hG1_le m
  have h3 :
      effGeo (fun n => C * (effEnv 6 Q.sigma n + 1)) m ≤
        2 * C * (effEnv 7 Q.sigma m + 1) := by
    simpa [C, effEnv_succ] using
      effGeo_scale hC hE5_nonneg m
  have h4 :
      2 * C * (effEnv 7 Q.sigma m + 1) =
        4 * (s5_K4 hS4 Q hQ eps + 1) * (effEnv 7 Q.sigma m + 1) := by
    dsimp [C]
    ring
  exact h1.trans (h2.trans (h3.trans_eq h4))

lemma s5_atomSigmaStar_eff_le_grade8 (hR3 : R3Eff) (hS4 : S4EffU)
    (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) :
    s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m ≤
      s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
        (4 * (2 * (s5_K4 hS4 Q hQ eps + 1) + 1) + 1) *
        (effEnv 8 Q.sigma m + 1) := by
  let C : ℝ := 2 * (s5_K4 hS4 Q hQ eps + 1) + 1
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [s5_K4_ge_one hS4 Q hQ eps]
  have hC_nonneg : 0 ≤ C := by linarith
  have hSigma_nonneg : ∀ n, 0 ≤ Q.sigma n := hQ.2.2.2.2.2.2.1.1
  have hAtomSigma_le : ∀ n,
      (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma n ≤
        C * (effEnv 6 Q.sigma n + 1) := by
    intro n
    dsimp [s5_atomQ_eff]
    have hSigma_le : Q.sigma n ≤ effEnv 6 Q.sigma n :=
      le_effEnv 6 Q.sigma n
    have hG1_le :=
      s5_geom_base_eff_le_grade6 hR3 hS4 hS1 hS2 Q hQ eps n
    have hE5_nonneg : 0 ≤ effEnv 6 Q.sigma n :=
      effEnv_nonneg 6 Q.sigma hSigma_nonneg n
    have hSigma_le_one : Q.sigma n ≤ effEnv 6 Q.sigma n + 1 := by
      linarith
    calc
      Q.sigma n +
          Real.sqrt
            ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps n + 1) *
              ((n : ℝ) + 1))
          ≤ (effEnv 6 Q.sigma n + 1) +
              2 * (s5_K4 hS4 Q hQ eps + 1) *
                (effEnv 6 Q.sigma n + 1) := by
            exact add_le_add hSigma_le_one hG1_le
      _ = C * (effEnv 6 Q.sigma n + 1) := by
            dsimp [C]
            ring
  have hmono :=
    effEnv_mono hAtomSigma_le 2 m
  have hcomp :=
    effEnv_comp 2 (i := 6) (C := C) hC (s := Q.sigma) hSigma_nonneg m
  have hEnv_le :
      effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m ≤
        (4 * C) * (effEnv 8 Q.sigma m + 1) := by
    have h := hmono.trans hcomp
    have hnorm :
        (2 ^ 2 * C) * (effEnv (6 + 2) Q.sigma m + 1) =
          (4 * C) * (effEnv 8 Q.sigma m + 1) := by
      norm_num
    exact h.trans_eq hnorm
  have hK3_nonneg : 0 ≤ s5_K3 hR3 hS4 hS1 hS2 Q hQ eps := by
    linarith [s5_K3_ge_one hR3 hS4 hS1 hS2 Q hQ eps]
  have hE7_nonneg : 0 ≤ effEnv 8 Q.sigma m :=
    effEnv_nonneg 8 Q.sigma hSigma_nonneg m
  unfold s5_atomSigmaStar_eff
  calc
    s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
        (effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m + 1)
        ≤ s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
            ((4 * C + 1) * (effEnv 8 Q.sigma m + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hK3_nonneg
          nlinarith
    _ = s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
        (4 * (2 * (s5_K4 hS4 Q hQ eps + 1) + 1) + 1) *
        (effEnv 8 Q.sigma m + 1) := by
          dsimp [C]
          ring

lemma s5_heavy_atom_fat_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (_hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (_hPinned : pinned Q m A q)
    (o : ℝ) (_ho1 : 0 ≤ o) (_ho2 : o < eps / 4)
    (env : ℝ) (_henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ)) :
    fat (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps) m Af q := by
  rcases hFat with ⟨_, _, hqMin, hqMax, hAbsA⟩
  set T : ℝ := Real.sqrt ((env + 1) * ((m : ℝ) + 1))
  set G1 : ℝ :=
    Real.sqrt
      ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1))
  have hA_card_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hT_prod_pos : 0 < (A.card : ℝ) * Real.exp (-T) :=
    mul_pos hA_card_pos (Real.exp_pos _)
  have hAf_card_pos_real : 0 < (Af.card : ℝ) :=
    lt_of_lt_of_le hT_prod_pos (by simpa [T] using hHeavy)
  have hAf_card_pos_nat : 0 < Af.card := by
    exact_mod_cast hAf_card_pos_real
  have hAfNonempty : Af.Nonempty := Finset.card_pos.mp hAf_card_pos_nat
  have hAfSub : Af ⊆ A := by
    rw [hAf]
    exact Finset.filter_subset _ _
  have hAf_card_le_A_card : (Af.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hAfSub
  have hlogAf_le_logA :
      Real.log (Af.card : ℝ) ≤ Real.log (A.card : ℝ) :=
    Real.log_le_log hAf_card_pos_real hAf_card_le_A_card
  have hEnv_le_base :
      env ≤ s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
    unfold s5_baseSlack_eff
    have hSigma_nonneg : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
    linarith
  have hT_le_G1 : T ≤ G1 := by
    dsimp [T, G1]
    exact Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hG1_nonneg : 0 ≤ G1 := by
    dsimp [G1]
    exact Real.sqrt_nonneg _
  have hlog_mul :
      Real.log ((A.card : ℝ) * Real.exp (-T)) =
        Real.log (A.card : ℝ) - T := by
    rw [Real.log_mul (ne_of_gt hA_card_pos) (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hlogAf_lower :
      Real.log (A.card : ℝ) - T ≤ Real.log (Af.card : ℝ) := by
    have hlog_le :=
      Real.log_le_log hT_prod_pos (by simpa [T] using hHeavy)
    simpa [hlog_mul] using hlog_le
  have hAbsParts := abs_le.mp hAbsA
  have hUpper :
      Real.log (Af.card : ℝ) - H q * (m : ℝ) ≤ Q.sigma m + G1 := by
    linarith
  have hLower :
      -(Q.sigma m + G1) ≤ Real.log (Af.card : ℝ) - H q * (m : ℝ) := by
    have h1 :
        Real.log (A.card : ℝ) - H q * (m : ℝ) - T ≤
          Real.log (Af.card : ℝ) - H q * (m : ℝ) := by
      linarith
    have h2 :
        -Q.sigma m - T ≤ Real.log (A.card : ℝ) - H q * (m : ℝ) - T := by
      linarith
    have h3 : -(Q.sigma m + G1) ≤ -Q.sigma m - T := by
      linarith
    linarith
  refine ⟨hAfNonempty, s5_atomQ_eff_valid hR3 hS4 hS1 hS2 Q hQ eps heps, ?_, ?_, ?_⟩
  · simpa [s5_atomQ_eff] using hqMin
  · simpa [s5_atomQ_eff] using hqMax
  · rw [abs_le]
    constructor
    · simpa [s5_atomQ_eff, G1, add_comm, add_left_comm, add_assoc] using hLower
    · simpa [s5_atomQ_eff, G1, add_comm, add_left_comm, add_assoc] using hUpper

lemma s5_heavy_atom_pinned_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (_hA : A.Nonempty) (_heps : 0 < eps) (_hepsQ : eps < Q.qMin)
    (_hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (_ho1 : 0 ≤ o) (_ho2 : o < eps / 4)
    (env : ℝ) (_henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (_henv_le : env ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (_hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ)) :
    pinned (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps) m Af q := by
  intro r hr
  have hAfSub : Af ⊆ A := by
    rw [hAf]
    exact Finset.filter_subset _ _
  have hcard :
      ((neighborhood r Af).card : ℝ) ≤ ((neighborhood r A).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (s5_neighborhood_mono_set hAfSub)
  have hrQ : r ≤ Nat.ceil (Q.s0 * (m : ℝ)) := by
    simpa [s5_atomQ_eff] using hr
  have hPinnedA := hPinned r hrQ
  have hExp :
      Real.exp (H (q + (r : ℝ) / (m : ℝ)) * (m : ℝ) + Q.sigma m) ≤
        Real.exp
          (H (q + (r : ℝ) / (m : ℝ)) * (m : ℝ) +
            (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m) := by
    apply Real.exp_le_exp.mpr
    dsimp [s5_atomQ_eff]
    have hsqrt : 0 ≤ Real.sqrt
        ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    linarith
  exact hcard.trans (hPinnedA.trans hExp)

lemma s5_heavy_atom_blockRegular_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ))
    (_hm : 30 ≤ m) :
    blockRegular m Af q (1 / 6) (s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m) := by
  have hAtomFat :=
    s5_heavy_atom_fat_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  have hAtomPinned :=
    s5_heavy_atom_pinned_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  exact s5_atomSigmaStar_eff_spec hR3 hS4 hS1 hS2 Q hQ eps heps m Af q
    hAtomFat.1 hAtomFat hAtomPinned

lemma s5_heavy_atom_E1_bound_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ))
    (hm : 30 ≤ m) :
    (((Finset.univ : Finset (Fin m)).filter
        (fun t => eps * Q.mu0 / 4 ≤ |hstep Af t - H q|)).card : ℝ) ≤
      24 * (s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m + Q.sigma m + Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1))) / (eps * Q.mu0 / 2) + 4 := by
  set star : ℝ := s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m
  set G1 : ℝ :=
    Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1))
  set s : ℝ := star + Q.sigma m + G1
  have hAtomFat :=
    s5_heavy_atom_fat_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  have hAfNonempty : Af.Nonempty := hAtomFat.1
  have hBR :=
    s5_heavy_atom_blockRegular_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy hm
  have hstar_nonneg : 0 ≤ star := by
    dsimp [star]
    exact s5_atomSigmaStar_eff_nonneg hR3 hS4 hS1 hS2 Q hQ eps m
  have hSigma_nonneg : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
  have hG1_nonneg : 0 ≤ G1 := by
    dsimp [G1]
    exact Real.sqrt_nonneg _
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    linarith
  have hmu_pos : 0 < Q.mu0 := hQ.2.2.2.2.1
  have hx_pos : 0 < eps * Q.mu0 := mul_pos heps hmu_pos
  have hepsS1 : 0 < eps * Q.mu0 / 4 := by
    positivity
  have hfloor_lower : (1 / 6 : ℝ) * (m : ℝ) ≤ ((m / 5 : ℕ) : ℝ) := by
    have hnat : m ≤ 6 * (m / 5) := by omega
    have hreal : (m : ℝ) ≤ 6 * ((m / 5 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    nlinarith
  have hfloor_upper :
      (m : ℝ) - ((m / 5 : ℕ) : ℝ) ≤ (1 - (1 / 6 : ℝ)) * (m : ℝ) := by
    have hnat : m ≤ 6 * (m / 5) := by omega
    have hreal : (m : ℝ) ≤ 6 * ((m / 5 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    nlinarith
  have hWindow :
      ∀ I : Finset (Fin m),
        ((m / 5 : ℕ) : ℝ) ≤ (I.card : ℝ) →
        (I.card : ℝ) ≤ (m : ℝ) - ((m / 5 : ℕ) : ℝ) →
        uH Af (proj I) ≤ H q * (I.card : ℝ) + s := by
    intro I hIlo hIhi
    have hlo : (1 / 6 : ℝ) * (m : ℝ) ≤ (I.card : ℝ) :=
      hfloor_lower.trans hIlo
    have hhi : (I.card : ℝ) ≤ (1 - (1 / 6 : ℝ)) * (m : ℝ) :=
      hIhi.trans hfloor_upper
    have hreg := (abs_le.mp (hBR.2.2 I hlo hhi)).2
    dsimp [s]
    linarith
  have hAtomAbs :
      |Real.log (Af.card : ℝ) - H q * (m : ℝ)| ≤ Q.sigma m + G1 := by
    simpa [s5_atomQ_eff, G1] using hAtomFat.2.2.2.2
  have hTotal :
      H q * (m : ℝ) - s ≤ uH Af (proj (Finset.univ : Finset (Fin m))) := by
    have hlog_lower := (abs_le.mp hAtomAbs).1
    rw [uH_proj_univ Af hAfNonempty]
    dsimp [s]
    linarith
  have hS1_result :=
    hS1 m Af (H q) s (eps * Q.mu0 / 4) hAfNonempty hs_nonneg hepsS1
      hWindow hTotal
  have hRhs :
      12 * s / (eps * Q.mu0 / 4) + 4 =
        24 * s / (eps * Q.mu0 / 2) + 4 := by
    field_simp [ne_of_gt hx_pos]
    ring
  simpa [s, star, G1] using hS1_result.trans_eq hRhs

lemma s5_heavy_atom_Markov_bound_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ))
    (hm : 30 ≤ m) :
    (((Finset.univ : Finset (Fin m)).filter
        (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q| ∧ |hstep Af t - H q| < eps * Q.mu0 / 4)).card : ℝ) ≤
      (64 / (eps * Q.mu0) ^ 2) * Real.sqrt ((Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) := by
  set x : ℝ := eps * Q.mu0
  set c : ℝ := x ^ 2 / 64
  set G1 : ℝ :=
    Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1))
  set G2 : ℝ := Real.sqrt ((G1 + 1) * ((m : ℝ) + 1))
  set M : Finset (Fin m) :=
    (Finset.univ : Finset (Fin m)).filter
      (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q| ∧
        |hstep Af t - H q| < eps * Q.mu0 / 4)
  let e : Fin m → ℝ := fun t =>
    uE Af (fun y =>
      |rho Af t (proj (below (Finset.univ : Finset (Fin m)) t) y) -
        rho A t (proj (below (Finset.univ : Finset (Fin m)) t) y)|)
  have hmu_pos : 0 < Q.mu0 := hQ.2.2.2.2.1
  have hx_pos : 0 < x := by
    dsimp [x]
    exact mul_pos heps hmu_pos
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hG1_nonneg : 0 ≤ G1 := by
    dsimp [G1]
    exact Real.sqrt_nonneg _
  have hG2_nonneg : 0 ≤ G2 := by
    dsimp [G2]
    exact Real.sqrt_nonneg _
  have hAfSub : Af ⊆ A := by
    rw [hAf]
    exact Finset.filter_subset _ _
  have hAtomFat :=
    s5_heavy_atom_fat_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  have hAfNonempty : Af.Nonempty := hAtomFat.1
  have hq1 : Q.qMin ≤ q := hFat.2.2.1
  have hq2 : q ≤ Q.qMax := hFat.2.2.2.1
  have hbinned : ∀ y ∈ Af, binnedFoldField A (eps / 4) o y = f := by
    intro y hy
    rw [hAf] at hy
    exact (Finset.mem_filter.mp hy).2
  have he_nonneg : ∀ t : Fin m, 0 ≤ e t := by
    intro t
    dsimp [e, uE]
    positivity
  have hpoint : ∀ t ∈ M, c ≤ e t := by
    intro t ht
    have ht' :
        3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q| ∧
          |hstep Af t - H q| < eps * Q.mu0 / 4 := by
      simpa [M] using ht
    have hbad := ht'.1
    have hgood : |hstep Af t - H q| < x / 4 := by
      simpa [x] using ht'.2
    set HA : ℝ :=
      uE Af (fun y =>
        H (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) y)))
    set HF : ℝ :=
      uE Af (fun y =>
        H (rho Af t (proj (below (Finset.univ : Finset (Fin m)) t) y)))
    set et : ℝ := e t
    have hsep :
        x / 2 ≤ |HA - H q| := by
      have h :=
        s5_same_bin_separation A Af Q hQ q eps o heps hq1 hq2 ho1 ho2
          f t hAfSub hAfNonempty hbinned hbad
      simpa [x, HA] using h
    have hstep_eq : hstep Af t = HF := by
      simpa [HF] using hstep_eq_uE_binEntropy_rho Af hAfNonempty t
    have hgoodHF : |HF - H q| < x / 4 := by
      simpa [hstep_eq] using hgood
    have htransfer : |HA - HF| ≤ 2 * Real.sqrt et := by
      have h :=
        s5_step_entropy_transfer A Af hAfSub hAfNonempty t
      simpa [HA, HF, et, e] using h
    have htri : |HA - H q| ≤ |HA - HF| + |HF - H q| := by
      calc
        |HA - H q| = |(HA - HF) + (HF - H q)| := by ring_nf
        _ ≤ |HA - HF| + |HF - H q| := abs_add_le _ _
    have hlt : |HA - H q| < 2 * Real.sqrt et + x / 4 := by
      exact lt_of_le_of_lt htri (add_lt_add_of_le_of_lt htransfer hgoodHF)
    have hsqrt_gt : x / 8 < Real.sqrt et := by
      linarith
    have het_nonneg : 0 ≤ et := by
      dsimp [et]
      exact he_nonneg t
    have hc_lt : c < et := by
      have hsq := (Real.lt_sqrt (show 0 ≤ x / 8 by positivity)).mp hsqrt_gt
      dsimp [c]
      nlinarith
    exact le_of_lt hc_lt
  have hM_sum :
      (M.card : ℝ) * c ≤ ∑ t ∈ M, e t := by
    calc
      (M.card : ℝ) * c = ∑ _t ∈ M, c := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ t ∈ M, e t := Finset.sum_le_sum hpoint
  have hM_sum_univ :
      ∑ t ∈ M, e t ≤ ∑ t : Fin m, e t := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by intro t ht; simp)
      (by intro t _ _; exact he_nonneg t)
  have hKL : (∑ t : Fin m, e t) ≤
      Real.sqrt ((m : ℝ) * Real.log ((A.card : ℝ) / (Af.card : ℝ)) / 2) := by
    simpa [e] using s5_kl_tilt A Af hAfSub hAfNonempty
  set T : ℝ := Real.sqrt ((env + 1) * ((m : ℝ) + 1))
  have hA_card_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hAf_card_pos : 0 < (Af.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAfNonempty
  have hHeavyT : (A.card : ℝ) * Real.exp (-T) ≤ (Af.card : ℝ) := by
    simpa [T] using hHeavy
  have hA_le_Af_exp : (A.card : ℝ) ≤ (Af.card : ℝ) * Real.exp T := by
    have hmul :=
      mul_le_mul_of_nonneg_right hHeavyT (le_of_lt (Real.exp_pos T))
    calc
      (A.card : ℝ) =
          ((A.card : ℝ) * Real.exp (-T)) * Real.exp T := by
            have hexp_cancel : Real.exp (-T) * Real.exp T = 1 := by
              rw [← Real.exp_add]
              ring_nf
              exact Real.exp_zero
            rw [mul_assoc, hexp_cancel, mul_one]
      _ ≤ (Af.card : ℝ) * Real.exp T := hmul
  have hratio_le_exp : (A.card : ℝ) / (Af.card : ℝ) ≤ Real.exp T := by
    rw [div_le_iff₀ hAf_card_pos]
    nlinarith
  have hlog_le_T : Real.log ((A.card : ℝ) / (Af.card : ℝ)) ≤ T := by
    have hratio_pos : 0 < (A.card : ℝ) / (Af.card : ℝ) :=
      div_pos hA_card_pos hAf_card_pos
    have hlog := Real.log_le_log hratio_pos hratio_le_exp
    simpa [Real.log_exp] using hlog
  have hKL_T :
      Real.sqrt ((m : ℝ) * Real.log ((A.card : ℝ) / (Af.card : ℝ)) / 2) ≤
        Real.sqrt ((m : ℝ) * T / 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left hlog_le_T (by positivity : 0 ≤ (m : ℝ))]
  have hEnv_le_base :
      env ≤ s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
    unfold s5_baseSlack_eff
    have hSigma_nonneg : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
    linarith
  have hT_le_G1 : T ≤ G1 := by
    dsimp [T, G1]
    exact Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hsqrt_T_le_G2 : Real.sqrt ((m : ℝ) * T / 2) ≤ G2 := by
    dsimp [G2]
    apply Real.sqrt_le_sqrt
    have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
    nlinarith [hT_le_G1, hG1_nonneg, hm_nonneg]
  have hsum_le_G2 : (∑ t : Fin m, e t) ≤ G2 :=
    hKL.trans (hKL_T.trans hsqrt_T_le_G2)
  have hM_c_le_G2 : (M.card : ℝ) * c ≤ G2 :=
    hM_sum.trans (hM_sum_univ.trans hsum_le_G2)
  have hM_bound : (M.card : ℝ) ≤ (64 / x ^ 2) * G2 := by
    calc
      (M.card : ℝ) ≤ G2 / c := (le_div_iff₀ hc_pos).mpr hM_c_le_G2
      _ = (64 / x ^ 2) * G2 := by
        dsimp [c]
        field_simp [ne_of_gt hx_pos]
  simpa [M, x, G1, G2] using hM_bound

lemma s5_heavy_atom_bad_bins_bound_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ)) :
    (((Finset.univ : Finset (Fin m)).filter
        (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|)).card : ℝ) ≤
      s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
  by_cases hm : 30 ≤ m
  · set B : Finset (Fin m) :=
      (Finset.univ : Finset (Fin m)).filter
        (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|)
    set E : Finset (Fin m) :=
      (Finset.univ : Finset (Fin m)).filter
        (fun t => eps * Q.mu0 / 4 ≤ |hstep Af t - H q|)
    set M : Finset (Fin m) :=
      (Finset.univ : Finset (Fin m)).filter
        (fun t =>
          3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q| ∧
            |hstep Af t - H q| < eps * Q.mu0 / 4)
    have hB_subset : B ⊆ M ∪ E := by
      intro t ht
      have htB : 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q| := by
        simpa [B] using ht
      by_cases htE : eps * Q.mu0 / 4 ≤ |hstep Af t - H q|
      · exact Finset.mem_union_right M (by simp [E, htE])
      · exact Finset.mem_union_left E (by
          have htlt : |hstep Af t - H q| < eps * Q.mu0 / 4 := lt_of_not_ge htE
          simp [M, htB, htlt])
    have hB_card_real :
        (B.card : ℝ) ≤ (M.card : ℝ) + (E.card : ℝ) := by
      have hnat : B.card ≤ M.card + E.card := by
        exact le_trans (Finset.card_le_card hB_subset) (Finset.card_union_le M E)
      exact_mod_cast hnat
    have hE :=
      s5_heavy_atom_E1_bound_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ
        hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy hm
    have hM :=
      s5_heavy_atom_Markov_bound_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ
        hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy hm
    set G1 : ℝ :=
      Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1))
    set G2 : ℝ := Real.sqrt ((G1 + 1) * ((m : ℝ) + 1))
    set star : ℝ := s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m
    set s : ℝ := star + Q.sigma m + G1
    set x : ℝ := eps * Q.mu0
    set a : ℝ := 64 / x ^ 2
    set b : ℝ := 48 / x
    have hx_pos : 0 < x := by
      dsimp [x]
      exact mul_pos heps hQ.2.2.2.2.1
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      positivity
    have hb_nonneg : 0 ≤ b := by
      dsimp [b]
      positivity
    have hG1_nonneg : 0 ≤ G1 := by
      dsimp [G1]
      exact Real.sqrt_nonneg _
    have hG2_nonneg : 0 ≤ G2 := by
      dsimp [G2]
      exact Real.sqrt_nonneg _
    have hstar_nonneg : 0 ≤ star := by
      dsimp [star]
      exact s5_atomSigmaStar_eff_nonneg hR3 hS4 hS1 hS2 Q hQ eps m
    have hsigma_nonneg : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
    have hs_le_inner : s ≤ G2 + star + Q.sigma m + G1 + 1 := by
      dsimp [s]
      linarith
    have hG2_le_inner : G2 ≤ G2 + star + Q.sigma m + G1 + 1 := by
      linarith
    have hE' : (E.card : ℝ) ≤ b * s + 4 := by
      dsimp [E, s, b, x] at hE ⊢
      convert hE using 1
      field_simp [ne_of_gt hx_pos]
      ring
    have hM' : (M.card : ℝ) ≤ a * G2 := by
      dsimp [M, a, x, G2, G1] at hM ⊢
      exact hM
    have hsum :
        (B.card : ℝ) ≤ a * G2 + (b * s + 4) := by
      linarith
    have hmain :
        a * G2 + (b * s + 4) ≤
          (a + b) * (G2 + star + Q.sigma m + G1 + 1) + 40 := by
      nlinarith [mul_le_mul_of_nonneg_left hG2_le_inner ha_nonneg,
        mul_le_mul_of_nonneg_left hs_le_inner hb_nonneg]
    have hcoeff : s5_sepCoeff eps Q.mu0 = a + b := by
      unfold s5_sepCoeff
      rw [dif_pos (by simpa [x] using hx_pos)]
    calc
      (((Finset.univ : Finset (Fin m)).filter
          (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|)).card : ℝ)
          = (B.card : ℝ) := by simp [B]
      _ ≤ a * G2 + (b * s + 4) := hsum
      _ ≤ (a + b) * (G2 + star + Q.sigma m + G1 + 1) + 40 := hmain
      _ = s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
        rw [← hcoeff]
        simp [s5_atomSlack_eff, G1, G2, star, add_comm]
  · have hm_lt : m < 30 := Nat.lt_of_not_ge hm
    have hCard :
        (((Finset.univ : Finset (Fin m)).filter
            (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|)).card : ℝ) ≤
          (m : ℝ) := by
      have hnat :
          ((Finset.univ : Finset (Fin m)).filter
            (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|)).card ≤ m := by
        simpa [Fintype.card_fin] using
          (((Finset.univ : Finset (Fin m)).filter
            (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|)).card_le_univ)
      exact_mod_cast hnat
    have hm_le_40 : (m : ℝ) ≤ (40 : ℝ) := by
      have hnat : m ≤ 40 := by omega
      exact_mod_cast hnat
    exact hCard.trans (hm_le_40.trans
      (s5_atomSlack_eff_ge_40 hR3 hS4 hS1 hS2 Q hQ eps m))

lemma s5_heavy_atoms_bad_steps_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ)) :
    (∑ x ∈ Af, ((badStepSet A q eps x).card : ℝ)) ≤ s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m * (Af.card : ℝ) := by
  have hBinsBound := s5_heavy_atom_bad_bins_bound_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  have hSum : (∑ x ∈ Af, ((badStepSet A q eps x).card : ℝ)) ≤
      ∑ x ∈ Af, s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
    apply Finset.sum_le_sum
    intro x hx
    have hx_f : binnedFoldField A (eps / 4) o x = f := by
      rw [hAf] at hx
      exact (Finset.mem_filter.mp hx).2
    have hSub := s5_badStep_subset_badBins A q eps o heps f x hx_f
    have hCard : ((badStepSet A q eps x).card : ℝ) ≤
        (((Finset.univ : Finset (Fin m)).filter
          (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSub
    linarith
  have hSum_eq : ∑ x ∈ Af, s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m =
      s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m * (Af.card : ℝ) := by
    simp [mul_comm]
  linarith

lemma s5_average_bad_steps_from_heavy_atoms_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (o : ℝ) (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (hHeavyBad : ∀ f Af, Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f) →
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ) →
      (∑ x ∈ Af, ((badStepSet A q eps x).card : ℝ)) ≤ s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m * (Af.card : ℝ)) :
    averageBadStepsLE A q eps
      (Real.sqrt ((env + 1) * ((m : ℝ) + 1)) +
        s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) := by
  unfold averageBadStepsLE
  let F : Cube m → Fin m → ℤ := binnedFoldField A (eps / 4) o
  set T : ℝ := Real.sqrt ((env + 1) * ((m : ℝ) + 1)) with hTdef
  set S : ℝ := s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m with hSdef
  change (∑ x ∈ A, ((badStepSet A q eps x).card : ℝ)) ≤
    (T + S + 1) * (A.card : ℝ)
  have henv_nonneg : 0 ≤ env := by
    exact (uH_nonneg A F).trans henv
  by_cases hA : A.Nonempty
  · have hTpos : 0 < T := by
      rw [hTdef]
      positivity
    have hPartition :
        (∑ f ∈ s5_classicalImage A F,
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) =
        ∑ x ∈ A, ((badStepSet A q eps x).card : ℝ) :=
      s5_sum_fiberwise_classical A F (fun x => ((badStepSet A q eps x).card : ℝ))
    rw [← hPartition]
    let heavy : Finset (Fin m → ℤ) :=
      (s5_classicalImage A F).filter fun f =>
        (A.card : ℝ) * Real.exp (-T) ≤ ((s5_classicalFiber A F f).card : ℝ)
    have hsplit :
        (∑ f ∈ s5_classicalImage A F,
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) =
        (∑ f ∈ heavy,
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) +
        (∑ f ∈ (s5_classicalImage A F).filter (fun f =>
          ¬ ((A.card : ℝ) * Real.exp (-T) ≤ ((s5_classicalFiber A F f).card : ℝ))),
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) := by
      simpa [heavy] using
        (Finset.sum_filter_add_sum_filter_not (s := s5_classicalImage A F)
          (p := fun f =>
            (A.card : ℝ) * Real.exp (-T) ≤ ((s5_classicalFiber A F f).card : ℝ))
          (f := fun f =>
            ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ))).symm
    rw [hsplit]
    have hHeavySum :
        (∑ f ∈ heavy,
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) ≤
        S * (∑ f ∈ heavy, ((s5_classicalFiber A F f).card : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun f hf => by
        have hfheavy :
            (A.card : ℝ) * Real.exp (-T) ≤
              ((s5_classicalFiber A F f).card : ℝ) :=
          (Finset.mem_filter.mp hf).2
        have hAf :
            s5_classicalFiber A F f =
              A.filter (fun x => binnedFoldField A (eps / 4) o x = f) := by
          ext x
          simp [s5_classicalFiber, F]
        simpa [F, T, S, hTdef, hSdef] using
          hHeavyBad f (s5_classicalFiber A F f) hAf
            (by simpa [hTdef] using hfheavy)
    have hLightSum :
        (∑ f ∈ (s5_classicalImage A F).filter (fun f =>
          ¬ ((A.card : ℝ) * Real.exp (-T) ≤ ((s5_classicalFiber A F f).card : ℝ))),
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) ≤
        (m : ℝ) *
          (∑ f ∈ (s5_classicalImage A F).filter (fun f =>
            ((s5_classicalFiber A F f).card : ℝ) < (A.card : ℝ) * Real.exp (-T)),
            ((s5_classicalFiber A F f).card : ℝ)) := by
      have hfilter_eq :
          (s5_classicalImage A F).filter (fun f =>
            ¬ ((A.card : ℝ) * Real.exp (-T) ≤
              ((s5_classicalFiber A F f).card : ℝ))) =
          (s5_classicalImage A F).filter (fun f =>
            ((s5_classicalFiber A F f).card : ℝ) <
              (A.card : ℝ) * Real.exp (-T)) := by
        ext f
        simp [not_le]
      rw [hfilter_eq, Finset.mul_sum]
      exact Finset.sum_le_sum fun f _ => by
        calc
          (∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ))
              ≤ ∑ x ∈ s5_classicalFiber A F f, (m : ℝ) := by
                exact Finset.sum_le_sum fun x _ => badStepSet_card_le_dim A q eps x
          _ = (m : ℝ) * ((s5_classicalFiber A F f).card : ℝ) := by
                simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hHeavyCard :
        (∑ f ∈ heavy, ((s5_classicalFiber A F f).card : ℝ)) ≤ (A.card : ℝ) := by
      have hsub : heavy ⊆ s5_classicalImage A F := Finset.filter_subset _ _
      have hsum_le :
          (∑ f ∈ heavy, ((s5_classicalFiber A F f).card : ℝ)) ≤
            ∑ f ∈ s5_classicalImage A F, ((s5_classicalFiber A F f).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro f _ _
          exact Nat.cast_nonneg _)
      have hcard_partition :
          (∑ f ∈ s5_classicalImage A F, ((s5_classicalFiber A F f).card : ℝ)) =
            (A.card : ℝ) := by
        have h := s5_sum_fiberwise_classical A F (fun _ => (1 : ℝ))
        simpa [Finset.sum_const, nsmul_eq_mul, s5_classicalFiber] using h
      exact hsum_le.trans_eq hcard_partition
    have hLightCard := s5_light_atom_card_sum_le_entropy A F env T hA hTpos henv
    have hLightBad :
        (∑ f ∈ (s5_classicalImage A F).filter (fun f =>
          ¬ ((A.card : ℝ) * Real.exp (-T) ≤ ((s5_classicalFiber A F f).card : ℝ))),
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) ≤
        (m : ℝ) * ((A.card : ℝ) * env / T) := by
      exact hLightSum.trans
        (mul_le_mul_of_nonneg_left hLightCard (by exact_mod_cast Nat.zero_le m))
    have hS_nonneg : 0 ≤ S := by
      rw [hSdef]
      exact s5_atomSlack_eff_nonneg hR3 hS4 hS1 hS2 Q hQ eps m
    have hHeavyBadTotal :
        (∑ f ∈ heavy,
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) ≤
        S * (A.card : ℝ) := by
      exact hHeavySum.trans
        (mul_le_mul_of_nonneg_left hHeavyCard hS_nonneg)
    have hm_nonneg : 0 ≤ (m : ℝ) := by
      exact_mod_cast Nat.zero_le m
    have hcard_nonneg : 0 ≤ (A.card : ℝ) := by
      exact_mod_cast Nat.zero_le A.card
    have hAlgScalar : (m : ℝ) * env / T ≤ T := by
      have hT_sq : T ^ 2 = (env + 1) * ((m : ℝ) + 1) := by
        rw [hTdef]
        exact Real.sq_sqrt (by positivity)
      rw [div_le_iff₀ hTpos]
      rw [← pow_two T, hT_sq]
      nlinarith [hm_nonneg, henv_nonneg]
    have hAlg : (m : ℝ) * ((A.card : ℝ) * env / T) ≤ T * (A.card : ℝ) := by
      calc
        (m : ℝ) * ((A.card : ℝ) * env / T)
            = (A.card : ℝ) * ((m : ℝ) * env / T) := by ring
        _ ≤ (A.card : ℝ) * T :=
            mul_le_mul_of_nonneg_left hAlgScalar hcard_nonneg
        _ = T * (A.card : ℝ) := by ring
    calc
      (∑ f ∈ heavy,
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ)) +
        (∑ f ∈ (s5_classicalImage A F).filter (fun f =>
          ¬ ((A.card : ℝ) * Real.exp (-T) ≤ ((s5_classicalFiber A F f).card : ℝ))),
          ∑ x ∈ s5_classicalFiber A F f, ((badStepSet A q eps x).card : ℝ))
          ≤ S * (A.card : ℝ) + (m : ℝ) * ((A.card : ℝ) * env / T) := by
            exact add_le_add hHeavyBadTotal hLightBad
      _ ≤ S * (A.card : ℝ) + T * (A.card : ℝ) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hAlg (S * (A.card : ℝ))
      _ ≤ (T + S + 1) * (A.card : ℝ) := by
            nlinarith [hcard_nonneg]
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [hAempty]

lemma s5_atom_average_slack_le_massSlack_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (eps : ℝ) (_heps : 0 < eps) (m : ℕ) :
    Real.sqrt ((s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
        s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1
      ≤ s5_massSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
  rfl

theorem s5_average_bad_steps_bound_eff (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement)
    (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q) :
    averageBadStepsLE A q eps (s5_massSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m) := by
  obtain ⟨o, ho1, ho2, henv⟩ :=
    s5_foldEnv_eff_spec hR3 hS4 hS1 hS2 Q hQ eps heps m A q hA
      hFat hPinned
  have hHeavyBad :
      ∀ f Af, Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f) →
        (A.card : ℝ) *
            Real.exp (-
              Real.sqrt
                ((s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
                  ((m : ℝ) + 1))) ≤
          (Af.card : ℝ) →
        (∑ x ∈ Af, ((badStepSet A q eps x).card : ℝ)) ≤
          s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m * (Af.card : ℝ) := by
    intro f Af hAf hHeavy
    exact s5_heavy_atoms_bad_steps_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 (s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m) henv
      (le_refl _)
      f Af hAf hHeavy
  have hAtoms :=
    s5_average_bad_steps_from_heavy_atoms_eff hR3 hS4 hS1 hS2 Q hQ m A q eps o
      (s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m) henv hHeavyBad
  exact averageBadStepsLE_mono_slack A
    (s5_atom_average_slack_le_massSlack_eff hR3 hS4 hS1 hS2 Q hQ eps heps m) hAtoms

lemma s5_eps_lt_one_of_valid (Q : QData) (hQ : validQData Q) {eps : ℝ}
    (hepsQ : eps < Q.qMin) : eps < 1 := by
  have hqMin_lt_half : Q.qMin < 1 / 2 := lt_of_le_of_lt hQ.2.1 hQ.2.2.1
  linarith

lemma s5_inv_one_le_inv_sq {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    1 / eps ≤ 1 / eps ^ 2 := by
  have hpos1 : 0 < eps := heps
  have hpos2 : 0 < eps ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos1 hpos2]
  have hmul : 0 ≤ eps * (1 - eps) := by
    exact mul_nonneg (le_of_lt heps) (by linarith)
  nlinarith

lemma s5_inv_sq_le_inv_four {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    1 / eps ^ 2 ≤ 1 / eps ^ 4 := by
  have hpos2 : 0 < eps ^ 2 := by positivity
  have hpos4 : 0 < eps ^ 4 := by positivity
  rw [div_le_div_iff₀ hpos2 hpos4]
  have hmul : 0 ≤ eps ^ 2 * (1 - eps ^ 2) := by
    apply mul_nonneg
    · positivity
    · have hmul1 : 0 ≤ eps * (1 - eps) := by
        exact mul_nonneg (le_of_lt heps) (by linarith)
      nlinarith
  nlinarith

lemma s5_one_le_inv_sq {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    1 ≤ 1 / eps ^ 2 := by
  have hpos2 : 0 < eps ^ 2 := by positivity
  rw [le_div_iff₀ hpos2]
  have hmul : 0 ≤ eps * (1 - eps) := by
    exact mul_nonneg (le_of_lt heps) (by linarith)
  nlinarith

lemma s5_one_le_inv_four {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    1 ≤ 1 / eps ^ 4 :=
  (s5_one_le_inv_sq heps heps1).trans (s5_inv_sq_le_inv_four heps heps1)

lemma s5_sqrt_scaled_effGeo_le (s : ℕ → ℝ) (n : ℕ) {D R : ℝ}
    (hD0 : 0 ≤ D) (hR0 : 0 ≤ R) (hDR : Real.sqrt D ≤ R) :
    Real.sqrt ((D * (s n + 1)) * ((n : ℝ) + 1)) ≤ R * (effGeo s n + 1) := by
  have hterm :
      Real.sqrt ((s n + 1) * ((n : ℝ) + 1)) ≤ effGeo s n + 1 := by
    have hle : Real.sqrt ((s n + 1) * ((n : ℝ) + 1)) ≤ effGeo s n := by
      unfold effGeo
      exact le_max_right _ _
    linarith
  calc
    Real.sqrt ((D * (s n + 1)) * ((n : ℝ) + 1))
        = Real.sqrt (D * ((s n + 1) * ((n : ℝ) + 1))) := by ring_nf
    _ = Real.sqrt D * Real.sqrt ((s n + 1) * ((n : ℝ) + 1)) := by
        rw [Real.sqrt_mul hD0]
    _ ≤ R * (effGeo s n + 1) := by
        exact mul_le_mul hDR hterm (Real.sqrt_nonneg _) hR0

lemma s5_sqrt_div_pow4_le {C eps : ℝ} (hC : 1 ≤ C) (heps : 0 < eps) :
    Real.sqrt (C / eps ^ 4) ≤ C / eps ^ 2 := by
  have hR0 : 0 ≤ C / eps ^ 2 := by positivity
  have hle : C / eps ^ 4 ≤ (C / eps ^ 2) ^ 2 := by
    field_simp [ne_of_gt heps]
    nlinarith [hC]
  have hsqrt := Real.sqrt_le_sqrt hle
  simpa [Real.sqrt_sq hR0] using hsqrt

lemma s5_sqrt_div_pow2_le {C eps : ℝ} (hC : 1 ≤ C) (heps : 0 < eps) :
    Real.sqrt (C / eps ^ 2) ≤ C / eps := by
  have hR0 : 0 ≤ C / eps := by positivity
  have hle : C / eps ^ 2 ≤ (C / eps) ^ 2 := by
    field_simp [ne_of_gt heps]
    nlinarith [hC]
  have hsqrt := Real.sqrt_le_sqrt hle
  simpa [Real.sqrt_sq hR0] using hsqrt

lemma s5_sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have hle : x ≤ x ^ 2 := by nlinarith
  have hsqrt := Real.sqrt_le_sqrt hle
  simpa [Real.sqrt_sq hx0] using hsqrt

lemma s5_K4_le_raw_div_pow4 (hS4 : S4EffU) (Q : QData) (hQ : validQData Q)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    s5_K4 hS4 Q hQ eps ≤ s5_K4_raw hS4 Q hQ / eps ^ 4 := by
  unfold s5_K4
  have hKraw : 1 ≤ s5_K4_raw hS4 Q hQ :=
    s5_K4_raw_ge_one hS4 Q hQ
  have hone : 1 ≤ s5_K4_raw hS4 Q hQ / eps ^ 4 := by
    have hpos4 : 0 < eps ^ 4 := by positivity
    rw [le_div_iff₀ hpos4]
    exact (le_trans (by
      have hle : eps ^ 4 ≤ 1 := by
        have h12 := s5_one_le_inv_four heps heps1
        rw [le_div_iff₀ hpos4] at h12
        simpa using h12
      simpa using hle) hKraw)
  exact max_le hone le_rfl

lemma s5_sepCoeff_le_uniform (Q : QData) (hQ : validQData Q)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    s5_sepCoeff eps Q.mu0 ≤
      (64 / Q.mu0 ^ 2 + 48 / Q.mu0) / eps ^ 2 := by
  have hmu : 0 < Q.mu0 := hQ.2.2.2.2.1
  unfold s5_sepCoeff
  rw [dif_pos (mul_pos heps hmu)]
  have hterm1 : 64 / (eps * Q.mu0) ^ 2 = (64 / Q.mu0 ^ 2) / eps ^ 2 := by
    field_simp [ne_of_gt heps, ne_of_gt hmu]
  have hterm2 : 48 / (eps * Q.mu0) ≤ (48 / Q.mu0) / eps ^ 2 := by
    have hinv := s5_inv_one_le_inv_sq heps heps1
    calc
      48 / (eps * Q.mu0) = (48 / Q.mu0) * (1 / eps) := by
        field_simp [ne_of_gt heps, ne_of_gt hmu]
      _ ≤ (48 / Q.mu0) * (1 / eps ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (48 / Q.mu0) / eps ^ 2 := by ring
  calc
    64 / (eps * Q.mu0) ^ 2 + 48 / (eps * Q.mu0)
        ≤ (64 / Q.mu0 ^ 2) / eps ^ 2 + (48 / Q.mu0) / eps ^ 2 := by
          exact add_le_add (le_of_eq hterm1) hterm2
    _ = (64 / Q.mu0 ^ 2 + 48 / Q.mu0) / eps ^ 2 := by ring

lemma s5_geom_base_eff_le_grade6_uniform (hR3 : R3Eff) (hS4 : S4EffU)
    (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (m : ℕ) :
    Real.sqrt
        ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
          ((m : ℝ) + 1)) ≤
      ((s5_K4_raw hS4 Q hQ + 1) / eps ^ 2) *
        (effEnv 6 Q.sigma m + 1) := by
  let K4raw : ℝ := s5_K4_raw hS4 Q hQ
  let C : ℝ := K4raw + 1
  set E4 : ℝ := effEnv 5 Q.sigma m
  have hK4raw_ge : 1 ≤ K4raw := by
    dsimp [K4raw]
    exact s5_K4_raw_ge_one hS4 Q hQ
  have hC_ge : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 ≤ C := by linarith
  have hE4_nonneg : 0 ≤ E4 := by
    dsimp [E4]
    exact effEnv_nonneg 5 Q.sigma hQ.2.2.2.2.2.2.1.1 m
  have hE4_one_nonneg : 0 ≤ E4 + 1 := by linarith
  have hE4_one_ge_one : 1 ≤ E4 + 1 := by linarith
  have hInv4 : 1 ≤ 1 / eps ^ 4 := s5_one_le_inv_four heps heps1
  have hSigma_le : Q.sigma m ≤ E4 := by
    dsimp [E4]
    exact le_effEnv 5 Q.sigma m
  have hK4_le :=
    s5_K4_le_raw_div_pow4 hS4 Q hQ heps heps1
  have hFold_le :
      s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m ≤
        (K4raw / eps ^ 4) * (E4 + 1) := by
    unfold s5_foldEnv_eff
    have hE : 0 ≤ effEnv 5 Q.sigma m + 1 := by
      simpa [E4] using hE4_one_nonneg
    have h := mul_le_mul_of_nonneg_right hK4_le hE
    simpa [K4raw, E4] using h
  have hSigma_one_le :
      Q.sigma m + 1 ≤ (1 / eps ^ 4) * (E4 + 1) := by
    have hsig : Q.sigma m + 1 ≤ E4 + 1 := by linarith
    have hscale : E4 + 1 ≤ (1 / eps ^ 4) * (E4 + 1) :=
      le_mul_of_one_le_left hE4_one_nonneg hInv4
    exact hsig.trans hscale
  have hbase_plus :
      s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1 ≤
        (C / eps ^ 4) * (E4 + 1) := by
    unfold s5_baseSlack_eff
    calc
      Q.sigma m + s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1
          = s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m + (Q.sigma m + 1) := by ring
      _ ≤ (K4raw / eps ^ 4) * (E4 + 1) +
            (1 / eps ^ 4) * (E4 + 1) := by
          exact add_le_add hFold_le hSigma_one_le
      _ = (C / eps ^ 4) * (E4 + 1) := by
          dsimp [C]
          ring
  have hD0 : 0 ≤ C / eps ^ 4 := by positivity
  have hR0 : 0 ≤ C / eps ^ 2 := by positivity
  have hsqrtD : Real.sqrt (C / eps ^ 4) ≤ C / eps ^ 2 :=
    s5_sqrt_div_pow4_le hC_ge heps
  calc
    Real.sqrt
        ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
          ((m : ℝ) + 1))
        ≤ Real.sqrt (((C / eps ^ 4) * (E4 + 1)) * ((m : ℝ) + 1)) := by
          exact Real.sqrt_le_sqrt
            (mul_le_mul_of_nonneg_right hbase_plus (by positivity))
    _ ≤ (C / eps ^ 2) * (effGeo (effEnv 5 Q.sigma) m + 1) := by
          simpa [E4] using
            s5_sqrt_scaled_effGeo_le (effEnv 5 Q.sigma) m hD0 hR0 hsqrtD
    _ = ((s5_K4_raw hS4 Q hQ + 1) / eps ^ 2) *
          (effEnv 6 Q.sigma m + 1) := by
          dsimp [C, K4raw]

lemma s5_geom2_base_eff_le_grade7_uniform (hR3 : R3Eff) (hS4 : S4EffU)
    (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (m : ℕ) :
    Real.sqrt
        ((Real.sqrt
            ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
              ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) ≤
      ((s5_K4_raw hS4 Q hQ + 2) / eps ^ 2) *
        (effEnv 7 Q.sigma m + 1) := by
  let C : ℝ := s5_K4_raw hS4 Q hQ + 2
  set E5 : ℝ := effEnv 6 Q.sigma m
  have hChoose_ge : 1 ≤ s5_K4_raw hS4 Q hQ :=
    s5_K4_raw_ge_one hS4 Q hQ
  have hC_ge : 1 ≤ C := by dsimp [C]; linarith
  have hE5_nonneg : 0 ≤ E5 := by
    dsimp [E5]
    exact effEnv_nonneg 6 Q.sigma hQ.2.2.2.2.2.2.1.1 m
  have hE5_one_nonneg : 0 ≤ E5 + 1 := by linarith
  have hInv2 : 1 ≤ 1 / eps ^ 2 := s5_one_le_inv_sq heps heps1
  have hG1_le :
      Real.sqrt
          ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
            ((m : ℝ) + 1)) + 1 ≤
        (C / eps ^ 2) * (E5 + 1) := by
    have hG1 :=
      s5_geom_base_eff_le_grade6_uniform hR3 hS4 hS1 hS2 Q hQ heps heps1 m
    have hone : 1 ≤ (1 / eps ^ 2) * (E5 + 1) := by
      have hprod :=
        mul_le_mul hInv2 (by linarith : (1 : ℝ) ≤ E5 + 1)
          (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 1 / eps ^ 2)
      simpa using hprod
    calc
      Real.sqrt
          ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
            ((m : ℝ) + 1)) + 1
          ≤ ((s5_K4_raw hS4 Q hQ + 1) / eps ^ 2) * (E5 + 1) +
              (1 / eps ^ 2) * (E5 + 1) := by
            exact add_le_add hG1 hone
      _ = (C / eps ^ 2) * (E5 + 1) := by
            dsimp [C]
            ring
  have hD0 : 0 ≤ C / eps ^ 2 := by positivity
  have hD_ge_one : 1 ≤ C / eps ^ 2 := by
    have hC_scale : C ≤ C / eps ^ 2 := by
      calc
        C = C * 1 := by ring
        _ ≤ C * (1 / eps ^ 2) :=
            mul_le_mul_of_nonneg_left hInv2 (by linarith)
        _ = C / eps ^ 2 := by ring
    exact hC_ge.trans hC_scale
  have hsqrtD : Real.sqrt (C / eps ^ 2) ≤ C / eps ^ 2 :=
    s5_sqrt_le_self_of_one_le hD_ge_one
  calc
    Real.sqrt
        ((Real.sqrt
            ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
              ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1))
        ≤ Real.sqrt (((C / eps ^ 2) * (E5 + 1)) * ((m : ℝ) + 1)) := by
          exact Real.sqrt_le_sqrt
            (mul_le_mul_of_nonneg_right hG1_le (by positivity))
    _ ≤ (C / eps ^ 2) * (effGeo (effEnv 6 Q.sigma) m + 1) := by
          simpa [E5] using
            s5_sqrt_scaled_effGeo_le (effEnv 6 Q.sigma) m hD0 hD0 hsqrtD
    _ = ((s5_K4_raw hS4 Q hQ + 2) / eps ^ 2) *
          (effEnv 7 Q.sigma m + 1) := by
          dsimp [C]

lemma s5_atomSigmaStar_eff_le_grade8_uniform (hR3 : R3Eff) (hS4 : S4EffU)
    (hS1 : S1Statement) (hS2 : S2Statement)
    (Q : QData) (hQ : validQData Q) {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) (m : ℕ) :
    s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m ≤
      s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
        ((4 * (s5_K4_raw hS4 Q hQ + 2) + 1) / eps ^ 2) *
        (effEnv 8 Q.sigma m + 1) := by
  let C : ℝ := s5_K4_raw hS4 Q hQ + 2
  have hChoose_ge : 1 ≤ s5_K4_raw hS4 Q hQ :=
    s5_K4_raw_ge_one hS4 Q hQ
  have hC_ge : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 ≤ C := by linarith
  have hInv2 : 1 ≤ 1 / eps ^ 2 := s5_one_le_inv_sq heps heps1
  have hSigma_nonneg : ∀ n, 0 ≤ Q.sigma n := hQ.2.2.2.2.2.2.1.1
  have hAtomSigma_le : ∀ n,
      (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma n ≤
        (C / eps ^ 2) * (effEnv 6 Q.sigma n + 1) := by
    intro n
    dsimp [s5_atomQ_eff]
    have hG1 :=
      s5_geom_base_eff_le_grade6_uniform hR3 hS4 hS1 hS2 Q hQ heps heps1 n
    have hE5_nonneg : 0 ≤ effEnv 6 Q.sigma n :=
      effEnv_nonneg 6 Q.sigma hSigma_nonneg n
    have hsig : Q.sigma n ≤ (1 / eps ^ 2) * (effEnv 6 Q.sigma n + 1) := by
      have hsig5 : Q.sigma n ≤ effEnv 6 Q.sigma n := le_effEnv 6 Q.sigma n
      have hscale : effEnv 6 Q.sigma n + 1 ≤
          (1 / eps ^ 2) * (effEnv 6 Q.sigma n + 1) :=
        le_mul_of_one_le_left (by linarith) hInv2
      exact (by linarith : Q.sigma n ≤ effEnv 6 Q.sigma n + 1).trans hscale
    calc
      Q.sigma n +
          Real.sqrt
            ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps n + 1) *
              ((n : ℝ) + 1))
          ≤ (1 / eps ^ 2) * (effEnv 6 Q.sigma n + 1) +
              ((s5_K4_raw hS4 Q hQ + 1) / eps ^ 2) *
                (effEnv 6 Q.sigma n + 1) := by
            exact add_le_add hsig hG1
      _ = (C / eps ^ 2) * (effEnv 6 Q.sigma n + 1) := by
            dsimp [C]
            ring
  have hCeps_ge : 1 ≤ C / eps ^ 2 := by
    calc
      1 ≤ C := hC_ge
      _ = C * 1 := by ring
      _ ≤ C * (1 / eps ^ 2) :=
          mul_le_mul_of_nonneg_left hInv2 hC0
      _ = C / eps ^ 2 := by ring
  have hEnv_le :
      effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m ≤
        (4 * (C / eps ^ 2)) * (effEnv 8 Q.sigma m + 1) := by
    have hmono := effEnv_mono hAtomSigma_le 2 m
    have hcomp :=
      effEnv_comp 2 (i := 6) (C := C / eps ^ 2) hCeps_ge
        (s := Q.sigma) hSigma_nonneg m
    have h := hmono.trans hcomp
    have hnorm :
        (2 ^ 2 * (C / eps ^ 2)) * (effEnv (6 + 2) Q.sigma m + 1) =
          (4 * (C / eps ^ 2)) * (effEnv 8 Q.sigma m + 1) := by
      norm_num
    exact h.trans_eq hnorm
  have hE7_nonneg : 0 ≤ effEnv 8 Q.sigma m :=
    effEnv_nonneg 8 Q.sigma hSigma_nonneg m
  have hone_E7 : 1 ≤ (1 / eps ^ 2) * (effEnv 8 Q.sigma m + 1) := by
    have hprod :=
      mul_le_mul hInv2 (by linarith : (1 : ℝ) ≤ effEnv 8 Q.sigma m + 1)
        (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 1 / eps ^ 2)
    simpa using hprod
  have hplus :
      effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m + 1 ≤
        ((4 * C + 1) / eps ^ 2) * (effEnv 8 Q.sigma m + 1) := by
    calc
      effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m + 1
          ≤ (4 * (C / eps ^ 2)) * (effEnv 8 Q.sigma m + 1) +
              (1 / eps ^ 2) * (effEnv 8 Q.sigma m + 1) := by
            exact add_le_add hEnv_le hone_E7
      _ = ((4 * C + 1) / eps ^ 2) * (effEnv 8 Q.sigma m + 1) := by
            ring
  have hK3_nonneg : 0 ≤ s5_K3 hR3 hS4 hS1 hS2 Q hQ eps := by
    linarith [s5_K3_ge_one hR3 hS4 hS1 hS2 Q hQ eps]
  unfold s5_atomSigmaStar_eff
  calc
    s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
        (effEnv 2 (s5_atomQ_eff hR3 hS4 hS1 hS2 Q hQ eps).sigma m + 1)
        ≤ s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
            (((4 * C + 1) / eps ^ 2) * (effEnv 8 Q.sigma m + 1)) := by
          exact mul_le_mul_of_nonneg_left hplus hK3_nonneg
    _ = s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
        ((4 * (s5_K4_raw hS4 Q hQ + 2) + 1) / eps ^ 2) *
        (effEnv 8 Q.sigma m + 1) := by
          dsimp [C]
          ring

lemma s5_massSlack_eff_le_grade8_uniform (hR3 : R3Eff) (hS4 : S4EffU)
    (hS1 : S1Statement) (hS2 : S2Statement)
    (qMin qMax s0 mu0 : ℝ)
    (hqMin : 0 < qMin) (hqMinMax : qMin ≤ qMax) (hqMax : qMax < 1 / 2)
    (hs0 : 0 < s0) (hmu0 : 0 < mu0) (hreg : qMax + s0 ≤ 1 / 2 - mu0) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (sigma : ℕ → ℝ) (hsub : Sublinear sigma) (hlog : ∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n),
      ∀ eps : ℝ, 0 < eps → eps < qMin →
        ∀ m : ℕ,
          s5_massSlack_eff hR3 hS4 hS1 hS2 ⟨qMin, qMax, s0, mu0, sigma⟩
            ⟨hqMin, hqMinMax, hqMax, hs0, hmu0, hreg, hsub, hlog⟩ eps m ≤
            (K / eps ^ 4) * (effEnv 8 sigma m + 1) := by
  let K4raw : ℝ :=
    s5_K4_raw_class hS4 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg
  let K3 : ℝ :=
    s5_K3_raw_class hR3 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg
  let Cg1 : ℝ := K4raw + 1
  let Cg2 : ℝ := K4raw + 2
  let Cstar : ℝ := K3 * (4 * Cg2 + 1)
  let Csep : ℝ := 64 / mu0 ^ 2 + 48 / mu0
  let Cinner : ℝ := Cg2 + Cstar + 1 + Cg1 + 1
  let Catom : ℝ := Csep * Cinner + 40
  let Cmass : ℝ := Cg1 + Catom + 1
  refine ⟨max 1 Cmass, le_max_left _ _, ?_⟩
  intro sigma hsub hlog eps heps hepsQ m
  let Q : QData := ⟨qMin, qMax, s0, mu0, sigma⟩
  let hQ : validQData Q := ⟨hqMin, hqMinMax, hqMax, hs0, hmu0, hreg, hsub, hlog⟩
  set E7 : ℝ := effEnv 8 Q.sigma m with hE7_def
  set E : ℝ := E7 + 1 with hE_def
  set T : ℝ :=
    Real.sqrt ((s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
      ((m : ℝ) + 1)) with hT_def
  set G1 : ℝ :=
    Real.sqrt ((s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m + 1) *
      ((m : ℝ) + 1)) with hG1_def
  set G2 : ℝ :=
    Real.sqrt ((G1 + 1) * ((m : ℝ) + 1)) with hG2_def
  set star : ℝ := s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m with hstar_def
  set atom : ℝ := s5_atomSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m
  have hK4raw_eq : s5_K4_raw hS4 Q hQ = K4raw := rfl
  have hK3eq : s5_K3 hR3 hS4 hS1 hS2 Q hQ eps = K3 := rfl
  have hK3eq_one : s5_K3 hR3 hS4 hS1 hS2 Q hQ 1 = K3 := rfl
  have hCg1_eq : Cg1 = s5_K4_raw hS4 Q hQ + 1 := rfl
  have hCg2_eq : Cg2 = s5_K4_raw hS4 Q hQ + 2 := rfl
  have heps1 : eps < 1 := s5_eps_lt_one_of_valid Q hQ hepsQ
  have hK4raw_ge : 1 ≤ K4raw := by
    simpa [hK4raw_eq] using s5_K4_raw_ge_one hS4 Q hQ
  have hK3_ge : 1 ≤ K3 := by
    simpa [hK3eq_one] using s5_K3_ge_one hR3 hS4 hS1 hS2 Q hQ 1
  have hK3_nonneg : 0 ≤ K3 := by linarith
  have hCg1_nonneg : 0 ≤ Cg1 := by dsimp [Cg1]; linarith
  have hCg2_nonneg : 0 ≤ Cg2 := by dsimp [Cg2]; linarith
  have hCstar_nonneg : 0 ≤ Cstar := by
    dsimp [Cstar]
    exact mul_nonneg hK3_nonneg (by positivity)
  have hmu : 0 < Q.mu0 := hQ.2.2.2.2.1
  have hCsep_nonneg : 0 ≤ Csep := by dsimp [Csep]; positivity
  have hCinner_nonneg : 0 ≤ Cinner := by
    dsimp [Cinner]
    positivity
  have hCatom_nonneg : 0 ≤ Catom := by
    dsimp [Catom]
    exact add_nonneg (mul_nonneg hCsep_nonneg hCinner_nonneg) (by norm_num)
  have hCmass_nonneg : 0 ≤ Cmass := by
    dsimp [Cmass]
    positivity
  have hE7_nonneg : 0 ≤ E7 := by
    dsimp [E7]
    exact effEnv_nonneg 8 Q.sigma hQ.2.2.2.2.2.2.1.1 m
  have hE_nonneg : 0 ≤ E := by dsimp [E]; linarith
  have hE_ge_one : 1 ≤ E := by dsimp [E]; linarith
  have hInv2 : 1 ≤ 1 / eps ^ 2 := s5_one_le_inv_sq heps heps1
  have hInv4 : 1 ≤ 1 / eps ^ 4 := s5_one_le_inv_four heps heps1
  have hInvSqLeInv4 : 1 / eps ^ 2 ≤ 1 / eps ^ 4 :=
    s5_inv_sq_le_inv_four heps heps1
  have hE_le_inv2E : E ≤ (1 / eps ^ 2) * E :=
    le_mul_of_one_le_left hE_nonneg hInv2
  have hE_le_inv4E : E ≤ (1 / eps ^ 4) * E :=
    le_mul_of_one_le_left hE_nonneg hInv4
  have hdiv_sq_le_four : ∀ {C : ℝ}, 0 ≤ C → C / eps ^ 2 ≤ C / eps ^ 4 := by
    intro C hC
    calc
      C / eps ^ 2 = C * (1 / eps ^ 2) := by ring
      _ ≤ C * (1 / eps ^ 4) :=
          mul_le_mul_of_nonneg_left hInvSqLeInv4 hC
      _ = C / eps ^ 4 := by ring
  have hG1_le_sq : G1 ≤ (Cg1 / eps ^ 2) * E := by
    have hG1 :=
      s5_geom_base_eff_le_grade6_uniform hR3 hS4 hS1 hS2 Q hQ heps heps1 m
    have h57 : effEnv 6 Q.sigma m + 1 ≤ E := by
      have h := s5_effEnv_five_le_seven Q m
      change effEnv 6 Q.sigma m + 1 ≤ effEnv 8 Q.sigma m + 1
      exact add_le_add h (le_refl (1 : ℝ))
    have hcoeff : 0 ≤ (s5_K4_raw hS4 Q hQ + 1) / eps ^ 2 := by
      exact div_nonneg (by linarith [s5_K4_raw_ge_one hS4 Q hQ])
        (sq_nonneg eps)
    have hG1E : G1 ≤ ((s5_K4_raw hS4 Q hQ + 1) / eps ^ 2) * E := by
      have hmul :
          ((s5_K4_raw hS4 Q hQ + 1) / eps ^ 2) * (effEnv 6 Q.sigma m + 1) ≤
            ((s5_K4_raw hS4 Q hQ + 1) / eps ^ 2) * E :=
        mul_le_mul_of_nonneg_left h57 hcoeff
      exact hG1.trans hmul
    exact hG1E.trans_eq
      (congrArg (fun x : ℝ => (x / eps ^ 2) * E) hCg1_eq.symm)
  have hT_le_G1 : T ≤ G1 := by
    have hEnv_le_base :
        s5_foldEnv_eff hR3 hS4 hS1 hS2 Q hQ eps m ≤
          s5_baseSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m := by
      unfold s5_baseSlack_eff
      have hSigma : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
      linarith
    have hm1_nonneg : 0 ≤ (m : ℝ) + 1 :=
      add_nonneg (Nat.cast_nonneg m) zero_le_one
    rw [hT_def, hG1_def]
    exact Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right (by linarith) hm1_nonneg)
  have hG1_scale :
      (Cg1 / eps ^ 2) * E ≤ (Cg1 / eps ^ 4) * E :=
    mul_le_mul_of_nonneg_right (hdiv_sq_le_four hCg1_nonneg) hE_nonneg
  have hG1_le_four : G1 ≤ (Cg1 / eps ^ 4) * E :=
    le_trans hG1_le_sq hG1_scale
  have hT_le_four : T ≤ (Cg1 / eps ^ 4) * E :=
    le_trans hT_le_G1 hG1_le_four
  have hG2_le_sq : G2 ≤ (Cg2 / eps ^ 2) * E := by
    have hG2_raw :
        G2 ≤ ((s5_K4_raw hS4 Q hQ + 2) / eps ^ 2) *
            (effEnv 7 Q.sigma m + 1) := by
      rw [hG2_def, hG1_def]
      exact @s5_geom2_base_eff_le_grade7_uniform hR3 hS4 hS1 hS2 Q hQ eps heps heps1 m
    have h67 : effEnv 7 Q.sigma m + 1 ≤ E := by
      have h := s5_effEnv_six_le_seven Q m
      change effEnv 7 Q.sigma m + 1 ≤ effEnv 8 Q.sigma m + 1
      exact add_le_add h (le_refl (1 : ℝ))
    have hcoeff : 0 ≤ (s5_K4_raw hS4 Q hQ + 2) / eps ^ 2 := by
      exact div_nonneg (by linarith [s5_K4_raw_ge_one hS4 Q hQ])
        (sq_nonneg eps)
    have hG2E : G2 ≤ ((s5_K4_raw hS4 Q hQ + 2) / eps ^ 2) * E := by
      have hmul :
          ((s5_K4_raw hS4 Q hQ + 2) / eps ^ 2) * (effEnv 7 Q.sigma m + 1) ≤
            ((s5_K4_raw hS4 Q hQ + 2) / eps ^ 2) * E :=
        mul_le_mul_of_nonneg_left h67 hcoeff
      exact hG2_raw.trans hmul
    exact hG2E.trans_eq
      (congrArg (fun x : ℝ => (x / eps ^ 2) * E) hCg2_eq.symm)
  have hG2_le_four : G2 ≤ (Cg2 / eps ^ 4) * E :=
    hG2_le_sq.trans
      (mul_le_mul_of_nonneg_right (hdiv_sq_le_four hCg2_nonneg) hE_nonneg)
  have hstar_le_sq : star ≤ (Cstar / eps ^ 2) * E := by
    have hstar_raw :
        s5_atomSigmaStar_eff hR3 hS4 hS1 hS2 Q hQ eps m ≤
          s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
            ((4 * (s5_K4_raw hS4 Q hQ + 2) + 1) / eps ^ 2) *
            (effEnv 8 Q.sigma m + 1) :=
      @s5_atomSigmaStar_eff_le_grade8_uniform hR3 hS4 hS1 hS2 Q hQ eps heps heps1 m
    have hRhs :
        s5_K3 hR3 hS4 hS1 hS2 Q hQ eps *
            ((4 * (s5_K4_raw hS4 Q hQ + 2) + 1) / eps ^ 2) *
            (effEnv 8 Q.sigma m + 1) =
          (Cstar / eps ^ 2) * E := by
      rw [hK3eq, ← hCg2_eq, hE_def, hE7_def]
      dsimp [Cstar]
      ring
    rw [hstar_def]
    exact hstar_raw.trans_eq hRhs
  have hstar_le_four : star ≤ (Cstar / eps ^ 4) * E :=
    hstar_le_sq.trans
      (mul_le_mul_of_nonneg_right (hdiv_sq_le_four hCstar_nonneg) hE_nonneg)
  have hsigma_le_four : Q.sigma m ≤ (1 / eps ^ 4) * E := by
    have hsig7 : Q.sigma m ≤ E := by
      have hsig : Q.sigma m ≤ effEnv 8 Q.sigma m := le_effEnv 8 Q.sigma m
      change Q.sigma m ≤ effEnv 8 Q.sigma m + 1
      linarith
    exact hsig7.trans hE_le_inv4E
  have hone_le_four : (1 : ℝ) ≤ (1 / eps ^ 4) * E := by
    exact hE_ge_one.trans hE_le_inv4E
  have hInner_le_sq :
      G2 + star + Q.sigma m + G1 + 1 ≤ (Cinner / eps ^ 2) * E := by
    have hsigma_sq : Q.sigma m ≤ (1 / eps ^ 2) * E := by
      have hsig7 : Q.sigma m ≤ E := by
        have hsig : Q.sigma m ≤ effEnv 8 Q.sigma m := le_effEnv 8 Q.sigma m
        change Q.sigma m ≤ effEnv 8 Q.sigma m + 1
        linarith
      exact hsig7.trans hE_le_inv2E
    have hone_sq : (1 : ℝ) ≤ (1 / eps ^ 2) * E :=
      hE_ge_one.trans hE_le_inv2E
    calc
      G2 + star + Q.sigma m + G1 + 1
          ≤ (Cg2 / eps ^ 2) * E + (Cstar / eps ^ 2) * E +
              (1 / eps ^ 2) * E + (Cg1 / eps ^ 2) * E +
              (1 / eps ^ 2) * E := by
            linarith
      _ = (Cinner / eps ^ 2) * E := by
            dsimp [Cinner]
            ring
  have hSep_le : s5_sepCoeff eps Q.mu0 ≤ (Csep / eps ^ 2) := by
    have h := s5_sepCoeff_le_uniform Q hQ heps heps1
    simpa [Csep] using h
  have hInner_nonneg : 0 ≤ G2 + star + Q.sigma m + G1 + 1 := by
    have hG2_nonneg : 0 ≤ G2 := by dsimp [G2]; exact Real.sqrt_nonneg _
    have hstar_nonneg : 0 ≤ star := by
      dsimp [star]
      exact s5_atomSigmaStar_eff_nonneg hR3 hS4 hS1 hS2 Q hQ eps m
    have hsigma_nonneg : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
    have hG1_nonneg : 0 ≤ G1 := by dsimp [G1]; exact Real.sqrt_nonneg _
    linarith
  have hAtom_def :
      atom = s5_sepCoeff eps Q.mu0 * (G2 + star + Q.sigma m + G1 + 1) + 40 := by
    dsimp [atom, s5_atomSlack_eff, G2, G1, star]
  have hAtom_le : atom ≤ (Catom / eps ^ 4) * E := by
    have hCsep_div_nonneg : 0 ≤ Csep / eps ^ 2 := by positivity
    have hprod :
        s5_sepCoeff eps Q.mu0 * (G2 + star + Q.sigma m + G1 + 1) ≤
          (Csep / eps ^ 2) * ((Cinner / eps ^ 2) * E) := by
      exact mul_le_mul hSep_le hInner_le_sq hInner_nonneg hCsep_div_nonneg
    have hforty : (40 : ℝ) ≤ (40 / eps ^ 4) * E := by
      calc
        (40 : ℝ) = 40 * 1 := by ring
        _ ≤ 40 * ((1 / eps ^ 4) * E) := by
            exact mul_le_mul_of_nonneg_left hone_le_four (by norm_num)
        _ = (40 / eps ^ 4) * E := by ring
    rw [hAtom_def]
    calc
      s5_sepCoeff eps Q.mu0 * (G2 + star + Q.sigma m + G1 + 1) + 40
          ≤ (Csep / eps ^ 2) * ((Cinner / eps ^ 2) * E) +
              (40 / eps ^ 4) * E := by
            exact add_le_add hprod hforty
      _ = ((Csep * Cinner + 40) / eps ^ 4) * E := by
            ring
      _ = (Catom / eps ^ 4) * E := by
            dsimp [Catom]
  have hMass_def :
      s5_massSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m = T + atom + 1 := by
    dsimp [s5_massSlack_eff, T, atom]
  have hMass_le :
      s5_massSlack_eff hR3 hS4 hS1 hS2 Q hQ eps m ≤
        (Cmass / eps ^ 4) * E := by
    rw [hMass_def]
    calc
      T + atom + 1
          ≤ (Cg1 / eps ^ 4) * E + (Catom / eps ^ 4) * E +
              (1 / eps ^ 4) * E := by
            exact add_le_add (add_le_add hT_le_four hAtom_le) hone_le_four
      _ = (Cmass / eps ^ 4) * E := by
            dsimp [Cmass]
            ring
  have hCmass_le_K : Cmass ≤ max 1 Cmass := le_max_right _ _
  have hK_nonneg : 0 ≤ max 1 Cmass := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  have hdiv_le : Cmass / eps ^ 4 ≤ (max 1 Cmass) / eps ^ 4 := by
    exact div_le_div_of_nonneg_right hCmass_le_K (by positivity)
  exact hMass_le.trans
    (mul_le_mul_of_nonneg_right hdiv_le hE_nonneg)

end S5U

theorem s5_effU (hR3 : R3Eff) (hS4 : S4EffU) (hS1 : S1Statement) (hS2 : S2Statement) : S5EffU := by
  intro qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg
  obtain ⟨K, hK, hKbound⟩ :=
    S5U.s5_massSlack_eff_le_grade8_uniform hR3 hS4 hS1 hS2 qMin qMax s0 mu0 hqMin hqMinMax hqMax hs0 hmu0 hreg
  refine ⟨K, hK, ?_⟩
  intro sigma hsub hlog eps heps hepsQ m A q hA hFat hPinned
  let Q : QData := ⟨qMin, qMax, s0, mu0, sigma⟩
  let hQ : validQData Q := ⟨hqMin, hqMinMax, hqMax, hs0, hmu0, hreg, hsub, hlog⟩
  exact averageBadStepsLE_mono_slack A (hKbound sigma hsub hlog eps heps hepsQ m)
    (S5U.s5_average_bad_steps_bound_eff hR3 hS4 hS1 hS2 Q hQ m A q eps hA heps
      hepsQ hFat hPinned)

end HarperStability
