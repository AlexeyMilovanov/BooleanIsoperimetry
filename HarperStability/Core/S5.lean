import HarperStability.Core.Basic
import HarperStability.Core.S5KL
import HarperStability.Core.S5Transfer
import HarperStability.Core.S5Separation

namespace HarperStability

noncomputable def s5_sFam (hR3 : R3Statement) (Q : QData) (hQ : validQData Q) :
    ℝ → ℕ → ℝ :=
  Classical.choose (blockRegularFamily_from_R3 Q hR3 hQ)

lemma s5_sFam_sublinear (hR3 : R3Statement) (Q : QData) (hQ : validQData Q) :
    ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (s5_sFam hR3 Q hQ pLow) :=
  (Classical.choose_spec (blockRegularFamily_from_R3 Q hR3 hQ)).1

lemma s5_sFam_blockRegular (hR3 : R3Statement) (Q : QData) (hQ : validQData Q) :
    ∀ m A q, A.Nonempty → fat Q m A q → pinned Q m A q →
      blockRegularFamily m A q (s5_sFam hR3 Q hQ) :=
  (Classical.choose_spec (blockRegularFamily_from_R3 Q hR3 hQ)).2

noncomputable def s5_vFam (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) :
    ℝ → ℕ → ℝ :=
  Classical.choose (varianceFamily_from_R3_S1_S2 Q hR3 hS1 hS2 hQ)

lemma s5_vFam_sublinear (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) :
    ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
      Sublinear (s5_vFam hR3 hS1 hS2 Q hQ pLow) :=
  (Classical.choose_spec (varianceFamily_from_R3_S1_S2 Q hR3 hS1 hS2 hQ)).1

lemma s5_vFam_variance (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (Q : QData) (hQ : validQData Q) :
    ∀ m A q, A.Nonempty → fat Q m A q → pinned Q m A q →
      ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
        varianceBudgetLE A pLow (s5_vFam hR3 hS1 hS2 Q hQ pLow m) :=
  (Classical.choose_spec (varianceFamily_from_R3_S1_S2 Q hR3 hS1 hS2 hQ)).2

noncomputable def s5_foldEnvWitness (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    ∃ env : ℕ → ℝ, Sublinear env ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty →
        blockRegularFamily m A q (s5_sFam hR3 Q hQ) →
        (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
          varianceBudgetLE A pLow (s5_vFam hR3 hS1 hS2 Q hQ pLow m)) →
        ∃ o : ℝ, 0 ≤ o ∧ o < eps / 4 ∧
          uH A (binnedFoldField A (eps / 4) o) ≤ env m :=
  hS4 (eps / 4) (by linarith)
    (s5_sFam hR3 Q hQ) (s5_vFam hR3 hS1 hS2 Q hQ)
    (s5_sFam_sublinear hR3 Q hQ)
    (s5_vFam_sublinear hR3 hS1 hS2 Q hQ)

noncomputable def s5_foldEnv (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) : ℕ → ℝ :=
  if heps : 0 < eps then
    Classical.choose (s5_foldEnvWitness hR3 hS1 hS2 hS4 Q hQ eps heps)
  else
    fun _ => 0

lemma s5_foldEnv_sublinear (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps) := by
  unfold s5_foldEnv
  rw [dif_pos heps]
  exact (Classical.choose_spec
    (s5_foldEnvWitness hR3 hS1 hS2 hS4 Q hQ eps heps)).1

lemma s5_foldEnv_spec (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty →
      blockRegularFamily m A q (s5_sFam hR3 Q hQ) →
      (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
        varianceBudgetLE A pLow (s5_vFam hR3 hS1 hS2 Q hQ pLow m)) →
      ∃ o : ℝ, 0 ≤ o ∧ o < eps / 4 ∧
        uH A (binnedFoldField A (eps / 4) o) ≤
          s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m := by
  unfold s5_foldEnv
  rw [dif_pos heps]
  exact (Classical.choose_spec
    (s5_foldEnvWitness hR3 hS1 hS2 hS4 Q hQ eps heps)).2

noncomputable def s5_baseSlack (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) : ℝ :=
  Q.sigma m + s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m

lemma s5_baseSlack_sublinear (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps) := by
  have hSigma : Sublinear Q.sigma := by
    rcases hQ with ⟨_, _, _, _, _, _, hSigma, _⟩
    exact hSigma
  unfold s5_baseSlack
  exact core_Sublinear_add hSigma
    (s5_foldEnv_sublinear hR3 hS1 hS2 hS4 Q hQ eps heps)

lemma s5_foldEnv_nonneg (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) :
    ∀ m, 0 ≤ s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m := by
  intro m
  unfold s5_foldEnv
  split_ifs with heps
  · exact (Classical.choose_spec
      (s5_foldEnvWitness hR3 hS1 hS2 hS4 Q hQ eps heps)).1.1 m
  · exact le_refl 0

lemma s5_baseSlack_nonneg (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) :
    ∀ m, 0 ≤ s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
  intro m
  unfold s5_baseSlack
  have hSigma : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
  have hEnv := s5_foldEnv_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
  linarith

/-- Q-data for the *heavy-atom class*: the same compact
`(qMin, qMax, s0, mu0)`, with the slack enlarged by the heavy-atom mass
threshold `G1(m) = sqrt((base(m)+1)*(m+1))`.  A heavy atom `Af` of a
fat+pinned `A` (mass ≥ `|A| * exp(-T)` with
`T = sqrt((env+1)*(m+1)) ≤ G1`) is fat+pinned for THIS data:
fat because the mass loss costs at most `T ≤ G1` on the lower side, and
pinned because `neighborhood r Af ⊆ neighborhood r A`.  Hence R3
applies to every heavy atom with the single class-uniform slack
`s5_atomSigmaStar` below (paper: Remark "uniformity; subsets"). -/
noncomputable def s5_atomQ (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) : QData :=
  { qMin := Q.qMin, qMax := Q.qMax, s0 := Q.s0, mu0 := Q.mu0,
    sigma := fun m =>
      Q.sigma m +
        Real.sqrt
          ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) }

lemma s5_atomQ_valid (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    validQData (s5_atomQ hR3 hS1 hS2 hS4 Q hQ eps) := by
  refine ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1, hQ.2.2.2.2.1, hQ.2.2.2.2.2.1,
    ?_, ?_⟩
  · dsimp only [s5_atomQ]
    exact core_Sublinear_add hQ.2.2.2.2.2.2.1
      (core_Sublinear_geomMean
        (s5_baseSlack_sublinear hR3 hS1 hS2 hS4 Q hQ eps heps))
  · intro m hm
    dsimp only [s5_atomQ]
    have hlog := hQ.2.2.2.2.2.2.2 m hm
    have hsqrt : 0 ≤ Real.sqrt
        ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    linarith

/-- The R3 (block-regularity) slack for the heavy-atom class
`s5_atomQ`, extracted once for the whole class at window density
`pLow = 1/6` (the band `m/5 ≤ |I| ≤ m - m/5` of S1 lies inside the
`1/6`-range for `m ≥ 30`). -/
noncomputable def s5_atomSigmaStar (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) : ℕ → ℝ :=
  if heps : 0 < eps then
    s5_sFam hR3 (s5_atomQ hR3 hS1 hS2 hS4 Q hQ eps)
      (s5_atomQ_valid hR3 hS1 hS2 hS4 Q hQ eps heps) (1 / 6)
  else fun _ => 0

lemma s5_atomSigmaStar_sublinear (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps) := by
  unfold s5_atomSigmaStar
  rw [dif_pos heps]
  exact s5_sFam_sublinear hR3 (s5_atomQ hR3 hS1 hS2 hS4 Q hQ eps)
    (s5_atomQ_valid hR3 hS1 hS2 hS4 Q hQ eps heps) (1 / 6)
    (by norm_num) (by norm_num)

lemma s5_atomSigmaStar_nonneg (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) :
    ∀ m, 0 ≤ s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m := by
  intro m
  unfold s5_atomSigmaStar
  split_ifs with heps
  · exact (s5_sFam_sublinear hR3 (s5_atomQ hR3 hS1 hS2 hS4 Q hQ eps)
      (s5_atomQ_valid hR3 hS1 hS2 hS4 Q hQ eps heps) (1 / 6)
      (by norm_num) (by norm_num)).1 m
  · exact le_refl 0

/-- The separation coefficient `64/(eps*mu0)^2 + 48/(eps*mu0)`: the
Markov constant of the tilt count (`16/Δ²` with `Δ = eps*mu0/2`)
plus the S1 count constant (`24/Δ`). -/
noncomputable def s5_sepCoeff (eps mu : ℝ) : ℝ :=
  if _h : 0 < eps * mu then 64 / (eps * mu) ^ 2 + 48 / (eps * mu) else 0

lemma s5_sepCoeff_nonneg (eps mu : ℝ) : 0 ≤ s5_sepCoeff eps mu := by
  unfold s5_sepCoeff
  split_ifs with h
  · positivity
  · exact le_refl 0

noncomputable def s5_epsCoeff (eps : ℝ) : ℝ :=
  if _heps : 0 < eps then 100 + 1 / eps else 0

lemma s5_epsCoeff_nonneg (eps : ℝ) : 0 ≤ s5_epsCoeff eps := by
  unfold s5_epsCoeff
  split_ifs <;> positivity

/-- Per-heavy-atom deviant-bin budget (paper §S5, assembled): the
tilt/Markov count `sepCoeff * G2`, the S1-on-the-atom count
`sepCoeff * (atomSigmaStar + base + G1)`, the S1 additive constant, and
a `+ 40` absorbing every dimension `m < 30`. -/
noncomputable def s5_atomSlack (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) : ℝ :=
  s5_sepCoeff eps Q.mu0 *
      (Real.sqrt
          ((Real.sqrt
              ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
            1) * ((m : ℝ) + 1)) +
        s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m +
        s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m +
        Real.sqrt
          ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
        1) +
    40

lemma s5_atomSlack_nonneg (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) :
    0 ≤ s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
  unfold s5_atomSlack
  have hInner :
      0 ≤ Real.sqrt
          ((Real.sqrt
              ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
            1) * ((m : ℝ) + 1)) +
        s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m +
        s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m +
        Real.sqrt
          ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
        1 := by
    have h1 := Real.sqrt_nonneg
      ((Real.sqrt
          ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
        1) * ((m : ℝ) + 1))
    have h2 := s5_atomSigmaStar_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
    have h3 := s5_baseSlack_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
    have h4 := Real.sqrt_nonneg
      ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))
    linarith
  have hCoeff := s5_sepCoeff_nonneg eps Q.mu0
  nlinarith [mul_nonneg hCoeff hInner]

lemma s5_atomSlack_ge_40 (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) :
    (40 : ℝ) ≤ s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
  unfold s5_atomSlack
  have hInner :
      0 ≤ Real.sqrt
          ((Real.sqrt
              ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
            1) * ((m : ℝ) + 1)) +
        s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m +
        s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m +
        Real.sqrt
          ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
        1 := by
    have h1 := Real.sqrt_nonneg
      ((Real.sqrt
          ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
        1) * ((m : ℝ) + 1))
    have h2 := s5_atomSigmaStar_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
    have h3 := s5_baseSlack_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
    have h4 := Real.sqrt_nonneg
      ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))
    linarith
  have hCoeff := s5_sepCoeff_nonneg eps Q.mu0
  nlinarith [mul_nonneg hCoeff hInner]

theorem s5_atomSlack_sublinear (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps) := by
  have hBase : Sublinear (s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps) :=
    s5_baseSlack_sublinear hR3 hS1 hS2 hS4 Q hQ eps heps
  have hG1 : Sublinear (fun m => Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))) :=
    core_Sublinear_geomMean hBase
  have hG2 : Sublinear (fun m => Real.sqrt ((Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1))) :=
    core_Sublinear_geomMean hG1
  have hStar : Sublinear (s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps) :=
    s5_atomSigmaStar_sublinear hR3 hS1 hS2 hS4 Q hQ eps heps
  have hInner : Sublinear (fun m =>
      Real.sqrt ((Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) +
        s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m +
        s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m +
        Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
        1) :=
    core_Sublinear_add
      (core_Sublinear_add
        (core_Sublinear_add
          (core_Sublinear_add hG2 hStar)
          hBase)
        hG1)
      (core_Sublinear_const (show 0 ≤ (1 : ℝ) by norm_num))
  have hSmul : Sublinear (fun m =>
      s5_sepCoeff eps Q.mu0 *
        (Real.sqrt ((Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) +
          s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m +
          s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m +
          Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
          1)) :=
    core_Sublinear_smul (s5_sepCoeff_nonneg eps Q.mu0) hInner
  simpa [s5_atomSlack] using
    core_Sublinear_add hSmul
      (core_Sublinear_const (show 0 ≤ (40 : ℝ) by norm_num))

noncomputable def s5_massSlack (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q) (eps : ℝ) (m : ℕ) : ℝ :=
  s5_epsCoeff eps *
    (s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m +
      Real.sqrt
        ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
      s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m +
      1)

theorem s5_massSlack_sublinear (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (eps : ℝ) (heps : 0 < eps) :
    Sublinear (s5_massSlack hR3 hS1 hS2 hS4 Q hQ eps) := by
  have hBase :
      Sublinear (s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps) :=
    s5_baseSlack_sublinear hR3 hS1 hS2 hS4 Q hQ eps heps
  have hGeom :
      Sublinear (fun m =>
        Real.sqrt
          ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))) :=
    core_Sublinear_geomMean hBase
  have hInner :
      Sublinear (fun m =>
        s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m +
          Real.sqrt
            ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
          s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m +
          1) := by
    have hAtom := s5_atomSlack_sublinear hR3 hS1 hS2 hS4 Q hQ eps heps
    exact core_Sublinear_add
      (core_Sublinear_add
        (core_Sublinear_add hBase hGeom)
        hAtom)
      (core_Sublinear_const (show 0 ≤ (1 : ℝ) by norm_num))
  have hCoeff_nonneg : 0 ≤ s5_epsCoeff eps := s5_epsCoeff_nonneg eps
  simpa [s5_massSlack] using core_Sublinear_smul hCoeff_nonneg hInner

noncomputable def s5_classicalImage {m : ℕ} {β : Type*}
    (A : Finset (Cube m)) (F : Cube m → β) : Finset β :=
  @Finset.image (Cube m) β (fun a b => Classical.propDecidable (a = b)) F A

noncomputable def s5_classicalFiber {m : ℕ} {β : Type*}
    (A : Finset (Cube m)) (F : Cube m → β) (f : β) : Finset (Cube m) :=
  @Finset.filter (Cube m) (fun x => F x = f)
    (fun x => Classical.propDecidable (F x = f)) A

lemma s5_sum_fiberwise_classical {m : ℕ} {β : Type*}
    (A : Finset (Cube m)) (F : Cube m → β) (g : Cube m → ℝ) :
    (∑ f ∈ s5_classicalImage A F, ∑ x ∈ s5_classicalFiber A F f, g x) =
      ∑ x ∈ A, g x := by
  classical
  have hmap : ∀ x ∈ A, F x ∈ s5_classicalImage A F := by
    intro x hx
    change F x ∈
      @Finset.image (Cube m) β (fun a b => Classical.propDecidable (a = b)) F A
    exact Finset.mem_image_of_mem F hx
  simpa [s5_classicalImage, s5_classicalFiber] using
    (Finset.sum_fiberwise_of_maps_to (s := A) (t := s5_classicalImage A F)
      (g := F) (f := g) hmap)

lemma s5_negMulLog_ge_mul_of_le_exp_neg {p T : ℝ} (hp_pos : 0 < p)
    (hp_le : p ≤ Real.exp (-T)) :
    p * T ≤ Real.negMulLog p := by
  have hlog_le : Real.log p ≤ -T := by
    have := Real.log_le_log hp_pos hp_le
    simpa [Real.log_exp] using this
  have hT_le : T ≤ - Real.log p := by linarith
  unfold Real.negMulLog
  nlinarith [mul_le_mul_of_nonneg_left hT_le (le_of_lt hp_pos)]

lemma s5_light_atom_card_sum_le_entropy {m : ℕ} {β : Type*}
    (A : Finset (Cube m)) (F : Cube m → β) (env T : ℝ)
    (hA : A.Nonempty) (hTpos : 0 < T) (henv : uH A F ≤ env) :
    (∑ f ∈ (s5_classicalImage A F).filter (fun f =>
        ((s5_classicalFiber A F f).card : ℝ) < (A.card : ℝ) * Real.exp (-T)),
      ((s5_classicalFiber A F f).card : ℝ)) ≤
        (A.card : ℝ) * env / T := by
  classical
  let light := (s5_classicalImage A F).filter (fun f =>
    ((s5_classicalFiber A F f).card : ℝ) < (A.card : ℝ) * Real.exp (-T))
  have hApos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hcoef_nonneg : 0 ≤ (A.card : ℝ) / T := by positivity
  have hpoint : ∀ f ∈ light,
      ((s5_classicalFiber A F f).card : ℝ) ≤
        ((A.card : ℝ) / T) * Real.negMulLog (pOn A F f) := by
    intro f hf
    have hf_img : f ∈ s5_classicalImage A F := (Finset.mem_filter.mp hf).1
    have hf_light : ((s5_classicalFiber A F f).card : ℝ) <
        (A.card : ℝ) * Real.exp (-T) := (Finset.mem_filter.mp hf).2
    have hfiber_nonempty : (s5_classicalFiber A F f).Nonempty := by
      rcases Finset.mem_image.mp (by simpa [s5_classicalImage] using hf_img) with
        ⟨x, hxA, rfl⟩
      exact ⟨x, by simp [s5_classicalFiber, hxA]⟩
    have hfiber_card_pos_nat : 0 < (s5_classicalFiber A F f).card :=
      Finset.card_pos.mpr hfiber_nonempty
    have hfiber_card_pos : 0 < ((s5_classicalFiber A F f).card : ℝ) := by
      exact_mod_cast hfiber_card_pos_nat
    have hp_pos : 0 < pOn A F f := by
      rw [show pOn A F f =
        ((s5_classicalFiber A F f).card : ℝ) / (A.card : ℝ) by rfl]
      exact div_pos hfiber_card_pos hApos
    have hp_le : pOn A F f ≤ Real.exp (-T) := by
      rw [show pOn A F f =
        ((s5_classicalFiber A F f).card : ℝ) / (A.card : ℝ) by rfl]
      rw [div_le_iff₀ hApos]
      rw [mul_comm]
      exact le_of_lt hf_light
    have hneg := s5_negMulLog_ge_mul_of_le_exp_neg hp_pos hp_le
    have hmul : (A.card : ℝ) * (pOn A F f * T) ≤
        (A.card : ℝ) * Real.negMulLog (pOn A F f) := by
      exact mul_le_mul_of_nonneg_left hneg (Nat.cast_nonneg _)
    have hcard_eq : ((s5_classicalFiber A F f).card : ℝ) =
        (A.card : ℝ) * pOn A F f := by
      rw [show pOn A F f =
        ((s5_classicalFiber A F f).card : ℝ) / (A.card : ℝ) by rfl]
      field_simp [ne_of_gt hApos]
    calc
      ((s5_classicalFiber A F f).card : ℝ)
          = (A.card : ℝ) * pOn A F f := hcard_eq
      _ = ((A.card : ℝ) * (pOn A F f * T)) / T := by
            rw [eq_div_iff (ne_of_gt hTpos)]
            ring
      _ ≤ ((A.card : ℝ) * Real.negMulLog (pOn A F f)) / T :=
            div_le_div_of_nonneg_right hmul (le_of_lt hTpos)
      _ = ((A.card : ℝ) / T) * Real.negMulLog (pOn A F f) := by ring
  calc
    (∑ f ∈ light, ((s5_classicalFiber A F f).card : ℝ))
        ≤ ∑ f ∈ light,
            ((A.card : ℝ) / T) * Real.negMulLog (pOn A F f) := by
          exact Finset.sum_le_sum hpoint
    _ = ((A.card : ℝ) / T) *
          (∑ f ∈ light, Real.negMulLog (pOn A F f)) := by
          rw [Finset.mul_sum]
    _ ≤ ((A.card : ℝ) / T) *
          (∑ f ∈ s5_classicalImage A F, Real.negMulLog (pOn A F f)) := by
          have hsub : light ⊆ s5_classicalImage A F := Finset.filter_subset _ _
          have hsum_le : (∑ f ∈ light, Real.negMulLog (pOn A F f)) ≤
              ∑ f ∈ s5_classicalImage A F, Real.negMulLog (pOn A F f) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
              intro f _ _
              exact Real.negMulLog_nonneg (pOn_nonneg A F f) (pOn_le_one A F f))
          exact mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
    _ ≤ ((A.card : ℝ) / T) * env := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [uH, s5_classicalImage] using henv) hcoef_nonneg
    _ = (A.card : ℝ) * env / T := by ring

/-- For an atom pinned to bin field `f`, every coordinate that is `eps`-bad for
some `x` in the atom lies in the `x`-independent set of coordinates whose pinned
bin lower endpoint is more than `3*eps/4` away from `q`. -/
lemma s5_badStep_subset_badBins {m : ℕ} (A : Finset (Cube m)) (q eps o : ℝ)
    (heps : 0 < eps) (f : Fin m → ℤ) (x : Cube m)
    (hx : binnedFoldField A (eps / 4) o x = f) :
    badStepSet A q eps x ⊆
      (Finset.univ : Finset (Fin m)).filter
        (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|) := by
  intro t ht
  simp only [badStepSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  obtain ⟨hlo, hhi⟩ := s5_fold_pinned_in_bin A eps o heps f x hx t
  set y := fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) with hy
  have hband : |y - (o + (f t : ℝ) * (eps / 4))| < eps / 4 := by
    rw [abs_lt]; constructor <;> nlinarith
  have htri : |y - q| ≤
      |y - (o + (f t : ℝ) * (eps / 4))| + |(o + (f t : ℝ) * (eps / 4)) - q| := by
    calc |y - q|
        = |(y - (o + (f t : ℝ) * (eps / 4))) + ((o + (f t : ℝ) * (eps / 4)) - q)| := by
          ring_nf
      _ ≤ _ := abs_add_le _ _
  nlinarith [hband, htri, ht]

lemma s5_neighborhood_mono_set {m r : ℕ} {A B : Finset (Cube m)}
    (hsub : A ⊆ B) : neighborhood r A ⊆ neighborhood r B := by
  intro x hx
  rw [mem_neighborhood_iff] at hx ⊢
  rcases hx with ⟨u, hu, hdist⟩
  exact ⟨u, hsub hu, hdist⟩

/-- **Heavy atoms have few deviant bins** (paper §S5, assembly of the
three proved/sorried leaves; this lemma is pure glue — every analytic
ingredient lives elsewhere).

`B_f := {t | 3*eps/4 < |o + f t * (eps/4) - q|}` is the deviant-bin
coordinate set of the atom
`Af = A.filter (binnedFoldField A (eps/4) o · = f)`.

Proof recipe:

0. *Degenerate cases.*  If `m < 30` then `|B_f| ≤ m ≤ 29 < 40`, and
   `40 ≤ s5_atomSlack ...` (its `+ 40` term; everything else is
   nonnegative by `s5_atomSlack_nonneg`'s sub-lemmas): done.  So assume
   `30 ≤ m`.  `Af` is nonempty (`hHeavy` with `A.Nonempty` gives
   `0 < |A| * exp(-T) ≤ |Af|`), and `Af ⊆ A` by `hAf ▸ filter_subset`.
1. *The atom is fat+pinned for the atom class `s5_atomQ`.*  Set
   `base := s5_baseSlack ... m`,
   `G1 := sqrt((base+1)*(m+1))`, `T := sqrt((env+1)*(m+1))`.
   `T ≤ G1` from `henv_le : env ≤ s5_foldEnv ... m` and
   `s5_foldEnv ... m ≤ base` (definition of `s5_baseSlack`, and
   `0 ≤ Q.sigma m`).
   * fat: `hHeavy` gives `Real.log |Af| ≥ Real.log |A| - T`
     (`Real.log_le_log`, `Real.log_mul`, `Real.log_exp`), so with
     `hFat : |log |A| - H q * m| ≤ Q.sigma m`:
     `|log |Af| - H q * m| ≤ Q.sigma m + G1 = (s5_atomQ ...).sigma m`
     (upper side from `Af ⊆ A` and monotonicity of `log`/`card`).
   * pinned: `neighborhood r Af ⊆ neighborhood r A` (monotonicity of
     the imported `neighborhood` in the set argument), then `hPinned`
     and `Q.sigma m ≤ (s5_atomQ ...).sigma m` (add the nonneg `G1`).
   * `(s5_atomQ ...).s0 = Q.s0`, `.qMin/.qMax` unchanged, so `q`-range
     and the radius cap `Nat.ceil (Q.s0 * m)` carry over verbatim.
2. *Block regularity of the atom.*
   `s5_sFam_blockRegular hR3 (s5_atomQ ...) (s5_atomQ_valid ... heps)
    m Af q hAfNonempty hAtomFat hAtomPinned` gives
   `blockRegularFamily m Af q (s5_sFam hR3 (s5_atomQ ...) ...)`;
   instantiate at `pLow := 1/6` (i.e. `(by norm_num : (0:ℝ) < 1/6)` and
   `1/6 ≤ 1/2`) and rewrite `s5_atomSigmaStar` by `dif_pos heps` to get
   `blockRegular m Af q (1/6) (s5_atomSigmaStar ... m)`.
3. *S1 on the atom* (this is what `hS1` is for).  Apply `hS1` to `Af`
   with `kappa := H q`, `eps' := Δ/2` where `Δ := eps * Q.mu0 / 2`, and
   `s := s5_atomSigmaStar ... m + Q.sigma m + G1`:
   * window caps: for `(↑(m/5 : ℕ) ≤ |I|` and `|I| ≤ m - ↑(m/5 : ℕ))`
     with `m ≥ 30`, floor arithmetic gives
     `(1/6)*m ≤ |I| ≤ (1 - 1/6)*m` (`m/5 - 1 ≥ m/6` for `m ≥ 30`), so
     step 2 gives `uH Af (proj I) ≤ H q * |I| + s5_atomSigmaStar ... m
     ≤ H q * |I| + s`  (`abs_le.mp`, left component);
   * total entropy: `uH Af (proj univ) = Real.log |Af|`
     (`uH_proj_univ Af hAfNonempty`), and by step 1
     `Real.log |Af| ≥ H q * m - (Q.sigma m + G1) ≥ H q * m - s`.
   Conclusion: the S1-exceptional set
   `E₁ := {t | Δ/2 ≤ |hstep Af t - H q|}` has
   `|E₁| ≤ 12*s/(Δ/2) + 4 = 24*s/Δ + 4`.
4. *Tilt+transfer control off `E₁`.*  Let
   `e t := uE Af (fun x => |rho Af t (proj (below univ t) x) -
                            rho A t (proj (below univ t) x)|)`.
   Fix `t ∈ B_f \ E₁`.  Then:
   * `s5_same_bin_separation A Af Q hQ q eps o heps hq1 hq2 ho1 ho2 f t
      hAfSub hAfNonempty hbinned hbad` (with `hq1/hq2` from `hFat`,
     `hbinned` from `hAf`-membership, `hbad` from `t ∈ B_f`):
     `Δ ≤ |uE Af (fun x => H (rho A t ...)) - H q|`;
   * `hstep_eq_uE_binEntropy_rho Af hAfNonempty t` rewrites
     `hstep Af t = uE Af (fun x => H (rho Af t ...))`, and
     `t ∉ E₁` gives `|uE Af (fun x => H (rho Af t ...)) - H q| < Δ/2`;
   * `s5_step_entropy_transfer A Af hAfSub hAfNonempty t` plus the
     triangle inequality force `Δ/2 < 2 * sqrt (e t)`, i.e.
     `Δ^2/16 < e t` (`Real.lt_sqrt`, squares).
   * `s5_kl_tilt A Af hAfSub hAfNonempty` plus `hHeavy` give
     `∑ t, e t ≤ sqrt (m * log(|A|/|Af|) / 2) ≤ sqrt (m * T / 2) ≤ G2`
     where `G2 := sqrt((G1+1)*(m+1))`
     (`log(|A|/|Af|) ≤ T` from `hHeavy`; `m * G1 / 2 ≤ (G1+1)*(m+1)`).
   * Markov over `t` (all `e t ≥ 0`):
     `|B_f \ E₁| ≤ (16/Δ^2) * G2`.
5. *Total.*  `|B_f| ≤ |B_f \ E₁| + |E₁|
     ≤ (16/Δ^2)*G2 + 24*s/Δ + 4`.
   With `Δ = eps*Q.mu0/2` (note `0 < eps * Q.mu0` from `heps` and
   `hQ`): `16/Δ^2 = 64/(eps*Q.mu0)^2 ≤ s5_sepCoeff eps Q.mu0` and
   `24/Δ = 48/(eps*Q.mu0) ≤ s5_sepCoeff eps Q.mu0` (`dif_pos`), and
   `s = atomSigmaStar + Q.sigma m + G1 ≤ atomSigmaStar + base + G1`
   (`Q.sigma m ≤ base`), so
   `|B_f| ≤ sepCoeff * (G2 + atomSigmaStar + base + G1 + 1) + 4
    ≤ s5_atomSlack ... m`  (`4 ≤ 40`; all summands nonneg).  ∎
-/
lemma s5_heavy_atom_fat (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (_hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (_hPinned : pinned Q m A q)
    (o : ℝ) (_ho1 : 0 ≤ o) (_ho2 : o < eps / 4)
    (env : ℝ) (_henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ)) :
    fat (s5_atomQ hR3 hS1 hS2 hS4 Q hQ eps) m Af q := by
  rcases hFat with ⟨_, _, hqMin, hqMax, hAbsA⟩
  set T : ℝ := Real.sqrt ((env + 1) * ((m : ℝ) + 1))
  set G1 : ℝ :=
    Real.sqrt
      ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))
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
      env ≤ s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
    unfold s5_baseSlack
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
  refine ⟨hAfNonempty, s5_atomQ_valid hR3 hS1 hS2 hS4 Q hQ eps heps, ?_, ?_, ?_⟩
  · simpa [s5_atomQ] using hqMin
  · simpa [s5_atomQ] using hqMax
  · rw [abs_le]
    constructor
    · simpa [s5_atomQ, G1, add_comm, add_left_comm, add_assoc] using hLower
    · simpa [s5_atomQ, G1, add_comm, add_left_comm, add_assoc] using hUpper

lemma s5_heavy_atom_pinned (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (_hA : A.Nonempty) (_heps : 0 < eps) (_hepsQ : eps < Q.qMin)
    (_hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (_ho1 : 0 ≤ o) (_ho2 : o < eps / 4)
    (env : ℝ) (_henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (_henv_le : env ≤ s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (_hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ)) :
    pinned (s5_atomQ hR3 hS1 hS2 hS4 Q hQ eps) m Af q := by
  intro r hr
  have hAfSub : Af ⊆ A := by
    rw [hAf]
    exact Finset.filter_subset _ _
  have hcard :
      ((neighborhood r Af).card : ℝ) ≤ ((neighborhood r A).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (s5_neighborhood_mono_set hAfSub)
  have hrQ : r ≤ Nat.ceil (Q.s0 * (m : ℝ)) := by
    simpa [s5_atomQ] using hr
  have hPinnedA := hPinned r hrQ
  have hExp :
      Real.exp (H (q + (r : ℝ) / (m : ℝ)) * (m : ℝ) + Q.sigma m) ≤
        Real.exp
          (H (q + (r : ℝ) / (m : ℝ)) * (m : ℝ) +
            (s5_atomQ hR3 hS1 hS2 hS4 Q hQ eps).sigma m) := by
    apply Real.exp_le_exp.mpr
    dsimp [s5_atomQ]
    have hsqrt : 0 ≤ Real.sqrt
        ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    linarith
  exact hcard.trans (hPinnedA.trans hExp)

lemma s5_heavy_atom_blockRegular (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ))
    (_hm : 30 ≤ m) :
    blockRegular m Af q (1 / 6) (s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m) := by
  have hAtomFat :=
    s5_heavy_atom_fat hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  have hAtomPinned :=
    s5_heavy_atom_pinned hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  have hFam :=
    s5_sFam_blockRegular hR3 (s5_atomQ hR3 hS1 hS2 hS4 Q hQ eps)
      (s5_atomQ_valid hR3 hS1 hS2 hS4 Q hQ eps heps)
      m Af q hAtomFat.1 hAtomFat hAtomPinned
  unfold s5_atomSigmaStar
  rw [dif_pos heps]
  exact hFam (1 / 6) (by norm_num) (by norm_num)

lemma s5_heavy_atom_E1_bound (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ))
    (hm : 30 ≤ m) :
    (((Finset.univ : Finset (Fin m)).filter
        (fun t => eps * Q.mu0 / 4 ≤ |hstep Af t - H q|)).card : ℝ) ≤
      24 * (s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m + Q.sigma m + Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))) / (eps * Q.mu0 / 2) + 4 := by
  set star : ℝ := s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m
  set G1 : ℝ :=
    Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))
  set s : ℝ := star + Q.sigma m + G1
  have hAtomFat :=
    s5_heavy_atom_fat hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  have hAfNonempty : Af.Nonempty := hAtomFat.1
  have hBR :=
    s5_heavy_atom_blockRegular hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy hm
  have hstar_nonneg : 0 ≤ star := by
    dsimp [star]
    exact s5_atomSigmaStar_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
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
    simpa [s5_atomQ, G1] using hAtomFat.2.2.2.2
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

lemma s5_heavy_atom_Markov_bound (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ))
    (hm : 30 ≤ m) :
    (((Finset.univ : Finset (Fin m)).filter
        (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q| ∧ |hstep Af t - H q| < eps * Q.mu0 / 4)).card : ℝ) ≤
      (64 / (eps * Q.mu0) ^ 2) * Real.sqrt ((Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) + 1) * ((m : ℝ) + 1)) := by
  set x : ℝ := eps * Q.mu0
  set c : ℝ := x ^ 2 / 64
  set G1 : ℝ :=
    Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))
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
    s5_heavy_atom_fat hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ
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
      env ≤ s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
    unfold s5_baseSlack
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

lemma s5_heavy_atom_bad_bins_bound (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ)) :
    (((Finset.univ : Finset (Fin m)).filter
        (fun t => 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|)).card : ℝ) ≤
      s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
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
      s5_heavy_atom_E1_bound hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ
        hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy hm
    have hM :=
      s5_heavy_atom_Markov_bound hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ
        hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy hm
    set G1 : ℝ :=
      Real.sqrt ((s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1))
    set G2 : ℝ := Real.sqrt ((G1 + 1) * ((m : ℝ) + 1))
    set star : ℝ := s5_atomSigmaStar hR3 hS1 hS2 hS4 Q hQ eps m
    set base : ℝ := s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m
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
      exact s5_atomSigmaStar_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
    have hbase_nonneg : 0 ≤ base := by
      dsimp [base]
      exact s5_baseSlack_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
    have hsigma_nonneg : 0 ≤ Q.sigma m := hQ.2.2.2.2.2.2.1.1 m
    have hbase_eq : base = Q.sigma m + s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m := by
      simp [base, s5_baseSlack]
    have hs_le_inner : s ≤ G2 + star + base + G1 + 1 := by
      have henv_nonneg := s5_foldEnv_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
      have hsigma_le_base : Q.sigma m ≤ base := by
        rw [hbase_eq]
        linarith
      dsimp [s]
      linarith
    have hG2_le_inner : G2 ≤ G2 + star + base + G1 + 1 := by
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
          (a + b) * (G2 + star + base + G1 + 1) + 40 := by
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
      _ ≤ (a + b) * (G2 + star + base + G1 + 1) + 40 := hmain
      _ = s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
        rw [← hcoeff]
        simp [s5_atomSlack, G1, G2, star, base, add_left_comm, add_comm]
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
      (s5_atomSlack_ge_40 hR3 hS1 hS2 hS4 Q hQ eps m))

lemma s5_heavy_atoms_bad_steps (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q)
    (o : ℝ) (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (henv_le : env ≤ s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m)
    (f : Fin m → ℤ)
    (Af : Finset (Cube m)) (hAf : Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f))
    (hHeavy :
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ)) :
    (∑ x ∈ Af, ((badStepSet A q eps x).card : ℝ)) ≤ s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m * (Af.card : ℝ) := by
  have hBinsBound := s5_heavy_atom_bad_bins_bound hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ hFat hPinned o ho1 ho2 env henv henv_le f Af hAf hHeavy
  have hSum : (∑ x ∈ Af, ((badStepSet A q eps x).card : ℝ)) ≤
      ∑ x ∈ Af, s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
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
  have hSum_eq : ∑ x ∈ Af, s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m =
      s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m * (Af.card : ℝ) := by
    simp [mul_comm]
  linarith

lemma s5_average_bad_steps_from_heavy_atoms (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (o : ℝ) (env : ℝ) (henv : uH A (binnedFoldField A (eps / 4) o) ≤ env)
    (hHeavyBad : ∀ f Af, Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f) →
      (A.card : ℝ) * Real.exp (- Real.sqrt ((env + 1) * ((m : ℝ) + 1))) ≤
        (Af.card : ℝ) →
      (∑ x ∈ Af, ((badStepSet A q eps x).card : ℝ)) ≤ s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m * (Af.card : ℝ)) :
    averageBadStepsLE A q eps
      (Real.sqrt ((env + 1) * ((m : ℝ) + 1)) +
        s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1) := by
  unfold averageBadStepsLE
  let F : Cube m → Fin m → ℤ := binnedFoldField A (eps / 4) o
  set T : ℝ := Real.sqrt ((env + 1) * ((m : ℝ) + 1)) with hTdef
  set S : ℝ := s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m with hSdef
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
      exact s5_atomSlack_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
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

lemma s5_atom_average_slack_le_massSlack (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (eps : ℝ) (heps : 0 < eps) (m : ℕ) :
    Real.sqrt ((s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m + 1) * ((m : ℝ) + 1)) +
        s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m + 1
      ≤ s5_massSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
  set env := s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m with henv_def
  set base := s5_baseSlack hR3 hS1 hS2 hS4 Q hQ eps m with hbase_def
  set geomEnv := Real.sqrt ((env + 1) * ((m : ℝ) + 1)) with hgeomEnv_def
  set smallEnv := s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m with hsmallEnv_def
  set geomBase := Real.sqrt ((base + 1) * ((m : ℝ) + 1)) with hgeomBase_def
  have hEnv_nonneg : 0 ≤ env := by
    simpa [henv_def] using
      (s5_foldEnv_sublinear hR3 hS1 hS2 hS4 Q hQ eps heps).1 m
  have hSigma_nonneg : 0 ≤ Q.sigma m := by
    exact hQ.2.2.2.2.2.2.1.1 m
  have hBase_eq : base = Q.sigma m + env := by
    simp [hbase_def, s5_baseSlack, henv_def]
  have hBase_nonneg : 0 ≤ base := by
    rw [hBase_eq]; positivity
  have hEnv_le_base : env ≤ base := by
    rw [hBase_eq]; linarith
  have hGeomEnv_le_base : geomEnv ≤ geomBase := by
    dsimp [geomEnv, geomBase]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hCoeff_ge_two : 1 ≤ s5_epsCoeff eps := by
    dsimp [s5_epsCoeff]; rw [if_pos heps]
    have : 0 ≤ 1 / eps := by positivity
    linarith
  have hSmallEnv_nonneg : 0 ≤ smallEnv := by
    rw [hsmallEnv_def]
    exact s5_atomSlack_nonneg hR3 hS1 hS2 hS4 Q hQ eps m
  have hInner_nonneg : 0 ≤ base + geomBase + smallEnv + 1 := by
    nlinarith [hBase_nonneg, hSmallEnv_nonneg, Real.sqrt_nonneg ((base + 1) * ((m : ℝ) + 1))]
  have hSlackCore : geomEnv + smallEnv + 1 ≤ base + geomBase + smallEnv + 1 := by
    nlinarith [hGeomEnv_le_base, hBase_nonneg, Real.sqrt_nonneg ((base + 1) * ((m : ℝ) + 1))]
  calc
    geomEnv + smallEnv + 1 ≤ base + geomBase + smallEnv + 1 := hSlackCore
    _ ≤ s5_epsCoeff eps * (base + geomBase + smallEnv + 1) := by
      exact le_mul_of_one_le_left hInner_nonneg hCoeff_ge_two
    _ = s5_massSlack hR3 hS1 hS2 hS4 Q hQ eps m := by
      simp [s5_massSlack, hgeomBase_def, base, geomBase, smallEnv]

theorem s5_average_bad_steps_bound (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement)
    (Q : QData) (hQ : validQData Q)
    (m : ℕ) (A : Finset (Cube m)) (q eps : ℝ)
    (hA : A.Nonempty) (heps : 0 < eps) (hepsQ : eps < Q.qMin)
    (hFat : fat Q m A q) (hPinned : pinned Q m A q) :
    averageBadStepsLE A q eps (s5_massSlack hR3 hS1 hS2 hS4 Q hQ eps m) := by
  obtain ⟨o, ho1, ho2, henv⟩ :=
    s5_foldEnv_spec hR3 hS1 hS2 hS4 Q hQ eps heps m A q hA
      (s5_sFam_blockRegular hR3 Q hQ m A q hA hFat hPinned)
      (s5_vFam_variance hR3 hS1 hS2 Q hQ m A q hA hFat hPinned)
  have hHeavyBad :
      ∀ f Af, Af = A.filter (fun x => binnedFoldField A (eps / 4) o x = f) →
        (A.card : ℝ) *
            Real.exp (-
              Real.sqrt
                ((s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m + 1) *
                  ((m : ℝ) + 1))) ≤
          (Af.card : ℝ) →
        (∑ x ∈ Af, ((badStepSet A q eps x).card : ℝ)) ≤
          s5_atomSlack hR3 hS1 hS2 hS4 Q hQ eps m * (Af.card : ℝ) := by
    intro f Af hAf hHeavy
    exact s5_heavy_atoms_bad_steps hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ
      hFat hPinned o ho1 ho2 (s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m) henv
      (le_refl _)
      f Af hAf hHeavy
  have hAtoms :=
    s5_average_bad_steps_from_heavy_atoms hR3 hS1 hS2 hS4 Q hQ m A q eps o
      (s5_foldEnv hR3 hS1 hS2 hS4 Q hQ eps m) henv hHeavyBad
  exact averageBadStepsLE_mono_slack A
    (s5_atom_average_slack_le_massSlack hR3 hS1 hS2 hS4 Q hQ eps heps m) hAtoms

theorem S5_skeleton (hR3 : R3Statement) (hS1 : S1Statement)
    (hS2 : S2Statement) (hS4 : S4Statement) :
    S5Statement := by
  intro Q hQ
  use s5_massSlack hR3 hS1 hS2 hS4 Q hQ
  constructor
  · intro eps heps
    exact s5_massSlack_sublinear hR3 hS1 hS2 hS4 Q hQ eps heps
  · intro m A q eps hA heps hepsQ hFat hPinned
    exact s5_average_bad_steps_bound hR3 hS1 hS2 hS4 Q hQ m A q eps hA heps hepsQ hFat hPinned
end HarperStability
