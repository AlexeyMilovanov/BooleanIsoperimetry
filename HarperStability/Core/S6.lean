import HarperStability.Core.S6Estimator
import HarperStability.Core.S6Window

namespace HarperStability

/-- Error budget for the center-majority estimator.  The third term is
the exact bad-window mass produced by `s6_expectedEstimatorError_le`
(windows outside the `[pLow*m, (1-pLow)*m]` band, where the variance
budget does not apply); `s6_badWindow_mass_le` (file `S6Window.lean`)
bounds it by the *m-independent* constant `4/(gap^2*(p-pLow)^2 * p) * p
= 4*(1-p)/(gap^2*(p-pLow)^2) ≤ 4/(gap^2*(p-pLow)^2)` via Chebyshev, so
at `pLow = p/2` the whole term is `≤ 16/(gap^2*p^2)` — constant in `m`,
hence sublinear; the `p → 0` diagonal (`s6_sublinear_diagonalize`)
absorbs it. -/
noncomputable def s6_errorBound (gap : ℝ) (vFam : ℝ → ℕ → ℝ)
    (bSlack : ℕ → ℝ) (p pLow : ℝ) (m : ℕ) : ℝ :=
  (4 / gap ^ 2) * (vFam pLow m / p) + 2 * (bSlack m / p) +
    (4 / gap ^ 2) * (((m : ℝ) / p) *
      ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
        ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
        windowProb J p)

/-- The bad-window sum is nonnegative (each `windowProb` is a product of
nonnegative powers). -/
lemma s6_badWindow_sum_nonneg (m : ℕ) (p pLow : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    0 ≤ ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
        ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
      windowProb J p := by
  refine Finset.sum_nonneg fun J _ => ?_
  unfold windowProb
  have h1 : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

lemma s6_uCondH_coord_le_log_two {m : ℕ} {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (hA : A.Nonempty) (t : Fin m) (g : Cube m → B) :
    uCondH A (coord t) g ≤ Real.log 2 := by
  rw [uCondH_bool_eq_uE_binEntropy A hA (coord t) g]
  unfold uE H
  have hcard_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  rw [div_le_iff₀ hcard_pos]
  calc
    (∑ x ∈ A, Real.binEntropy (pOn (A.filter fun y => g y = g x) (coord t) true))
        ≤ ∑ _x ∈ A, Real.log 2 := by
          exact Finset.sum_le_sum fun _ _ => Real.binEntropy_le_log_two
    _ = Real.log 2 * (A.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma s6_uH_proj_le_log_two_mul {m : ℕ} (A : Finset (Cube m))
    (hA : A.Nonempty) (I : Finset (Fin m)) :
    uH A (proj I) ≤ Real.log 2 * (I.card : ℝ) := by
  rw [uH_proj_chain A hA I]
  calc
    (∑ t ∈ I, uCondH A (coord t) (proj (below I t)))
        ≤ ∑ _t ∈ I, Real.log 2 := by
          exact Finset.sum_le_sum fun t _ =>
            s6_uCondH_coord_le_log_two A hA t (proj (below I t))
    _ = Real.log 2 * (I.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

lemma s6_Sublinear_mexp (c : ℝ) (hc : 0 < c) :
    Sublinear (fun m => (m : ℝ) * Real.exp (-c * (m : ℝ))) := by
  refine ⟨fun _ => by positivity, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, Real.exp (-c * (n : ℝ)) ≤ ε := by
    simpa [neg_mul] using
      (Real.tendsto_exp_atBot.comp
        (Filter.tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop.const_mul_atTop hc))).eventually
        (ge_mem_nhds hε)
  exact ⟨N, fun n hn => by
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hN n hn) (Nat.cast_nonneg n)⟩

lemma s6_Sublinear_entropyTerm (g : ℕ → ℝ) (hg : Sublinear g) :
    Sublinear (fun m => (m : ℝ) * H (min (g m / (m : ℝ)) (1 / 2))) := by
  refine ⟨fun m => ?_, fun ε hε => ?_⟩ <;> norm_num [H] at *
  · exact mul_nonneg (Nat.cast_nonneg _)
      (Real.binEntropy_nonneg
        (by
          cases min_cases (g m / (m : ℝ)) (1 / 2) <;>
            nlinarith [hg.1 m,
              show 0 ≤ g m / (m : ℝ) from
                div_nonneg (hg.1 m) (Nat.cast_nonneg m)])
        (by
          cases min_cases (g m / (m : ℝ)) (1 / 2) <;> linarith))
  · obtain ⟨δ, hδ_pos, hδ⟩ :
        ∃ δ > 0, ∀ x ∈ Set.Icc (0 : ℝ) δ, Real.binEntropy x ≤ ε := by
      have hcont := Metric.continuousAt_iff.mp
        (show ContinuousAt (fun x : ℝ => Real.binEntropy x) 0 by
          exact Real.binEntropy_continuous.continuousAt) ε hε
      simp only [Real.binEntropy_zero, sub_zero, dist_eq_norm, Real.norm_eq_abs] at hcont
      obtain ⟨δ, hδ₁, hδ₂⟩ := hcont
      refine ⟨δ / 2, half_pos hδ₁, fun x hx => ?_⟩
      have hlt : |x| < δ := by
        rw [abs_of_nonneg hx.1]
        linarith [hx.2]
      exact le_of_lt (abs_lt.mp (hδ₂ hlt)).2
    obtain ⟨N, hN⟩ := hg.2 δ hδ_pos
    refine ⟨N + 1, fun n hn => ?_⟩
    rw [mul_comm]
    gcongr
    exact hδ _ ⟨
      by
        exact le_min (div_nonneg (hg.1 _) (Nat.cast_nonneg _)) (by norm_num),
      by
        exact min_le_of_left_le
          (div_le_of_le_mul₀
            (by norm_cast; linarith)
            (by positivity)
            (by linarith [hN n (by linarith)]))⟩

lemma s6_errorBound_sublinear (gap : ℝ) (vFam : ℝ → ℕ → ℝ)
    (bSlack : ℕ → ℝ)
    (hvFam : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow))
    (hbSlack : Sublinear bSlack) (p : ℝ) (hp : 0 < p) (hp_half : p ≤ 1 / 2) :
    Sublinear (fun m => s6_errorBound gap vFam bSlack p (p / 2) m) := by
  have hpLow_pos : 0 < p / 2 := by linarith
  have hpLow_half : p / 2 ≤ 1 / 2 := by linarith
  have hV :
      Sublinear (fun m => ((4 / gap ^ 2) * (1 / p)) * vFam (p / 2) m) :=
    core_Sublinear_smul (by positivity) (hvFam (p / 2) hpLow_pos hpLow_half)
  have hB : Sublinear (fun m => (2 * (1 / p)) * bSlack m) :=
    core_Sublinear_smul (by positivity) hbSlack
  have htail :
      Sublinear (fun m => (4 / gap ^ 2) * (((m : ℝ) / p) *
        ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
          ¬ (p / 2 * (m : ℝ) ≤ (J.card : ℝ) ∧
            (J.card : ℝ) ≤ (1 - p / 2) * (m : ℝ))),
          windowProb J p)) := by
    have hp1 : p ≤ 1 := hp_half.trans (by norm_num)
    refine core_Sublinear_of_le
      (fun m => ?_)
      (fun m => ?_)
      (core_Sublinear_const
        (show (0 : ℝ) ≤ (4 / gap ^ 2) * (4 / p ^ 2) by positivity))
    · have hsum := s6_badWindow_sum_nonneg m p (p / 2) (le_of_lt hp) hp1
      have hm : (0 : ℝ) ≤ (m : ℝ) / p := by positivity
      have h4 : (0 : ℝ) ≤ 4 / gap ^ 2 := by positivity
      exact mul_nonneg h4 (mul_nonneg hm hsum)
    · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        simp only [Nat.cast_zero, zero_div, zero_mul, mul_zero]
        positivity
      · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
        have hbad := s6_badWindow_mass_le m p (p / 2)
          (by linarith) (by linarith) hp_half
        have hstep : ((m : ℝ) / p) *
            (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
              ¬ (p / 2 * (m : ℝ) ≤ (J.card : ℝ) ∧
                (J.card : ℝ) ≤ (1 - p / 2) * (m : ℝ))),
              windowProb J p) ≤
            ((m : ℝ) / p) * (p / ((p - p / 2) ^ 2 * (m : ℝ))) := by
          have hm : (0 : ℝ) ≤ (m : ℝ) / p := by positivity
          exact mul_le_mul_of_nonneg_left hbad hm
        have hcalc : ((m : ℝ) / p) * (p / ((p - p / 2) ^ 2 * (m : ℝ))) =
            4 / p ^ 2 := by
          have hp0 : p ≠ 0 := ne_of_gt hp
          have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
          field_simp
          ring
        have h4 : (0 : ℝ) ≤ 4 / gap ^ 2 := by positivity
        calc (4 / gap ^ 2) * (((m : ℝ) / p) *
              ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
                ¬ (p / 2 * (m : ℝ) ≤ (J.card : ℝ) ∧
                  (J.card : ℝ) ≤ (1 - p / 2) * (m : ℝ))),
                windowProb J p)
            ≤ (4 / gap ^ 2) * (((m : ℝ) / p) *
                (p / ((p - p / 2) ^ 2 * (m : ℝ)))) :=
              mul_le_mul_of_nonneg_left hstep h4
          _ = (4 / gap ^ 2) * (4 / p ^ 2) := by rw [hcalc]
  convert core_Sublinear_add (core_Sublinear_add hV hB) htail using 1
  ext m
  dsimp [s6_errorBound]
  ring_nf

noncomputable def s6_Sfam (gap : ℝ) (vFam : ℝ → ℕ → ℝ)
    (bSlack : ℕ → ℝ) (p : ℝ) (m : ℕ) : ℝ :=
  let e := s6_errorBound gap vFam bSlack p (p / 2) m
  (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) +
    e * Real.log 2 + 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8)

lemma s6_Sfam_sublinear (gap : ℝ) (vFam : ℝ → ℕ → ℝ)
    (bSlack : ℕ → ℝ)
    (hvFam : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow))
    (hbSlack : Sublinear bSlack) (p : ℝ) (hp : 0 < p) (hp_half : p ≤ 1 / 2) :
    Sublinear (s6_Sfam gap vFam bSlack p) := by
  have herr := s6_errorBound_sublinear gap vFam bSlack hvFam hbSlack p hp hp_half
  have hent := s6_Sublinear_entropyTerm _ herr
  have herr_log : Sublinear (fun m =>
      s6_errorBound gap vFam bSlack p (p / 2) m * Real.log 2) := by
    convert core_Sublinear_smul (show 0 ≤ Real.log 2 by positivity) herr using 1
    ext m
    ring_nf
  have htail : Sublinear (fun m =>
      2 * ((m : ℝ) * Real.exp (-(p / 8) * (m : ℝ)))) :=
    core_Sublinear_smul (by norm_num) (s6_Sublinear_mexp (p / 8) (by positivity))
  convert core_Sublinear_add (core_Sublinear_add hent herr_log) htail using 1
  ext m
  dsimp [s6_Sfam]
  ring_nf

lemma s6_sublinear_diagonalize (Sfam : ℝ → ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hS : ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → Sublinear (Sfam p)) :
    ∃ (env : ℕ → ℝ) (P : ℕ → ℝ),
      Sublinear env ∧
      (∀ m : ℕ, 0 < P m ∧ P m ≤ 1 / 2) ∧
      (∀ m : ℕ, Sfam (P m) m + c * P m * (m : ℝ) ≤ env m) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, StrictMono N ∧ N 0 = 0 ∧ ∀ k ≥ 1, ∀ m ≥ N k, Sfam (1 / (k + 2)) m ≤ (1 / (k + 2)) * m := by
    have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ m ≥ N, Sfam (1 / (k + 2)) m ≤ (1 / (k + 2)) * m := by
      intro k
      convert hS (1 / (k + 2)) (by positivity)
        (by rw [div_le_iff₀] <;> linarith) |>.2 (1 / (k + 2)) (by positivity) using 1
    choose N hN using hN
    refine' ⟨fun k => Nat.recOn k 0 fun k ih => Max.max (N (k + 1)) (ih + 1),
      strictMono_nat_of_lt_succ fun k => _, _, _⟩ <;> norm_num
    intro k hk m hm
    specialize hN k m
    induction hk <;> aesop
  refine' ⟨fun m => Sfam ((Nat.findGreatest (fun k => N k ≤ m) m + 2 : ℝ)⁻¹) m +
      c * ((Nat.findGreatest (fun k => N k ≤ m) m + 2 : ℝ)⁻¹) * m,
    fun m => ((Nat.findGreatest (fun k => N k ≤ m) m + 2 : ℝ)⁻¹), _, _, _⟩ <;> norm_num
  · refine' ⟨fun m => add_nonneg (_) (mul_nonneg (mul_nonneg hc (inv_nonneg.2 (by positivity))) (Nat.cast_nonneg m)), _⟩
    · have := hS ((Nat.findGreatest (fun k => N k ≤ m) m + 2 : ℝ)⁻¹) (by positivity)
        (by
          have hden : (2 : ℝ) ≤ (Nat.findGreatest (fun k => N k ≤ m) m + 2 : ℝ) := by
            norm_num
          simpa [one_div] using
            one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden)
      exact this.1 m
    · intro ε hε
      obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 ≤ k ∧ (1 + c) / (k + 2 : ℝ) ≤ ε := by
        exact ⟨⌊(1 + c) / ε⌋₊ + 1, by linarith,
          by rw [div_le_iff₀] <;> push_cast <;>
            nlinarith [Nat.lt_floor_add_one ((1 + c) / ε),
              mul_div_cancel₀ (1 + c) hε.ne']⟩
      use N k
      intro n hn
      have hidx : Nat.findGreatest (fun k => N k ≤ n) n ≥ k := by
        apply Nat.le_findGreatest
        · exact le_trans (hN.1.id_le _) hn
        · linarith
      have hP : (Nat.findGreatest (fun k => N k ≤ n) n + 2 : ℝ)⁻¹ ≤
          (k + 2 : ℝ)⁻¹ := by
        exact inv_anti₀ (by positivity) (by norm_cast; linarith)
      have hSfam :
          Sfam ((Nat.findGreatest (fun k => N k ≤ n) n + 2 : ℝ)⁻¹) n ≤
            (1 / (k + 2 : ℝ)) * n := by
        have := hN.2.2 (Nat.findGreatest (fun k => N k ≤ n) n) (by linarith) n ?_ <;> norm_num at *
        · simpa [one_div] using
            this.trans (mul_le_mul_of_nonneg_right hP <| Nat.cast_nonneg _)
        · have := Nat.findGreatest_eq_iff.mp
            (rfl : Nat.findGreatest (fun k => N k ≤ n) n = _)
          aesop
      have henv :
          Sfam ((Nat.findGreatest (fun k => N k ≤ n) n + 2 : ℝ)⁻¹) n +
              c * ((Nat.findGreatest (fun k => N k ≤ n) n + 2 : ℝ)⁻¹) * n
            ≤ ε * n := by
        refine le_trans ?_ (mul_le_mul_of_nonneg_right hk.2 <| Nat.cast_nonneg _)
        convert add_le_add hSfam
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (show ((Nat.findGreatest (fun k => N k ≤ n) n + 2 : ℝ)⁻¹) ≤
                  (1 / (k + 2 : ℝ)) from by simpa [one_div] using hP)
              hc)
            (Nat.cast_nonneg n)) using 1
        ring_nf
      exact henv.trans' (by norm_num [add_comm])
  · exact fun m => ⟨by positivity,
      by
        have hden : (2 : ℝ) ≤ (Nat.findGreatest (fun k => N k ≤ m) m + 2 : ℝ) := by
          norm_num
        simpa [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden⟩

lemma s6_diagonal_entropy_envelope
    (qMin qMax eps gap : ℝ) (sFam vFam : ℝ → ℕ → ℝ) (bSlack : ℕ → ℝ)
    (_hsFam : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (sFam pLow))
    (hvFam : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow))
    (hbSlack : Sublinear bSlack) :
    ∃ cEnv : ℕ → ℝ, Sublinear cEnv ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        qMin ≤ q → q ≤ qMax →
        A.Nonempty →
        blockRegularFamily m A q sFam →
        (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
          varianceBudgetLE A pLow (vFam pLow m)) →
        averageBadStepsLE A q eps (bSlack m) →
        (∀ p pLow : ℝ, 0 < pLow → pLow ≤ p → p ≤ 1 / 2 →
          uH A (fun x t => coord t (predictableCenter A x)) ≤
            2 * Real.log 2 * p * (m : ℝ) +
            (m : ℝ) *
              H (min (s6_errorBound gap vFam bSlack p pLow m / (m : ℝ)) (1 / 2)) +
            s6_errorBound gap vFam bSlack p pLow m * Real.log 2 +
            2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8)) →
        uH A (predictableCenter A) ≤ cEnv m := by
  classical
  let Sfam : ℝ → ℕ → ℝ := s6_Sfam gap vFam bSlack
  have hSfam :
      ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → Sublinear (Sfam p) := by
    intro p hp hp_half
    exact s6_Sfam_sublinear gap vFam bSlack hvFam hbSlack p hp hp_half
  have hc : 0 ≤ 2 * Real.log 2 := by positivity
  obtain ⟨cEnv, P, hcEnv, hP, hdom⟩ :=
    s6_sublinear_diagonalize Sfam (2 * Real.log 2) hc hSfam
  refine ⟨cEnv, hcEnv, ?_⟩
  intro m A q _hqMin _hqMax hA _h_reg _h_var _h_bad hbound
  have hp := (hP m).1
  have hp_half := (hP m).2
  have hpLow_pos : 0 < P m / 2 := by linarith
  have hpLow_le : P m / 2 ≤ P m := by linarith
  have hcoord :=
    hbound (P m) (P m / 2) hpLow_pos hpLow_le hp_half
  have hcenter := uH_predictableCenter_le_coordField A
  have htoEnv :
      2 * Real.log 2 * P m * (m : ℝ) +
          ((m : ℝ) *
              H (min (s6_errorBound gap vFam bSlack (P m) (P m / 2) m /
                  (m : ℝ)) (1 / 2)) +
            s6_errorBound gap vFam bSlack (P m) (P m / 2) m * Real.log 2 +
            2 * (m : ℝ) * Real.exp (-P m * (m : ℝ) / 8)) ≤ cEnv m := by
    have h := hdom m
    dsimp [Sfam, s6_Sfam] at h
    linarith
  have hcoord_to_env :
      uH A (fun x t => coord t (predictableCenter A x)) ≤ cEnv m := by
    linarith [hcoord, htoEnv]
  exact hcenter.trans hcoord_to_env

lemma s6_apply_s3 (_hS3 : S3Statement)
    (m : ℕ) (A : Finset (Cube m)) (q qMax eps gap : ℝ)
    (hq_le : q ≤ qMax) (hqMax : qMax < 1 / 2)
    (heps : 0 < eps) (hgap : 0 < gap) (hgap_le : qMax + eps ≤ 1 / 2 - gap)
    (sFam vFam : ℝ → ℕ → ℝ) (bSlack : ℕ → ℝ)
    (hA : A.Nonempty)
    (_h_reg : blockRegularFamily m A q sFam)
    (h_var : ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → varianceBudgetLE A pLow (vFam pLow m))
    (h_bad : averageBadStepsLE A q eps (bSlack m))
    (hvFam : ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow))
    (hbSlack : Sublinear bSlack)
    (p pLow : ℝ) (hpLow_pos : 0 < pLow) (hpLow_le : pLow ≤ p) (hp : p ≤ 1 / 2) :
    uH A (fun x t => coord t (predictableCenter A x)) ≤
      2 * Real.log 2 * p * (m : ℝ) +
      (m : ℝ) *
        H (min (s6_errorBound gap vFam bSlack p pLow m / (m : ℝ)) (1 / 2)) +
      s6_errorBound gap vFam bSlack p pLow m * Real.log 2 +
      2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8) := by
  classical
  have hpLow_half : pLow ≤ 1 / 2 := hpLow_le.trans hp
  have hp_pos : 0 < p := hpLow_pos.trans_le hpLow_le
  have hp_one : p ≤ 1 := hp.trans (by norm_num)
  let e : ℝ := s6_errorBound gap vFam bSlack p pLow m
  have hv_nonneg : 0 ≤ vFam pLow m := (hvFam pLow hpLow_pos hpLow_half).1 m
  have hb_nonneg : 0 ≤ bSlack m := hbSlack.1 m
  have hsum_nonneg :=
    s6_badWindow_sum_nonneg m p pLow (le_of_lt hp_pos) hp_one
  have he_nonneg : 0 ≤ e := by
    dsimp [e, s6_errorBound]
    have h1 : (0 : ℝ) ≤ (4 / gap ^ 2) * (vFam pLow m / p) :=
      mul_nonneg (by positivity) (div_nonneg hv_nonneg (le_of_lt hp_pos))
    have h2 : (0 : ℝ) ≤ 2 * (bSlack m / p) :=
      mul_nonneg (by norm_num) (div_nonneg hb_nonneg (le_of_lt hp_pos))
    have h3 : (0 : ℝ) ≤ (4 / gap ^ 2) * (((m : ℝ) / p) *
        ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
          ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧
            (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
          windowProb J p) := by
      have hm : (0 : ℝ) ≤ (m : ℝ) / p := by positivity
      have h4 : (0 : ℝ) ≤ 4 / gap ^ 2 := by positivity
      exact mul_nonneg h4 (mul_nonneg hm hsum_nonneg)
    linarith
  have hErr :
      expectedEstimatorError A
        (fun x t => coord t (predictableCenter A x))
        (centerMajorityEstimator A) p ≤ e := by
    dsimp [e, s6_errorBound]
    exact s6_expectedEstimatorError_le A q qMax eps gap p pLow (vFam pLow m)
      (bSlack m) hA hv_nonneg hb_nonneg hq_le hqMax heps hgap hgap_le
      hpLow_pos hpLow_le hp
      (h_var pLow hpLow_pos hpLow_half) h_bad
  have hS3_apply := _hS3 m A (Real.log 2) 0 Bool
    (fun x t => coord t (predictableCenter A x)) p e 2
    hA (by positivity) (by norm_num) hp_pos hp he_nonneg (by norm_num)
    (by
      intro I _ _
      have hproj := s6_uH_proj_le_log_two_mul A hA I
      linarith)
    (by
      intro t
      have hcard :
          (@Finset.image (Cube m) Bool
            (fun a b => Classical.propDecidable (a = b))
            (fun x => (fun x t => coord t (predictableCenter A x)) x t) A).card ≤ 2 := by
        simpa using
          (Finset.card_le_univ
            (s := @Finset.image (Cube m) Bool
              (fun a b => Classical.propDecidable (a = b))
              (fun x => (fun x t => coord t (predictableCenter A x)) x t) A))
      exact_mod_cast hcard)
    ⟨centerMajorityEstimator A, center_majority_estimator_dependsOnWindow A, hErr⟩
  simpa [e, zero_add, s6_errorBound] using hS3_apply

-- ============================================================================
-- S7 Leaves (Heavy Ball Assembly)
-- ============================================================================

theorem S6_skeleton (_hS3 : S3Statement) : S6Statement := by
  intro qMin qMax eps gap hqMin_pos hqMin_le hqMax heps hgap hgap_le sFam vFam
    bSlack hsFam hvFam hbSlack
  have ⟨cEnv, hcEnv_sublin, hcEnv_bound⟩ := s6_diagonal_entropy_envelope qMin qMax eps gap sFam vFam bSlack hsFam hvFam hbSlack
  use cEnv, hcEnv_sublin
  intro m A q hqMin_le_q hq_le hA h_reg h_var h_bad
  apply hcEnv_bound m A q hqMin_le_q hq_le hA h_reg h_var h_bad
  intro p pLow hpLow_pos hpLow_le hp
  apply s6_apply_s3 _hS3 m A q qMax eps gap hq_le hqMax heps hgap hgap_le sFam vFam bSlack hA h_reg h_var h_bad hvFam hbSlack p pLow hpLow_pos hpLow_le hp

end HarperStability
