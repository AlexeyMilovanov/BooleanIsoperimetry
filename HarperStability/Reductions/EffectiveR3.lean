import HarperStability.Reductions.Basic
import HarperStability.Reductions.R3Fiber
import HarperStability.Volume.Basic
import HarperStability.Interface.Effective

/-!
# Effective R3 (v0.3): block regularity at grade 2

Target: `R3Eff` — for fat+pinned `A`, every `pLow`-window is
`H(q)`-regular with slack `K * (effEnv 2 Q.sigma m + 1)`
(≈ `K·σ^{1/4}·m^{3/4}`; grade 2 is deliberately generous — the honest
loss of the ζ²-Markov route is `√(σm)`, grade 1).

Route: replay the PROVED v0.2 chain (`r3_cond_entropy_bound`,
`r3_fiber_log_lower`, `r3_fiber_growth_V_bound`) with explicit slack
bookkeeping instead of `Sublinear` packaging:
* the effective volume inputs come from `BallVolumeTwoSidedEff` /
  `InteriorVolumeCalculusEff` (hypotheses below) — their `effLog` slack
  is ≤ `effEnv 1` of any valid sigma (`σ ≥ log m`);
* the ζ-integration/Markov step yields deficits `≤ C·√((σ+effLog)·m)`
  — bound by `C'·(effEnv 1 Q.sigma m + 1)` and then by grade 2;
* the running-max over window dimensions (`r3_runMax`) is monotone
  envelope algebra (`effEnv_mono`, `effEnv_comp` from the toolkit);
* absorb finitely many small `m` into `K` (σ ≥ log m helps below the
  threshold).
Do NOT modify `Interface/Effective.lean` (hash-frozen).
-/

namespace HarperStability

private lemma r3_eff_uH_proj_pair_compl_eq_univ {m : ℕ} (A : Finset (Cube m))
    (I : Finset (Fin m)) :
    uH A (fun x => (proj I x, proj Iᶜ x)) =
      uH A (proj (Finset.univ : Finset (Fin m))) := by
  classical
  apply le_antisymm
  · have hfun :
        (fun x : Cube m =>
          (proj I (proj (Finset.univ : Finset (Fin m)) x),
            proj Iᶜ (proj (Finset.univ : Finset (Fin m)) x))) =
          (fun x : Cube m => (proj I x, proj Iᶜ x)) := by
      funext x
      simp [proj]
    have hle := uH_comp_le A (proj (Finset.univ : Finset (Fin m)))
      (fun y : Cube m => (proj I y, proj Iᶜ y))
    simpa [hfun] using hle
  · have hfun :
        (fun x : Cube m => (proj I x, proj Iᶜ x).1 ∪ (proj I x, proj Iᶜ x).2) =
          (proj (Finset.univ : Finset (Fin m))) := by
      funext x
      ext t
      simp only [proj, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
        Finset.mem_univ, and_true]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
        · exact hx
        · exact hx
      · intro hx
        by_cases ht : t ∈ I
        · exact Or.inl ⟨hx, ht⟩
        · exact Or.inr ⟨hx, ht⟩
    have hle := uH_comp_le A (fun x => (proj I x, proj Iᶜ x))
      (fun p : Cube m × Cube m => p.1 ∪ p.2)
    simpa [hfun] using hle

/-- Entropy of an injective-on-`A` statistic is the full `log |A|`. -/
private lemma r3_eff_uH_of_injOn_eq_log_card {m : ℕ} {B : Type*}
    (A : Finset (Cube m)) (hA : A.Nonempty) (f : Cube m → B)
    (hinj : Set.InjOn f A) : uH A f = Real.log (A.card : ℝ) := by
  classical
  have hApos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hpOn : ∀ b ∈ A.image f, pOn A f b = 1 / (A.card : ℝ) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨x, hx, rfl⟩
    unfold pOn
    congr 1
    norm_cast
    rw [Finset.card_eq_one]
    refine ⟨x, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hyA, hyf⟩
      exact hinj hyA hx hyf
    · rintro rfl
      exact ⟨hx, rfl⟩
  have hcard_img : (A.image f).card = A.card := Finset.card_image_of_injOn hinj
  have hnegMulLog : Real.negMulLog (1 / (A.card : ℝ)) =
      (1 / (A.card : ℝ)) * Real.log (A.card : ℝ) := by
    unfold Real.negMulLog
    rw [Real.log_div one_ne_zero hApos.ne', Real.log_one]
    ring
  unfold uH
  calc (∑ b ∈ A.image f, Real.negMulLog (pOn A f b))
      = ∑ _b ∈ A.image f, (1 / (A.card : ℝ)) * Real.log (A.card : ℝ) := by
        refine Finset.sum_congr rfl (fun b hb => ?_)
        rw [hpOn b hb, hnegMulLog]
    _ = ((A.image f).card : ℝ) * ((1 / (A.card : ℝ)) * Real.log (A.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = Real.log (A.card : ℝ) := by
        rw [hcard_img]
        field_simp

/-- On a fiber of `proj Iᶜ`, the window projection `proj I` is injective. -/
private lemma r3_eff_projI_injOn_fiber {m : ℕ} (A : Finset (Cube m))
    (I : Finset (Fin m)) (z : Cube m) :
    Set.InjOn (proj I) (A.filter fun x => proj Iᶜ x = z) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_filter] at hx hy
  ext t
  by_cases ht : t ∈ I
  · have h := congrArg (fun w => t ∈ w) hxy
    simpa [proj, ht] using h
  · have ht' : t ∈ Iᶜ := Finset.mem_compl.mpr ht
    have h := congrArg (fun w => t ∈ w) (hx.2.trans hy.2.symm)
    simpa [proj, ht'] using h

/-- The conditional entropy of a window given its complement is exactly the
expected log fiber size. -/
private lemma r3_eff_uCondH_eq_expected_log_fiber {m : ℕ} (A : Finset (Cube m))
    (hA : A.Nonempty) (I : Finset (Fin m)) :
    uCondH A (proj I) (proj Iᶜ) =
      ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
        Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
  classical
  unfold uCondH
  rw [uH_prod_sub_eq_sum A hA (proj I) (proj Iᶜ)]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  congr 1
  have hfib_ne : (A.filter fun x => proj Iᶜ x = z).Nonempty := by
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  have hinner :
      (∑ b ∈ A.image (proj I),
        Real.negMulLog (pOn (A.filter fun y => proj Iᶜ y = z) (proj I) b)) =
      uH (A.filter fun y => proj Iᶜ y = z) (proj I) := by
    unfold uH
    refine (Finset.sum_subset ?_ ?_).symm
    · intro y hy
      simp only [Finset.mem_image, Finset.mem_filter] at hy ⊢
      obtain ⟨x, ⟨hxA, _⟩, hxy⟩ := hy
      exact ⟨x, hxA, hxy⟩
    · intro b _hb hb'
      have hzero : pOn (A.filter fun y => proj Iᶜ y = z) (proj I) b = 0 := by
        unfold pOn
        rw [div_eq_zero_iff]
        left
        simp only [Nat.cast_eq_zero, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff]
        intro y hy hyb
        refine hb' ?_
        simp only [Finset.mem_image]
        exact ⟨y, hy, hyb⟩
      rw [hzero, Real.negMulLog_zero]
  rw [hinner,
    r3_eff_uH_of_injOn_eq_log_card _ hfib_ne _ (r3_eff_projI_injOn_fiber A I z)]


private lemma r3_eff_nH_inv_le_log_add_one (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * H (1 / (n : ℝ)) ≤ Real.log (n : ℝ) + 1 := by
  by_cases hn1 : n = 1
  · subst hn1
    norm_num [H, Real.binEntropy]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnone : (1 : ℝ) < (n : ℝ) :=
    by exact_mod_cast (Nat.lt_of_le_of_ne hn (Ne.symm hn1))
  have hdenpos : 0 < 1 - (1 / (n : ℝ)) := by
    rw [sub_pos]
    have : (1 : ℝ) / 1 < (n : ℝ) := by simpa using hnone
    exact (one_div_lt hnpos zero_lt_one).2 this
  have hfirst :
      (n : ℝ) * ((1 / (n : ℝ)) * Real.log ((1 / (n : ℝ))⁻¹)) =
        Real.log (n : ℝ) := by
    have hinv : (1 / (n : ℝ))⁻¹ = (n : ℝ) := by
      field_simp [ne_of_gt hnpos]
    rw [hinv]
    field_simp [ne_of_gt hnpos]
  have hlog2 :
      Real.log ((1 - 1 / (n : ℝ))⁻¹) ≤
        (1 - 1 / (n : ℝ))⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsecond_base :
      (1 - 1 / (n : ℝ)) * Real.log ((1 - 1 / (n : ℝ))⁻¹) ≤
        (1 - 1 / (n : ℝ)) * ((1 - 1 / (n : ℝ))⁻¹ - 1) := by
    exact mul_le_mul_of_nonneg_left hlog2 (by linarith)
  have hsecond_eq :
      (1 - 1 / (n : ℝ)) * ((1 - 1 / (n : ℝ))⁻¹ - 1) =
        1 / (n : ℝ) := by
    have hden : 1 - 1 / (n : ℝ) ≠ 0 := ne_of_gt hdenpos
    calc (1 - 1 / (n : ℝ)) * ((1 - 1 / (n : ℝ))⁻¹ - 1)
        = (1 - 1 / (n : ℝ)) * (1 - 1 / (n : ℝ))⁻¹ -
            (1 - 1 / (n : ℝ)) := by ring
      _ = 1 - (1 - 1 / (n : ℝ)) := by rw [mul_inv_cancel₀ hden]
      _ = 1 / (n : ℝ) := by ring
  have hsecond :
      (n : ℝ) * ((1 - 1 / (n : ℝ)) *
        Real.log ((1 - 1 / (n : ℝ))⁻¹)) ≤ 1 := by
    calc (n : ℝ) * ((1 - 1 / (n : ℝ)) *
          Real.log ((1 - 1 / (n : ℝ))⁻¹))
        ≤ (n : ℝ) * (1 / (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (by linarith [hsecond_base, hsecond_eq]) hnpos.le
      _ = 1 := by field_simp [ne_of_gt hnpos]
  unfold H Real.binEntropy
  have hsplit :
      (n : ℝ) * ((1 / (n : ℝ)) * Real.log ((1 / (n : ℝ))⁻¹) +
          (1 - 1 / (n : ℝ)) *
            Real.log ((1 - 1 / (n : ℝ))⁻¹)) =
        (n : ℝ) * ((1 / (n : ℝ)) * Real.log ((1 / (n : ℝ))⁻¹)) +
          (n : ℝ) * ((1 - 1 / (n : ℝ)) *
            Real.log ((1 - 1 / (n : ℝ))⁻¹)) := by
    ring
  rw [hsplit]
  linarith


set_option maxHeartbeats 5000000

/-- Effective per-fiber Harper growth (σ- and pLow-uniform leaf; the
v0.2 proved counterpart is `r3_fiber_growth_V_bound` in
`Reductions/R3Fiber.lean`).  The growth exponent is the EXPLICIT
`(pLow/8)·ζ²·m` (the v0.2 gain `2tζ` with `t ≈ pLow·ζ/2` gives
`c ≈ pLow`; the 8 is margin for the robust/δ losses), and the slack
carries the honest `pLow⁻¹` factor.  `sigma` enters only through the slack. -/
lemma r3_fiber_growth_V_bound_eff (hBV : BallVolumeTwoSidedEff)
    (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff)
    (qMin qMax s0 mu0 : ℝ)
    (h1 : 0 < qMin) (h2 : qMin ≤ qMax) (h3 : qMax < 1 / 2)
    (h4 : 0 < s0) (h5 : 0 < mu0) (h6 : qMax + s0 ≤ 1 / 2 - mu0) :
    ∃ K : ℝ, 1 ≤ K ∧
    ∀ (pLow : ℝ), 0 < pLow → pLow ≤ 1 / 2 →
    ∀ (sigma : ℕ → ℝ), Sublinear sigma →
      (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
    ∀ (m : ℕ) (q : ℝ), qMin ≤ q → q ≤ qMax →
      ∀ Icard : ℕ, pLow * (m : ℝ) ≤ (Icard : ℝ) →
        (Icard : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ q / 2 → ζ ≤ 2 * s0 / pLow →
      let θ : ℕ := min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (s0 * (m : ℝ)))
      ∀ k : ℕ, (k : ℝ) ≤ Real.exp (H (q - ζ) * (Icard : ℝ)) →
      Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) +
          (pLow / 8) * ζ ^ 2 * (m : ℝ) -
          (K / pLow) * (effEnv 1 sigma m + 1)) * (k : ℝ) ≤
        (V Icard k θ : ℝ) := by
  rcases hBV with ⟨K_BV, hK_BV, h_bounds⟩
  let dummy_sigma : ℕ → ℝ := fun n => Real.log ((n : ℝ) + 1)
  have hsub_dummy : Sublinear dummy_sigma := by
    refine Sublinear_of_le (fun n => ?_) (fun n => ?_) sublinear_log_succ
    · exact Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
    · apply le_of_eq; rfl
  have hvalid_dummy : validQData ⟨qMin, qMax, s0, mu0, dummy_sigma⟩ :=
    ⟨h1, h2, h3, h4, h5, h6, hsub_dummy, fun n hn => by apply Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_add_right n 1)⟩
  obtain ⟨L, hLpos, hchord⟩ := r3_entropy_compact_inverse_chord ⟨qMin, qMax, s0, mu0, dummy_sigma⟩ hvalid_dummy

  set vSlack := effLog K_BV
  have hK10 : 0 ≤ K_BV := by linarith
  have hlog_add : ∀ n : ℕ, Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) + 1) + Real.log 2 := by
    intro n
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have hn_nn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hvsub : Sublinear vSlack := by
    show Sublinear (effLog K_BV)
    refine Sublinear_of_le (fun n => by
      unfold effLog
      exact mul_nonneg hK10 (add_nonneg (Real.log_nonneg (by linarith)) zero_le_one))
      (fun n => ?_)
      (Sublinear_add
        (Sublinear_smul hK10 sublinear_log_succ)
        (@Sublinear_const (K_BV * (Real.log 2 + 1))
          (mul_nonneg hK10 (add_nonneg (Real.log_nonneg (by norm_num)) zero_le_one))))
    unfold effLog
    have hstep : K_BV * (Real.log ((n : ℝ) + 2) + 1) ≤ K_BV * (Real.log ((n : ℝ) + 1) + Real.log 2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hlog_add n]) hK10
    have h_eq : K_BV * (Real.log ((n : ℝ) + 1) + Real.log 2 + 1) = K_BV * Real.log ((n : ℝ) + 1) + K_BV * (Real.log 2 + 1) := by ring
    rw [h_eq] at hstep
    exact hstep
  have hvol : ∀ (n t : ℕ), t ≤ n / 2 → Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - vSlack n) ≤ ((ball (∅ : Cube n) t).card : ℝ) ∧ ((ball (∅ : Cube n) t).card : ℝ) ≤ Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + vSlack n) := h_bounds

  classical
  obtain ⟨N, hN⟩ := r3_fiber_growth_witness_safe vSlack hvsub hvol ⟨qMin, qMax, s0, mu0, dummy_sigma⟩ hvalid_dummy L hLpos hchord

  let Λ := Real.log ((1 - qMin / 2) / (qMin / 2))
  let K := K_BV * 8 + (N : ℝ) * Real.log 2 * 2 + (N : ℝ) + 20 +
    4 * Λ * K_BV / L + 2 + 8 * K_BV
  use K
  have hK_BV_4 : 1 ≤ K := by
    have hNlog : 0 ≤ (N : ℝ) * Real.log 2 * 2 := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) (by norm_num)
    have hNnn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have hL : 0 ≤ Λ * K_BV / L := div_nonneg (mul_nonneg (Real.log_nonneg (by
      have : qMin ≤ 1 / 2 := by linarith
      rw [one_le_div (by linarith)]
      linarith)) hK10) hLpos.le
    have hL4 : 0 ≤ 4 * Λ * K_BV / L := by
      have htmp : 0 ≤ 4 * (Λ * K_BV / L) := mul_nonneg (by norm_num) hL
      convert htmp using 1
      ring
    have hk : 0 ≤ 2 * K_BV := mul_nonneg (by norm_num) hK10
    have hKBV8 : 8 ≤ K_BV * 8 := by nlinarith
    dsimp [K]
    nlinarith [hNlog, hNnn, hL, hL4, hk, hKBV8]
  refine ⟨hK_BV_4, ?_⟩
  intro pLow hlow hhigh sigma hsigma hsigma_log m q hqmin hqmax Icard hIlow hIhigh ζ hζpos hζle hζscale θ k hk
  have hvalid : validQData ⟨qMin, qMax, s0, mu0, sigma⟩ := ⟨h1, h2, h3, h4, h5, h6, hsigma, hsigma_log⟩
  let Nm := ⌈(N : ℝ) / pLow⌉₊ + 1
  by_cases hm_cases : m < Nm
  · rcases Nat.eq_zero_or_pos k with hk0 | h_k_ge_1
    · subst hk0
      simp only [Nat.cast_zero, mul_zero]
      exact Nat.cast_nonneg _
    have hm_cases_le : (m : ℝ) ≤ Nm := mod_cast hm_cases.le
    have hV_nonneg : 0 ≤ (V Icard k θ : ℝ) := Nat.cast_nonneg _
    have hkn : k ≤ 2 ^ Icard := by
      have hexp : Real.exp (H (q - ζ) * (Icard : ℝ)) ≤ ((2 ^ Icard : ℕ) : ℝ) := by
        have h_H_bound : H (q - ζ) * (Icard : ℝ) ≤ Real.log 2 * (Icard : ℝ) :=
          mul_le_mul_of_nonneg_right Real.binEntropy_le_log_two (Nat.cast_nonneg _)
        calc Real.exp (H (q - ζ) * (Icard : ℝ))
              ≤ Real.exp (Real.log 2 * (Icard : ℝ)) := Real.exp_le_exp.mpr h_H_bound
          _ = (2 : ℝ) ^ Icard := by
                rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
          _ = ((2 ^ Icard : ℕ) : ℝ) := by push_cast; ring
      exact_mod_cast le_trans hk hexp
    rcases hVPlus Icard k θ (by exact_mod_cast h_k_ge_1) hkn with ⟨t, ht_max, hk_le, ht_lt, htV⟩
    have h_empty_mem : (∅ : Cube Icard) ∈ ball (∅ : Cube Icard) (t + θ) := by
      simp [ball, hDist, symmDiff]
    have h_ball_ge_1 : (1 : ℝ) ≤ ((ball (∅ : Cube Icard) (t + θ)).card : ℝ) := by
      have : 1 ≤ (ball (∅ : Cube Icard) (t + θ)).card := Finset.card_pos.mpr ⟨∅, h_empty_mem⟩
      exact_mod_cast this
    have hk_le_V : (1 : ℝ) ≤ (V Icard k θ : ℝ) := le_trans h_ball_ge_1 htV

    have h_log_k : Real.log (k : ℝ) ≤ (Icard : ℝ) * Real.log 2 := by
      have hkpos : 0 < (k : ℝ) := by exact_mod_cast h_k_ge_1
      have hexp : Real.exp (Real.log (k : ℝ)) ≤ Real.exp (Real.log 2 * (Icard : ℝ)) := by
        calc Real.exp (Real.log (k : ℝ)) = (k : ℝ) := Real.exp_log hkpos
          _ ≤ Real.exp (H (q - ζ) * (Icard : ℝ)) := hk
          _ ≤ Real.exp (Real.log 2 * (Icard : ℝ)) := by
                apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_right Real.binEntropy_le_log_two (Nat.cast_nonneg _)
      have h1 : Real.log (k : ℝ) ≤ Real.log 2 * (Icard : ℝ) := (Real.exp_le_exp).mp hexp
      linarith

    have hIcard_le_m : (Icard : ℝ) ≤ (m : ℝ) := by
      have : 0 ≤ pLow * (m : ℝ) := mul_nonneg hlow.le (Nat.cast_nonneg _)
      linarith [hIhigh]

    have hm_bound : (m : ℝ) ≤ (N : ℝ) / pLow + 1 := by
      have hm_le_ceil_nat : m ≤ ⌈(N : ℝ) / pLow⌉₊ := by
        dsimp [Nm] at hm_cases
        omega
      have hm_le_ceil : (m : ℝ) ≤ (⌈(N : ℝ) / pLow⌉₊ : ℝ) := by
        exact_mod_cast hm_le_ceil_nat
      have hNp_nonneg : 0 ≤ (N : ℝ) / pLow :=
        div_nonneg (Nat.cast_nonneg _) hlow.le
      have hceil_lt : (⌈(N : ℝ) / pLow⌉₊ : ℝ) < (N : ℝ) / pLow + 1 :=
        Nat.ceil_lt_add_one hNp_nonneg
      linarith
    have h_zeta_bound : ζ ^ 2 ≤ 1 / 16 := by
      have : ζ ≤ 1 / 4 := by linarith [hqmax, h3, hζle]
      nlinarith
    have h_env_bound : 1 ≤ effEnv 1 sigma m + 1 := by
      have : 0 ≤ effEnv 1 sigma m := effEnv_nonneg 1 sigma hsigma.1 m
      linarith
    have h_H_bound : H (q + (θ : ℝ) / (m : ℝ)) ≤ Real.log 2 := Real.binEntropy_le_log_two
    have h_Hq_bound : 0 ≤ H q := Real.binEntropy_nonneg (by linarith) (by linarith)

    have h_LHS : (pLow / 8) * ζ ^ 2 * (m : ℝ) ≤ (N : ℝ) / 128 + pLow / 128 := by
      have hl1 : (pLow / 8) * ζ ^ 2 * (m : ℝ) ≤ (pLow / 8) * (1 / 16) * (m : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        apply mul_le_mul_of_nonneg_left h_zeta_bound (by linarith)
        exact Nat.cast_nonneg _
      have hl2 : (pLow / 128) * (m : ℝ) ≤ (pLow / 128) * ((N : ℝ) / pLow + 1) := by
        apply mul_le_mul_of_nonneg_left hm_bound (by linarith)
      have hpLow_ne_0 : pLow ≠ 0 := by linarith
      have hl3 : (pLow / 128) * ((N : ℝ) / pLow + 1) = (N : ℝ) / 128 + pLow / 128 := by
        have hl4 : (pLow / 128) * ((N : ℝ) / pLow) = (N : ℝ) / 128 := by
          calc (pLow / 128) * ((N : ℝ) / pLow)
            _ = (pLow / pLow) * ((N : ℝ) / 128) := by ring
            _ = 1 * ((N : ℝ) / 128) := by rw [div_self hpLow_ne_0]
            _ = (N : ℝ) / 128 := by ring
        calc (pLow / 128) * ((N : ℝ) / pLow + 1)
          _ = (pLow / 128) * ((N : ℝ) / pLow) + pLow / 128 := by ring
          _ = (N : ℝ) / 128 + pLow / 128 := by rw [hl4]
      linarith

    have h_RHS : - (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)) - Real.log (k : ℝ) ≥ - (N : ℝ) * Real.log 2 * 2 / pLow - 2 * Real.log 2 := by
      have hr1 : H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) ≤ Real.log 2 * (m : ℝ) := mul_le_mul_of_nonneg_right h_H_bound (Nat.cast_nonneg _)
      have hr2 : 0 ≤ H q * (m : ℝ) := mul_nonneg h_Hq_bound (Nat.cast_nonneg _)
      have hr3 : (Icard : ℝ) * Real.log 2 ≤ (m : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hIcard_le_m (Real.log_nonneg (by norm_num))
      have hr4 : 0 ≤ 2 * Real.log 2 := mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
      have hr5 : 2 * Real.log 2 * (m : ℝ) ≤ 2 * Real.log 2 * ((N : ℝ) / pLow + 1) := mul_le_mul_of_nonneg_left hm_bound hr4
      have hr6 : 2 * Real.log 2 * ((N : ℝ) / pLow + 1) = (N : ℝ) * Real.log 2 * 2 / pLow + 2 * Real.log 2 := by ring
      calc
        - (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)) - Real.log (k : ℝ)
            ≥ - (Real.log 2 * (m : ℝ)) - (Icard : ℝ) * Real.log 2 := by nlinarith
        _ ≥ - (Real.log 2 * (m : ℝ)) - (m : ℝ) * Real.log 2 := by nlinarith
        _ = - 2 * Real.log 2 * (m : ℝ) := by ring
        _ ≥ - 2 * Real.log 2 * ((N : ℝ) / pLow + 1) := by nlinarith
        _ = - (N : ℝ) * Real.log 2 * 2 / pLow - 2 * Real.log 2 := by ring

    have h_K_bound : (N : ℝ) / 128 + pLow / 128 - (K / pLow) ≤ - (N : ℝ) * Real.log 2 * 2 / pLow - 2 * Real.log 2 := by
      have hp_ne : pLow ≠ 0 := ne_of_gt hlow
      have hp0 : 0 < pLow := hlow
      have hmul :
          ((N : ℝ) / 128 + pLow / 128 - (K / pLow)) * pLow ≤
            (- (N : ℝ) * Real.log 2 * 2 / pLow - 2 * Real.log 2) * pLow := by
        calc ((N : ℝ) / 128 + pLow / 128 - (K / pLow)) * pLow
          = (N : ℝ) * pLow / 128 + pLow * pLow / 128 - K := by
              field_simp [hp_ne]
        _ ≤ (N : ℝ) / 256 + 1 / 512 - K := by
              have hNterm : (N : ℝ) * pLow / 128 ≤ (N : ℝ) * (1 / 2) / 128 := by
                gcongr
              have hpterm : pLow * pLow / 128 ≤ (1 / 2) * (1 / 2) / 128 := by
                gcongr
              norm_num at hpterm ⊢
              nlinarith
        _ ≤ - (N : ℝ) * Real.log 2 * 2 - 2 := by
              have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
              have hlog2_le_one : Real.log 2 ≤ 1 := by
                have h_log : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
                linarith
              have hΛnn : 0 ≤ Λ := by
                dsimp [Λ]
                apply Real.log_nonneg
                have : qMin ≤ 1 / 2 := by linarith
                rw [one_le_div (by linarith)]
                linarith
              have hΛterm : 0 ≤ Λ * K_BV / L := div_nonneg (mul_nonneg hΛnn hK10) hLpos.le
              have hΛterm4 : 0 ≤ 4 * Λ * K_BV / L := by
                have htmp : 0 ≤ 4 * (Λ * K_BV / L) := mul_nonneg (by norm_num) hΛterm
                convert htmp using 1
                ring
              have hNnn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
              dsimp [K]
              nlinarith [hK10, hΛterm4, hNnn]
        _ ≤ - (N : ℝ) * Real.log 2 * 2 - 2 * Real.log 2 * pLow := by
              have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
              have hlog2_le_one : Real.log 2 ≤ 1 := by
                have h_log : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
                linarith
              have hp_half : pLow ≤ 1 := by linarith
              have hp_nonneg : 0 ≤ pLow := hlow.le
              have hprod : 2 * Real.log 2 * pLow ≤ 2 := by nlinarith
              nlinarith
        _ = (- (N : ℝ) * Real.log 2 * 2 / pLow - 2 * Real.log 2) * pLow := by
              field_simp [hp_ne]
      exact le_of_mul_le_mul_right hmul hp0

    have h_exp_nonpos : H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1) + Real.log (k : ℝ) ≤ 0 := by
      have h1 : (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1) ≤ - (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)) - Real.log (k : ℝ) := by
        have h2 : (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1) ≤ (N : ℝ) / 128 + pLow / 128 - (K / pLow) * 1 := by
          have henv : 1 ≤ effEnv 1 sigma m + 1 := h_env_bound
          have hK_pos : 0 ≤ K / pLow := div_nonneg (by exact hK_BV_4.trans' (by norm_num)) hlow.le
          have h3 : (K / pLow) * 1 ≤ (K / pLow) * (effEnv 1 sigma m + 1) := mul_le_mul_of_nonneg_left henv hK_pos
          linarith
        calc (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1)
          ≤ (N : ℝ) / 128 + pLow / 128 - (K / pLow) * 1 := h2
          _ = (N : ℝ) / 128 + pLow / 128 - (K / pLow) := by ring
          _ ≤ - (N : ℝ) * Real.log 2 * 2 / pLow - 2 * Real.log 2 := h_K_bound
          _ ≤ - (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ)) - Real.log (k : ℝ) := h_RHS
      linarith

    have h_exp_le_1 : Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1) + Real.log (k : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr h_exp_nonpos
    have h_exp_split : Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1)) * (k : ℝ) = Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1) + Real.log (k : ℝ)) := by
      rw [Real.exp_add, Real.exp_log (by exact_mod_cast h_k_ge_1)]
    calc Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1)) * (k : ℝ)
      = Real.exp (H (q + (θ : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + (pLow / 8) * ζ ^ 2 * (m : ℝ) - (K / pLow) * (effEnv 1 sigma m + 1) + Real.log (k : ℝ)) := h_exp_split
      _ ≤ 1 := h_exp_le_1
      _ ≤ (V Icard k θ : ℝ) := hk_le_V

  · have h_Nm_le_m : Nm ≤ m := not_lt.mp hm_cases
    have hm1 : 1 ≤ m := le_trans (Nat.le_add_left 1 _) h_Nm_le_m
    have h_N_le_Icard : N ≤ Icard := by
      have hlt : (N : ℝ) / pLow ≤ (Nm : ℝ) := by
        have hB : (N : ℝ) / pLow ≤ (⌈(N : ℝ) / pLow⌉₊ : ℝ) := Nat.le_ceil _
        have hC : (⌈(N : ℝ) / pLow⌉₊ : ℝ) ≤ (Nm : ℝ) := by
          dsimp [Nm]
          exact_mod_cast Nat.le_succ _
        exact le_trans hB hC
      have : (N : ℝ) ≤ pLow * (Nm : ℝ) := by
        rw [mul_comm]
        exact (div_le_iff₀ hlow).mp hlt
      have hNm_m : (Nm : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr h_Nm_le_m
      have hpm : pLow * (Nm : ℝ) ≤ pLow * (m : ℝ) := mul_le_mul_of_nonneg_left hNm_m hlow.le
      have : (N : ℝ) ≤ (Icard : ℝ) := le_trans (le_trans this hpm) hIlow
      exact Nat.cast_le.mp this

    have h_theta_bound : (θ : ℝ) ≤ pLow * ζ * (m : ℝ) / 2 := by
      have h1 : θ ≤ ⌊pLow * ζ * (m : ℝ) / 2⌋₊ := min_le_left _ _
      have hnn : (0 : ℝ) ≤ pLow * ζ * (m : ℝ) / 2 := by
        apply div_nonneg _ (by norm_num)
        exact mul_nonneg (mul_nonneg hlow.le hζpos.le) (Nat.cast_nonneg m)
      calc (θ : ℝ) ≤ (⌊pLow * ζ * (m : ℝ) / 2⌋₊ : ℝ) := Nat.cast_le.mpr h1
        _ ≤ pLow * ζ * (m : ℝ) / 2 := Nat.floor_le hnn

    have hIcard_pos : (0 : ℝ) < (Icard : ℝ) := by
      have hpm : (0 : ℝ) < pLow * (m : ℝ) := by
        apply mul_pos hlow; exact_mod_cast hm1
      exact lt_of_lt_of_le hpm hIlow
    have h_theta_Icard : (θ : ℝ) / (Icard : ℝ) ≤ ζ / 2 := by
      rw [div_le_div_iff₀ hIcard_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [h_theta_bound, mul_le_mul_of_nonneg_left hIlow hζpos.le]

    rcases Nat.eq_zero_or_pos k with hk0 | h_k_ge_1
    · subst hk0
      simp only [Nat.cast_zero, mul_zero]
      exact Nat.cast_nonneg _
    have hkn : k ≤ 2 ^ Icard := by
      have hexp : Real.exp (H (q - ζ) * (Icard : ℝ)) ≤ ((2 ^ Icard : ℕ) : ℝ) := by
        have h1 : H (q - ζ) * (Icard : ℝ) ≤ Real.log 2 * (Icard : ℝ) :=
          mul_le_mul_of_nonneg_right Real.binEntropy_le_log_two (Nat.cast_nonneg _)
        calc Real.exp (H (q - ζ) * (Icard : ℝ))
              ≤ Real.exp (Real.log 2 * (Icard : ℝ)) := Real.exp_le_exp.mpr h1
          _ = (2 : ℝ) ^ Icard := by
                rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
          _ = ((2 ^ Icard : ℕ) : ℝ) := by push_cast; ring
      exact_mod_cast le_trans hk hexp
    obtain ⟨t, ht_max, hk_le, ht_lt, htV⟩ := hVPlus Icard k θ h_k_ge_1 hkn
    have h_wit := hN Icard h_N_le_Icard q ζ hqmin hqmax hζpos hζle θ h_theta_Icard k h_k_ge_1 hk t ht_max hk_le ht_lt
    rcases h_wit with ⟨hsafe1, hsafe2, harad⟩

    have hmpos : 1 ≤ m := hm1
    have hk_succ : (k : ℝ) ≤ ((ball (∅ : Cube Icard) (t + 1)).card : ℝ) := by
      exact_mod_cast (r3_vplus_witness_succ_card Icard k t ht_lt (by omega)).le

    have hqle_half : q ≤ 1 / 2 := le_of_lt (lt_of_le_of_lt hqmax h3)
    have henv : 1 ≤ effEnv 1 sigma m + 1 := by
      have : 0 ≤ effEnv 1 sigma m := effEnv_nonneg 1 sigma hsigma.1 m
      linarith
    have hIpos : 0 < (Icard : ℝ) := lt_of_lt_of_le (mul_pos hlow (by exact_mod_cast hm1)) hIlow
    have hLog_nn : 0 ≤ Real.log ((1 - q / 2) / (q / 2)) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; nlinarith)
    have hLog_le : Real.log ((1 - q / 2) / (q / 2)) ≤ Λ := by
      apply Real.log_le_log (div_pos (by linarith) (by linarith))
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hqmin]
    have hmIcard : (m : ℝ) / (Icard : ℝ) ≤ 1 / pLow := by
      rw [div_le_div_iff₀ hIpos hlow]
      nlinarith
    have hIcard_le_m_nat : Icard ≤ m := by
      have hreal : (Icard : ℝ) ≤ (m : ℝ) := by
        have hpm_nonneg : 0 ≤ pLow * (m : ℝ) :=
          mul_nonneg hlow.le (Nat.cast_nonneg _)
        linarith [hIhigh]
      exact Nat.cast_le.mp hreal
    have hvSlack_Icard_le :
        vSlack Icard ≤ (4 * K_BV) * (effEnv 1 sigma m + 1) := by
      have hI2_le_3m_nat : Icard + 2 ≤ 3 * m := by omega
      have hI2_le_3m : (Icard : ℝ) + 2 ≤ 3 * (m : ℝ) := by
        exact_mod_cast hI2_le_3m_nat
      have hmpos' : 0 < (m : ℝ) := by exact_mod_cast hm1
      have hlogI2_le : Real.log ((Icard : ℝ) + 2) ≤
          Real.log 3 + Real.log (m : ℝ) := by
        calc Real.log ((Icard : ℝ) + 2)
            ≤ Real.log (3 * (m : ℝ)) :=
                Real.log_le_log (by positivity) hI2_le_3m
          _ = Real.log 3 + Real.log (m : ℝ) := by
                rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hmpos'.ne']
      have hlog3_le_two : Real.log 3 ≤ 2 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        norm_num at h ⊢
        exact h
      have hlogI2_add :
          Real.log ((Icard : ℝ) + 2) + 1 ≤ 4 * (effEnv 1 sigma m + 1) := by
        have hlogm_le := hsigma_log m hm1
        have hsigma_le : sigma m ≤ effEnv 1 sigma m := le_effEnv 1 sigma m
        have henv0 : 0 ≤ effEnv 1 sigma m := effEnv_nonneg 1 sigma hsigma.1 m
        calc Real.log ((Icard : ℝ) + 2) + 1
            ≤ Real.log 3 + Real.log (m : ℝ) + 1 := by linarith
          _ ≤ sigma m + 3 := by linarith
          _ ≤ effEnv 1 sigma m + 3 := by linarith
          _ ≤ 4 * (effEnv 1 sigma m + 1) := by nlinarith
      unfold vSlack effLog
      calc K_BV * (Real.log ((Icard : ℝ) + 2) + 1)
          ≤ K_BV * (4 * (effEnv 1 sigma m + 1)) :=
              mul_le_mul_of_nonneg_left hlogI2_add hK10
        _ = (4 * K_BV) * (effEnv 1 sigma m + 1) := by ring

    have h_term1 : 2 * ζ ≤ (1 / pLow) * (effEnv 1 sigma m + 1) := by
      have h_zeta_bound : 2 * ζ ≤ 1 := by linarith [hζle, hqle_half]
      calc 2 * ζ ≤ 1 := h_zeta_bound
        _ ≤ 2 := by linarith
        _ ≤ 1 / pLow := by rw [le_div_iff₀ hlow]; linarith
        _ ≤ (1 / pLow) * (effEnv 1 sigma m + 1) := by
          have : 1 / pLow ≤ (1 / pLow) * (effEnv 1 sigma m + 1) := by
            nth_rw 1 [← mul_one (1 / pLow)]
            apply mul_le_mul_of_nonneg_left henv (by positivity)
          exact this

    have h_term2 : (m : ℝ) * ((vSlack Icard) / ((Icard : ℝ) * L)) * Real.log ((1 - q / 2) / (q / 2)) ≤ ((4 * Λ * K_BV / L) / pLow) * (effEnv 1 sigma m + 1) := by
      calc (m : ℝ) * ((vSlack Icard) / ((Icard : ℝ) * L)) * Real.log ((1 - q / 2) / (q / 2))
        = ((m : ℝ) / (Icard : ℝ)) * (vSlack Icard / L) * Real.log ((1 - q / 2) / (q / 2)) := by ring
        _ ≤ (1 / pLow) * (vSlack Icard / L) * Λ := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hmIcard
              (div_nonneg (hvsub.1 Icard) hLpos.le)
          · exact hLog_le
          · exact hLog_nn
          · exact mul_nonneg (div_nonneg zero_le_one hlow.le)
              (div_nonneg (hvsub.1 Icard) hLpos.le)
        _ = (Λ / (pLow * L)) * vSlack Icard := by ring
        _ ≤ (Λ / (pLow * L)) * ((4 * K_BV) * (effEnv 1 sigma m + 1)) := by
          apply mul_le_mul_of_nonneg_left hvSlack_Icard_le
          apply div_nonneg
          · dsimp [Λ]
            apply Real.log_nonneg
            rw [one_le_div (by linarith)]
            linarith
          · exact mul_nonneg hlow.le hLpos.le
        _ = ((4 * Λ * K_BV / L) / pLow) * (effEnv 1 sigma m + 1) := by ring

    have h_term3 : (Icard : ℝ) * (H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ))) ≤ (1 / pLow) * (effEnv 1 sigma m + 1) := by
      have hshift : H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ)) ≤ H (1 / (Icard : ℝ)) := by
        have hle1 : (t : ℝ) / (Icard : ℝ) + 1 / (Icard : ℝ) ≤ 1 := by
          rw [← add_div, div_le_one hIpos]
          push_cast
          exact_mod_cast (le_trans hsafe2 (by omega))
        have := r3_H_shift_le (a := (t : ℝ) / (Icard : ℝ)) (δ := 1 / (Icard : ℝ)) (by positivity) (by positivity) hle1
        rwa [← add_div] at this
      calc (Icard : ℝ) * (H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ)))
        ≤ (Icard : ℝ) * H (1 / (Icard : ℝ)) := mul_le_mul_of_nonneg_left hshift hIpos.le
        _ ≤ Real.log (Icard : ℝ) + 1 := by
          exact r3_eff_nH_inv_le_log_add_one Icard (Nat.cast_pos.mp hIpos)
        _ ≤ Real.log (m : ℝ) + 1 := by
          have hlog_le : Real.log (Icard : ℝ) ≤ Real.log (m : ℝ) :=
            Real.log_le_log hIpos (by exact_mod_cast hIcard_le_m_nat)
          linarith
        _ ≤ sigma m + 1 := by linarith [hsigma_log m hm1]
        _ ≤ effEnv 1 sigma m + 1 := by
          linarith [le_effEnv 1 sigma m]
        _ ≤ effEnv 1 sigma m + 1 := by linarith
        _ ≤ (1 / pLow) * (effEnv 1 sigma m + 1) := by
          nth_rw 1 [← one_mul (effEnv 1 sigma m + 1)]
          apply mul_le_mul_of_nonneg_right (by rw [le_div_iff₀ hlow]; linarith) (by linarith)

    have h_term4 : 2 * (vSlack Icard) ≤ ((8 * K_BV) / pLow) * (effEnv 1 sigma m + 1) := by
      calc 2 * (vSlack Icard : ℝ) ≤ 2 * ((4 * K_BV) * (effEnv 1 sigma m + 1)) := mul_le_mul_of_nonneg_left hvSlack_Icard_le (by norm_num)
        _ = (8 * K_BV) * (effEnv 1 sigma m + 1) := by ring
        _ ≤ ((8 * K_BV) / pLow) * (effEnv 1 sigma m + 1) := by
          apply mul_le_mul_of_nonneg_right
          · rw [le_div_iff₀ hlow]
            calc 8 * K_BV * pLow ≤ 8 * K_BV * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              _ = 8 * K_BV := by ring
          · linarith

    have h_LHS : 2 * ζ + (m : ℝ) * ((vSlack Icard) / ((Icard : ℝ) * L)) * Real.log ((1 - q / 2) / (q / 2)) + (Icard : ℝ) * (H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ))) + 2 * (vSlack Icard) ≤ ((4 * Λ * K_BV / L + 2 + 8 * K_BV) / pLow) * (effEnv 1 sigma m + 1) := by
      calc 2 * ζ + (m : ℝ) * ((vSlack Icard) / ((Icard : ℝ) * L)) * Real.log ((1 - q / 2) / (q / 2)) + (Icard : ℝ) * (H ((t + 1 : ℝ) / (Icard : ℝ)) - H ((t : ℝ) / (Icard : ℝ))) + 2 * (vSlack Icard)
        _ ≤ (1 / pLow) * (effEnv 1 sigma m + 1) + ((4 * Λ * K_BV / L) / pLow) * (effEnv 1 sigma m + 1) + (1 / pLow) * (effEnv 1 sigma m + 1) + ((8 * K_BV) / pLow) * (effEnv 1 sigma m + 1) := by
          apply add_le_add
          · apply add_le_add
            · apply add_le_add
              · exact h_term1
              · exact h_term2
            · exact h_term3
          · exact h_term4
        _ = ((4 * Λ * K_BV / L + 2 + 8 * K_BV) / pLow) * (effEnv 1 sigma m + 1) := by ring

    have h_RHS : ((4 * Λ * K_BV / L + 2 + 8 * K_BV) / pLow) * (effEnv 1 sigma m + 1) ≤ (K / pLow) * (effEnv 1 sigma m + 1) - (pLow / 8) * ζ ^ 2 * (m : ℝ) + (pLow / 2) * ζ ^ 2 * (m : ℝ) := by
      have h1 : ((4 * Λ * K_BV / L + 2 + 8 * K_BV) / pLow) * (effEnv 1 sigma m + 1) ≤ (K / pLow) * (effEnv 1 sigma m + 1) := by
        have hcoef :
            4 * Λ * K_BV / L + 2 + 8 * K_BV ≤ K := by
          dsimp [K]
          have hNlog : 0 ≤ (N : ℝ) * Real.log 2 * 2 :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
              (by norm_num)
          have hNnn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
          nlinarith [hK10, hNlog, hNnn]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hcoef hlow.le) (by linarith)
      have h2 : 0 ≤ - (pLow / 8) * ζ ^ 2 * (m : ℝ) + (pLow / 2) * ζ ^ 2 * (m : ℝ) := by
        have heq :
            - (pLow / 8) * ζ ^ 2 * (m : ℝ) + (pLow / 2) * ζ ^ 2 * (m : ℝ) =
              (3 / 8 * pLow) * ζ ^ 2 * (m : ℝ) := by ring
        rw [heq]
        positivity
      exact le_trans h1 (by linarith [h2])

    exact (r3_fiber_growth_safe_bound vSlack hvsub hvol ⟨qMin, qMax, s0, mu0, sigma⟩ hvalid pLow hlow hhigh m hmpos q hqmax
      Icard hIlow hIhigh ζ hζpos hζle hζscale L hLpos k θ rfl t hsafe1 hsafe2 harad
      hk_succ htV ((K / pLow) * (effEnv 1 sigma m + 1) - (pLow / 8) * ζ ^ 2 * (m : ℝ) + (pLow / 2) * ζ ^ 2 * (m : ℝ)) (le_trans h_LHS h_RHS)).trans' (by
        apply mul_le_mul_of_nonneg_right
        apply Real.exp_le_exp.mpr
        linarith
        exact Nat.cast_nonneg _)

/-
Effective sparse-fiber mass bound: for any admissible `ζ`, the total
`proj Iᶜ`-mass of fibers below the density threshold `exp(H(q-ζ)·|I|)`
decays like `exp(-(pLow/8)·ζ²·m + (K/pLow)·(effEnv 1 σ m + 1))`.

This is the explicit (σ- and pLow-uniform) counterpart of the v0.2
`r3_sparse_fibers_mass`, built from the already-proved effective growth
leaf `r3_fiber_growth_V_bound_eff`, the pinned neighborhood budget
`r3_sparse_neighborhood_budget`, and the fiber Harper embedding
`r3_fiber_harper`.
-/
lemma r3_sparse_mass_eff (hBV : BallVolumeTwoSidedEff)
    (hVPlus : VPlusStatement) (hIVC : InteriorVolumeCalculusEff)
    (qMin qMax s0 mu0 : ℝ)
    (h1 : 0 < qMin) (h2 : qMin ≤ qMax) (h3 : qMax < 1 / 2)
    (h4 : 0 < s0) (h5 : 0 < mu0) (h6 : qMax + s0 ≤ 1 / 2 - mu0) :
    ∃ K : ℝ, 1 ≤ K ∧
    ∀ (pLow : ℝ), 0 < pLow → pLow ≤ 1 / 2 →
    ∀ (sigma : ℕ → ℝ), Sublinear sigma →
      (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
      pinned ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) →
        (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ q / 2 → ζ ≤ 2 * s0 / pLow →
      (∑ z ∈ (A.image (proj Iᶜ)).filter (fun z =>
          (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
            Real.exp (H (q - ζ) * (I.card : ℝ))),
        pOn A (proj Iᶜ) z) ≤
        Real.exp (- (pLow / 8) * ζ ^ 2 * (m : ℝ) +
          (K / pLow) * (effEnv 1 sigma m + 1)) := by
  by_contra h_contra;
  -- Apply the lemma `r3_fiber_growth_V_bound_eff` to obtain the existence of such a K.
  obtain ⟨K, hK⟩ := r3_fiber_growth_V_bound_eff hBV hVPlus hIVC qMin qMax s0 mu0 h1 h2 h3 h4 h5 h6;
  refine' h_contra ⟨ K + 2, by linarith, fun pLow hpLow hpLow' sigma hsigma hlog m A q hA hfat hpinned I hIlow hIhigh ζ hζpos hζle hζscale => _ ⟩;
  -- Apply the lemma `r3_fiber_harper` to obtain the inequality for each fiber.
  have h_fiber_ineq : ∀ z ∈ (A.image (proj Iᶜ)).filter (fun z => ((A.filter fun x => proj Iᶜ x = z).card : ℝ) ≤ Real.exp (H (q - ζ) * (I.card : ℝ))), (V I.card ((A.filter fun x => proj Iᶜ x = z).card) (min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (s0 * (m : ℝ))) : ℕ) : ℝ) ≤ ((neighborhood (min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (s0 * (m : ℝ))) : ℕ) (A.filter fun x => proj Iᶜ x = z)).filter (fun y => proj Iᶜ y = z)).card := by
    exact fun z hz => Nat.cast_le.mpr <| r3_fiber_harper A I z _;
  -- Apply the lemma `r3_fiber_growth_V_bound_eff` to obtain the inequality for each fiber and sum them up.
  have h_sum_ineq : Real.exp (H (q + (min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (s0 * (m : ℝ))) : ℝ) / (m : ℝ)) * (m : ℝ) - H q * (m : ℝ) + (pLow / 8) * ζ ^ 2 * (m : ℝ) - K / pLow * (effEnv 1 sigma m + 1)) * (A.card : ℝ) * (∑ z ∈ (A.image (proj Iᶜ)).filter (fun z => ((A.filter fun x => proj Iᶜ x = z).card : ℝ) ≤ Real.exp (H (q - ζ) * (I.card : ℝ))), pOn A (proj Iᶜ) z) ≤ Real.exp (H (q + (min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (s0 * (m : ℝ))) : ℝ) / (m : ℝ)) * (m : ℝ) + sigma m) := by
    have h_sum_ineq : ∑ z ∈ (A.image (proj Iᶜ)).filter (fun z => ((A.filter fun x => proj Iᶜ x = z).card : ℝ) ≤ Real.exp (H (q - ζ) * (I.card : ℝ))), (V I.card ((A.filter fun x => proj Iᶜ x = z).card) (min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (s0 * (m : ℝ))) : ℕ) : ℝ) ≤ Real.exp (H (q + (min ⌊pLow * ζ * (m : ℝ) / 2⌋₊ (Nat.ceil (s0 * (m : ℝ))) : ℝ) / (m : ℝ)) * (m : ℝ) + sigma m) := by
      refine' le_trans ( Finset.sum_le_sum h_fiber_ineq ) _;
      convert r3_sparse_neighborhood_budget ⟨ qMin, qMax, s0, mu0, sigma ⟩ A q hpinned I ( min ⌊pLow * ζ * m / 2⌋₊ ⌈s0 * m⌉₊ ) ( min_le_right _ _ ) _ using 1;
      norm_num [ Nat.cast_min ];
    refine le_trans ?_ h_sum_ineq;
    rw [ Finset.mul_sum _ _ _ ];
    refine Finset.sum_le_sum fun z hz => ?_;
    convert hK.2 pLow hpLow hpLow' sigma hsigma hlog m q hfat.2.2.1 hfat.2.2.2.1 I.card hIlow hIhigh ζ hζpos hζle hζscale _ _ using 1;
    · unfold pOn; ring;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, hA.ne_empty ] ; ring;
      convert rfl;
    · exact Finset.mem_filter.mp hz |>.2;
  -- Apply the lemma `r3_eff_nH_inv_le_log_add_one` to obtain the inequality for the cardinality of A.
  have h_card_ineq : Real.exp (H q * (m : ℝ) - sigma m) ≤ (A.card : ℝ) := by
    have := hfat.2.2.2.2;
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by exact Nat.cast_pos.mpr hA.card_pos ), Real.log_exp ] ; linarith [ abs_le.mp this ];
  contrapose! h_sum_ineq;
  refine' lt_of_le_of_lt _ ( mul_lt_mul_of_pos_left h_sum_ineq _ );
  · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_card_ineq <| Real.exp_nonneg _ ) <| Real.exp_nonneg _ );
    norm_num [ ← Real.exp_add ] ; ring_nf ; norm_num [ hpLow.ne' ];
    have h_sigma_le_effGeo : sigma m ≤ effGeo sigma m := by
      exact le_max_left _ _;
    nlinarith [ inv_pos.mpr hpLow, mul_inv_cancel₀ hpLow.ne', show ( 0 : ℝ ) ≤ effGeo sigma m from effGeo_nonneg sigma m ];
  · exact mul_pos ( Real.exp_pos _ ) ( Nat.cast_pos.mpr hA.card_pos )

/-
The residual mass envelope `m·exp(-2√m)` is bounded by a constant.
-/
private lemma r3_eff_m_mul_exp_neg_two_sqrt_le_one (m : ℕ) :
    (m : ℝ) * Real.exp (-2 * Real.sqrt (m : ℝ)) ≤ 1 := by
  rcases m with ( _ | _ | n ) <;> norm_num at * ; ring_nf at *;
  rw [ Real.exp_neg ];
  field_simp;
  rw [ two_mul, Real.exp_add ];
  nlinarith [ Real.add_one_le_exp ( Real.sqrt ( 2 + n ) ), Real.sqrt_nonneg ( 2 + n ), Real.mul_self_sqrt ( show 0 ≤ 2 + ( n : ℝ ) by positivity ) ]

/-
`√m ≤ effEnv 1 σ m` for nonnegative slacks.
-/
private lemma r3_eff_sqrt_le_effEnv1 (sigma : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ sigma n) (m : ℕ) :
    Real.sqrt (m : ℝ) ≤ effEnv 1 sigma m := by
  refine' le_max_of_le_right _;
  exact Real.sqrt_le_sqrt <| by nlinarith! [ h0 m ] ;

/-
Geometric-mean lower bound on grade 2: `√((effEnv 1 σ m + 1)·m) ≤ effEnv 2 σ m`.
-/
private lemma r3_eff_sqrt_effEnv1_mul_le_effEnv2 (sigma : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ sigma n) (m : ℕ) :
    Real.sqrt ((effEnv 1 sigma m + 1) * (m : ℝ)) ≤ effEnv 2 sigma m := by
  refine' le_trans _ ( le_max_right _ _ );
  exact Real.sqrt_le_sqrt <| mul_le_mul_of_nonneg_left ( by linarith ) <| add_nonneg ( effEnv_nonneg 1 sigma h0 m ) zero_le_one

/-
`m^{3/4} = √(√m·m) ≤ effEnv 2 σ m`.
-/
private lemma r3_eff_m34_le_effEnv2 (sigma : ℕ → ℝ)
    (h0 : ∀ n, 0 ≤ sigma n) (m : ℕ) :
    Real.sqrt (Real.sqrt (m : ℝ) * (m : ℝ)) ≤ effEnv 2 sigma m := by
  refine' le_trans _ ( le_max_right _ _ );
  exact Real.sqrt_le_sqrt ( by nlinarith [ r3_eff_sqrt_le_effEnv1 sigma h0 m, Real.sqrt_nonneg m, Real.sq_sqrt ( Nat.cast_nonneg m ) ] )

/-
Case-1 (mass regime) Lipschitz bound: the diagonal `ζ·m` is dominated by
grade 2.  Here `ζ = √(16·((K0/pLow)·(E+1)+√m)/(pLow·m))`.
-/
private lemma r3_eff_zeta_m_bound (pLow K0 E E2 M : ℝ)
    (hpLow : 0 < pLow) (hpLow1 : pLow ≤ 1) (hK0 : 0 ≤ K0)
    (hE : 0 ≤ E) (hM : 0 ≤ M) (hE2 : 0 ≤ E2)
    (hsqE : Real.sqrt ((E + 1) * M) ≤ E2)
    (hsqm : Real.sqrt (Real.sqrt M * M) ≤ E2) :
    Real.sqrt (16 * ((K0 / pLow) * (E + 1) + Real.sqrt M) / (pLow * M)) * M ≤
      (4 * (Real.sqrt K0 + 1) / pLow) * E2 := by
  by_cases hM : M = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · positivity;
  · -- Simplify the left-hand side of the inequality.
    suffices h_simp : Real.sqrt ((K0 / pLow * (E + 1) + Real.sqrt M) * M / pLow) ≤ (Real.sqrt K0 + 1) / pLow * E2 by
      convert mul_le_mul_of_nonneg_left h_simp ( show 0 ≤ 4 by norm_num ) using 1 <;> ring ; norm_num [ hpLow.le, hpLow.ne', hM ] ; ring;
      field_simp;
      rw [ show M * ( K0 * ( 1 + E ) + pLow * Real.sqrt M ) / pLow ^ 2 = ( ( K0 * ( 1 + E ) + pLow * Real.sqrt M ) / pLow ) * ( M / pLow ) by ring, Real.sqrt_mul ( by positivity ), Real.sqrt_div ( by positivity ) ] ; ring ; norm_num [ hpLow.le, hpLow.ne' ] ; ring;
      rw [ Real.sq_sqrt ( by positivity ) ];
    -- Apply the subadditivity of the square root function.
    have h_subadd : Real.sqrt ((K0 / pLow * (E + 1) + Real.sqrt M) * M / pLow) ≤ Real.sqrt ((K0 / pLow) * (E + 1) * M / pLow) + Real.sqrt (Real.sqrt M * M / pLow) := by
      rw [ Real.sqrt_le_iff ] ; ring_nf ; norm_num;
      exact ⟨ by positivity, by nlinarith [ show 0 ≤ Real.sqrt ( K0 * ( pLow ^ 2 ) ⁻¹ * E * M + K0 * ( pLow ^ 2 ) ⁻¹ * M ) * ( Real.sqrt ( pLow⁻¹ * M ) * Real.sqrt ( Real.sqrt M ) ) by positivity, Real.mul_self_sqrt ( show 0 ≤ K0 * ( pLow ^ 2 ) ⁻¹ * E * M + K0 * ( pLow ^ 2 ) ⁻¹ * M by positivity ), Real.mul_self_sqrt ( show 0 ≤ pLow⁻¹ * M by positivity ), Real.mul_self_sqrt ( show 0 ≤ Real.sqrt M by positivity ) ] ⟩;
    -- Apply the given bounds to the simplified expression further.
    have h_bound2 : Real.sqrt (Real.sqrt M * M / pLow) ≤ E2 / pLow := by
      rw [ Real.sqrt_le_iff ] at *;
      field_simp;
      exact ⟨ by linarith, by nlinarith [ show 0 ≤ Real.sqrt M * Real.sqrt ( Real.sqrt M ) by positivity, show 0 ≤ Real.sqrt M * M by positivity, Real.mul_self_sqrt ( show 0 ≤ M by positivity ), Real.mul_self_sqrt ( show 0 ≤ Real.sqrt M by positivity ), Real.sqrt_nonneg M, Real.sqrt_nonneg ( Real.sqrt M ), mul_le_mul_of_nonneg_left hpLow1 ( Real.sqrt_nonneg M ), mul_le_mul_of_nonneg_left hpLow1 ( Real.sqrt_nonneg ( Real.sqrt M ) ) ] ⟩;
    -- Apply the given bounds to the simplified expression further for the first term.
    have h_bound1 : Real.sqrt (K0 / pLow * (E + 1) * M / pLow) ≤ Real.sqrt K0 / pLow * E2 := by
      convert mul_le_mul_of_nonneg_left hsqE ( show 0 ≤ Real.sqrt K0 / pLow by positivity ) using 1 ; ring;
      rw [ show K0 * pLow⁻¹ ^ 2 * E * M + K0 * pLow⁻¹ ^ 2 * M = ( pLow⁻¹ * Real.sqrt K0 * Real.sqrt M * Real.sqrt ( 1 + E ) ) ^ 2 by rw [ mul_pow, mul_pow, mul_pow, Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity ] ; ring ] ; rw [ Real.sqrt_sq <| by positivity ];
    grind

/-
Case-2 (trivial regime) slack bound: when the diagonal would exceed the
admissible cap, the grade-2 envelope already dominates `H(q)·|I|`.
-/
private lemma r3_eff_trivial_slack (pLow K K0 E E2 M c2min : ℝ)
    (hpLow : 0 < pLow) (hMpos : 0 < M) (hc2min : 0 < c2min)
    (hK0 : 1 ≤ K0) (hE : 0 ≤ E) (hE2 : 0 ≤ E2)
    (hsqE : Real.sqrt ((E + 1) * M) ≤ E2) (hsqmE2 : Real.sqrt M ≤ E2)
    (hsplit : pLow * M * c2min ^ 2 / 16 < (K0 / pLow) * (E + 1) + Real.sqrt M)
    (hKb : 32 * Real.log 2 / c2min ^ 2 ≤ K)
    (hKc : Real.log 2 * Real.sqrt (32 * K0) / c2min ≤ K) :
    Real.log 2 * M ≤ (K / pLow) * (E2 + 1) := by
  rw [ div_le_iff₀ ( by positivity ) ] at *;
  rw [ div_mul_eq_mul_div, le_div_iff₀ ] at * <;> try positivity;
  by_cases hcase : pLow * M * c2min ^ 2 / 32 ≤ Real.sqrt M;
  · nlinarith [ show 0 < Real.sqrt M * c2min ^ 2 by positivity, Real.mul_self_sqrt ( show 0 ≤ M by positivity ), Real.log_pos one_lt_two, mul_le_mul_of_nonneg_left hcase <| show 0 ≤ pLow * c2min ^ 2 by positivity ];
  · -- From the sub-b inequality, we have $pLow^2 * M^2 * c2min^2 / (32 * K0) ≤ (E + 1) * M$.
    have hsubb : pLow^2 * M^2 * c2min^2 / (32 * K0) ≤ (E + 1) * M := by
      rw [ div_le_iff₀ ] <;> try positivity;
      rw [ div_add', lt_div_iff₀ ] at hsplit <;> nlinarith [ mul_pos hpLow hMpos, mul_pos hpLow hc2min, mul_pos hMpos hc2min, Real.sqrt_nonneg M, Real.sq_sqrt hMpos.le ];
    -- From the sub-b inequality, we have $E2 \geq pLow * M * c2min / \sqrt{32 * K0}$.
    have hE2_ge : E2 ≥ pLow * M * c2min / Real.sqrt (32 * K0) := by
      refine le_trans ?_ hsqE;
      refine Real.le_sqrt_of_sq_le ?_;
      convert hsubb using 1 ; rw [ div_pow, mul_pow, mul_pow, Real.sq_sqrt <| by positivity ];
    rw [ ge_iff_le, div_le_iff₀ ( by positivity ) ] at hE2_ge;
    nlinarith [ show 0 < pLow * M by positivity, show 0 < c2min by positivity, show 0 < Real.sqrt ( 32 * K0 ) by positivity, Real.mul_self_sqrt ( show 0 ≤ 32 * K0 by positivity ), Real.log_pos one_lt_two, mul_le_mul_of_nonneg_left hKc ( show 0 ≤ pLow * M by positivity ), mul_le_mul_of_nonneg_left hE2_ge ( show 0 ≤ pLow * M by positivity ) ]

/-- Effective expected-log fiber lower bound (σ- and pLow-uniform leaf;
the v0.2 proved counterpart is `r3_fiber_log_lower` in
`Reductions/R3Fiber.lean`).  One constant serves all window densities
and all admissible slacks; the `pLow⁻¹` factor pays the honest density cost, the grade-2 envelope dominates
`sigma + volume-log` unconditionally. -/
lemma r3_fiber_log_lower_eff (hBV : BallVolumeTwoSidedEff)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusEff)
    (qMin qMax s0 mu0 : ℝ)
    (h1 : 0 < qMin) (h2 : qMin ≤ qMax) (h3 : qMax < 1 / 2)
    (h4 : 0 < s0) (h5 : 0 < mu0) (h6 : qMax + s0 ≤ 1 / 2 - mu0) :
    ∃ K : ℝ, 1 ≤ K ∧
    ∀ (pLow : ℝ), 0 < pLow → pLow ≤ 1 / 2 →
    ∀ (sigma : ℕ → ℝ), Sublinear sigma →
      (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
      pinned ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) →
        (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      H q * (I.card : ℝ) - (K / pLow) * (effEnv 2 sigma m + 1) ≤
        ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
          Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
  classical
  obtain ⟨K0, hK0, hmass⟩ :=
    r3_sparse_mass_eff hBV hVPlus hVC qMin qMax s0 mu0 h1 h2 h3 h4 h5 h6
  obtain ⟨L, hL0, hLgap⟩ :
      ∃ L, 0 ≤ L ∧ ∀ a z : ℝ, qMin ≤ a → a ≤ qMax → 0 ≤ z → z ≤ a / 2 →
        H a - H (a - z) ≤ L * z := by
    have hsub_dummy : Sublinear (fun n : ℕ => Real.log ((n : ℝ) + 1)) := by
      refine Sublinear_of_le (fun n => ?_) (fun n => le_of_eq rfl) sublinear_log_succ
      exact Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
    have hvalid_dummy :
        validQData ⟨qMin, qMax, s0, mu0, fun n => Real.log ((n : ℝ) + 1)⟩ :=
      ⟨h1, h2, h3, h4, h5, h6, hsub_dummy, fun n hn =>
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_add_right n 1)⟩
    obtain ⟨L, hL0, hLgap⟩ :=
      r3_entropy_gap_lipschitz ⟨qMin, qMax, s0, mu0, fun n => Real.log ((n : ℝ) + 1)⟩
        hvalid_dummy
    exact ⟨L, hL0, hLgap⟩
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  set c2min : ℝ := min (qMin / 2) (4 * s0) with hc2min_def
  have hc2min_pos : 0 < c2min := lt_min (by linarith) (by linarith)
  set K : ℝ := 1 + K0 + 4 * L * (Real.sqrt K0 + 1) + 32 * Real.log 2 / c2min ^ 2 +
      Real.log 2 * Real.sqrt (32 * K0) / c2min with hK_def
  have ht1 : 0 ≤ 4 * L * (Real.sqrt K0 + 1) := by positivity
  have ht2 : 0 ≤ 32 * Real.log 2 / c2min ^ 2 := by positivity
  have ht3 : 0 ≤ Real.log 2 * Real.sqrt (32 * K0) / c2min := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; nlinarith [hK0, ht1, ht2, ht3]
  have hKa : 4 * L * (Real.sqrt K0 + 1) ≤ K := by rw [hK_def]; linarith [hK0, ht2, ht3]
  have hKb : 32 * Real.log 2 / c2min ^ 2 ≤ K := by rw [hK_def]; linarith [hK0, ht1, ht3]
  have hKc : Real.log 2 * Real.sqrt (32 * K0) / c2min ≤ K := by
    rw [hK_def]; linarith [hK0, ht1, ht2]
  have hK0pos : 0 < K0 := by linarith
  refine ⟨K, hK1, ?_⟩
  intro pLow hlow hhigh sigma hsub hlog m A q hA hfat hpinned I hIlow hIhigh
  have hsig0 : ∀ n, 0 ≤ sigma n := hsub.1
  have hE1n : 0 ≤ effEnv 1 sigma m := effEnv_nonneg 1 sigma hsig0 m
  have hE2n : 0 ≤ effEnv 2 sigma m := effEnv_nonneg 2 sigma hsig0 m
  have hqmin : qMin ≤ q := hfat.2.2.1
  have hqmax : q ≤ qMax := hfat.2.2.2.1
  have hqpos : 0 < q := by linarith
  have hMnn : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hIc_le_M : (I.card:ℝ) ≤ (m:ℝ) := by nlinarith [hIhigh, mul_nonneg hlow.le hMnn]
  have hHq_le : H q ≤ Real.log 2 := Real.binEntropy_le_log_two
  have hHq0 : 0 ≤ H q := Real.binEntropy_nonneg (by linarith) (by linarith [hqmax, h3])
  have hKpLow_ge1 : 1 ≤ K / pLow := by rw [le_div_iff₀ hlow]; nlinarith [hK1]
  have hExp0 : 0 ≤ ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
      Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
    refine Finset.sum_nonneg (fun z hz => ?_)
    have hfib_ne : (A.filter fun x => proj Iᶜ x = z).Nonempty := by
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    have hcard1 : (1:ℝ) ≤ ((A.filter fun x => proj Iᶜ x = z).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hfib_ne
    exact mul_nonneg (pOn_nonneg A (proj Iᶜ) z) (Real.log_nonneg hcard1)
  have hsq1 : Real.sqrt ((effEnv 1 sigma m + 1) * (m:ℝ)) ≤ effEnv 2 sigma m :=
    r3_eff_sqrt_effEnv1_mul_le_effEnv2 sigma hsig0 m
  have hsq2 : Real.sqrt (Real.sqrt (m:ℝ) * (m:ℝ)) ≤ effEnv 2 sigma m :=
    r3_eff_m34_le_effEnv2 sigma hsig0 m
  have hsqmE2 : Real.sqrt (m:ℝ) ≤ effEnv 2 sigma m :=
    le_trans (r3_eff_sqrt_le_effEnv1 sigma hsig0 m) (le_effGeo (effEnv 1 sigma) m)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: the window is trivial and the slack is nonnegative.
    have hI0 : I.card = 0 :=
      Nat.le_zero.mp ((Finset.card_le_univ I).trans_eq (by simp [hm0]))
    have hIc0 : (I.card:ℝ) = 0 := by rw [hI0]; simp
    have hslack : 0 ≤ (K / pLow) * (effEnv 2 sigma m + 1) :=
      mul_nonneg (div_nonneg (by linarith [hK1]) hlow.le) (by linarith [hE2n])
    rw [hIc0, mul_zero]
    linarith [hExp0, hslack]
  · have hMpos : 0 < (m:ℝ) := by exact_mod_cast hmpos
    have hEp1 : 0 < effEnv 1 sigma m + 1 := by linarith [hE1n]
    have hSpos : 0 < (K0 / pLow) * (effEnv 1 sigma m + 1) := mul_pos (div_pos hK0pos hlow) hEp1
    have hradnn : 0 ≤ 16 * ((K0 / pLow) * (effEnv 1 sigma m + 1) + Real.sqrt (m:ℝ)) /
        (pLow * (m:ℝ)) :=
      div_nonneg (by nlinarith [hSpos, Real.sqrt_nonneg (m:ℝ)]) (mul_pos hlow hMpos).le
    set zeta : ℝ := Real.sqrt (16 * ((K0 / pLow) * (effEnv 1 sigma m + 1) + Real.sqrt (m:ℝ)) /
        (pLow * (m:ℝ))) with hzeta_def
    have hzeta_pos : 0 < zeta := by
      rw [hzeta_def]; apply Real.sqrt_pos.mpr; apply div_pos
      · nlinarith [hSpos, Real.sqrt_nonneg (m:ℝ)]
      · exact mul_pos hlow hMpos
    have hzeta_nn : 0 ≤ zeta := hzeta_pos.le
    have hzsq : (pLow / 8) * zeta ^ 2 * (m:ℝ) =
        2 * ((K0 / pLow) * (effEnv 1 sigma m + 1) + Real.sqrt (m:ℝ)) := by
      rw [hzeta_def, Real.sq_sqrt hradnn]
      field_simp
      ring
    have hc2_pos : 0 < min (q / 2) (2 * s0 / pLow) := lt_min (by linarith) (by positivity)
    have hc2min_le_c2 : c2min ≤ min (q / 2) (2 * s0 / pLow) := by
      apply le_min
      · calc c2min ≤ qMin / 2 := by rw [hc2min_def]; exact min_le_left _ _
          _ ≤ q / 2 := by linarith
      · calc c2min ≤ 4 * s0 := by rw [hc2min_def]; exact min_le_right _ _
          _ ≤ 2 * s0 / pLow := by rw [le_div_iff₀ hlow]; nlinarith [h4, hhigh]
    by_cases hcase : zeta ≤ min (q / 2) (2 * s0 / pLow)
    · -- Mass regime: the diagonal `ζ` is admissible.
      have hz_q2 : zeta ≤ q / 2 := le_trans hcase (min_le_left _ _)
      have hz_sc : zeta ≤ 2 * s0 / pLow := le_trans hcase (min_le_right _ _)
      have hmassbd := hmass pLow hlow hhigh sigma hsub hlog m A q hA hfat hpinned I hIlow
        hIhigh zeta hzeta_pos hz_q2 hz_sc
      have hexp_le : -(pLow / 8) * zeta ^ 2 * (m:ℝ) +
          (K0 / pLow) * (effEnv 1 sigma m + 1) ≤ -2 * Real.sqrt (m:ℝ) := by
        nlinarith [hzsq, hSpos, Real.sqrt_nonneg (m:ℝ)]
      have hmule : (∑ z ∈ (A.image (proj Iᶜ)).filter (fun z =>
            (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) ≤
              Real.exp (H (q - zeta) * (I.card : ℝ))),
          pOn A (proj Iᶜ) z) ≤ Real.exp (-2 * Real.sqrt (m:ℝ)) :=
        le_trans hmassbd (Real.exp_le_exp.mpr hexp_le)
      have hqz_nn : 0 ≤ q - zeta := by linarith
      have hqz_le1 : q - zeta ≤ 1 := by linarith [hqmax, h3]
      have hT0 : 0 ≤ H (q - zeta) * (I.card : ℝ) :=
        mul_nonneg (Real.binEntropy_nonneg hqz_nn hqz_le1) (Nat.cast_nonneg _)
      have honce := r3_expected_log_from_sparse_mass_once A hA I q zeta
        (Real.exp (-2 * Real.sqrt (m:ℝ))) hT0 hmule
      have honce' : H (q - zeta) * (I.card : ℝ) -
          H (q - zeta) * (I.card : ℝ) * Real.exp (-2 * Real.sqrt (m:ℝ)) ≤
          ∑ z ∈ A.image (proj Iᶜ), pOn A (proj Iᶜ) z *
            Real.log (((A.filter fun x => proj Iᶜ x = z).card : ℝ)) := by
        have heq : H (q - zeta) * (I.card : ℝ) * (1 - Real.exp (-2 * Real.sqrt (m:ℝ))) =
            H (q - zeta) * (I.card : ℝ) -
              H (q - zeta) * (I.card : ℝ) * Real.exp (-2 * Real.sqrt (m:ℝ)) := by ring
        rw [heq] at honce; exact honce
      have hlip : H q - H (q - zeta) ≤ L * zeta := hLgap q zeta hqmin hqmax hzeta_nn hz_q2
      have hμ_nn : 0 ≤ Real.exp (-2 * Real.sqrt (m:ℝ)) := (Real.exp_pos _).le
      have hHqz_le : H (q - zeta) ≤ Real.log 2 := Real.binEntropy_le_log_two
      have hHqz_nn : 0 ≤ H (q - zeta) := Real.binEntropy_nonneg hqz_nn hqz_le1
      -- Loss piece 1: the Lipschitz term is grade 2.
      have hzm : zeta * (m:ℝ) ≤ (4 * (Real.sqrt K0 + 1) / pLow) * effEnv 2 sigma m := by
        rw [hzeta_def]
        exact r3_eff_zeta_m_bound pLow K0 (effEnv 1 sigma m) (effEnv 2 sigma m) (m:ℝ)
          hlow (by linarith) hK0pos.le hE1n (Nat.cast_nonneg m) hE2n hsq1 hsq2
      have hcoef : 4 * L * (Real.sqrt K0 + 1) / pLow ≤ K / pLow := by
        have := mul_le_mul_of_nonneg_right hKa (le_of_lt (inv_pos.mpr hlow))
        simpa [div_eq_mul_inv] using this
      have hLzm : L * zeta * (m:ℝ) ≤ (K / pLow) * effEnv 2 sigma m := by
        have hstep : L * zeta * (m:ℝ) ≤
            (4 * L * (Real.sqrt K0 + 1) / pLow) * effEnv 2 sigma m := by
          calc L * zeta * (m:ℝ) = L * (zeta * (m:ℝ)) := by ring
            _ ≤ L * ((4 * (Real.sqrt K0 + 1) / pLow) * effEnv 2 sigma m) :=
                mul_le_mul_of_nonneg_left hzm hL0
            _ = (4 * L * (Real.sqrt K0 + 1) / pLow) * effEnv 2 sigma m := by ring
        exact le_trans hstep (mul_le_mul_of_nonneg_right hcoef hE2n)
      -- Loss piece 2: the residual mass term is bounded by a constant.
      have hmn1 : (m:ℝ) * Real.exp (-2 * Real.sqrt (m:ℝ)) ≤ 1 :=
        r3_eff_m_mul_exp_neg_two_sqrt_le_one m
      have hres : Real.log 2 * (m:ℝ) * Real.exp (-2 * Real.sqrt (m:ℝ)) ≤ 1 := by
        have hprod : (m:ℝ) * Real.exp (-2 * Real.sqrt (m:ℝ)) ≥ 0 :=
          mul_nonneg hMnn hμ_nn
        nlinarith [hmn1, hlog2_le1, hlog2_pos.le, hprod]
      -- Combine.
      have hA1 : (H q - L * zeta) * (I.card : ℝ) ≤ H (q - zeta) * (I.card : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [hlip]) (Nat.cast_nonneg _)
      have hc_eq : (H q - L * zeta) * (I.card : ℝ) =
          H q * (I.card : ℝ) - L * zeta * (I.card : ℝ) := by ring
      have hA2 : L * zeta * (I.card : ℝ) ≤ L * zeta * (m:ℝ) :=
        mul_le_mul_of_nonneg_left hIc_le_M (mul_nonneg hL0 hzeta_nn)
      have hqz_ic : H (q - zeta) * (I.card : ℝ) ≤ Real.log 2 * (m:ℝ) :=
        mul_le_mul hHqz_le hIc_le_M (Nat.cast_nonneg _) hlog2_pos.le
      have hA3 : H (q - zeta) * (I.card : ℝ) * Real.exp (-2 * Real.sqrt (m:ℝ)) ≤
          Real.log 2 * (m:ℝ) * Real.exp (-2 * Real.sqrt (m:ℝ)) :=
        mul_le_mul_of_nonneg_right hqz_ic hμ_nn
      have hslack_split : (K / pLow) * effEnv 2 sigma m + 1 ≤
          (K / pLow) * (effEnv 2 sigma m + 1) := by
        have : (K / pLow) * (effEnv 2 sigma m + 1) =
            (K / pLow) * effEnv 2 sigma m + K / pLow := by ring
        rw [this]; linarith [hKpLow_ge1]
      linarith [honce', hA1, hc_eq, hA2, hA3, hLzm, hres, hslack_split]
    · -- Trivial regime: the diagonal exceeds the cap, so grade 2 dominates.
      push_neg at hcase
      have hz2 : zeta ^ 2 =
          16 * ((K0 / pLow) * (effEnv 1 sigma m + 1) + Real.sqrt (m:ℝ)) / (pLow * (m:ℝ)) := by
        rw [hzeta_def]; exact Real.sq_sqrt hradnn
      have hc2sq : (min (q / 2) (2 * s0 / pLow)) ^ 2 < zeta ^ 2 := by
        nlinarith [hcase, hc2_pos]
      have hcc : c2min ^ 2 ≤ (min (q / 2) (2 * s0 / pLow)) ^ 2 := by
        nlinarith [hc2min_le_c2, hc2min_pos, hc2_pos]
      have hsplit : pLow * (m:ℝ) * c2min ^ 2 / 16 <
          (K0 / pLow) * (effEnv 1 sigma m + 1) + Real.sqrt (m:ℝ) := by
        rw [hz2] at hc2sq
        rw [lt_div_iff₀ (mul_pos hlow hMpos)] at hc2sq
        nlinarith [hc2sq, mul_le_mul_of_nonneg_right hcc (mul_pos hlow hMpos).le]
      have htriv : Real.log 2 * (m:ℝ) ≤ (K / pLow) * (effEnv 2 sigma m + 1) :=
        r3_eff_trivial_slack pLow K K0 (effEnv 1 sigma m) (effEnv 2 sigma m) (m:ℝ) c2min
          hlow hMpos hc2min_pos hK0 hE1n hE2n hsq1 hsqmE2 hsplit hKb hKc
      have hHqIc : H q * (I.card : ℝ) ≤ Real.log 2 * (m:ℝ) :=
        mul_le_mul hHq_le hIc_le_M (Nat.cast_nonneg _) hlog2_pos.le
      linarith [hHqIc, htriv, hExp0]

lemma r3_cond_entropy_bound_eff (hBV : BallVolumeTwoSidedEff)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusEff)
    (qMin qMax s0 mu0 : ℝ)
    (h1 : 0 < qMin) (h2 : qMin ≤ qMax) (h3 : qMax < 1 / 2)
    (h4 : 0 < s0) (h5 : 0 < mu0) (h6 : qMax + s0 ≤ 1 / 2 - mu0) :
    ∃ K : ℝ, 1 ≤ K ∧
    ∀ (pLow : ℝ), 0 < pLow → pLow ≤ 1 / 2 →
    ∀ (sigma : ℕ → ℝ), Sublinear sigma →
      (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
      pinned ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
      ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) → (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      |uCondH A (proj I) (proj Iᶜ) - H q * (I.card : ℝ)| ≤
        (K / pLow) * (effEnv 2 sigma m + 1) := by
  classical
  obtain ⟨K, hK, hlower⟩ :=
    r3_fiber_log_lower_eff hBV hVPlus hVC qMin qMax s0 mu0 h1 h2 h3 h4 h5 h6
  refine ⟨K + 1, by linarith, ?_⟩
  intro pLow hlow hhigh sigma hsub hlog m A q hA hfat hpinned I hIlow hIhigh
  have hp2 : (0 : ℝ) < pLow ^ 2 := by positivity
  have hp2le : pLow ^ 2 ≤ 1 := by nlinarith
  have hIcard_le : I.card ≤ m := by
    simpa [Fintype.card_fin] using (Finset.card_le_univ I)
  have hcard_comp_nat : (Iᶜ).card = m - I.card := by
    simpa [Fintype.card_fin] using (Finset.card_compl I)
  have hcard_comp : ((Iᶜ).card : ℝ) = (m : ℝ) - (I.card : ℝ) := by
    rw [hcard_comp_nat]
    norm_num [Nat.cast_sub hIcard_le]
  have hIc_low : pLow * (m : ℝ) ≤ ((Iᶜ).card : ℝ) := by
    rw [hcard_comp]
    nlinarith
  have hIc_high : ((Iᶜ).card : ℝ) ≤ (1 - pLow) * (m : ℝ) := by
    rw [hcard_comp]
    nlinarith
  set Kp : ℝ := K / pLow with hKp_def
  have hKp1 : 1 ≤ Kp := by
    rw [hKp_def, le_div_iff₀ hlow]
    nlinarith
  let E := effEnv 2 sigma m + 1
  have hEnv0 : 0 ≤ effEnv 2 sigma m :=
    effEnv_nonneg 2 sigma hsub.1 m
  have hE0 : 0 ≤ E := by
    have h : 0 ≤ effEnv 2 sigma m + 1 := by linarith
    simpa [E] using h
  have hσ_le_E : sigma m ≤ E := by
    have h : sigma m ≤ effEnv 2 sigma m + 1 := by
      have := le_effEnv 2 sigma m
      linarith
    simpa [E] using h
  have hgap : Kp * E + E ≤ ((K + 1) / pLow) * E := by
    have hcoef : Kp + 1 ≤ (K + 1) / pLow := by
      rw [hKp_def, le_div_iff₀ hlow, add_mul, div_mul_cancel₀ _ (ne_of_gt hlow)]
      nlinarith
    nlinarith [hE0, hcoef]
  have hid_I := r3_eff_uCondH_eq_expected_log_fiber A hA I
  have hlow_I : H q * (I.card : ℝ) - Kp * E ≤ uCondH A (proj I) (proj Iᶜ) := by
    rw [hid_I]
    simpa [E, hKp_def] using
      hlower pLow hlow hhigh sigma hsub hlog m A q hA hfat hpinned I hIlow hIhigh
  have hid_Ic : uCondH A (proj Iᶜ) (proj I) =
      ∑ z ∈ A.image (proj I), pOn A (proj I) z *
        Real.log (((A.filter fun x => proj I x = z).card : ℝ)) := by
    have h := r3_eff_uCondH_eq_expected_log_fiber A hA Iᶜ
    simpa [compl_compl] using h
  have hlow_Ic : H q * ((Iᶜ).card : ℝ) - Kp * E ≤ uCondH A (proj Iᶜ) (proj I) := by
    rw [hid_Ic]
    have h := hlower pLow hlow hhigh sigma hsub hlog m A q hA hfat hpinned Iᶜ hIc_low hIc_high
    simpa [E, hKp_def, compl_compl] using h
  have hsubadd : uCondH A (proj Iᶜ) (proj I) ≤ uH A (proj Iᶜ) := by
    have h := uH_prod_le A hA (proj Iᶜ) (proj I)
    unfold uCondH
    linarith
  have hpair : uH A (fun x => (proj I x, proj Iᶜ x)) =
      uH A (proj (Finset.univ : Finset (Fin m))) :=
    r3_eff_uH_proj_pair_compl_eq_univ A I
  have hcond_eq : uCondH A (proj I) (proj Iᶜ) =
      uH A (proj (Finset.univ : Finset (Fin m))) - uH A (proj Iᶜ) := by
    unfold uCondH
    rw [hpair]
  have htotal :
      |uH A (proj (Finset.univ : Finset (Fin m))) - H q * (m : ℝ)| ≤ sigma m := by
    rw [uH_proj_univ A hA]
    exact hfat.2.2.2.2
  rw [abs_le] at htotal ⊢
  constructor
  · have hKp_le : Kp * E ≤ ((K + 1) / pLow) * E := by
      nlinarith [hgap, hE0]
    linarith [hlow_I, hE0, hKp_le]
  · have hup : uCondH A (proj I) (proj Iᶜ) ≤
        (H q * (m : ℝ) + sigma m) - (H q * ((Iᶜ).card : ℝ) - Kp * E) := by
      rw [hcond_eq]
      have h1' : uH A (proj Iᶜ) ≥ H q * ((Iᶜ).card : ℝ) - Kp * E :=
        le_trans hlow_Ic hsubadd
      linarith [htotal.2]
    have harith : (H q * (m : ℝ) + sigma m) -
          (H q * ((Iᶜ).card : ℝ) - Kp * E) =
        H q * (I.card : ℝ) + (sigma m + Kp * E) := by
      rw [hcard_comp]
      ring
    have hfinal : sigma m + Kp * E ≤ ((K + 1) / pLow) * E := by
      calc sigma m + Kp * E ≤ E + Kp * E := by linarith [hσ_le_E]
        _ = Kp * E + E := by ring
        _ ≤ ((K + 1) / pLow) * E := hgap
    linarith [hup]

private lemma r3_eff_from_cond_entropy (Q : QData) (pLow K : ℝ) (hK : 1 ≤ K)
    (hlow : 0 < pLow) (hhigh : pLow ≤ 1 / 2)
    (hcond : ∀ m (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty → fat Q m A q → pinned Q m A q →
        ∀ I : Finset (Fin m), pLow * (m : ℝ) ≤ (I.card : ℝ) → (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
        |uCondH A (proj I) (proj Iᶜ) - H q * (I.card : ℝ)| ≤ K * (effEnv 2 Q.sigma m + 1)) :
    ∀ m (A : Finset (Cube m)) (q : ℝ),
      A.Nonempty → fat Q m A q → pinned Q m A q →
      blockRegular m A q pLow ((K + 1) * (effEnv 2 Q.sigma m + 1)) := by
  intro m A q hA hfat hpinned
  refine ⟨hlow, hhigh, ?_⟩
  intro I hI_low hI_high
  classical
  have hIcard_le : I.card ≤ m := by
    simpa [Fintype.card_fin] using (Finset.card_le_univ I)
  have hcard_comp_nat : (Iᶜ).card = m - I.card := by
    simpa [Fintype.card_fin] using (Finset.card_compl I)
  have hcard_comp : ((Iᶜ).card : ℝ) = (m : ℝ) - (I.card : ℝ) := by
    rw [hcard_comp_nat]
    norm_num [Nat.cast_sub hIcard_le]
  have hIc_low : pLow * (m : ℝ) ≤ ((Iᶜ).card : ℝ) := by
    rw [hcard_comp]
    nlinarith
  have hIc_high : ((Iᶜ).card : ℝ) ≤ (1 - pLow) * (m : ℝ) := by
    rw [hcard_comp]
    nlinarith
  have hcondIc := hcond m A q hA hfat hpinned Iᶜ hIc_low hIc_high
  have hcondIc' :
      |uCondH A (proj Iᶜ) (proj I) - H q * ((Iᶜ).card : ℝ)| ≤ K * (effEnv 2 Q.sigma m + 1) := by
    simpa using hcondIc
  have hpair : uH A (fun x => (proj Iᶜ x, proj I x)) =
      uH A (proj (Finset.univ : Finset (Fin m))) := by
    simpa [compl_compl] using (r3_eff_uH_proj_pair_compl_eq_univ A Iᶜ)
  have hcond_eq : uCondH A (proj Iᶜ) (proj I) =
      uH A (proj (Finset.univ : Finset (Fin m))) - uH A (proj I) := by
    unfold uCondH
    rw [hpair]
  have htotal :
      |uH A (proj (Finset.univ : Finset (Fin m))) - H q * (m : ℝ)| ≤ Q.sigma m := by
    rw [uH_proj_univ A hA]
    exact hfat.2.2.2.2
  have hsigma_le : Q.sigma m ≤ effEnv 2 Q.sigma m := by
    exact le_effEnv 2 Q.sigma m
  rw [abs_le] at htotal hcondIc' ⊢
  rw [hcond_eq, hcard_comp] at hcondIc'
  constructor <;> nlinarith

theorem r3_eff (hBV : BallVolumeTwoSidedEff) (hVPlus : VPlusStatement)
    (hIVC : InteriorVolumeCalculusEff) : R3Eff := by
  intro qMin qMax s0 mu0 h1 h2 h3 h4 h5 h6
  obtain ⟨K, hK, hcond⟩ :=
    r3_cond_entropy_bound_eff hBV hVPlus hIVC qMin qMax s0 mu0 h1 h2 h3 h4 h5 h6
  refine ⟨K + 2, by linarith, ?_⟩
  intro pLow hlow hhigh sigma hsub hlog m A q hA hfat hpinned
  have hKp1 : 1 ≤ K / pLow := by
    rw [le_div_iff₀ hlow]
    nlinarith
  have hbr := r3_eff_from_cond_entropy ⟨qMin, qMax, s0, mu0, sigma⟩ pLow
      (K / pLow) hKp1 hlow hhigh
      (hcond pLow hlow hhigh sigma hsub hlog) m A q hA hfat hpinned
  obtain ⟨hb1, hb2, hb3⟩ := hbr
  refine ⟨hb1, hb2, ?_⟩
  intro I hI1 hI2
  have hE0 : (0 : ℝ) ≤ effEnv 2 sigma m + 1 := by
    have := effEnv_nonneg 2 sigma hsub.1 m
    linarith
  have hcoef : K / pLow + 1 ≤ (K + 2) / pLow := by
    have hple : pLow ≤ 1 := by nlinarith
    have e1 : (K / pLow + 1) * pLow = K + pLow := by
      field_simp
    have e2 : ((K + 2) / pLow) * pLow = K + 2 := by
      field_simp
    have hle : (K / pLow + 1) * pLow ≤
        ((K + 2) / pLow) * pLow := by
      rw [e1, e2]
      nlinarith
    exact le_of_mul_le_mul_right hle hlow
  have hmul : (K / pLow + 1) * (effEnv 2 sigma m + 1) ≤
      ((K + 2) / pLow) * (effEnv 2 sigma m + 1) :=
    mul_le_mul_of_nonneg_right hcoef hE0
  exact le_trans (hb3 I hI1 hI2) hmul

end HarperStability