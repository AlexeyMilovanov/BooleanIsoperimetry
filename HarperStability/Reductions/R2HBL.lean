import HarperStability.Reductions.Basic

namespace HarperStability

/-!
R2 heavy-ball reduction worker.

This file is split out of `Reductions.Basic` so the remaining
`r2_hbl_from_q_and_dp` proof can be attacked independently from the R3 fiber
argument.
-/

private lemma validQData_of_validData_buffered (D : StabilityData) (hvalid : validData D)
    (sigma_total : ℕ → ℝ) (hsub : Sublinear sigma_total)
    (hlog : ∀ m : ℕ, 1 ≤ m → Real.log (m : ℝ) ≤ sigma_total m) :
    validQData {
      qMin := D.alphaMin
      qMax := D.alphaMax
      s0 := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4)
      mu0 := (1 / 2 - D.alphaMax) / 2
      sigma := sigma_total
    } := by
  dsimp [validQData]
  obtain ⟨hrho, hd1, hd2, hcsize, hamin, h_min_max, h_max_half, hsub_D, hlog_D⟩ := hvalid
  refine ⟨hamin, h_min_max, h_max_half, ?_, ?_, ?_, hsub, hlog⟩
  · exact lt_min (by linarith) (by linarith)
  · linarith
  · have : min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4) ≤ (1 / 2 - D.alphaMax) / 4 := min_le_right _ _
    linarith

private lemma fat_of_classMember (D : StabilityData) (_ : validData D)
    (Q : QData) (hQ : validQData Q)
    (n : ℕ) (r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ)
    (hclass : classMember D n r S alpha beta)
    (hnonempty : S.Nonempty)
    (hsigma : ∀ m, D.cSize * D.sigma m ≤ Q.sigma m)
    (hq_bounds : Q.qMin ≤ alpha ∧ alpha ≤ Q.qMax) :
    fat Q n S alpha := by
  dsimp [fat]
  refine ⟨hnonempty, hQ, hq_bounds.1, hq_bounds.2, ?_⟩
  exact le_trans hclass.2.2.2.2.2.1 (hsigma n)

private lemma pinned_of_dp (D : StabilityData)
    (Q : QData) (hQ : validQData Q)
    (n : ℕ) (r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ)
    (hclass : classMember D n r S alpha beta)
    (sigmaDP : ℕ → ℝ)
    (hDP : ∀ tau : ℝ, 0 < tau → tau ≤ beta →
      ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
        Real.exp (H (min (alpha + tau) (1 / 2)) * (n : ℝ) + sigmaDP n))
    (hsigma_dp : ∀ m, sigmaDP m ≤ Q.sigma m)
    (hsigma_size : ∀ m, D.cSize * D.sigma m ≤ Q.sigma m)
    (hs0 : Q.s0 ≤ D.rho / 2)
    (hceil_half : ∀ s : ℕ, s ≤ Nat.ceil (Q.s0 * (n : ℝ)) →
      alpha + (s : ℝ) / (n : ℝ) ≤ 1 / 2) :
    pinned Q n S alpha := by
  classical
  intro s hsceil
  by_cases hs_zero : s = 0
  · subst s
    rw [neighborhood_zero_eq]
    by_cases hS0 : S.card = 0
    · simp [hS0]
      positivity
    · have hSpos : 0 < (S.card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hS0
      have hsize := hclass.2.2.2.2.2.1
      rw [sizeHyp, abs_le] at hsize
      have hlog :
          Real.log (S.card : ℝ) ≤ H alpha * (n : ℝ) + Q.sigma n := by
        linarith [hsize.2, hsigma_size n]
      have hcard :
          (S.card : ℝ) ≤ Real.exp (H alpha * (n : ℝ) + Q.sigma n) :=
        (Real.log_le_iff_le_exp hSpos).mp hlog
      simpa using hcard
  · have hs_pos : 0 < s := Nat.pos_of_ne_zero hs_zero
    have hn_pos_nat : 0 < n := by
      by_contra hn_not
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn_not
      subst n
      norm_num at hsceil
      omega
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hceil_le_r : Nat.ceil (Q.s0 * (n : ℝ)) ≤ r := by
      apply Nat.ceil_le.mpr
      have hs0_nonneg : 0 ≤ Q.s0 := le_of_lt hQ.2.2.2.1
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hrad := hclass.2.2.2.2.1
      have hmul_le : Q.s0 * (n : ℝ) ≤ (D.rho / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hs0 hn_nonneg
      have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      nlinarith [hmul_le, hrad, mul_nonneg hs0_nonneg hn_nonneg, hr_nonneg]
    have hs_le_r : s ≤ r := le_trans hsceil hceil_le_r
    let tau : ℝ := (s : ℝ) / (n : ℝ)
    have htau_pos : 0 < tau := by
      dsimp [tau]
      positivity
    have htau_le_beta : tau ≤ beta := by
      rw [hclass.2.1]
      dsimp [tau]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hs_le_r) hn_pos.le
    have hdp := hDP tau htau_pos htau_le_beta
    have hceil_eq : Nat.ceil (tau * (n : ℝ)) = s := by
      have hmul : tau * (n : ℝ) = (s : ℝ) := by
        dsimp [tau]
        field_simp [hn_ne]
      rw [hmul]
      simp
    rw [hceil_eq] at hdp
    have hmin :
        min (alpha + tau) (1 / 2) = alpha + tau := by
      exact min_eq_left (hceil_half s hsceil)
    rw [hmin] at hdp
    exact le_trans hdp (Real.exp_le_exp.mpr (by linarith [hsigma_dp n]))

private lemma heavyBall_of_not_bad (n : ℕ) (S : Finset (Cube n)) (alpha : ℝ)
    (delta eta : ℝ) (hnot_bad : ¬ bad n S alpha delta eta)
    (radius_slack : ℕ)
    (h_rmin_slack :
      Nat.ceil ((alpha + delta) * (n : ℝ)) ≤ rmin n S.card + radius_slack) :
    heavyBallConclusion n S (eta * (n : ℝ)) radius_slack := by
  classical
  dsimp [heavyBallConclusion]
  rw [bad] at hnot_bad
  push_neg at hnot_bad
  rcases hnot_bad with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hsub :
      (S.filter fun x => hDist x a ≤ Nat.ceil ((alpha + delta) * (n : ℝ))) ⊆
        (S.filter fun x => hDist x a ≤ rmin n S.card + radius_slack) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 h_rmin_slack⟩
  have hcard :
      (((S.filter fun x => hDist x a ≤ Nat.ceil ((alpha + delta) * (n : ℝ))).card : ℕ) : ℝ) ≤
        (((S.filter fun x => hDist x a ≤ rmin n S.card + radius_slack).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hmass :
      Real.exp (-(eta * (n : ℝ))) * (S.card : ℝ) ≤
        (((S.filter fun x => hDist x a ≤ Nat.ceil ((alpha + delta) * (n : ℝ))).card : ℕ) : ℝ) := by
    simpa [neg_mul] using ha.le
  exact le_trans hmass hcard

private lemma radius_alpha_to_rmin_slack (_hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (n : ℕ) (S : Finset (Cube n)) (alpha : ℝ)
    (delta : ℝ) (_hsize : sizeHyp D n S alpha) :
    ∃ radius_slack : ℕ,
      Nat.ceil ((alpha + delta) * (n : ℝ)) ≤ rmin n S.card + radius_slack := by
  exact ⟨Nat.ceil ((alpha + delta) * (n : ℝ)), Nat.le_add_left _ _⟩

/-- The Q-scheme plus downward pinning produce the heavy-ball conclusion for
a degraded tuple.

Proof route (prose R2): fix a class member `(n, r, S, alpha, beta)`.  Choose
`s0 := min(D.rho, (1/2 - D.alphaMax)/2)` and `mu0 := (1/2 - D.alphaMax)/2`
and build `Q : QData` with `qMin := D.alphaMin`, `qMax := D.alphaMax`,
`sigma := D.cSize • D.sigma`; then `S` itself witnesses `fat Q n S alpha`
(size hypothesis) and `pinned Q n S alpha` (downward pinning `hDP`, using
`tau := r'/n ≤ s0 ≤ beta` and `alpha + tau ≤ qMax + s0 ≤ 1/2 - mu0` so the
`min` is inactive).  `QuestionQ Q` at `(delta, eta) := (1/j, 1/j)` denies
`bad`, i.e. produces a ball of radius `⌈(alpha + 1/j) n⌉` capturing an
`exp(-n/j)` mass fraction; `sublinear_diag_envelope` over the thresholds
`m0 j` turns the family into one sublinear slack, and the volume calculus
(`hVC` at `r := 0`, whose `rmin` conclusion needs no radius range) converts
`⌈(alpha + 1/j) n⌉` into `rmin(n, |S|) + ⌈sigma' n⌉`.  Dimensions below the
diagonal threshold are absorbed by a prefix bump (`a ∈ S` alone captures
`exp(-n log 2)|S|` mass in radius `0`). -/
private noncomputable def qdata_of_stabilityData (D : StabilityData) (sigmaDP : ℕ → ℝ) : QData := {
  qMin := D.alphaMin
  qMax := D.alphaMax
  s0 := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4)
  mu0 := (1 / 2 - D.alphaMax) / 2
  sigma := fun n => D.cSize * D.sigma n + sigmaDP n
}

private lemma r2_sublinear_const_mul {s : ℕ → ℝ} (c : ℝ) (hc : 0 ≤ c)
    (hs : Sublinear s) : Sublinear (fun n => c * s n) := by
  refine ⟨fun n => mul_nonneg hc (hs.1 n), fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hs.2 (ε / (c + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 : c * s n ≤ c * (ε / (c + 1) * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 hc
  have h3 : c * (ε / (c + 1) * (n : ℝ)) ≤ ε * (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_mul_eq_mul_div, mul_div_assoc']
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < c + 1)]
    nlinarith
  linarith

set_option maxHeartbeats 1600000 in
private lemma r2_hbl_m0_exists (D : StabilityData) (hvalid : validData D)
    (hQ : ∀ Q : QData, validQData Q → QuestionQ Q)
    (sigmaDP : ℕ → ℝ) (hsub_dp : Sublinear sigmaDP) :
    ∃ m0 : ℕ → ℕ, 1 ≤ m0 1 ∧ ∀ j, 1 ≤ j →
      ∀ n ≥ m0 j, ∀ r S alpha beta, classMember D n r S alpha beta →
      (∀ tau : ℝ, 0 < tau → tau ≤ beta →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (min (alpha + tau) (1 / 2)) * (n : ℝ) + sigmaDP n)) →
      ¬ bad n S alpha (1 / j) (1 / j) := by
  rcases hvalid with ⟨ hrho, hdelta_pos, hdelta_lt, hcsize, hamin, haminmax, hamaxhalf, hsubD, hlogD ⟩;
  set Q : QData := ⟨D.alphaMin, D.alphaMax, min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4), (1 / 2 - D.alphaMax) / 2, fun n => D.cSize * D.sigma n + sigmaDP n⟩;
  obtain ⟨hvalidQ, hQ_valid⟩ : validQData Q ∧ QuestionQ Q := by
    apply And.intro;
    · convert validQData_of_validData_buffered D _ _ _ _ using 1;
      · exact ⟨ hrho, hdelta_pos, hdelta_lt, hcsize, hamin, haminmax, hamaxhalf, hsubD, hlogD ⟩;
      · convert reductions_sublinear_add ( r2_sublinear_const_mul D.cSize ( by linarith ) hsubD ) hsub_dp using 1;
      · exact fun n hn => le_add_of_le_of_nonneg ( le_trans ( hlogD n hn ) ( le_mul_of_one_le_left ( hsubD.1 n ) hcsize ) ) ( hsub_dp.1 n );
    · apply hQ;
      convert validQData_of_validData_buffered D _ _ _ _ using 1;
      · exact ⟨ hrho, hdelta_pos, hdelta_lt, hcsize, hamin, haminmax, hamaxhalf, hsubD, hlogD ⟩;
      · convert reductions_sublinear_add ( r2_sublinear_const_mul D.cSize ( by linarith ) hsubD ) hsub_dp using 1;
      · exact fun n hn => le_add_of_le_of_nonneg ( le_trans ( hlogD n hn ) ( le_mul_of_one_le_left ( hsubD.1 n ) hcsize ) ) ( hsub_dp.1 n );
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ n ≥ N1, D.cSize * D.sigma n ≤ (Real.binEntropy D.alphaMin / 2) * n := by
    convert r2_sublinear_const_mul D.cSize ( by linarith ) hsubD |>.2 ( Real.binEntropy D.alphaMin / 2 ) ( by linarith [ Real.binEntropy_pos hamin ( by linarith ) ] ) using 1;
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ n ≥ N2, 1 ≤ n ∧ (1 : ℝ) / n ≤ (1 / 2 - D.alphaMax) / 4 := by
    exact ⟨ ⌈4 / ( 1 / 2 - D.alphaMax ) ⌉₊ + 1, fun n hn => ⟨ by linarith, by rw [ div_le_iff₀ ] <;> nlinarith [ Nat.le_ceil ( 4 / ( 1 / 2 - D.alphaMax ) ), show ( n : ℝ ) ≥ ⌈4 / ( 1 / 2 - D.alphaMax ) ⌉₊ + 1 by exact_mod_cast hn, mul_div_cancel₀ 4 ( by linarith : ( 1 / 2 - D.alphaMax ) ≠ 0 ) ] ⟩ ⟩;
  refine' ⟨ fun j => if h : 1 ≤ j then max ( max ( max 1 N1 ) N2 ) ( Classical.choose ( hQ_valid ( 1 / ( j : ℝ ) ) ( 1 / ( j : ℝ ) ) ( by positivity ) ( by positivity ) ) ) else 1, _, _ ⟩ <;> simp +decide;
  intro j hj n hn r S alpha beta hclass hpin hbad
  have hfat : fat Q n S alpha := by
    apply fat_of_classMember;
    exact ⟨ hrho, hdelta_pos, hdelta_lt, hcsize, hamin, haminmax, hamaxhalf, hsubD, hlogD ⟩;
    exact hvalidQ;
    exact hclass;
    · contrapose! hbad; simp_all +decide [ bad ] ;
      obtain ⟨ hsize, hnear, hcap ⟩ := hclass;
      have := hcap.2.2.2.1; norm_num [ sizeHyp ] at this;
      -- Since $H(\alpha)$ is positive and $n \geq 1$, we have $H(\alpha) * n > 0$.
      have h_pos : 0 < H alpha * n := by
        exact mul_pos ( Real.binEntropy_pos ( by linarith ) ( by linarith ) ) ( Nat.cast_pos.mpr ( by linarith [ hN2 n hn.2.1 ] ) );
      rw [ abs_of_nonneg ( show 0 ≤ H alpha from Real.binEntropy_nonneg ( by linarith ) ( by linarith ) ) ] at this ; nlinarith [ hN1 n hn.1, show ( Real.binEntropy D.alphaMin : ℝ ) ≤ H alpha from Real.binEntropy_strictMonoOn.monotoneOn ( by constructor <;> linarith ) ( by constructor <;> linarith ) ( by linarith ) ] ;
    · exact fun m => le_add_of_nonneg_right ( hsub_dp.1 m );
    · exact ⟨ hclass.2.2.1, hclass.2.2.2.1 ⟩
  have hpinned : pinned Q n S alpha := by
    apply pinned_of_dp;
    any_goals assumption;
    · aesop;
    · exact fun m => le_add_of_nonneg_left ( mul_nonneg ( by linarith ) ( hsubD.1 m ) );
    · exact fun m => le_add_of_nonneg_right ( hsub_dp.1 m );
    · exact min_le_left _ _;
    · intro s hs
      have hceil : (s : ℝ) ≤ Q.s0 * n + 1 := by
        exact le_trans ( Nat.cast_le.mpr hs ) ( Nat.ceil_lt_add_one ( mul_nonneg ( le_min ( by linarith ) ( by linarith ) ) ( Nat.cast_nonneg _ ) ) |> le_of_lt );
      have hceil_half : (s : ℝ) / n ≤ Q.s0 + 1 / n := by
        rw [ add_div', div_le_div_iff_of_pos_right ] <;> norm_num ; linarith [ hN2 n ( by split_ifs at hn ; omega ) ]; all_goals grind;
      have hceil_half : Q.s0 + 1 / (n : ℝ) ≤ (1 / 2 - D.alphaMax) / 2 := by
        grind;
      linarith [ hclass.2.2.2.1 ]
  have hbad' : bad n S alpha (1 / (j : ℝ)) (1 / (j : ℝ)) := by
    simpa using hbad
  have hcontradiction : ¬(fat Q n S alpha ∧ pinned Q n S alpha ∧ bad n S alpha (1 / (j : ℝ)) (1 / (j : ℝ))) := by
    grind +revert
  exact hcontradiction ⟨hfat, hpinned, hbad'⟩

private lemma r2_sublinear_prefix_log (N : ℕ) :
    Sublinear (fun n => if n < N then (n : ℝ) * Real.log 2 else 0) := by
  refine ⟨fun n => by
    by_cases h : n < N
    · simp [h, mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg one_le_two)]
    · simp [h], fun ε hε => ?_⟩
  refine ⟨N, fun n hn => ?_⟩
  have h : ¬ n < N := not_lt.mpr hn
  simp only [h, if_false]
  exact mul_nonneg hε.le (Nat.cast_nonneg n)

private lemma r2_sublinear_diag_envelope (m0 : ℕ → ℕ) :
    ∃ s : ℕ → ℝ, Sublinear s ∧
      ∀ m : ℕ, m0 1 ≤ m → 1 ≤ m →
        ∃ j : ℕ, 1 ≤ j ∧ m0 j ≤ m ∧ (m : ℝ) / (j : ℝ) ≤ s m := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ, StrictMono K ∧ ∀ m, K m ≥ m0 (m + 1) + m + 1 := by
    exact ⟨ fun m => Nat.recOn m (m0 1 + 1 + 1) fun n ih => ih + m0 (n + 2) + 2,
      strictMono_nat_of_lt_succ fun n => by linarith,
      fun n => Nat.recOn n (by linarith) fun n ih => by linarith ⟩
  refine' ⟨ fun m => (m : ℝ) / ( ( Nat.findGreatest ( fun n => K n ≤ m ) m + 1 ) : ℝ ), _, _ ⟩ <;> norm_num [ Sublinear ]
  · refine' ⟨ fun n => by positivity, fun ε hε => ⟨ Nat.ceil ( K ( Nat.ceil ( ε⁻¹ ) ) ), fun n hn => _ ⟩ ⟩
    rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num at *
    have h_findGreatest : Nat.findGreatest (fun n_1 => K n_1 ≤ n) n ≥ ⌈ε⁻¹⌉₊ := by
      refine' Nat.le_findGreatest _ _ <;> norm_num [ hn ]
      exact le_trans ( Nat.le_ceil _ ) ( mod_cast hn.trans' ( hK.1.id_le _ ) )
    nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( Nat.findGreatest ( fun n_1 => K n_1 ≤ n ) n : ℝ ) ≥ ⌈ε⁻¹⌉₊ by exact_mod_cast h_findGreatest, mul_nonneg hε.le ( Nat.cast_nonneg n ) ]
  · intro m hm₁ hm₂
    have := Nat.findGreatest_eq_iff.mp ( rfl : Nat.findGreatest ( fun n => K n ≤ m ) m = _ )
    grind

private lemma r2_hbl_dhbl_exists (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D)
    (m0 : ℕ → ℕ) :
    ∃ Dhbl : StabilityData, degradedData D Dhbl ∧
      (∀ n ≥ m0 1, 1 ≤ n →
        ∀ (S : Finset (Cube n)) (alpha : ℝ),
          S.Nonempty →
          sizeHyp D n S alpha →
          D.alphaMin ≤ alpha → alpha ≤ D.alphaMax →
          ∃ j : ℕ, 1 ≤ j ∧ m0 j ≤ n ∧
            (1 / (j : ℝ)) * (n : ℝ) ≤ Dhbl.sigma n ∧
            Nat.ceil ((alpha + 1 / (j : ℝ)) * (n : ℝ)) ≤
              rmin n S.card + Nat.ceil (Dhbl.sigma n)) ∧
      ∀ n, n < m0 1 → (n : ℝ) * Real.log 2 ≤ Dhbl.sigma n := by
  classical
  obtain ⟨hrho, hdelta_pos, hdelta_lt, hcsize, hamin, haminmax, hamaxhalf,
    hsubD, hlogD⟩ := hvalid
  let c0 : ℝ := (1 / 2 - D.alphaMax) / 2
  have hc0 : 0 < c0 := by
    dsimp [c0]
    linarith
  obtain ⟨C_V, hC_V, volSlack, hvolSlack, hcalc⟩ :=
    hVC D.alphaMin c0 hamin hc0
  obtain ⟨diagSlack, hdiagSub, hdiag⟩ := r2_sublinear_diag_envelope m0
  let prefixSlack : (ℕ → ℝ) := fun n => if n < m0 1 then (n : ℝ) * Real.log 2 else 0
  let sigma' : (ℕ → ℝ) := fun n =>
    D.sigma n + C_V * (D.cSize * D.sigma n) + volSlack n + diagSlack n + prefixSlack n
  have hmainSub : Sublinear (fun n => C_V * (D.cSize * D.sigma n)) := by
    have hcoef : 0 ≤ C_V * D.cSize := by nlinarith [hC_V, hcsize]
    have h := r2_sublinear_const_mul (C_V * D.cSize) hcoef hsubD
    convert h using 2 with n
    ring
  have hprefixSub : Sublinear prefixSlack := by
    simpa [prefixSlack] using r2_sublinear_prefix_log (m0 1)
  have hsigmaSub : Sublinear sigma' := by
    have h1 := reductions_sublinear_add hsubD hmainSub
    have h2 := reductions_sublinear_add h1 hvolSlack
    have h3 := reductions_sublinear_add h2 hdiagSub
    have h4 := reductions_sublinear_add h3 hprefixSub
    convert h4 using 2 with n
  have hprefix_nonneg : ∀ n, 0 ≤ prefixSlack n := by
    intro n
    by_cases hn : n < m0 1
    · simp [prefixSlack, hn, mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg one_le_two)]
    · simp [prefixSlack, hn]
  have hsigma_ge_D : ∀ n, D.sigma n ≤ sigma' n := by
    intro n
    have hmain_nonneg : 0 ≤ C_V * (D.cSize * D.sigma n) :=
      mul_nonneg (le_trans zero_le_one hC_V)
        (mul_nonneg (le_trans zero_le_one hcsize) (hsubD.1 n))
    have hvol_nonneg : 0 ≤ volSlack n := hvolSlack.1 n
    have hdiag_nonneg : 0 ≤ diagSlack n := hdiagSub.1 n
    have hpref_nonneg : 0 ≤ prefixSlack n := hprefix_nonneg n
    simp [sigma']
    linarith
  let Dhbl : StabilityData := { D with sigma := sigma' }
  have hvalidDhbl : validData Dhbl := by
    refine ⟨hrho, hdelta_pos, hdelta_lt, hcsize, hamin, haminmax, hamaxhalf,
      ?_, ?_⟩
    · exact hsigmaSub
    · intro n hn
      exact le_trans (hlogD n hn) (hsigma_ge_D n)
  have hdeg : degradedData D Dhbl :=
    ⟨hvalidDhbl, rfl, rfl, le_rfl, rfl, rfl, hsigma_ge_D⟩
  refine ⟨Dhbl, hdeg, ?_, ?_⟩
  · intro n hnlarge hn1 S alpha hSnonempty hsize halpha_min halpha_max
    obtain ⟨j, hj1, hm0j, hdiagj⟩ := hdiag n hnlarge hn1
    refine ⟨j, hj1, hm0j, ?_, ?_⟩
    · have hdiagj' : (1 / (j : ℝ)) * (n : ℝ) ≤ diagSlack n := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiagj
      have hdiagj_inv : (j : ℝ)⁻¹ * (n : ℝ) ≤ diagSlack n := by
        simpa [one_div] using hdiagj'
      have hnonneg_main : 0 ≤ C_V * (D.cSize * D.sigma n) :=
        mul_nonneg (le_trans zero_le_one hC_V)
          (mul_nonneg (le_trans zero_le_one hcsize) (hsubD.1 n))
      have hnonneg_vol : 0 ≤ volSlack n := hvolSlack.1 n
      have hnonneg_D : 0 ≤ D.sigma n := hsubD.1 n
      have hnonneg_prefix : 0 ≤ prefixSlack n := hprefix_nonneg n
      simp [Dhbl, sigma']
      linarith
    · have h_alpha_half : alpha ≤ 1 / 2 :=
        le_of_lt (lt_of_le_of_lt halpha_max hamaxhalf)
      have hsizeSlack_nonneg : 0 ≤ D.cSize * D.sigma n :=
        mul_nonneg (le_trans zero_le_one hcsize) (hsubD.1 n)
      have hbeta_zero : (0 : ℝ) = ((0 : ℕ) : ℝ) / (n : ℝ) := by simp
      have hrange : alpha + (0 : ℝ) ≤ 1 / 2 - c0 := by
        dsimp [c0]
        nlinarith [halpha_max, hamaxhalf]
      have hS1 : 1 ≤ S.card := Finset.card_pos.mpr hSnonempty
      have hScap : S.card ≤ 2 ^ n := by
        calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
          _ = 2 ^ n := by
              rw [Finset.card_univ]
              exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
      obtain ⟨_, hrmin_abs⟩ :=
        hcalc n S.card 0 alpha 0 (D.cSize * D.sigma n)
          halpha_min h_alpha_half hsizeSlack_nonneg hbeta_zero hrange
          hS1 hScap hsize
      have hrmin_lower :
          alpha * (n : ℝ) - (C_V * (D.cSize * D.sigma n) + volSlack n) ≤
            (rmin n S.card : ℝ) := by
        have := (abs_le.mp hrmin_abs).1
        linarith
      have hdiagj' : (1 / (j : ℝ)) * (n : ℝ) ≤ diagSlack n := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiagj
      have hdiagj_inv : (j : ℝ)⁻¹ * (n : ℝ) ≤ diagSlack n := by
        simpa [one_div] using hdiagj'
      have hslack_bound :
          C_V * (D.cSize * D.sigma n) + volSlack n +
              (1 / (j : ℝ)) * (n : ℝ) ≤ Dhbl.sigma n := by
        have hnonneg_D : 0 ≤ D.sigma n := hsubD.1 n
        have hnonneg_prefix : 0 ≤ prefixSlack n := hprefix_nonneg n
        simp [Dhbl, sigma']
        linarith
      apply Nat.ceil_le.mpr
      rw [Nat.cast_add]
      have hceil_sigma : Dhbl.sigma n ≤ (Nat.ceil (Dhbl.sigma n) : ℝ) :=
        Nat.le_ceil _
      calc
        (alpha + 1 / (j : ℝ)) * (n : ℝ)
            = alpha * (n : ℝ) + (1 / (j : ℝ)) * (n : ℝ) := by ring
        _ ≤ (rmin n S.card : ℝ) +
              (C_V * (D.cSize * D.sigma n) + volSlack n +
                (1 / (j : ℝ)) * (n : ℝ)) := by linarith
        _ ≤ (rmin n S.card : ℝ) + Dhbl.sigma n := by linarith
        _ ≤ (rmin n S.card : ℝ) + Nat.ceil (Dhbl.sigma n) := by linarith
  · intro n hn
    have hpref : prefixSlack n = (n : ℝ) * Real.log 2 := by simp [prefixSlack, hn]
    have hnonneg_D : 0 ≤ D.sigma n := hsubD.1 n
    have hnonneg_main : 0 ≤ C_V * (D.cSize * D.sigma n) :=
      mul_nonneg (le_trans zero_le_one hC_V)
        (mul_nonneg (le_trans zero_le_one hcsize) (hsubD.1 n))
    have hnonneg_vol : 0 ≤ volSlack n := hvolSlack.1 n
    have hnonneg_diag : 0 ≤ diagSlack n := hdiagSub.1 n
    simp [Dhbl, sigma', hpref]
    linarith

private lemma heavyBallConclusion_mono_mass {n : ℕ} {S : Finset (Cube n)}
    {massSlack massSlack' : ℝ} {radiusSlack : ℕ}
    (hmass : massSlack ≤ massSlack')
    (hball : heavyBallConclusion n S massSlack radiusSlack) :
    heavyBallConclusion n S massSlack' radiusSlack := by
  rcases hball with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le S.card
  have hexp : Real.exp (-massSlack') ≤ Real.exp (-massSlack) :=
    Real.exp_le_exp.mpr (by linarith)
  exact le_trans (mul_le_mul_of_nonneg_right hexp hcard_nonneg) ha

private lemma r2_cube_card_le_exp (n : ℕ) (S : Finset (Cube n)) :
    (S.card : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) := by
  have h1 : S.card ≤ 2 ^ n := by
    calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
      _ = 2 ^ n := by
          rw [Finset.card_univ]
          exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
  have h2 : ((2 : ℝ)) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc (S.card : ℝ) ≤ ((2 : ℝ)) ^ n := by exact_mod_cast h1
    _ = Real.exp ((n : ℝ) * Real.log 2) := h2

private lemma r2_hbl_from_q_and_dp_small_n (D Dhbl : StabilityData) (m0_1 : ℕ)
    (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ)
    (_hclass : classMember D n r S alpha beta)
    (hprefix : ∀ n, n < m0_1 → (n : ℝ) * Real.log 2 ≤ Dhbl.sigma n)
    (hn : n < m0_1) :
    heavyBallConclusion n S (Dhbl.sigma n) (Nat.ceil (Dhbl.sigma n)) := by
  classical
  dsimp [heavyBallConclusion]
  by_cases hS : S.Nonempty
  · rcases hS with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hcard := r2_cube_card_le_exp n S
    have hsigma := hprefix n hn
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le S.card
    have hexp :
        Real.exp (-(Dhbl.sigma n)) ≤ Real.exp (-((n : ℝ) * Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hmass_one :
        Real.exp (-(Dhbl.sigma n)) * (S.card : ℝ) ≤ 1 := by
      calc
        Real.exp (-(Dhbl.sigma n)) * (S.card : ℝ)
            ≤ Real.exp (-((n : ℝ) * Real.log 2)) *
                Real.exp ((n : ℝ) * Real.log 2) := by
              exact mul_le_mul hexp hcard hcard_nonneg (Real.exp_pos _).le
        _ = 1 := by
              rw [← Real.exp_add]
              ring_nf
              exact Real.exp_zero
    have hfilter_one :
        (1 : ℝ) ≤
          ((S.filter fun x =>
            hDist x a ≤ rmin n S.card + Nat.ceil (Dhbl.sigma n)).card : ℝ) := by
      have hmem :
          a ∈ S.filter fun x =>
            hDist x a ≤ rmin n S.card + Nat.ceil (Dhbl.sigma n) := by
        rw [Finset.mem_filter]
        exact ⟨ha, by simp [hDist]⟩
      exact_mod_cast Finset.card_pos.mpr ⟨a, hmem⟩
    exact le_trans hmass_one hfilter_one
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    refine ⟨(∅ : Cube n), ?_⟩
    simp [hSempty]

private lemma r2_hbl_from_q_and_dp (_hBV : BallVolumeTwoSidedStatement)
    (_hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D)
    (hQ : ∀ Q : QData, validQData Q → QuestionQ Q)
    (sigmaDP : ℕ → ℝ) (hsub_dp : Sublinear sigmaDP)
    (hDP : ∀ n r S alpha beta, classMember D n r S alpha beta →
      ∀ tau : ℝ, 0 < tau → tau ≤ beta →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (min (alpha + tau) (1 / 2)) * (n : ℝ) + sigmaDP n)) :
    ∃ Dhbl : StabilityData, degradedData D Dhbl ∧ HBLFor D Dhbl := by
  classical
  obtain ⟨m0, hm0_one, hm0⟩ :=
    r2_hbl_m0_exists D hvalid hQ sigmaDP hsub_dp
  obtain ⟨Dhbl, hdeg, hlarge, hprefix⟩ :=
    r2_hbl_dhbl_exists hVC D hvalid m0
  refine ⟨Dhbl, hdeg, ?_⟩
  intro n r S alpha beta hclass
  by_cases hnlarge : m0 1 ≤ n
  · have hn1 : 1 ≤ n := le_trans hm0_one hnlarge
    by_cases hS : S.Nonempty
    · obtain ⟨j, hj_one, hm0j, hmass, hradius⟩ :=
        hlarge n hnlarge hn1 S alpha hS hclass.2.2.2.2.2.1
          hclass.2.2.1 hclass.2.2.2.1
      have hnot_bad :
          ¬ bad n S alpha (1 / (j : ℝ)) (1 / (j : ℝ)) :=
        hm0 j hj_one n hm0j r S alpha beta hclass
          (hDP n r S alpha beta hclass)
      have hball :
          heavyBallConclusion n S ((1 / (j : ℝ)) * (n : ℝ))
            (Nat.ceil (Dhbl.sigma n)) :=
        heavyBall_of_not_bad n S alpha (1 / (j : ℝ)) (1 / (j : ℝ))
          hnot_bad (Nat.ceil (Dhbl.sigma n)) hradius
      exact heavyBallConclusion_mono_mass hmass hball
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      dsimp [heavyBallConclusion]
      refine ⟨(∅ : Cube n), ?_⟩
      simp [hSempty]
  · have hnsmall : n < m0 1 := Nat.lt_of_not_ge hnlarge
    exact r2_hbl_from_q_and_dp_small_n D Dhbl (m0 1) n r S alpha beta
      hclass hprefix hnsmall

private lemma r2_hbl_of_qdata (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D)
    (hQ : ∀ Q : QData, validQData Q → QuestionQ Q) :
    ∃ Dhbl : StabilityData, degradedData D Dhbl ∧ HBLFor D Dhbl := by
  obtain ⟨sigmaDP, hsub_dp, hDP⟩ := r2_downward_pinning hBV hVPlus hVC D hvalid
  exact r2_hbl_from_q_and_dp hBV hVPlus hVC D hvalid hQ sigmaDP hsub_dp hDP

theorem R2_skeleton (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) :
    R2Statement := by
  intro hQ D hvalid
  exact r2_hbl_of_qdata hBV hVPlus hVC D hvalid hQ

end HarperStability
