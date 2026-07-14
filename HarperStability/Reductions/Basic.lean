import HarperStability.Interface
import HarperStability.Entropy

namespace HarperStability

/-!
R1--R3 reduction layer.

This module will eventually prove `R1aStatement`, `R1bStatement`,
`R2Statement`, and `R3Statement`.

This worker proves closed reduction contracts.  Under the monorepo policy,
future reduction proofs may import/use the upstream `Volume` and `Entropy`
toolkit libraries; cross-worker theorem dependencies remain explicit in the
statements and assembly layer.
-/

private lemma classMember_of_degraded {Din Dout : StabilityData} {n r : ℕ}
    {S : Finset (Cube n)} {alpha beta : ℝ}
    (hdeg : degradedData Din Dout)
    (hmem : classMember Din n r S alpha beta) :
    classMember Dout n r S alpha beta := by
  rcases hdeg with
    ⟨hDout, hrho, hdelta, hcSize, halphaMin, halphaMax, hsigma⟩
  rcases hmem with
    ⟨hDin, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩
  have hDout_keep := hDout
  rcases hDin with
    ⟨_hDin_rho_pos, _hDin_delta_pos, _hDin_delta_lt, _hDin_cSize,
      _hDin_alpha_pos, _hDin_alpha_le, _hDin_alpha_lt, hDin_sigma, _hDin_log⟩
  rcases hDout with
    ⟨_hDout_rho_pos, _hDout_delta_pos, _hDout_delta_lt, hDout_cSize,
      _hDout_alpha_pos, _hDout_alpha_le, _hDout_alpha_lt, _hDout_sigma,
      _hDout_log⟩
  refine ⟨hDout_keep, hbeta, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [← halphaMin] using halpha_min
  · simpa [← halphaMax] using halpha_max
  · simpa [← hrho] using hradius
  · dsimp [sizeHyp] at hsize ⊢
    refine le_trans hsize ?_
    exact mul_le_mul hcSize (hsigma n) (hDin_sigma.1 n) (by linarith)
  · dsimp [nearOptimalHyp] at hnear ⊢
    refine le_trans hnear ?_
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hsigma n))
      (by positivity)
  · simpa [capHyp, ← hdelta] using hcap

lemma degradedData_trans {D₁ D₂ D₃ : StabilityData}
    (h12 : degradedData D₁ D₂) (h23 : degradedData D₂ D₃) :
    degradedData D₁ D₃ := by
  rcases h12 with
    ⟨_hD2, hrho12, hdelta12, hcSize12, halphaMin12, halphaMax12, hsigma12⟩
  rcases h23 with
    ⟨hD3, hrho23, hdelta23, hcSize23, halphaMin23, halphaMax23, hsigma23⟩
  refine ⟨hD3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrho12.trans hrho23
  · exact hdelta12.trans hdelta23
  · exact le_trans hcSize12 hcSize23
  · exact halphaMin12.trans halphaMin23
  · exact halphaMax12.trans halphaMax23
  · intro n
    exact le_trans (hsigma12 n) (hsigma23 n)

private lemma degradedData_refl {D : StabilityData} (hD : validData D) :
    degradedData D D := by
  exact ⟨hD, rfl, rfl, le_rfl, rfl, rfl, fun _ => le_rfl⟩

lemma reductions_sublinear_add {s t : ℕ → ℝ} (hs : Sublinear s)
    (ht : Sublinear t) :
    Sublinear (fun n => s n + t n) := by
  refine ⟨fun n => add_nonneg (hs.1 n) (ht.1 n), fun ε hε => ?_⟩
  obtain ⟨N1, hN1⟩ := hs.2 (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := ht.2 (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 := hN2 n (le_trans (le_max_right _ _) hn)
  simp only
  linarith

lemma sublinear_const (c : ℝ) (hc : 0 ≤ c) : Sublinear (fun _ => c) := by
  refine ⟨fun _ => hc, fun ε hε => ⟨Nat.ceil (c / ε), fun n hn => ?_⟩⟩
  have h1 : c / ε ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  calc c = ε * (c / ε) := by field_simp
    _ ≤ ε * (n : ℝ) := by exact mul_le_mul_of_nonneg_left h1 hε.le

lemma sublinear_const_mul {s : ℕ → ℝ} (c : ℝ) (hc : 0 ≤ c)
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
    rw [div_le_iff₀ (by positivity : (0:ℝ) < c + 1)]
    nlinarith
  linarith

/-- A nonnegative envelope supported on finitely many dimensions is
sublinear. -/
lemma sublinear_indicator_prefix (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (N : ℕ) : Sublinear (fun n => if n < N then B n else 0) := by
  refine ⟨fun n => by by_cases h : n < N <;> simp [h, hB n], fun ε hε => ?_⟩
  refine ⟨N, fun n hn => ?_⟩
  have h : ¬ n < N := not_lt.mpr hn
  simp only [h, if_false]
  positivity

private lemma hDist_triangle_local {n : ℕ} (x y z : Cube n) :
    hDist x z ≤ hDist x y + hDist y z := by
  classical
  unfold hDist
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_union, Finset.mem_symmDiff] at hi ⊢
  rcases hi with ⟨hix, hiz⟩ | ⟨hiz, hix⟩
  · by_cases hiy : i ∈ y
    · right
      exact Or.inl ⟨hiy, hiz⟩
    · left
      exact Or.inl ⟨hix, hiy⟩
  · by_cases hiy : i ∈ y
    · left
      exact Or.inr ⟨hiy, hix⟩
    · right
      exact Or.inr ⟨hiz, hiy⟩

lemma subset_neighborhood_self {n : ℕ} (r : ℕ) (A : Finset (Cube n)) :
    A ⊆ neighborhood r A := by
  intro x hx
  rw [mem_neighborhood_iff]
  exact ⟨x, hx, by simp [hDist]⟩

lemma neighborhood_mono_set {n r : ℕ} {R S : Finset (Cube n)}
    (hsub : R ⊆ S) : neighborhood r R ⊆ neighborhood r S := by
  intro x hx
  rw [mem_neighborhood_iff] at hx ⊢
  rcases hx with ⟨u, hu, hdist⟩
  exact ⟨u, hsub hu, hdist⟩

private lemma neighborhood_neighborhood_subset {n a b : ℕ} (A : Finset (Cube n)) :
    neighborhood a (neighborhood b A) ⊆ neighborhood (a + b) A := by
  intro x hx
  rw [mem_neighborhood_iff] at hx ⊢
  rcases hx with ⟨y, hy, hyx⟩
  rw [mem_neighborhood_iff] at hy
  rcases hy with ⟨z, hz, hzy⟩
  refine ⟨z, hz, ?_⟩
  exact le_trans (hDist_triangle_local z y x) (by omega)

lemma neighborhood_zero_eq {n : ℕ} (A : Finset (Cube n)) :
    neighborhood 0 A = A := by
  classical
  ext x
  constructor
  · intro hx
    rw [mem_neighborhood_iff] at hx
    rcases hx with ⟨u, hu, hdist⟩
    have hdist0 : hDist u x = 0 := Nat.eq_zero_of_le_zero hdist
    have hux : u = x := by
      rw [hDist, Finset.card_eq_zero, Finset.symmDiff_eq_empty] at hdist0
      exact hdist0
    simpa [hux] using hu
  · intro hx
    rw [mem_neighborhood_iff]
    refine ⟨x, hx, ?_⟩
    simp [hDist]

lemma cube_card_le_two_pow {n : ℕ} (A : Finset (Cube n)) :
    (A.card : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) := by
  have h1 : A.card ≤ 2 ^ n := by
    calc A.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ A
      _ = 2 ^ n := by
          rw [Finset.card_univ]
          exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
  have h2 : ((2 : ℝ)) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  calc (A.card : ℝ) ≤ ((2 : ℝ)) ^ n := by exact_mod_cast h1
    _ = Real.exp ((n : ℝ) * Real.log 2) := h2

/-- The Harper minimum dominates the base cardinality (every set is contained
in its own neighborhood). -/
lemma card_le_V {n : ℕ} (k r : ℕ) (hk : k ≤ 2 ^ n) :
    (k : ℝ) ≤ (V n k r : ℝ) := by
  classical
  have hk_univ : k ≤ (Finset.univ : Finset (Cube n)).card := by
    rw [Finset.card_univ]
    exact le_trans hk (le_of_eq ((Fintype.card_finset (α := Fin n)).trans
      (by rw [Fintype.card_fin])).symm)
  obtain ⟨A0, _hA0sub, hA0card⟩ := Finset.exists_subset_card_eq hk_univ
  set fams := (Finset.univ : Finset (Cube n)).powerset.filter
    (fun A : Finset (Cube n) => A.card = k) with hfams
  set vals := fams.image (fun A => (neighborhood r A).card) with hvals
  have hmemA0 : A0 ∈ fams :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ A0), hA0card⟩
  have hne : vals.Nonempty := ⟨_, Finset.mem_image.mpr ⟨A0, hmemA0, rfl⟩⟩
  have hlb : ∀ v ∈ vals, k ≤ v := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨A, hA, rfl⟩
    have hAcard : A.card = k := (Finset.mem_filter.mp hA).2
    calc k = A.card := hAcard.symm
      _ ≤ (neighborhood r A).card :=
          Finset.card_le_card (subset_neighborhood_self r A)
  have : k ≤ V n k r := by
    unfold V
    simp only [← hfams, ← hvals, dif_pos hne]
    exact hlb _ (vals.min'_mem hne)
  exact_mod_cast this

/-- Strong concavity of the binary entropy at the equator: the quadratic gap
`H(1/2 - u) ≤ log 2 - 2 u^2` (nats).  This is the quantitative tool that
converts the sub-equatorial cap into a definite distance from `1/2`. -/
private lemma binEntropy_le_log_two_sub_two_sq {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2) :
    H (1 / 2 - u) ≤ Real.log 2 - 2 * u ^ 2 := by
  have hconc := concaveOn_binEntropy_add_two_sq
  have hx : (1 / 2 - u : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hy : (1 / 2 + u : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcomb := hconc.2 hx hy (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
  have hmid : (1/2 : ℝ) • (1/2 - u) + (1/2 : ℝ) • (1/2 + u) = (1/2 : ℝ) := by
    simp only [smul_eq_mul]; ring
  rw [hmid] at hcomb
  simp only [smul_eq_mul] at hcomb
  have hsym : Real.binEntropy (1/2 + u) = Real.binEntropy (1/2 - u) := by
    rw [show (1/2 + u : ℝ) = 2⁻¹ + u by norm_num,
      show (1/2 - u : ℝ) = 2⁻¹ - u by norm_num]
    exact Real.binEntropy_two_inv_add u
  have hhalf : Real.binEntropy (1/2 : ℝ) = Real.log 2 := by
    rw [show (1/2 : ℝ) = 2⁻¹ by norm_num]
    exact Real.binEntropy_two_inv
  rw [hsym, hhalf] at hcomb
  unfold H
  nlinarith [hcomb]

private lemma H_mono_on_half {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1 / 2) : H x ≤ H y :=
  Real.binEntropy_strictMonoOn.monotoneOn ⟨hx, by norm_num; linarith⟩
    ⟨by linarith, by norm_num; linarith⟩ hxy

/-
Chord lower bound for the binary entropy on the increasing branch
(`H` concave with derivative `log((1-x)/x)`): for `0 < a ≤ b ≤ 1/2`,
`H b - H a ≥ (b - a) * log((1-b)/b)`.

Proof route: concavity gives `H b - H a ≥ (b - a) * H'(b)` on the increasing
branch; `Real.hasDerivAt_binEntropy` supplies the derivative.  Textbook
calculus; isolated as an Aristotle-shaped leaf.
-/
private lemma binEntropy_chord_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) :
    (b - a) * Real.log ((1 - b) / b) ≤ H b - H a := by
  by_cases h_eq : a = b;
  · aesop;
  · -- By the Mean Value Theorem, there exists some $c \in (a, b)$ such that $H'(c) = (H(b) - H(a)) / (b - a)$.
    obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo a b, deriv H c = (H b - H a) / (b - a) := by
      apply_rules [ exists_deriv_eq_slope ];
      · exact lt_of_le_of_ne hab h_eq;
      · refine' ContinuousOn.congr _ _;
        use fun x => -x * Real.log x - ( 1 - x ) * Real.log ( 1 - x );
        · exact ContinuousOn.sub ( ContinuousOn.mul ( continuousOn_id.neg ) ( Real.continuousOn_log.mono ( by intro x hx; exact ne_of_gt ( by linarith [ hx.1 ] ) ) ) ) ( ContinuousOn.mul ( continuousOn_const.sub continuousOn_id ) ( ContinuousOn.log ( continuousOn_const.sub continuousOn_id ) ( by intro x hx; exact ne_of_gt ( by linarith [ hx.2 ] ) ) ) );
        · intro x hx; unfold H; norm_num [ Real.binEntropy ] ;
          ring;
      · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact Real.hasDerivAt_binEntropy ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) |> HasDerivAt.differentiableAt );
    have h_deriv : deriv H c = Real.log (1 - c) - Real.log c := by
      convert Real.deriv_binEntropy c using 1;
    have h_log_div : Real.log ((1 - b) / b) ≤ Real.log (1 - c) - Real.log c := by
      rw [ ← Real.log_div ( by linarith [ hc.1.1, hc.1.2 ] ) ( by linarith [ hc.1.1, hc.1.2 ] ) ] ; exact Real.log_le_log ( div_pos ( by linarith [ hc.1.1, hc.1.2 ] ) ( by linarith [ hc.1.1, hc.1.2 ] ) ) ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ hc.1.1, hc.1.2 ] ) ;
    rw [ eq_div_iff ] at hc <;> nlinarith [ hc.1.1, hc.1.2 ]

/-
Chord upper bound, mirror of `binEntropy_chord_lower`:
for `0 < a ≤ b ≤ 1/2`, `H b - H a ≤ (b - a) * log((1-a)/a)`.
-/
lemma binEntropy_chord_upper {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) :
    H b - H a ≤ (b - a) * Real.log ((1 - a) / a) := by
  by_cases h : a = b <;> simp_all +decide;
  -- Apply the mean value theorem to the interval [a, b].
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo a b, deriv Real.binEntropy c = (Real.binEntropy b - Real.binEntropy a) / (b - a) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact lt_of_le_of_ne hab h;
    · refine' ContinuousOn.add _ _ <;> norm_num at *;
      · exact ContinuousOn.neg ( Real.continuous_mul_log.continuousOn );
      · exact ContinuousOn.neg ( ContinuousOn.mul ( continuousOn_const.sub continuousOn_id ) ( ContinuousOn.log ( continuousOn_const.sub continuousOn_id ) fun x hx => by linarith [ hx.1, hx.2 ] ) );
    · refine' fun x hx => DifferentiableAt.differentiableWithinAt _;
      exact Real.hasDerivAt_binEntropy ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) |> HasDerivAt.differentiableAt;
  -- By the properties of the derivative and the concavity of the binary entropy function, we have:
  have h_deriv : deriv Real.binEntropy c ≤ Real.log ((1 - a) / a) := by
    rw [ Real.deriv_binEntropy ];
    rw [ Real.log_div ] <;> try linarith [ hc.1.1, hc.1.2 ];
    exact sub_le_sub ( Real.log_le_log ( by linarith [ hc.1.1, hc.1.2 ] ) ( by linarith [ hc.1.1, hc.1.2 ] ) ) ( Real.log_le_log ( by linarith [ hc.1.1, hc.1.2 ] ) ( by linarith [ hc.1.1, hc.1.2 ] ) );
  rw [ hc.2, div_le_iff₀ ] at h_deriv <;> linarith! [ hc.1.1, hc.1.2 ]

/-- Range control: the sub-equatorial cap forces `alpha + beta` away from the
equator, uniformly over the class, for all large `n`.

Proof route (prose R1, repaired round): `V(n,|S|,r) ≤ |Γ_r(S)| ≤
exp((1-δ)n log 2)` by `V_le_neighborhood_card` and `capHyp`; `V+` gives a
maximal `t*` with `ball(t*) ≤ |S| < ball(t*+1)` and
`ball(t*+r) ≤ V(n,|S|,r)`; the two-sided ball volume (`hBV`) turns this into
`H((t*+r)/n) ≤ (1-δ) log 2 + o(1)` (if `t*+r > n/2` the cap is violated
outright for large `n`), and `binEntropy_le_log_two_sub_two_sq` converts the
entropy deficit into `(t*+r)/n ≤ 1/2 - c0'`; finally `t*/n ≥ alpha - o(1)`
via the size hypothesis, the lower ball volume, and the chord bound
`binEntropy_chord_upper` (the derivative is bounded below on
`[alphaMin, alphaMax]` since `alphaMax < 1/2`). -/
private lemma r1_range_control_t_star (hVPlus : VPlusStatement) (n r : ℕ)
    (S : Finset (Cube n)) (hS_nonempty : S.Nonempty) (hS_not_full : S.card < 2 ^ n) :
    ∃ t : ℕ, t ≤ n ∧ (ball (∅ : Cube n) t).card ≤ S.card ∧
      ((ball (∅ : Cube n) (t + r)).card : ℝ) ≤ (V n S.card r : ℝ) ∧
      (S.card : ℝ) < ((ball (∅ : Cube n) (t + 1)).card : ℝ) := by
  classical
  have hS_one : 1 ≤ S.card := Finset.card_pos.mpr hS_nonempty
  have hS_le : S.card ≤ 2 ^ n := hS_not_full.le
  obtain ⟨t, ht_le, ht_card, ht_max, htV⟩ := hVPlus n S.card r hS_one hS_le
  refine ⟨t, ht_le, ht_card, htV, ?_⟩
  by_cases ht_succ : t + 1 ≤ n
  · by_contra hnot
    have hball_le_real :
        (((ball (∅ : Cube n) (t + 1)).card : ℕ) : ℝ) ≤ (S.card : ℝ) :=
      not_lt.mp hnot
    have hball_le : (ball (∅ : Cube n) (t + 1)).card ≤ S.card := by
      exact_mod_cast hball_le_real
    have := ht_max (t + 1) ht_succ hball_le
    omega
  · have hn_le : n ≤ t + 1 := Nat.le_of_not_ge ht_succ
    have huniv_subset : (Finset.univ : Finset (Cube n)) ⊆ ball (∅ : Cube n) (t + 1) := by
      intro x _hx
      have hdist_le_n : hDist x (∅ : Cube n) ≤ n := by
        unfold hDist
        calc (symmDiff x (∅ : Cube n)).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
          _ = n := by simp
      simpa [ball] using le_trans hdist_le_n hn_le
    have hcube_le_ball : 2 ^ n ≤ (ball (∅ : Cube n) (t + 1)).card := by
      calc 2 ^ n = (Finset.univ : Finset (Cube n)).card := by
            rw [Finset.card_univ]
            exact ((Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])).symm
        _ ≤ (ball (∅ : Cube n) (t + 1)).card :=
            Finset.card_le_card huniv_subset
    exact_mod_cast lt_of_lt_of_le hS_not_full hcube_le_ball

/-- Monotonicity of centered ball cardinality in the radius. -/
private lemma ball_empty_card_mono {n r s : ℕ} (h : r ≤ s) :
    (ball (∅ : Cube n) r).card ≤ (ball (∅ : Cube n) s).card := by
  apply Finset.card_le_card
  intro x hx
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact le_trans hx (by exact_mod_cast h)

/-- Near the equator the binary entropy exceeds any level below `log 2`. -/
private lemma binEntropy_near_half_gt {c : ℝ} (hc : c < Real.log 2) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 < 1 / 2 ∧ c < Real.binEntropy d0 := by
  have hval : Real.binEntropy (1/2 : ℝ) = Real.log 2 :=
    Real.binEntropy_eq_log_two.mpr (by norm_num)
  have hpre : Real.binEntropy ⁻¹' (Set.Ioi c) ∈ nhds (1/2 : ℝ) := by
    have htend : Filter.Tendsto Real.binEntropy (nhds (1/2:ℝ))
        (nhds (Real.binEntropy (1/2:ℝ))) := Real.binEntropy_continuous.continuousAt
    apply htend
    rw [hval]
    exact Ioi_mem_nhds hc
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨ε, hε, hsub⟩ := hpre
  refine ⟨1/2 - min (ε/2) (1/4), ?_, ?_, ?_⟩
  · have : min (ε/2) (1/4) ≤ 1/4 := min_le_right _ _
    linarith
  · have : 0 < min (ε/2) (1/4) := lt_min (by linarith) (by norm_num)
    linarith
  · have hmem : (1/2 - min (ε/2) (1/4)) ∈ Metric.ball (1/2:ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 : min (ε/2) (1/4) ≤ ε/2 := min_le_left _ _
      have h2 : 0 < min (ε/2) (1/4) := lt_min (by linarith) (by norm_num)
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact hsub hmem

private lemma r1_range_control_upper (hBV : BallVolumeTwoSidedStatement) (D : StabilityData) (hvalid : validData D) :
    ∃ c0' : ℝ, 0 < c0' ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n, N ≤ n → ∀ t r : ℕ,
        ((ball (∅ : Cube n) (t + r)).card : ℝ) ≤ Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) →
        ((t + r : ℝ) / (n : ℝ)) ≤ 1 / 2 - c0' := by
  classical
  obtain ⟨volumeSlack, hslack, hbound⟩ := hBV
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdelta_pos : 0 < D.deltaCap := hvalid.2.1
  have hdelta_lt : D.deltaCap < 1 := hvalid.2.2.1
  set c : ℝ := (1 - D.deltaCap) * Real.log 2 with hc_def
  have hc : c < Real.log 2 := by
    have hmul : 0 < D.deltaCap * Real.log 2 := mul_pos hdelta_pos hlog2
    rw [hc_def]; nlinarith [hmul]
  obtain ⟨d0, hd0pos, hd0half, hd0entropy⟩ := binEntropy_near_half_gt hc
  set g : ℝ := Real.binEntropy d0 - c with hg_def
  have hg_pos : 0 < g := by rw [hg_def]; linarith
  obtain ⟨N0, hN0⟩ := hslack.2 (g / 2) (by linarith)
  have h1m2d0 : 0 < 1 - 2 * d0 := by linarith
  set Nhalf : ℕ := ⌈1 / (1 - 2 * d0)⌉₊ with hNhalf_def
  refine ⟨1 / 2 - d0, by linarith, max (max N0 Nhalf) 1, le_max_right _ _, ?_⟩
  intro n hn t r hcard
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < (n : ℝ) := by linarith
  rw [show (1 : ℝ) / 2 - (1 / 2 - d0) = d0 by ring]
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : d0 < (↑t + ↑r) / ↑n`
  have hcast : ((t : ℝ) + (r : ℝ)) = ((t + r : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at hcon
  set m : ℕ := t + r with hm_def
  set t0 : ℕ := min m (n / 2) with ht0_def
  -- Numeric slacks
  have hN0_le : N0 ≤ n :=
    le_trans (le_trans (le_max_left N0 Nhalf) (le_max_left _ 1)) hn
  have hNhalf_le : Nhalf ≤ n :=
    le_trans (le_trans (le_max_right N0 Nhalf) (le_max_left _ 1)) hn
  have hslackn : volumeSlack n ≤ (g / 2) * (n : ℝ) := hN0 n hN0_le
  -- lower bound: `d0 * n ≤ ↑m`
  have hmn : d0 * (n : ℝ) < (m : ℝ) := (lt_div_iff₀ hnpos).mp hcon
  -- lower bound for the half radius: `d0 * n ≤ ↑(n/2)`
  have hn_ceil : (1 : ℝ) / (1 - 2 * d0) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hNhalf_le)
  have hn_prod : (1 : ℝ) ≤ (n : ℝ) * (1 - 2 * d0) := by
    rw [div_le_iff₀ h1m2d0] at hn_ceil; linarith
  have hhalf_nat : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    exact_mod_cast this
  have hhalf_n : d0 * (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by nlinarith [hn_prod, hhalf_nat]
  -- `d0 * n ≤ ↑t0`
  have ht0_cast : ((t0 : ℕ) : ℝ) = min (m : ℝ) ((n / 2 : ℕ) : ℝ) := by
    rw [ht0_def]; exact_mod_cast Nat.cast_min m (n / 2)
  have ht0_ge : d0 * (n : ℝ) ≤ (t0 : ℝ) := by
    rw [ht0_cast]; exact le_min hmn.le hhalf_n
  have hd0_le : d0 ≤ (t0 : ℝ) / (n : ℝ) := (le_div_iff₀ hnpos).mpr ht0_ge
  -- `↑t0 / n ≤ 1/2`
  have ht0_le_half_nat : ((t0 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have h1 : (t0 : ℕ) ≤ n / 2 := by rw [ht0_def]; exact min_le_right _ _
    have h2 : ((t0 : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
      have : 2 * (n / 2) ≤ n := by omega
      have : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    linarith
  have ht0_le_half : (t0 : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hnpos]; linarith [ht0_le_half_nat]
  -- monotonicity of binary entropy
  have hmem_d0 : d0 ∈ Set.Icc (0 : ℝ) 2⁻¹ :=
    ⟨hd0pos.le, by rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]; exact hd0half.le⟩
  have hmem_t0 : (t0 : ℝ) / (n : ℝ) ∈ Set.Icc (0 : ℝ) 2⁻¹ :=
    ⟨by positivity, by rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]; exact ht0_le_half⟩
  have hHmono : Real.binEntropy d0 ≤ H ((t0 : ℝ) / (n : ℝ)) :=
    Real.binEntropy_strictMonoOn.monotoneOn hmem_d0 hmem_t0 hd0_le
  -- volume chain
  have hlow := (hbound n t0 (by rw [ht0_def]; exact min_le_right _ _)).1
  have hmono_ball : ((ball (∅ : Cube n) t0).card : ℝ) ≤ ((ball (∅ : Cube n) m).card : ℝ) := by
    exact_mod_cast ball_empty_card_mono (n := n) (by rw [ht0_def]; exact min_le_left m (n / 2))
  have hcard' : ((ball (∅ : Cube n) m).card : ℝ) ≤ Real.exp (c * (n : ℝ)) := by
    have heq : (1 - D.deltaCap) * (n : ℝ) * Real.log 2 = c * (n : ℝ) := by rw [hc_def]; ring
    rw [heq] at hcard
    exact hcard
  have hchain : Real.exp (H ((t0 : ℝ) / (n : ℝ)) * (n : ℝ) - volumeSlack n) ≤
      Real.exp (c * (n : ℝ)) :=
    le_trans hlow (le_trans hmono_ball hcard')
  have hle := Real.exp_le_exp.mp hchain
  have hbd0 : Real.binEntropy d0 = c + g := by rw [hg_def]; ring
  rw [hbd0] at hHmono
  nlinarith [mul_le_mul_of_nonneg_right hHmono hnpos.le, hle, hslackn, hnpos, hg_pos]

private lemma r1_range_control_lower (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D) :
    ∃ s : ℕ → ℝ, Sublinear s ∧
      ∀ n, 1 ≤ n → ∀ t : ℕ, ∀ S : Finset (Cube n), ∀ alpha : ℝ,
        D.alphaMin ≤ alpha → alpha ≤ D.alphaMax →
        sizeHyp D n S alpha →
        (ball (∅ : Cube n) t).card ≤ S.card →
        (S.card : ℝ) < ((ball (∅ : Cube n) (t + 1)).card : ℝ) →
        alpha - s n / (n : ℝ) ≤ (t : ℝ) / (n : ℝ) := by
  classical
  let c0 : ℝ := (1 / 2 - D.alphaMax) / 2
  have hc0 : 0 < c0 := by
    dsimp [c0]
    linarith [hvalid.2.2.2.2.2.2.1]
  obtain ⟨C_V, hC_V, volSlack, hvolSlack, hcalc⟩ :=
    hVC D.alphaMin c0 hvalid.2.2.2.2.1 hc0
  refine ⟨fun n => C_V * (D.cSize * D.sigma n) + volSlack n + 1, ?_, ?_⟩
  · have hcoef : 0 ≤ C_V * D.cSize := by
      nlinarith [hC_V, hvalid.2.2.2.1]
    have hmain : Sublinear (fun n => (C_V * D.cSize) * D.sigma n) :=
      sublinear_const_mul (C_V * D.cSize) hcoef hvalid.2.2.2.2.2.2.2.1
    have hconst : Sublinear (fun _ : ℕ => (1 : ℝ)) := sublinear_const 1 (by norm_num)
    have hsum := reductions_sublinear_add (reductions_sublinear_add hmain hvolSlack) hconst
    convert hsum using 2 with n
    ring
  · intro n hn t S alpha halpha_min halpha_max hsize ht_card ht_strict
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have halpha_half : alpha ≤ 1 / 2 :=
      le_of_lt (lt_of_le_of_lt halpha_max hvalid.2.2.2.2.2.2.1)
    have hslack_nonneg : 0 ≤ D.cSize * D.sigma n := by
      exact mul_nonneg (le_trans zero_le_one hvalid.2.2.2.1)
        (hvalid.2.2.2.2.2.2.2.1.1 n)
    have hS1 : 1 ≤ S.card := by
      have hball_pos : 0 < (ball (∅ : Cube n) t).card := by
        apply Finset.card_pos.mpr
        exact ⟨∅, by simp [ball, hDist]⟩
      exact le_trans hball_pos ht_card
    have hScap : S.card ≤ 2 ^ n := by
      calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
        _ = 2 ^ n := by
            rw [Finset.card_univ]
            exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
    have hrange : alpha + (0 : ℝ) ≤ 1 / 2 - c0 := by
      dsimp [c0]
      nlinarith [halpha_max]
    obtain ⟨_, hrmin⟩ := hcalc n S.card 0 alpha 0 (D.cSize * D.sigma n)
      halpha_min halpha_half hslack_nonneg (by simp) hrange hS1 hScap hsize
    have hcard_succ : S.card ≤ (ball (∅ : Cube n) (t + 1)).card := by
      have hstrict_nat : S.card < (ball (∅ : Cube n) (t + 1)).card := by
        exact_mod_cast ht_strict
      exact hstrict_nat.le
    have hrmin_le_succ : rmin n S.card ≤ t + 1 := by
      let vals := (Finset.range (n + 1)).filter
        fun r => S.card ≤ (ball (∅ : Cube n) r).card
      by_cases ht_le_n : t + 1 ≤ n
      · have hmem : t + 1 ∈ vals := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ht_le_n), hcard_succ⟩
        have hvals : vals.Nonempty := ⟨t + 1, hmem⟩
        unfold rmin
        change (if h : vals.Nonempty then vals.min' h else n) ≤ t + 1
        rw [dif_pos hvals]
        exact vals.min'_le (t + 1) hmem
      · have hn_le_t : n ≤ t + 1 := Nat.le_of_not_ge ht_le_n
        have hrmin_le_n : rmin n S.card ≤ n := by
          unfold rmin
          change (if h : vals.Nonempty then vals.min' h else n) ≤ n
          by_cases hvals : vals.Nonempty
          · rw [dif_pos hvals]
            exact Nat.lt_succ_iff.mp
              (Finset.mem_range.mp (Finset.mem_filter.mp (vals.min'_mem hvals)).1)
          · rw [dif_neg hvals]
        exact le_trans hrmin_le_n hn_le_t
    have hE_lower :
        alpha * (n : ℝ) - (C_V * (D.cSize * D.sigma n) + volSlack n) ≤
          (rmin n S.card : ℝ) := by
      have := (abs_le.mp hrmin).1
      linarith
    have hrmin_le_succ_real : (rmin n S.card : ℝ) ≤ (t : ℝ) + 1 := by
      exact_mod_cast hrmin_le_succ
    have ht_lower :
        alpha * (n : ℝ) - (C_V * (D.cSize * D.sigma n) + volSlack n) - 1 ≤
          (t : ℝ) := by
      linarith
    rw [le_div_iff₀ hnpos]
    field_simp [hn_ne]
    nlinarith

/-- Harper-minimum bound: for any set `S`, the Harper minimum `V n |S| r` is at
most the size of `S`'s own `r`-neighborhood (since `S` is one of the families of
cardinality `|S|` over which `V` minimizes).  This is the elementary lower
containment used throughout the volume-based reduction arguments. -/
private lemma V_le_neighborhood_card {n : ℕ} (r : ℕ) (S : Finset (Cube n)) :
    (V n S.card r : ℝ) ≤ ((neighborhood r S).card : ℝ) := by
  classical
  set fams := (Finset.univ : Finset (Cube n)).powerset.filter
    (fun A : Finset (Cube n) => A.card = S.card) with hfams
  set vals := fams.image (fun A => (neighborhood r A).card) with hvals
  have hmem : (neighborhood r S).card ∈ vals := by
    refine Finset.mem_image.mpr ⟨S, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), rfl⟩
  have hne : vals.Nonempty := ⟨_, hmem⟩
  have hle : V n S.card r ≤ (neighborhood r S).card := by
    unfold V
    simp only [← hfams, ← hvals, dif_pos hne]
    exact Finset.min'_le _ _ hmem
  exact_mod_cast hle

lemma r1_range_control (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n, N ≤ n → ∀ (r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ),
        classMember D n r S alpha beta → alpha + beta ≤ 1 / 2 - c0 := by
  classical
  obtain ⟨cUpper, hcUpper, NUpper, hNUpper1, hupper⟩ :=
    r1_range_control_upper hBV D hvalid
  obtain ⟨sLower, hsLower, hlower⟩ := r1_range_control_lower hVC D hvalid
  obtain ⟨NSlack, hNSlack⟩ := hsLower.2 (cUpper / 2) (by linarith)
  have halphaMin_pos : 0 < D.alphaMin := hvalid.2.2.2.2.1
  have halphaMin_lt_one : D.alphaMin < 1 := by
    linarith [hvalid.2.2.2.2.2.1, hvalid.2.2.2.2.2.2.1]
  have hHamin_pos : 0 < H D.alphaMin := by
    unfold H
    exact Real.binEntropy_pos halphaMin_pos halphaMin_lt_one
  have hcSize_pos : 0 < D.cSize := lt_of_lt_of_le zero_lt_one hvalid.2.2.2.1
  obtain ⟨NNonempty, hNNonempty⟩ :=
    hvalid.2.2.2.2.2.2.2.1.2 (H D.alphaMin / (2 * D.cSize)) (by positivity)
  refine ⟨cUpper / 2, by linarith, max NUpper (max NSlack (max NNonempty 1)), ?_, ?_⟩
  · omega
  · intro n hn r S alpha beta hmem
    have hNUpper : NUpper ≤ n := by omega
    have hNSlack_n : NSlack ≤ n := by omega
    have hNNonempty_n : NNonempty ≤ n := by omega
    have hn1 : 1 ≤ n := le_trans hNUpper1 hNUpper
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    rcases hmem with
      ⟨_hvalidD, hbeta, halpha_min, halpha_max, _hradius, hsize, _hnear, hcap⟩
    have halpha_nonneg : 0 ≤ alpha := le_trans halphaMin_pos.le halpha_min
    have halpha_half : alpha ≤ 1 / 2 :=
      le_of_lt (lt_of_le_of_lt halpha_max hvalid.2.2.2.2.2.2.1)
    have hHalpha_nonneg : 0 ≤ H alpha := by
      unfold H
      exact Real.binEntropy_nonneg halpha_nonneg (by linarith)
    have hHamin_le_alpha : H D.alphaMin ≤ H alpha :=
      H_mono_on_half halphaMin_pos.le halpha_min halpha_half
    have hS_nonempty : S.Nonempty := by
      have hS_pos_nat : 0 < S.card := by
        by_contra hnot_pos
        have hS0 : S.card = 0 := Nat.eq_zero_of_not_pos hnot_pos
        have hHn_nonneg : 0 ≤ H alpha * (n : ℝ) :=
          mul_nonneg hHalpha_nonneg (Nat.cast_nonneg n)
        have hHn_le : H alpha * (n : ℝ) ≤ D.cSize * D.sigma n := by
          rw [sizeHyp, hS0, Nat.cast_zero, Real.log_zero] at hsize
          simpa [abs_of_nonneg hHn_nonneg] using hsize
        have hsigma_bound :
            D.sigma n ≤ (H D.alphaMin / (2 * D.cSize)) * (n : ℝ) :=
          hNNonempty n hNNonempty_n
        have hc_sigma :
          D.cSize * D.sigma n ≤ (H D.alphaMin / 2) * (n : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left hsigma_bound hcSize_pos.le
          have heq :
              D.cSize * (H D.alphaMin / (2 * D.cSize) * (n : ℝ)) =
                (H D.alphaMin / 2) * (n : ℝ) := by
            field_simp [hcSize_pos.ne']
          simpa [heq] using hmul
        have hHamin_n_le : H D.alphaMin * (n : ℝ) ≤ H alpha * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hHamin_le_alpha (Nat.cast_nonneg n)
        nlinarith
      exact Finset.card_pos.mp hS_pos_nat
    have hS_not_full : S.card < 2 ^ n := by
      by_contra hnot_lt
      have hpow_le_S : 2 ^ n ≤ S.card := Nat.le_of_not_gt hnot_lt
      have hpow_le_neigh_nat : 2 ^ n ≤ (neighborhood r S).card :=
        le_trans hpow_le_S (Finset.card_le_card (subset_neighborhood_self r S))
      have hpow_le_neigh :
          (((2 ^ n : ℕ) : ℝ) ≤ ((neighborhood r S).card : ℝ)) := by
        exact_mod_cast hpow_le_neigh_nat
      have hpow_exp : ((2 ^ n : ℕ) : ℝ) =
          Real.exp ((n : ℝ) * Real.log 2) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hexp_le :
          Real.exp ((n : ℝ) * Real.log 2) ≤
            Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) := by
        rw [← hpow_exp]
        exact le_trans hpow_le_neigh hcap
      have harg_le := Real.exp_le_exp.mp hexp_le
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hprod_pos : 0 < D.deltaCap * (n : ℝ) * Real.log 2 :=
        mul_pos (mul_pos hvalid.2.1 hnpos) hlog2_pos
      nlinarith
    obtain ⟨t, _ht_le, ht_card, htV, ht_strict⟩ :=
      r1_range_control_t_star hVPlus n r S hS_nonempty hS_not_full
    have hball_cap :
        ((ball (∅ : Cube n) (t + r)).card : ℝ) ≤
          Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) := by
      calc ((ball (∅ : Cube n) (t + r)).card : ℝ)
          ≤ (V n S.card r : ℝ) := htV
        _ ≤ ((neighborhood r S).card : ℝ) := V_le_neighborhood_card r S
        _ ≤ Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) := hcap
    have hupper_n := hupper n hNUpper t r hball_cap
    have hlower_n :=
      hlower n hn1 t S alpha halpha_min halpha_max hsize ht_card ht_strict
    have hsdiv : sLower n / (n : ℝ) ≤ cUpper / 2 := by
      rw [div_le_iff₀ hnpos]
      exact hNSlack n hNSlack_n
    have ht_add : ((t : ℝ) + (r : ℝ)) / (n : ℝ) =
        (t : ℝ) / (n : ℝ) + beta := by
      rw [hbeta]
      field_simp [hn_ne]
    rw [ht_add] at hupper_n
    nlinarith

private lemma rmin_mono {n k1 k2 : ℕ} (h : k1 ≤ k2) : rmin n k1 ≤ rmin n k2 := by
  classical
  let vals1 := (Finset.range (n + 1)).filter fun r => k1 ≤ (ball (∅ : Cube n) r).card
  let vals2 := (Finset.range (n + 1)).filter fun r => k2 ≤ (ball (∅ : Cube n) r).card
  have hsubset : vals2 ⊆ vals1 := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hr'.1, le_trans h hr'.2⟩
  unfold rmin
  change (if h1 : vals1.Nonempty then vals1.min' h1 else n) ≤
    (if h2 : vals2.Nonempty then vals2.min' h2 else n)
  by_cases h2 : vals2.Nonempty
  · have h1 : vals1.Nonempty := by
      rcases h2 with ⟨r, hr⟩
      exact ⟨r, hsubset hr⟩
    rw [dif_pos h1, dif_pos h2]
    exact vals1.min'_le (vals2.min' h2) (hsubset (vals2.min'_mem h2))
  · rw [dif_neg h2]
    by_cases h1 : vals1.Nonempty
    · rw [dif_pos h1]
      exact Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp (vals1.min'_mem h1)).1)
    · rw [dif_neg h1]

lemma r1a_subset_sizeHyp {Din : StabilityData} {n : ℕ} {S R : Finset (Cube n)} {epsCover alpha : ℝ}
    (heps : 0 < epsCover) (heps_le : epsCover ≤ 1)
    (hsub : R ⊆ S) (hlarge : epsCover * (S.card : ℝ) ≤ (R.card : ℝ))
    (hsize : sizeHyp Din n S alpha) :
    |Real.log (R.card : ℝ) - H alpha * (n : ℝ)| ≤ Din.cSize * Din.sigma n - Real.log epsCover := by
  classical
  have hlog_eps_nonpos : Real.log epsCover ≤ 0 := Real.log_nonpos heps.le heps_le
  have hrhs_mono :
      Din.cSize * Din.sigma n ≤ Din.cSize * Din.sigma n - Real.log epsCover := by
    linarith
  have hcard_RS : R.card ≤ S.card := Finset.card_le_card hsub
  by_cases hS0 : S.card = 0
  · have hR0 : R.card = 0 := Nat.eq_zero_of_le_zero (by simpa [hS0] using hcard_RS)
    exact (by
      rw [sizeHyp] at hsize
      simpa [hR0, hS0] using le_trans hsize hrhs_mono)
  · have hSpos_nat : 0 < S.card := Nat.pos_of_ne_zero hS0
    have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hSpos_nat
    have hRpos : 0 < (R.card : ℝ) := lt_of_lt_of_le (mul_pos heps hSpos) hlarge
    have hlogR_le_logS : Real.log (R.card : ℝ) ≤ Real.log (S.card : ℝ) := by
      exact Real.log_le_log hRpos (by exact_mod_cast hcard_RS)
    have hlog_mul_le_logR :
        Real.log (epsCover * (S.card : ℝ)) ≤ Real.log (R.card : ℝ) := by
      exact Real.log_le_log (mul_pos heps hSpos) hlarge
    have hlog_eps_add_logS_le_logR :
        Real.log epsCover + Real.log (S.card : ℝ) ≤ Real.log (R.card : ℝ) := by
      simpa [Real.log_mul heps.ne' hSpos.ne'] using hlog_mul_le_logR
    rw [sizeHyp] at hsize
    rw [abs_le] at hsize ⊢
    constructor
    · linarith
    · linarith

private lemma r1a_subset_nearOptimalHyp (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (Din : StabilityData) (epsCover : ℝ) (hvalid : validData Din) (heps : 0 < epsCover)
    (heps_le : epsCover ≤ 1) :
    ∃ (D_R : StabilityData), degradedData Din D_R ∧
      (∀ n, D_R.cSize * D_R.sigma n ≥ Din.cSize * Din.sigma n - Real.log epsCover) ∧
    ∀ n r S R alpha beta, classMember Din n r S alpha beta →
      R ⊆ S → epsCover * (S.card : ℝ) ≤ (R.card : ℝ) →
      nearOptimalHyp D_R n r R := by
  classical
  obtain ⟨c0, hc0, N, hN1, hrange⟩ := r1_range_control hBV hVPlus hVC Din hvalid
  obtain ⟨C_V, hC_V, volSlack, hvolSlack, hcalc⟩ :=
    hVC Din.alphaMin c0 hvalid.2.2.2.2.1 hc0
  have hlogeps : Real.log epsCover ≤ 0 := Real.log_nonpos heps.le heps_le
  have hsigma0 : ∀ n, 0 ≤ Din.sigma n := hvalid.2.2.2.2.2.2.2.1.1
  have hcSize1 : (1 : ℝ) ≤ Din.cSize := hvalid.2.2.2.1
  -- the degraded envelope: prefix bump + main volume-calculus slack
  set E : ℕ → ℝ := fun n =>
    Din.sigma n + 2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) +
      2 * volSlack n with hE
  set sigma' : ℕ → ℝ := fun n =>
    (if n < N then (n : ℝ) * Real.log 2 else 0) + E n with hsigma'
  have hterm_nonneg : ∀ n, 0 ≤ Din.cSize * Din.sigma n - Real.log epsCover := by
    intro n
    have h := mul_nonneg (le_trans zero_le_one hcSize1) (hsigma0 n)
    linarith
  have hE_ge_sigma : ∀ n, Din.sigma n ≤ E n := by
    intro n
    have h1 : 0 ≤ 2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) := by
      nlinarith [hterm_nonneg n, hC_V]
    have h2 : 0 ≤ volSlack n := hvolSlack.1 n
    simp only [hE]
    linarith
  have hE_sub : Sublinear E := by
    have h1 : Sublinear (fun n => 2 * C_V * (Din.cSize * Din.sigma n)) := by
      have := sublinear_const_mul (2 * C_V * Din.cSize)
        (by nlinarith [hC_V, hcSize1]) hvalid.2.2.2.2.2.2.2.1
      convert this using 2 with n
      ring
    have h2 : Sublinear (fun n => 2 * C_V * (-Real.log epsCover)) :=
      sublinear_const _ (by nlinarith [hC_V, hlogeps])
    have h3 : Sublinear (fun n => 2 * volSlack n) :=
      sublinear_const_mul 2 (by norm_num) hvolSlack
    have h12 := reductions_sublinear_add h1 h2
    have h123 := reductions_sublinear_add h12 h3
    have h := reductions_sublinear_add hvalid.2.2.2.2.2.2.2.1 h123
    convert h using 2 with n
    simp only [hE]
    ring
  have hif_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ if n < N then (n : ℝ) * Real.log 2 else 0 := by
    intro n
    by_cases h : n < N
    · simp only [if_pos h]
      exact mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg one_le_two)
    · simp [h]
  have hsigma'_sub : Sublinear sigma' :=
    reductions_sublinear_add
      (sublinear_indicator_prefix _
        (fun n => mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg one_le_two)) N)
      hE_sub
  have hsigma'_ge_sigma : ∀ n, Din.sigma n ≤ sigma' n := by
    intro n
    have h1 := hif_nonneg n
    have := hE_ge_sigma n
    simp only [hsigma']
    linarith
  have hsigma'_nonneg : ∀ n, 0 ≤ sigma' n := fun n =>
    le_trans (hsigma0 n) (hsigma'_ge_sigma n)
  set D_R : StabilityData := { Din with sigma := sigma' } with hD_R
  have hvalidR : validData D_R := by
    refine ⟨hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1,
      hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1, hvalid.2.2.2.2.2.2.1,
      hsigma'_sub, ?_⟩
    intro n hn
    exact le_trans (hvalid.2.2.2.2.2.2.2.2 n hn) (hsigma'_ge_sigma n)
  have hdeg : degradedData Din D_R :=
    ⟨hvalidR, rfl, rfl, le_rfl, rfl, rfl, hsigma'_ge_sigma⟩
  have hslack_ge : ∀ n, D_R.cSize * D_R.sigma n ≥
      Din.cSize * Din.sigma n - Real.log epsCover := by
    intro n
    have h1 : sigma' n ≥ E n := by
      have h0 := hif_nonneg n
      simp only [hsigma']
      linarith
    have h2 : E n ≥ Din.cSize * Din.sigma n - Real.log epsCover := by
      have ht := hterm_nonneg n
      have hv := hvolSlack.1 n
      have hs := hsigma0 n
      have : 2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) ≥
          Din.cSize * Din.sigma n - Real.log epsCover := by nlinarith
      simp only [hE]
      linarith
    have h3 : D_R.cSize * D_R.sigma n ≥ D_R.sigma n := by
      have : D_R.sigma n = sigma' n := rfl
      have hs' := hsigma'_nonneg n
      nlinarith [hcSize1]
    calc D_R.cSize * D_R.sigma n ≥ D_R.sigma n := h3
      _ = sigma' n := rfl
      _ ≥ E n := h1
      _ ≥ Din.cSize * Din.sigma n - Real.log epsCover := h2
  refine ⟨D_R, hdeg, hslack_ge, ?_⟩
  intro n r S R alpha beta hmem hsub hlarge
  dsimp [nearOptimalHyp]
  -- trivial cases first: empty S (hence empty R), then small n
  by_cases hS0 : S.card = 0
  · have hR0 : R.card = 0 :=
      Nat.eq_zero_of_le_zero (le_trans (Finset.card_le_card hsub) (le_of_eq hS0))
    have hRempty : R = ∅ := Finset.card_eq_zero.mp hR0
    have hΓ : neighborhood r R = ∅ := by
      rw [hRempty]
      ext x
      simp [mem_neighborhood_iff]
    rw [hΓ]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hSpos : 0 < (S.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hS0
    have hRpos : 0 < (R.card : ℝ) := lt_of_lt_of_le (by positivity) hlarge
    have hRpos_nat : 1 ≤ R.card := by exact_mod_cast hRpos
    have hR1 : (1 : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast hRpos_nat
    have hRcap : R.card ≤ 2 ^ n := by
      calc R.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ R
        _ = 2 ^ n := by
            rw [Finset.card_univ]
            exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
    have hV_R_ge : (R.card : ℝ) ≤ (V n R.card r : ℝ) := card_le_V R.card r hRcap
    have hV_R_pos : 0 < (V n R.card r : ℝ) := lt_of_lt_of_le hRpos hV_R_ge
    by_cases hn_small : n < N
    · -- bump branch: the whole cube fits under the prefix envelope
      have hbump : sigma' n = (n : ℝ) * Real.log 2 + E n := by
        simp only [hsigma', if_pos hn_small]
      have hcard := cube_card_le_two_pow (neighborhood r R)
      have hEn : 0 ≤ E n := le_trans (hsigma0 n) (hE_ge_sigma n)
      calc ((neighborhood r R).card : ℝ)
          ≤ Real.exp ((n : ℝ) * Real.log 2) := hcard
        _ ≤ Real.exp ((n : ℝ) * Real.log 2) * (V n R.card r : ℝ) :=
            le_mul_of_one_le_right (Real.exp_pos _).le (le_trans hR1 hV_R_ge)
        _ ≤ Real.exp (D_R.sigma n) * (V n R.card r : ℝ) := by
            have hle : Real.exp ((n : ℝ) * Real.log 2) ≤ Real.exp (D_R.sigma n) := by
              apply Real.exp_le_exp.mpr
              show (n : ℝ) * Real.log 2 ≤ sigma' n
              rw [hbump]
              linarith
            exact mul_le_mul_of_nonneg_right hle hV_R_pos.le
    · -- main branch: range control + two applications of the volume calculus
      have hnN : N ≤ n := not_lt.mp hn_small
      have hn1 : 1 ≤ n := le_trans hN1 hnN
      have hrange_n := hrange n hnN r S alpha beta hmem
      have hαmin : Din.alphaMin ≤ alpha := hmem.2.2.1
      have hαhalf : alpha ≤ 1 / 2 :=
        le_of_lt (lt_of_le_of_lt hmem.2.2.2.1 hvalid.2.2.2.2.2.2.1)
      have hbeta : beta = (r : ℝ) / (n : ℝ) := hmem.2.1
      have hScap : S.card ≤ 2 ^ n := by
        calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
          _ = 2 ^ n := by
              rw [Finset.card_univ]
              exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
      have hS1 : 1 ≤ S.card := by
        exact_mod_cast Nat.pos_of_ne_zero hS0
      have hsizeS := hmem.2.2.2.2.2.1
      have hslackS : (0 : ℝ) ≤ Din.cSize * Din.sigma n :=
        mul_nonneg (le_trans zero_le_one hcSize1) (hsigma0 n)
      obtain ⟨hVS, _⟩ := hcalc n S.card r alpha beta (Din.cSize * Din.sigma n)
        hαmin hαhalf hslackS hbeta hrange_n hS1 hScap hsizeS
      have hsizeR := r1a_subset_sizeHyp heps heps_le hsub hlarge hsizeS
      obtain ⟨hVR, _⟩ := hcalc n R.card r alpha beta
        (Din.cSize * Din.sigma n - Real.log epsCover)
        hαmin hαhalf (hterm_nonneg n) hbeta hrange_n hRpos_nat hRcap hsizeR
      -- combine the two-sided volume estimates
      have hV_S_pos : 0 < (V n S.card r : ℝ) :=
        lt_of_lt_of_le hSpos (card_le_V S.card r hScap)
      have hVS' := abs_le.mp hVS
      have hVR' := abs_le.mp hVR
      have hlog_le : Real.log (V n S.card r : ℝ) ≤
          (2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) +
            2 * volSlack n) + Real.log (V n R.card r : ℝ) := by
        have h1 : C_V * (Din.cSize * Din.sigma n) ≤
            C_V * (Din.cSize * Din.sigma n - Real.log epsCover) := by
          nlinarith [hC_V, hlogeps]
        linarith [hVS'.2, hVR'.1]
      have hVcompare : (V n S.card r : ℝ) ≤
          Real.exp (2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) +
            2 * volSlack n) * (V n R.card r : ℝ) := by
        have h := Real.exp_le_exp.mpr hlog_le
        rwa [Real.exp_log hV_S_pos, Real.exp_add, Real.exp_log hV_R_pos] at h
      have hnearS := hmem.2.2.2.2.2.2.1
      have hmono : ((neighborhood r R).card : ℝ) ≤ ((neighborhood r S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (neighborhood_mono_set hsub)
      have hnoBump : sigma' n = E n := by
        simp only [hsigma', if_neg hn_small, zero_add]
      calc ((neighborhood r R).card : ℝ)
          ≤ ((neighborhood r S).card : ℝ) := hmono
        _ ≤ Real.exp (Din.sigma n) * (V n S.card r : ℝ) := hnearS
        _ ≤ Real.exp (Din.sigma n) *
              (Real.exp (2 * C_V * (Din.cSize * Din.sigma n - Real.log epsCover) +
                2 * volSlack n) * (V n R.card r : ℝ)) :=
            mul_le_mul_of_nonneg_left hVcompare (Real.exp_pos (Din.sigma n)).le
        _ = Real.exp (E n) * (V n R.card r : ℝ) := by
            rw [← mul_assoc, ← Real.exp_add]
            congr 1
            simp only [hE]
            ring_nf
        _ = Real.exp (D_R.sigma n) * (V n R.card r : ℝ) := by
            rw [show D_R.sigma n = sigma' n from rfl, hnoBump]

lemma r1a_subset_capHyp {Din Dout : StabilityData} {n r : ℕ} {S R : Finset (Cube n)}
    (hsub : R ⊆ S) (hdeg : degradedData Din Dout) (hcap : capHyp Din n r S) :
    capHyp Dout n r R := by
  have hneigh_sub : neighborhood r R ⊆ neighborhood r S := by
    intro x hx
    rw [mem_neighborhood_iff] at hx ⊢
    rcases hx with ⟨u, hu, hdist⟩
    exact ⟨u, hsub hu, hdist⟩
  have hcard :
      ((neighborhood r R).card : ℝ) ≤ ((neighborhood r S).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hneigh_sub
  dsimp [capHyp] at hcap ⊢
  exact le_trans hcard (by simpa [← hdeg.2.2.1] using hcap)

private lemma r1a_degraded_for_subset (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (Din : StabilityData) (epsCover : ℝ) (hvalid : validData Din) (heps : 0 < epsCover)
    (heps_le : epsCover ≤ 1) :
    ∃ D_R : StabilityData, degradedData Din D_R ∧
    ∀ n r S R alpha beta, classMember Din n r S alpha beta →
      R ⊆ S → epsCover * (S.card : ℝ) ≤ (R.card : ℝ) →
      classMember D_R n r R alpha beta := by
  obtain ⟨D_R, hdeg, hsigma, hnear⟩ :=
    r1a_subset_nearOptimalHyp hBV hVPlus hVC Din epsCover hvalid heps heps_le
  refine ⟨D_R, hdeg, ?_⟩
  intro n r S R alpha beta hmem hsub hlarge
  have hcap_S : capHyp Din n r S := hmem.2.2.2.2.2.2.2
  have hcap_R : capHyp D_R n r R := r1a_subset_capHyp hsub hdeg hcap_S
  have hsize_S : sizeHyp Din n S alpha := hmem.2.2.2.2.2.1
  have hsize_R_bound : |Real.log (R.card : ℝ) - H alpha * (n : ℝ)| ≤ Din.cSize * Din.sigma n - Real.log epsCover :=
    r1a_subset_sizeHyp heps heps_le hsub hlarge hsize_S
  have hsize_R : sizeHyp D_R n R alpha := le_trans hsize_R_bound (hsigma n)
  refine ⟨hdeg.1, hmem.2.1, ?_, ?_, ?_, hsize_R, hnear n r S R alpha beta hmem hsub hlarge, hcap_R⟩
  · exact le_trans (by rw [← hdeg.2.2.2.2.1]; exact hmem.2.2.1) le_rfl
  · exact le_trans le_rfl (by rw [← hdeg.2.2.2.2.2.1]; exact hmem.2.2.2.1)
  · exact (by rw [← hdeg.2.1]; exact hmem.2.2.2.2.1)

lemma stabilityCoverConclusion_empty_of_one_le {n : ℕ}
    {S : Finset (Cube n)} {epsCover coverSlack : ℝ} {radiusSlack : ℕ}
    (heps : 1 ≤ epsCover) :
    stabilityCoverConclusion n S epsCover coverSlack radiusSlack := by
  refine ⟨∅, ?_, ?_⟩
  · simpa using (Real.exp_nonneg coverSlack)
  · simp [coveredByBalls]
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le S.card
    nlinarith

private lemma heavyBallConclusion_of_degraded_hbl {Din Dout : StabilityData} {n r : ℕ}
    {S : Finset (Cube n)} {alpha beta : ℝ}
    (_hdeg : degradedData Din Dout) (hHBL : HBLFor Din Dout)
    (hmem : classMember Din n r S alpha beta) :
    heavyBallConclusion n S (Dout.sigma n) (Nat.ceil (Dout.sigma n)) :=
  hHBL hmem

private lemma CoverFor_of_one_le {Din Dout : StabilityData} {epsCover : ℝ}
    (heps : 1 ≤ epsCover) : CoverFor Din Dout epsCover := by
  intro n r S alpha beta _hmem
  exact stabilityCoverConclusion_empty_of_one_le (n := n) (S := S)
    (epsCover := epsCover) (coverSlack := Dout.sigma n)
    (radiusSlack := Nat.ceil (Dout.sigma n)) heps

private lemma coveredByBalls_mono_radius {n : ℕ} (S centers : Finset (Cube n))
    {radius radius' : ℕ} (hradius : radius ≤ radius') :
    coveredByBalls S centers radius ⊆ coveredByBalls S centers radius' := by
  intro x hx
  rcases (by simpa [coveredByBalls] using hx) with ⟨hxS, c, hc, hdist⟩
  exact (by
    simp [coveredByBalls, hxS]
    exact ⟨c, hc, le_trans hdist hradius⟩)

lemma stabilityCoverConclusion_mono {n : ℕ} {S : Finset (Cube n)}
    {epsCover coverSlack coverSlack' : ℝ} {radiusSlack radiusSlack' : ℕ}
    (hcoverSlack : coverSlack ≤ coverSlack')
    (hradiusSlack : radiusSlack ≤ radiusSlack')
    (hcover : stabilityCoverConclusion n S epsCover coverSlack radiusSlack) :
    stabilityCoverConclusion n S epsCover coverSlack' radiusSlack' := by
  rcases hcover with ⟨centers, hcenters, hmiss⟩
  refine ⟨centers, ?_, ?_⟩
  · exact le_trans hcenters (Real.exp_le_exp.mpr hcoverSlack)
  · let oldRadius := rmin n S.card + radiusSlack
    let newRadius := rmin n S.card + radiusSlack'
    have hradius : oldRadius ≤ newRadius := by
      dsimp [oldRadius, newRadius]
      exact Nat.add_le_add_left hradiusSlack (rmin n S.card)
    have hsubset :
        coveredByBalls S centers oldRadius ⊆ coveredByBalls S centers newRadius :=
      coveredByBalls_mono_radius S centers hradius
    have hcard_le :
        (coveredByBalls S centers oldRadius).card ≤
          (coveredByBalls S centers newRadius).card :=
      Finset.card_le_card hsubset
    have hmiss_le :
        ((S.card - (coveredByBalls S centers newRadius).card : ℕ) : ℝ) ≤
          ((S.card - (coveredByBalls S centers oldRadius).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_left hcard_le S.card
    exact le_trans hmiss_le (by simpa [oldRadius] using hmiss)

/-
Abstract greedy peeling for a heavy-ball cover.  If, for every residual
subset `R ⊆ S` whose mass is still at least `thresh`, some center captures a
`δ`-fraction of `R` within `radius`, then after `k` greedy steps we can cover
`S` with at most `k` centers so that the uncovered mass is either already below
`thresh` or has decayed by the factor `(1 - δ) ^ k`.
-/
private lemma greedy_peel_cover {n : ℕ} (S : Finset (Cube n)) (radius : ℕ)
    (δ thresh : ℝ) (hδ1 : δ ≤ 1)
    (hstep : ∀ R : Finset (Cube n), R ⊆ S → thresh ≤ (R.card : ℝ) →
        ∃ a : Cube n,
          δ * (R.card : ℝ) ≤
            ((R.filter fun x => hDist x a ≤ radius).card : ℝ)) :
    ∀ k : ℕ, ∃ centers : Finset (Cube n),
        centers.card ≤ k ∧
        ((S.card : ℝ) - ((coveredByBalls S centers radius).card : ℝ) ≤ thresh
          ∨ (S.card : ℝ) - ((coveredByBalls S centers radius).card : ℝ)
              ≤ (1 - δ) ^ k * (S.card : ℝ)) := by
  intro k;
  induction' k with k ih generalizing S;
  · unfold coveredByBalls; aesop;
  · obtain ⟨ centers, hcenters₁, hcenters₂ ⟩ := ih S hstep;
    by_cases h : (S.card : ℝ) - (coveredByBalls S centers radius).card ≤ thresh;
    · exact ⟨ centers, Nat.le_succ_of_le hcenters₁, Or.inl h ⟩;
    · obtain ⟨ a, ha ⟩ := hstep ( S \ coveredByBalls S centers radius ) ( Finset.sdiff_subset ) ( by
        rw [ Finset.card_sdiff ];
        rw [ Nat.cast_sub ];
        · rw [ Finset.inter_eq_left.mpr ];
          · linarith;
          · exact fun x hx => Finset.mem_filter.mp hx |>.1;
        · exact Finset.card_le_card fun x hx => by aesop; );
      refine' ⟨ Insert.insert a centers, _, _ ⟩ <;> simp_all +decide [ Finset.card_sdiff ];
      · exact Finset.card_insert_le _ _ |> le_trans <| Nat.succ_le_succ hcenters₁;
      · have h_covered : (coveredByBalls S (insert a centers) radius).card ≥ (coveredByBalls S centers radius).card + (Finset.filter (fun x => hDist x a ≤ radius) (S \ coveredByBalls S centers radius)).card := by
          rw [ ← Finset.card_union_of_disjoint ];
          · refine Finset.card_mono ?_;
            simp +decide [ Finset.subset_iff, coveredByBalls ];
            grind;
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx₂ |>.1 ) |>.2 hx₁;
        rw [ Nat.cast_sub ] at *;
        · rw [ show ( coveredByBalls S centers radius ∩ S : Finset ( Cube n ) ) = coveredByBalls S centers radius from Finset.inter_eq_left.mpr <| Finset.filter_subset _ _ ] at ha;
          exact Or.inr ( by rw [ pow_succ' ] ; nlinarith [ show ( Finset.card ( coveredByBalls S ( insert a centers ) radius ) : ℝ ) ≥ Finset.card ( coveredByBalls S centers radius ) + Finset.card ( Finset.filter ( fun x => hDist x a ≤ radius ) ( S \ coveredByBalls S centers radius ) ) by exact_mod_cast h_covered ] );
        · exact Finset.card_le_card fun x hx => by aesop;

lemma r1a_cover_of_hbl (Din D_R Dhbl : StabilityData) (epsCover : ℝ)
    (heps : 0 < epsCover) (hdeg : degradedData Din Dhbl) (hHBL : HBLFor D_R Dhbl)
    (h_subset : ∀ n r S R alpha beta, classMember Din n r S alpha beta →
      R ⊆ S → epsCover * (S.card : ℝ) ≤ (R.card : ℝ) →
      classMember D_R n r R alpha beta) :
    ∃ Dcover : StabilityData, degradedData Din Dcover ∧
      CoverFor Din Dcover epsCover := by
  use {Dhbl with sigma := fun n => Dhbl.sigma n + Real.log (max 0 (-Real.log epsCover) + 1)};
  constructor;
  · constructor;
    · obtain ⟨ h₁, h₂ ⟩ := hdeg.1;
      refine' ⟨ h₁, h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2.1, by norm_num; linarith, _, _ ⟩;
      · refine' ⟨ fun n => add_nonneg ( h₂.2.2.2.2.2.2.1.1 n ) ( Real.log_nonneg ( by linarith [ le_max_left 0 ( -Real.log epsCover ), le_max_right 0 ( -Real.log epsCover ) ] ) ), fun ε hε => _ ⟩;
        obtain ⟨ N, hN ⟩ := h₂.2.2.2.2.2.2.1.2 ( ε / 2 ) ( half_pos hε );
        exact ⟨ N + ⌈Real.log ( max 0 ( -Real.log epsCover ) + 1 ) / ( ε / 2 ) ⌉₊ + 1, fun n hn => by nlinarith [ Nat.le_ceil ( Real.log ( max 0 ( -Real.log epsCover ) + 1 ) / ( ε / 2 ) ), hN n ( by linarith ), mul_div_cancel₀ ( Real.log ( max 0 ( -Real.log epsCover ) + 1 ) ) ( by linarith : ( ε / 2 ) ≠ 0 ), show ( n : ℝ ) ≥ N + ⌈Real.log ( max 0 ( -Real.log epsCover ) + 1 ) / ( ε / 2 ) ⌉₊ + 1 by exact_mod_cast hn ] ⟩;
      · exact fun n hn => le_add_of_le_of_nonneg ( h₂.2.2.2.2.2.2.2 n hn ) ( Real.log_nonneg ( by linarith [ le_max_left 0 ( -Real.log epsCover ), le_max_right 0 ( -Real.log epsCover ) ] ) );
    · exact ⟨ hdeg.2.1, hdeg.2.2.1, hdeg.2.2.2.1, hdeg.2.2.2.2.1, hdeg.2.2.2.2.2.1, fun n => le_add_of_le_of_nonneg ( hdeg.2.2.2.2.2.2 n ) ( Real.log_nonneg ( by linarith [ le_max_left 0 ( -Real.log epsCover ), le_max_right 0 ( -Real.log epsCover ) ] ) ) ⟩;
  · intro n r S alpha beta hmem
    set L := max 0 (-Real.log epsCover)
    set radius := rmin n S.card + Nat.ceil (Dhbl.sigma n)
    set δ := Real.exp (-(Dhbl.sigma n))
    set thresh := epsCover * (S.card : ℝ);
    -- Apply `greedy_peel_cover` with `k := Nat.ceil (Real.exp (Dhbl.sigma n) * L)`.
    obtain ⟨centers, hcenters_card, hcenters_bound⟩ := greedy_peel_cover S radius δ thresh (by
    have := hdeg.1.2.2.2.2.2.2.2.1;
    exact Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ( this.1 n ) )) (by
    intros R hR_sub hR_thresh
    obtain ⟨a, ha⟩ := hHBL (h_subset n r S R alpha beta hmem hR_sub hR_thresh);
    refine' ⟨ a, ha.trans _ ⟩;
    gcongr;
    exact add_le_add ( rmin_mono <| Finset.card_le_card hR_sub ) le_rfl) (Nat.ceil (Real.exp (Dhbl.sigma n) * L));
    refine' ⟨ centers, _, _ ⟩;
    · refine' le_trans ( Nat.cast_le.mpr hcenters_card ) _;
      refine' le_trans ( Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ) _;
      rw [ Real.exp_add, Real.exp_log ( by positivity ) ];
      nlinarith [ Real.add_one_le_exp ( Dhbl.sigma n ), show 0 ≤ Dhbl.sigma n from hdeg.1.2.2.2.2.2.2.2.1.1 n ];
    · rw [ Nat.cast_sub ];
      · refine' le_trans _ ( hcenters_bound.elim ( fun h => h ) fun h => h.trans _ );
        · gcongr;
          refine' coveredByBalls_mono_radius _ _ _;
          exact Nat.add_le_add_left ( Nat.ceil_mono <| le_add_of_nonneg_right <| Real.log_nonneg <| by linarith [ le_max_left 0 ( -Real.log epsCover ), le_max_right 0 ( -Real.log epsCover ) ] ) _;
        · -- Since $1 - \delta \leq \exp(-\delta)$, we have $(1 - \delta)^k \leq \exp(-\delta k)$.
          have h_exp : (1 - δ) ^ ⌈Real.exp (Dhbl.sigma n) * L⌉₊ ≤ Real.exp (-δ * ⌈Real.exp (Dhbl.sigma n) * L⌉₊) := by
            have h_exp : (1 - δ) ≤ Real.exp (-δ) := by
              linarith [ Real.add_one_le_exp ( -δ ) ];
            exact le_trans ( pow_le_pow_left₀ ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| neg_nonpos.2 <| show 0 ≤ Dhbl.sigma n from by
                                                                                                          exact hdeg.1.2.2.2.2.2.2.2.1.1 _ ) h_exp _ ) <| by rw [ ← Real.exp_nat_mul ] ; ring_nf; norm_num;
          refine' mul_le_mul_of_nonneg_right ( h_exp.trans _ ) ( Nat.cast_nonneg _ );
          rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
          simp +zetaDelta at *;
          rw [ Real.exp_neg ];
          cases max_cases ( 0 : ℝ ) ( -Real.log epsCover ) <;> nlinarith [ Nat.le_ceil ( Real.exp ( Dhbl.sigma n ) * max 0 ( -Real.log epsCover ) ), Real.exp_pos ( Dhbl.sigma n ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( Dhbl.sigma n ) ) ), Real.log_le_sub_one_of_pos heps ];
      · exact Finset.card_filter_le _ _

theorem R1a_skeleton (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement) :
    R1aStatement := by
  intro Din epsCover hvalid heps hHBL_oracle
  by_cases heps_one : 1 ≤ epsCover
  · refine ⟨Din, degradedData_refl hvalid, ?_⟩
    intro n r S alpha beta _hmem
    refine ⟨∅, ?_, ?_⟩
    · simpa using (Real.exp_nonneg (Din.sigma n))
    · simp [coveredByBalls]
      have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le S.card
      nlinarith
  · have heps_le : epsCover ≤ 1 := le_of_not_ge heps_one
    obtain ⟨D_R, hdeg_R, h_subset⟩ :=
      r1a_degraded_for_subset hBV hVPlus hVC Din epsCover hvalid heps heps_le
    obtain ⟨Dhbl, hdeg_hbl, hHBL⟩ := hHBL_oracle D_R hdeg_R.1
    have hdeg_Dhbl : degradedData Din Dhbl := degradedData_trans hdeg_R hdeg_hbl
    exact r1a_cover_of_hbl Din D_R Dhbl epsCover heps hdeg_Dhbl hHBL h_subset

theorem R1b_skeleton : R1bStatement := by
  -- pigeonhole only; no volume input needed
  classical
  intro D _hD hcover n r S alpha beta hmem
  dsimp [heavyBallConclusion]
  let rad : ℕ := rmin n S.card + Nat.ceil (D.sigma n)
  let T : ℝ := Real.exp (-(D.sigma n + Real.log 2)) * (S.card : ℝ)
  by_cases hS0 : S.card = 0
  · refine ⟨(∅ : Cube n), ?_⟩
    simp [hS0]
  · obtain ⟨centers, hcenters_card, hmiss⟩ := hcover hmem
    let covered := coveredByBalls S centers rad
    have hcov_sub_S : covered ⊆ S := by
      intro x hx
      have hx' : x ∈ S ∧ ∃ c ∈ centers, hDist x c ≤ rad := by
        simpa [covered, coveredByBalls] using hx
      exact hx'.1
    have hcov_card_le : covered.card ≤ S.card := Finset.card_le_card hcov_sub_S
    have hmiss' :
        ((S.card - covered.card : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * (S.card : ℝ) := by
      simpa [covered, rad] using hmiss
    have hmiss_real :
        (S.card : ℝ) - (covered.card : ℝ) ≤ (1 / 2 : ℝ) * (S.card : ℝ) := by
      rwa [← Nat.cast_sub hcov_card_le]
    have hcov_lower : (S.card : ℝ) / 2 ≤ (covered.card : ℝ) := by
      linarith
    have hSpos_nat : 0 < S.card := Nat.pos_of_ne_zero hS0
    have hSpos : 0 < (S.card : ℝ) := by
      exact_mod_cast hSpos_nat
    have hcovered_pos_real : 0 < (covered.card : ℝ) := by
      nlinarith
    have hcovered_pos_nat : 0 < covered.card := by
      exact_mod_cast hcovered_pos_real
    have hcovered_nonempty : covered.Nonempty := Finset.card_pos.mp hcovered_pos_nat
    rcases hcovered_nonempty with ⟨x, hx⟩
    have hx' : x ∈ S ∧ ∃ c ∈ centers, hDist x c ≤ rad := by
      simpa [covered, coveredByBalls] using hx
    rcases hx' with ⟨_hxS, c0, hc0, _hdist0⟩
    have hcenters_nonempty : centers.Nonempty := ⟨c0, hc0⟩
    by_contra hno
    have hTpos : 0 < T := by
      dsimp [T]
      positivity
    have hlt_ind :
        ∀ c ∈ centers, (((S.filter fun x => hDist x c ≤ rad).card : ℕ) : ℝ) < T := by
      intro c hc
      exact lt_of_not_ge (by
        intro hcHeavy
        exact hno ⟨c, by simpa [T, rad] using hcHeavy⟩)
    have hcov_subset_union :
        covered ⊆ centers.biUnion (fun c => S.filter fun x => hDist x c ≤ rad) := by
      intro x hx
      have hx' : x ∈ S ∧ ∃ c ∈ centers, hDist x c ≤ rad := by
        simpa [covered, coveredByBalls] using hx
      rcases hx' with ⟨hxS, c, hc, hdist⟩
      simpa [hxS] using ⟨c, hc, hdist⟩
    have hcov_card_le_sum_nat :
        covered.card ≤ ∑ c ∈ centers, (S.filter fun x => hDist x c ≤ rad).card := by
      exact le_trans (Finset.card_le_card hcov_subset_union) (Finset.card_biUnion_le)
    have hcov_card_le_sum :
        (covered.card : ℝ) ≤
          ∑ c ∈ centers, (((S.filter fun x => hDist x c ≤ rad).card : ℕ) : ℝ) := by
      have hcast :
          (covered.card : ℝ) ≤
            ((∑ c ∈ centers, (S.filter fun x => hDist x c ≤ rad).card : ℕ) : ℝ) := by
        exact_mod_cast hcov_card_le_sum_nat
      simpa [Nat.cast_sum] using hcast
    have hsum_lt :
        (∑ c ∈ centers, (((S.filter fun x => hDist x c ≤ rad).card : ℕ) : ℝ)) <
          ∑ _c ∈ centers, T := by
      apply Finset.sum_lt_sum
      · intro c hc
        exact le_of_lt (hlt_ind c hc)
      · rcases hcenters_nonempty with ⟨c, hc⟩
        exact ⟨c, hc, hlt_ind c hc⟩
    have hsum_const : (∑ _c ∈ centers, T) = (centers.card : ℝ) * T := by
      simp
    have hsum_const_le_exp : (centers.card : ℝ) * T ≤ Real.exp (D.sigma n) * T := by
      exact mul_le_mul_of_nonneg_right hcenters_card (le_of_lt hTpos)
    have hhalf : Real.exp (D.sigma n) * T = (S.card : ℝ) / 2 := by
      dsimp [T]
      rw [← mul_assoc]
      have hexp :
          Real.exp (D.sigma n) * Real.exp (-(D.sigma n + Real.log 2)) =
            (2 : ℝ)⁻¹ := by
        rw [← Real.exp_add]
        have harg : D.sigma n + -(D.sigma n + Real.log 2) = -Real.log 2 := by
          ring
        rw [harg, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [hexp]
      ring
    have hcovered_lt_half : (covered.card : ℝ) < (S.card : ℝ) / 2 := by
      exact lt_of_le_of_lt hcov_card_le_sum
        (lt_of_lt_of_le hsum_lt (by simpa [hsum_const, hhalf] using hsum_const_le_exp))
    exact (not_lt_of_ge hcov_lower) hcovered_lt_half

/-- The neighborhood is monotone in the radius. -/
lemma neighborhood_mono_radius {n s r : ℕ} (h : s ≤ r) (S : Finset (Cube n)) :
    neighborhood s S ⊆ neighborhood r S := by
  intro x hx
  rw [mem_neighborhood_iff] at hx ⊢
  rcases hx with ⟨u, hu, hd⟩
  exact ⟨u, hu, le_trans hd h⟩

/-- Peeling bound: if the near-optimal bound holds at radius `r`, then the
Harper minimum of the `s`-neighborhood grown by `r - s` is controlled by the
same near-optimal right-hand side.  This packages the Hamming-triangle
chaining `Γ_{r-s}(Γ_s(S)) ⊆ Γ_r(S)` together with `V ≤ neighborhood`. -/
lemma V_peel_le {n : ℕ} (S : Finset (Cube n)) (s r : ℕ) (hsr : s ≤ r)
    (sig : ℝ)
    (hnear : ((neighborhood r S).card : ℝ) ≤ Real.exp sig * (V n S.card r : ℝ)) :
    (V n (neighborhood s S).card (r - s) : ℝ) ≤ Real.exp sig * (V n S.card r : ℝ) := by
  have h1 : (V n (neighborhood s S).card (r - s) : ℝ)
      ≤ ((neighborhood (r - s) (neighborhood s S)).card : ℝ) :=
    V_le_neighborhood_card _ _
  have hsub : neighborhood (r - s) (neighborhood s S) ⊆ neighborhood r S := by
    have h := neighborhood_neighborhood_subset (a := r - s) (b := s) S
    rwa [Nat.sub_add_cancel hsr] at h
  have h2 : ((neighborhood (r - s) (neighborhood s S)).card : ℝ)
      ≤ ((neighborhood r S).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  linarith

/-
Upper bound on the Harper minimum for a class member, via the interior
volume calculus.  This is a direct packaging of `hVC`.
-/
lemma V_upper_of_classMember (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ C_V : ℝ, 1 ≤ C_V ∧ ∃ volSlack : ℕ → ℝ, Sublinear volSlack ∧
      ∀ (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ),
        D.alphaMin ≤ alpha → alpha ≤ 1 / 2 → beta = (r : ℝ) / (n : ℝ) →
        alpha + beta ≤ 1 / 2 - c0 → 1 ≤ S.card → S.card ≤ 2 ^ n →
        sizeHyp D n S alpha →
        (V n S.card r : ℝ) ≤
          Real.exp (H (alpha + beta) * (n : ℝ) +
            (C_V * (D.cSize * D.sigma n) + volSlack n)) := by
  specialize hVC D.alphaMin c0 hvalid.2.2.2.2.1 hc0;
  obtain ⟨ C_V, hC_V, volSlack, hvolSlack, hcalc ⟩ := hVC; use C_V, hC_V, volSlack, hvolSlack; intro n r S alpha beta halpha halpha' hbeta hbeta' hS hS' hsize; specialize hcalc n S.card r alpha beta ( D.cSize * D.sigma n ) ; simp_all +decide [ sizeHyp ] ;
  rw [ ← Real.log_le_iff_le_exp ];
  · grind;
  · exact_mod_cast card_le_V _ _ hS' |> lt_of_lt_of_le ( Nat.cast_pos.mpr hS.card_pos )

/-- A sublinear function is eventually below any positive linear rate. -/
lemma sublinear_lt_of_pos {f : ℕ → ℝ} (hf : Sublinear f) {γ : ℝ}
    (hγ : 0 < γ) : ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → f n < γ * (n : ℝ) := by
  obtain ⟨N, hN⟩ := hf.2 (γ / 2) (by linarith)
  refine ⟨N + 1, by omega, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have := hN n (by omega)
  nlinarith

/-- Real bounds on the natural-number half. -/
private lemma cast_nat_half_bounds (n : ℕ) :
    ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 ∧ (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
  refine ⟨?_, ?_⟩
  · have h : 2 * (n / 2) ≤ n := by omega
    have : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  · have h : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith

/-- Monotonicity of the chord slope `log((1-x)/x)` (decreasing in `x`): a
lower bound at the right endpoint. -/
private lemma log_ratio_lower {b hi : ℝ} (hb0 : 0 < b) (hbhi : b ≤ hi)
    (hhi : hi < 1 / 2) :
    Real.log ((1 - hi) / hi) ≤ Real.log ((1 - b) / b) := by
  have h1 : (0 : ℝ) < (1 - hi) / hi := div_pos (by linarith) (by linarith)
  have h2 : (1 - hi) / hi ≤ (1 - b) / b := by
    rw [div_le_div_iff₀ (by linarith) hb0]; nlinarith
  exact Real.log_le_log h1 h2

/-- Monotonicity of the chord slope `log((1-x)/x)`: an upper bound at the
left endpoint. -/
lemma log_ratio_upper {a lo : ℝ} (hlo0 : 0 < lo) (hloa : lo ≤ a)
    (ha : a ≤ 1 / 2) :
    Real.log ((1 - a) / a) ≤ Real.log ((1 - lo) / lo) := by
  have h1 : (0 : ℝ) < (1 - a) / a := div_pos (by linarith) (by linarith)
  have h2 : (1 - a) / a ≤ (1 - lo) / lo := by
    rw [div_le_div_iff₀ (by linarith) hlo0]; nlinarith
  exact Real.log_le_log h1 h2

/-- If `H b` is only slightly above `H(1/2 - c0)`, then `b` stays away from
the equator. -/
private lemma H_bound_away_half {c0 b δ : ℝ} (_hc0 : 0 < c0) (hc0' : c0 < 1)
    (hb : b ≤ 1 / 2)
    (hδ : δ < H (1 / 2 - c0 / 2) - H (1 / 2 - c0))
    (hHb : H b ≤ H (1 / 2 - c0) + δ) : b < 1 / 2 - c0 / 2 := by
  by_contra hcon
  push_neg at hcon
  have hmono : H (1 / 2 - c0 / 2) ≤ H b :=
    H_mono_on_half (by linarith) hcon hb
  linarith

/-- Chord inversion (lower slope): a bound on the entropy gap controls the
argument gap. -/
private lemma chord_arg_le {a b δ κ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1 / 2) (hκ : 0 < κ) (hslope : κ ≤ Real.log ((1 - b) / b))
    (hchord : H b - H a ≤ δ) : b - a ≤ δ / κ := by
  have h1 := binEntropy_chord_lower ha hab hb
  have hba : 0 ≤ b - a := by linarith
  have h2 : (b - a) * κ ≤ (b - a) * Real.log ((1 - b) / b) :=
    mul_le_mul_of_nonneg_left hslope hba
  rw [le_div_iff₀ hκ]; linarith

/-- Chord bound (upper slope): the entropy gap is controlled by the argument
gap. -/
lemma H_diff_le {a b L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2)
    (hL : Real.log ((1 - a) / a) ≤ L) : H b - H a ≤ (b - a) * L := by
  have h1 := binEntropy_chord_upper ha hab hb
  have hba : 0 ≤ b - a := by linarith
  have h2 : (b - a) * Real.log ((1 - a) / a) ≤ (b - a) * L :=
    mul_le_mul_of_nonneg_left hL hba
  linarith

set_option maxHeartbeats 1000000 in
/-- The single-dimension crux of the volume-calculus inversion, in the
large-`n` regime.  For a fixed `n` in the range where the slack rates are
small, the Harper-minimum upper bound at effective density `target + rho/n`
transfers to a `log |T|` bound at density `target`, with the explicit affine
slack `(L/κ + 1)·(Gf n + volumeSlack n) + (L + 2)` where
`κ = log((1/2+c0/2)/(1/2-c0/2))` and `L = log((1-lo)/lo)`. -/
lemma logsize_le_of_V_upper_large (hVPlus : VPlusStatement)
    (c0 lo : ℝ) (hc0 : 0 < c0) (_hc0half : c0 < 1 / 2) (hlo : 0 < lo)
    (hlohalf : lo ≤ 1 / 2 - c0) (volumeSlack : ℕ → ℝ) (Gf : ℕ → ℝ)
    (hvbound : ∀ n t : ℕ, t ≤ n / 2 →
      Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - volumeSlack n) ≤
        ((ball (∅ : Cube n) t).card : ℝ) ∧
      ((ball (∅ : Cube n) t).card : ℝ) ≤
        Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + volumeSlack n))
    (n rho : ℕ) (T : Finset (Cube n)) (target : ℝ)
    (hT : T.Nonempty) (hT2 : T.card < 2 ^ n) (htar : lo ≤ target)
    (hg : target + (rho : ℝ) / (n : ℝ) ≤ 1 / 2 - c0)
    (hV : (V n T.card rho : ℝ) ≤
      Real.exp (H (target + (rho : ℝ) / (n : ℝ)) * (n : ℝ) + Gf n))
    (hthr1 : Gf n + volumeSlack n < (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) * (n : ℝ))
    (hthr2 : Gf n + volumeSlack n <
      Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) * (c0 / 2) * (n : ℝ))
    (hthr3 : (1 : ℝ) < c0 / 2 * (n : ℝ)) (hn : 1 ≤ n)
    (hvsnn : 0 ≤ volumeSlack n) (hGfnn : 0 ≤ Gf n) :
    Real.log (T.card : ℝ) ≤ H target * (n : ℝ) +
      (Real.log ((1 - lo) / lo) / Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) + 1) *
        (Gf n + volumeSlack n) + (Real.log ((1 - lo) / lo) + 2) := by
  set κ := Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) with hκdef
  set L := Real.log ((1 - lo) / lo) with hLdef
  set g := target + (rho : ℝ) / (n : ℝ) with hgdef
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hκpos : 0 < κ := by
    rw [hκdef]; apply Real.log_pos
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hLnn : 0 ≤ L := by
    rw [hLdef]; apply Real.log_nonneg
    rw [le_div_iff₀ hlo]; linarith
  have hGvnn : 0 ≤ Gf n + volumeSlack n := by linarith
  have htarpos : 0 < target := lt_of_lt_of_le hlo htar
  have hrhonn : 0 ≤ (rho : ℝ) / (n : ℝ) := by positivity
  have hgpos : 0 < g := by rw [hgdef]; linarith
  have hδ1 : (Gf n + volumeSlack n) / (n : ℝ) < H (1 / 2 - c0 / 2) - H (1 / 2 - c0) := by
    rw [div_lt_iff₀ hnpos]; linarith [hthr1]
  have hδ2 : (Gf n + volumeSlack n) / (n : ℝ) < κ * (c0 / 2) := by
    rw [div_lt_iff₀ hnpos]; linarith [hthr2]
  have hinvn : 1 / (n : ℝ) < c0 / 2 := by
    rw [div_lt_iff₀ hnpos]; linarith [hthr3]
  obtain ⟨t, ht_le, hbt, hbtr, hbt1⟩ := r1_range_control_t_star hVPlus n rho T hT hT2
  -- Uniform entropy bound for radii below `t + rho`.
  have hHbound : ∀ m : ℕ, m ≤ n / 2 → m ≤ t + rho →
      H ((m : ℝ) / (n : ℝ)) ≤ H g + (Gf n + volumeSlack n) / (n : ℝ) := by
    intro m hm hmt
    have h1 := (hvbound n m hm).1
    have h2 : ((ball (∅ : Cube n) m).card : ℝ) ≤ ((ball (∅ : Cube n) (t + rho)).card : ℝ) := by
      exact_mod_cast ball_empty_card_mono hmt
    have h3 : Real.exp (H ((m : ℝ) / (n : ℝ)) * (n : ℝ) - volumeSlack n) ≤
        Real.exp (H g * (n : ℝ) + Gf n) :=
      le_trans h1 (le_trans h2 (le_trans hbtr hV))
    have h4 := Real.exp_le_exp.mp h3
    have hmul : H ((m : ℝ) / (n : ℝ)) * (n : ℝ) ≤
        (H g + (Gf n + volumeSlack n) / (n : ℝ)) * (n : ℝ) := by
      have hexp : (H g + (Gf n + volumeSlack n) / (n : ℝ)) * (n : ℝ) =
          H g * (n : ℝ) + (Gf n + volumeSlack n) := by field_simp
      rw [hexp]; linarith
    exact le_of_mul_le_mul_right hmul hnpos
  have hHg : H g ≤ H (1 / 2 - c0) :=
    H_mono_on_half (by linarith) (by linarith [hg]) (by linarith)
  -- STEP A: `t + rho ≤ n / 2`.
  have htrle : t + rho ≤ n / 2 := by
    by_contra hcon
    push_neg at hcon
    have hb := hHbound (n / 2) (le_refl _) (le_of_lt hcon)
    have hb2 : H (((n / 2 : ℕ) : ℝ) / (n : ℝ)) ≤ H (1 / 2 - c0) + (Gf n + volumeSlack n) / (n : ℝ) := by
      linarith
    have hbhalf : ((n / 2 : ℕ) : ℝ) / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hnpos]; linarith [(cast_nat_half_bounds n).1]
    have haway : ((n / 2 : ℕ) : ℝ) / (n : ℝ) < 1 / 2 - c0 / 2 :=
      H_bound_away_half hc0 (by linarith) hbhalf hδ1 hb2
    have hlow : 1 / 2 - 1 / (2 * (n : ℝ)) ≤ ((n / 2 : ℕ) : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      have hmul : (1 / 2 - 1 / (2 * (n : ℝ))) * (n : ℝ) = (n : ℝ) / 2 - 1 / 2 := by
        have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
        field_simp
      rw [hmul]; linarith [(cast_nat_half_bounds n).2]
    have hquarter : 1 / (2 * (n : ℝ)) < c0 / 2 := by
      have he : 1 / (2 * (n : ℝ)) = (1 / (n : ℝ)) / 2 := by ring
      rw [he]; linarith [hinvn]
    linarith
  -- STEP A': `(t + rho) / n < 1/2 - c0/2`.
  have htrlt : ((t + rho : ℕ) : ℝ) / (n : ℝ) < 1 / 2 - c0 / 2 := by
    have hb := hHbound (t + rho) htrle (le_refl _)
    have hb2 : H (((t + rho : ℕ) : ℝ) / (n : ℝ)) ≤
        H (1 / 2 - c0) + (Gf n + volumeSlack n) / (n : ℝ) := by linarith
    have hbhalf : ((t + rho : ℕ) : ℝ) / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hnpos]
      have h1 : ((t + rho : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast htrle
      linarith [(cast_nat_half_bounds n).1]
    exact H_bound_away_half hc0 (by linarith) hbhalf hδ1 hb2
  -- STEP B: density bound.
  have htdens : (t : ℝ) / (n : ℝ) ≤ target + (Gf n + volumeSlack n) / (κ * (n : ℝ)) := by
    have hsplit : ((t + rho : ℕ) : ℝ) / (n : ℝ) = (t : ℝ) / (n : ℝ) + (rho : ℝ) / (n : ℝ) := by
      push_cast; ring
    have hb := hHbound (t + rho) htrle (le_refl _)
    by_cases hcase : ((t + rho : ℕ) : ℝ) / (n : ℝ) ≤ g
    · have hslack_nn : 0 ≤ (Gf n + volumeSlack n) / (κ * (n : ℝ)) := by positivity
      rw [hgdef, hsplit] at hcase
      linarith
    · push_neg at hcase
      have hslope : κ ≤ Real.log ((1 - ((t + rho : ℕ) : ℝ) / (n : ℝ)) / (((t + rho : ℕ) : ℝ) / (n : ℝ))) := by
        rw [hκdef]
        have hbpos : 0 < ((t + rho : ℕ) : ℝ) / (n : ℝ) := lt_trans hgpos hcase
        have := log_ratio_lower hbpos (le_of_lt htrlt) (by linarith : (1:ℝ)/2 - c0/2 < 1/2)
        have heq : (1 : ℝ) - (1 / 2 - c0 / 2) = 1 / 2 + c0 / 2 := by ring
        rwa [heq] at this
      have hchord : H (((t + rho : ℕ) : ℝ) / (n : ℝ)) - H g ≤ (Gf n + volumeSlack n) / (n : ℝ) := by
        linarith
      have hcarg := chord_arg_le hgpos (le_of_lt hcase) (by linarith [htrlt]) hκpos hslope hchord
      have hdiveq : (Gf n + volumeSlack n) / (n : ℝ) / κ = (Gf n + volumeSlack n) / (κ * (n : ℝ)) := by
        rw [div_div]; ring_nf
      rw [hgdef, hsplit] at hcarg
      rw [hdiveq] at hcarg
      linarith
  -- STEP C: `t + 1 ≤ n / 2`.
  have hdivkn : (Gf n + volumeSlack n) / (κ * (n : ℝ)) < c0 / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have : (Gf n + volumeSlack n) < κ * (c0 / 2) * (n : ℝ) := by
      rw [div_lt_iff₀ hnpos] at hδ2; linarith
    nlinarith [this]
  have htlt : (t : ℝ) / (n : ℝ) < 1 / 2 - c0 / 2 := by
    linarith [htdens, hg, hdivkn]
  have ht1le : t + 1 ≤ n / 2 := by
    have h1 : (t : ℝ) + 1 ≤ (n : ℝ) / 2 := by
      rw [div_lt_iff₀ hnpos] at htlt
      have hexp : (1 / 2 - c0 / 2) * (n : ℝ) = (n : ℝ) / 2 - c0 / 2 * (n : ℝ) := by ring
      rw [hexp] at htlt
      linarith [htlt, hthr3]
    by_contra hcon
    push_neg at hcon
    have hcc : (n / 2 : ℕ) + 1 ≤ t + 1 := by omega
    have hcast : ((n / 2 : ℕ) : ℝ) + 1 ≤ (t : ℝ) + 1 := by exact_mod_cast hcc
    linarith [h1, (cast_nat_half_bounds n).2, hcast]
  -- upper bound on `log |T|`.
  have hlogT : Real.log (T.card : ℝ) ≤ H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ) + volumeSlack n := by
    have hup := (hvbound n (t + 1) ht1le).2
    have hle : (T.card : ℝ) ≤ Real.exp (H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ) + volumeSlack n) :=
      le_of_lt (lt_of_lt_of_le hbt1 hup)
    exact (Real.log_le_iff_le_exp (by exact_mod_cast hT.card_pos)).2 hle
  have ht1half : ((t + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hnpos]
    have h1 : ((t + 1 : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast ht1le
    linarith [(cast_nat_half_bounds n).1]
  have ht1dens : ((t + 1 : ℕ) : ℝ) / (n : ℝ) ≤ target + (Gf n + volumeSlack n) / (κ * (n : ℝ)) + 1 / (n : ℝ) := by
    have hsplit : ((t + 1 : ℕ) : ℝ) / (n : ℝ) = (t : ℝ) / (n : ℝ) + 1 / (n : ℝ) := by
      push_cast; ring
    rw [hsplit]; linarith [htdens]
  -- final combination.
  have htarhalf : target ≤ 1 / 2 := by linarith [hg, hrhonn]
  by_cases hc : ((t + 1 : ℕ) : ℝ) / (n : ℝ) ≤ target
  · have hmono : H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ H target :=
      H_mono_on_half (by positivity) hc htarhalf
    have hmn := mul_le_mul_of_nonneg_right hmono hnpos.le
    have hslack : volumeSlack n ≤
        (L / κ + 1) * (Gf n + volumeSlack n) + (L + 2) := by
      have hcoef : 0 ≤ L / κ := by positivity
      nlinarith [hGvnn, hGfnn, hLnn, hcoef]
    linarith [hlogT, hmn, hslack]
  · push_neg at hc
    have hslope : Real.log ((1 - target) / target) ≤ L := by
      rw [hLdef]; exact log_ratio_upper hlo htar htarhalf
    have hdiff := H_diff_le htarpos (le_of_lt hc) ht1half hslope
    have hmul1 : (H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) - H target) * (n : ℝ) ≤
        (((t + 1 : ℕ) : ℝ) / (n : ℝ) - target) * L * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hdiff hnpos.le
    -- Clean product bound: `((t+1)/n - target) * n ≤ (Gf+vol)/κ + 1`.
    have hrw : ((Gf n + volumeSlack n) / (κ * (n : ℝ)) + 1 / (n : ℝ)) * (n : ℝ) =
        (Gf n + volumeSlack n) / κ + 1 := by
      have hκne : κ ≠ 0 := ne_of_gt hκpos
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      field_simp
    have hdn : (((t + 1 : ℕ) : ℝ) / (n : ℝ) - target) * (n : ℝ) ≤
        (Gf n + volumeSlack n) / κ + 1 := by
      have hmuln : (((t + 1 : ℕ) : ℝ) / (n : ℝ) - target) * (n : ℝ) ≤
          ((Gf n + volumeSlack n) / (κ * (n : ℝ)) + 1 / (n : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [ht1dens]) hnpos.le
      linarith [hmuln, hrw]
    have hcomb : (H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) - H target) * (n : ℝ) ≤
        L / κ * (Gf n + volumeSlack n) + L := by
      have hb2 : (((t + 1 : ℕ) : ℝ) / (n : ℝ) - target) * L * (n : ℝ) =
          (((t + 1 : ℕ) : ℝ) / (n : ℝ) - target) * (n : ℝ) * L := by ring
      have hb3 : (((t + 1 : ℕ) : ℝ) / (n : ℝ) - target) * (n : ℝ) * L ≤
          ((Gf n + volumeSlack n) / κ + 1) * L :=
        mul_le_mul_of_nonneg_right hdn hLnn
      have hb4 : ((Gf n + volumeSlack n) / κ + 1) * L =
          L / κ * (Gf n + volumeSlack n) + L := by ring
      linarith [hmul1, hb2, hb3, hb4]
    have hfin : Real.log (T.card : ℝ) ≤
        H target * (n : ℝ) + L / κ * (Gf n + volumeSlack n) + L + volumeSlack n := by
      have hexp : H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ) =
          H target * (n : ℝ) + (H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) - H target) * (n : ℝ) := by ring
      calc Real.log (T.card : ℝ)
          ≤ H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ) + volumeSlack n := hlogT
        _ = H target * (n : ℝ) + (H (((t + 1 : ℕ) : ℝ) / (n : ℝ)) - H target) * (n : ℝ) + volumeSlack n := by
            rw [hexp]
        _ ≤ H target * (n : ℝ) + (L / κ * (Gf n + volumeSlack n) + L) + volumeSlack n := by linarith
        _ = H target * (n : ℝ) + L / κ * (Gf n + volumeSlack n) + L + volumeSlack n := by ring
    have hlast : L / κ * (Gf n + volumeSlack n) + L + volumeSlack n ≤
        (L / κ + 1) * (Gf n + volumeSlack n) + (L + 2) := by
      nlinarith [hGfnn, hGvnn, hLnn]
    linarith [hfin, hlast]

/-- Inversion of the volume calculus: an upper bound on the Harper minimum of
a set `T` grown by `rho`, at effective density `target + rho/n`, yields an
upper bound on `log |T|` at density `target`, up to an affine sublinear
slack.  The multiplicative constant `Cc` and envelope `w` depend only on the
fixed density window `[lo, 1/2 - c0]` (through the bounded chord slopes of
the binary entropy on that window). -/
lemma logsize_le_of_V_upper (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (c0 lo : ℝ) (hc0 : 0 < c0) (hlo : 0 < lo)
    (hlohalf : lo ≤ 1 / 2 - c0)
    (Gf : ℕ → ℝ) (hGf : Sublinear Gf) :
    ∃ w : ℕ → ℝ, Sublinear w ∧
      ∀ (n rho : ℕ) (T : Finset (Cube n)) (target : ℝ),
        T.Nonempty → T.card < 2 ^ n → lo ≤ target →
        target + (rho : ℝ) / (n : ℝ) ≤ 1 / 2 - c0 →
        (V n T.card rho : ℝ) ≤
          Real.exp (H (target + (rho : ℝ) / (n : ℝ)) * (n : ℝ) + Gf n) →
        Real.log (T.card : ℝ) ≤ H target * (n : ℝ) + w n := by
  classical
  obtain ⟨volumeSlack, hvsub, hvbound⟩ := hBV
  have hc0half : c0 < 1 / 2 := by linarith
  have hκpos : 0 < Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) := by
    apply Real.log_pos; rw [lt_div_iff₀ (by linarith)]; linarith
  have hLnn : 0 ≤ Real.log ((1 - lo) / lo) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hlo]; linarith
  have hγ : 0 < H (1 / 2 - c0 / 2) - H (1 / 2 - c0) := by
    have hmem1 : (1 / 2 - c0) ∈ Set.Icc (0 : ℝ) 2⁻¹ :=
      ⟨by linarith, by rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]; linarith⟩
    have hmem2 : (1 / 2 - c0 / 2) ∈ Set.Icc (0 : ℝ) 2⁻¹ :=
      ⟨by linarith, by rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]; linarith⟩
    have hlt := Real.binEntropy_strictMonoOn hmem1 hmem2 (by linarith)
    unfold H; linarith
  set rate := min (H (1 / 2 - c0 / 2) - H (1 / 2 - c0))
    (Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) * (c0 / 2)) with hratedef
  have hrate_pos : 0 < rate := by
    rw [hratedef]; exact lt_min hγ (by positivity)
  obtain ⟨N1, hN1pos, hN1⟩ :=
    sublinear_lt_of_pos (reductions_sublinear_add hGf hvsub) hrate_pos
  set N := max N1 (⌈(2 : ℝ) / c0⌉₊ + 1) with hNdef
  have hcoefnn : 0 ≤ Real.log ((1 - lo) / lo) /
      Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) + 1 := by
    have : 0 ≤ Real.log ((1 - lo) / lo) /
        Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) := div_nonneg hLnn hκpos.le
    linarith
  refine ⟨fun n => (if n < N then (n : ℝ) * Real.log 2 else 0) +
    (Real.log ((1 - lo) / lo) /
        Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) + 1) * (Gf n + volumeSlack n) +
    (Real.log ((1 - lo) / lo) + 2), ?_, ?_⟩
  · refine reductions_sublinear_add (reductions_sublinear_add ?_ ?_) ?_
    · exact sublinear_indicator_prefix (fun n => (n : ℝ) * Real.log 2)
        (fun n => by positivity) N
    · exact sublinear_const_mul _ hcoefnn (reductions_sublinear_add hGf hvsub)
    · exact sublinear_const _ (by linarith)
  · intro n rho T target hT hT2 htar hg hV
    have hHtarget_nn : 0 ≤ H target := by
      have hrhonn : 0 ≤ (rho : ℝ) / (n : ℝ) := by positivity
      unfold H
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    have hGvnn : 0 ≤ Gf n + volumeSlack n := by
      have := hGf.1 n; have := hvsub.1 n; linarith
    by_cases hn : n < N
    · simp only [if_pos hn]
      have hcard : (T.card : ℝ) ≤ (2 : ℝ) ^ n := by
        have : (T.card : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hT2
        rw [Nat.cast_pow] at this; push_cast at this; linarith
      have hlog : Real.log (T.card : ℝ) ≤ Real.log ((2 : ℝ) ^ n) :=
        Real.log_le_log (by exact_mod_cast hT.card_pos) hcard
      rw [Real.log_pow] at hlog
      have hcoefterm : 0 ≤ (Real.log ((1 - lo) / lo) /
          Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) + 1) * (Gf n + volumeSlack n) :=
        mul_nonneg hcoefnn hGvnn
      have hlast : 0 ≤ Real.log ((1 - lo) / lo) + 2 := by linarith
      nlinarith [hlog, hHtarget_nn, hcoefterm, hlast, mul_nonneg hHtarget_nn (Nat.cast_nonneg n)]
    · simp only [if_neg hn]
      push_neg at hn
      have hn1 : 1 ≤ n := le_trans hN1pos (le_trans (le_max_left _ _) hn)
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hrate_n := hN1 n (le_trans (le_max_left _ _) hn)
      have hthr1 : Gf n + volumeSlack n < (H (1 / 2 - c0 / 2) - H (1 / 2 - c0)) * (n : ℝ) := by
        have hle : rate ≤ H (1 / 2 - c0 / 2) - H (1 / 2 - c0) := min_le_left _ _
        exact lt_of_lt_of_le hrate_n (mul_le_mul_of_nonneg_right hle hnR.le)
      have hthr2 : Gf n + volumeSlack n <
          Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) * (c0 / 2) * (n : ℝ) := by
        have hle : rate ≤ Real.log ((1 / 2 + c0 / 2) / (1 / 2 - c0 / 2)) * (c0 / 2) :=
          min_le_right _ _
        exact lt_of_lt_of_le hrate_n (mul_le_mul_of_nonneg_right hle hnR.le)
      have hthr3 : (1 : ℝ) < c0 / 2 * (n : ℝ) := by
        have hnge : ⌈(2 : ℝ) / c0⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
        have hlt : ⌈(2 : ℝ) / c0⌉₊ < n := by omega
        have hn_gt : (2 : ℝ) / c0 < (n : ℝ) := by
          have h1 : (2 : ℝ) / c0 ≤ (⌈(2 : ℝ) / c0⌉₊ : ℝ) := Nat.le_ceil _
          have h2 : ((⌈(2 : ℝ) / c0⌉₊ : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hlt
          linarith
        have hmul := mul_lt_mul_of_pos_left hn_gt (show (0 : ℝ) < c0 / 2 by linarith)
        rw [show c0 / 2 * ((2 : ℝ) / c0) = 1 by field_simp] at hmul
        linarith
      have hvsnn := hvsub.1 n
      have hGfnn := hGf.1 n
      have hmain := logsize_le_of_V_upper_large hVPlus c0 lo hc0 hc0half hlo hlohalf
        volumeSlack Gf hvbound n rho T target hT hT2 htar hg hV hthr1 hthr2 hthr3 hn1
        hvsnn hGfnn
      linarith [hmain]

set_option maxHeartbeats 1000000 in
/-- Downward-pinning core (sub-equatorial branch).

Proof route (prose R2, "pinning transfer"): let `r' := ⌈tau n⌉`.  The chained
inclusion `Γ_{r-r'}(Γ_{r'}(S)) ⊆ Γ_r(S)` (Hamming triangle inequality) gives
`V(n, |Γ_{r'}(S)|, r - r') ≤ |Γ_r(S)| ≤ exp(σ n)·V(n,|S|,r)`.  If
`|Γ_{r'}(S)|` exceeded `exp(H(alpha+tau)n + (big slack))`, then `V+` from the
larger base plus the two-sided ball volume (`hBV`) and the chord bound
`binEntropy_chord_lower` would force `V(n, |Γ_{r'}(S)|, r-r')` to exceed the
right-hand side (`r1_range_control` keeps all densities in the strictly
increasing branch of `H`, where the excess cannot be absorbed).  The
contradiction bounds the excess by an explicit sublinear envelope. -/
private lemma r2_dp_core (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D) :
    ∃ sigmaDP : ℕ → ℝ, Sublinear sigmaDP ∧
    ∀ n r S alpha beta, classMember D n r S alpha beta →
      ∀ tau : ℝ, 0 < tau → tau ≤ beta → alpha + tau < 1 / 2 →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (alpha + tau) * (n : ℝ) + sigmaDP n) := by
  classical
  obtain ⟨c0, hc0pos, N, hNpos, hc0⟩ := r1_range_control hBV hVPlus hVC D hvalid
  have halphaMax_half : D.alphaMax < 1 / 2 := hvalid.2.2.2.2.2.2.1
  have halphaMin_pos : 0 < D.alphaMin := hvalid.2.2.2.2.1
  have halphaMin_le_max : D.alphaMin ≤ D.alphaMax := hvalid.2.2.2.2.2.1
  set c0star := min c0 ((1 / 2 - D.alphaMax) / 2) with hc0stardef
  have hc0star_pos : 0 < c0star := by
    rw [hc0stardef]; exact lt_min hc0pos (by linarith)
  have hc0star_le : c0star ≤ c0 := min_le_left _ _
  have hc0star_le2 : c0star ≤ (1 / 2 - D.alphaMax) / 2 := min_le_right _ _
  have hlo_half : D.alphaMin ≤ 1 / 2 - c0star := by linarith
  have hL''nn : 0 ≤ Real.log ((1 - D.alphaMin) / D.alphaMin) := by
    apply Real.log_nonneg; rw [le_div_iff₀ halphaMin_pos]; linarith
  obtain ⟨C_V, hC_V, volSlack, hvolSlack, hVup⟩ :=
    V_upper_of_classMember hVC D hvalid c0star hc0star_pos
  have hsigma_sub : Sublinear D.sigma := hvalid.2.2.2.2.2.2.2.1
  have hcSize_nn : 0 ≤ D.cSize := le_trans zero_le_one hvalid.2.2.2.1
  have hCV_nn : 0 ≤ C_V := le_trans zero_le_one hC_V
  have hGf_sub : Sublinear (fun n => D.sigma n + C_V * (D.cSize * D.sigma n) +
      volSlack n + Real.log ((1 - D.alphaMin) / D.alphaMin)) := by
    refine reductions_sublinear_add (reductions_sublinear_add
      (reductions_sublinear_add hsigma_sub ?_) hvolSlack) (sublinear_const _ hL''nn)
    exact sublinear_const_mul C_V hCV_nn (sublinear_const_mul D.cSize hcSize_nn hsigma_sub)
  obtain ⟨w, hwsub, hw⟩ :=
    logsize_le_of_V_upper hBV hVPlus c0star D.alphaMin hc0star_pos halphaMin_pos
      hlo_half _ hGf_sub
  refine ⟨fun n => w n + (if n < N then (n : ℝ) * Real.log 2 else 0), ?_, ?_⟩
  · exact reductions_sublinear_add hwsub
      (sublinear_indicator_prefix (fun n => (n : ℝ) * Real.log 2) (fun n => by positivity) N)
  · intro n r S alpha beta hmem tau htau htaub hhalf
    obtain ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩ := hmem
    have hHtar_nn : 0 ≤ H (alpha + tau) := by
      unfold H
      exact Real.binEntropy_nonneg (by linarith) (by linarith)
    by_cases hSne : S.Nonempty
    · by_cases hn : n < N
      · -- small n: the whole cube bounds the neighborhood
        simp only [if_pos hn]
        have hcard : ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
            Real.exp ((n : ℝ) * Real.log 2) := cube_card_le_two_pow _
        have hwnn : 0 ≤ w n := hwsub.1 n
        have hmono : Real.exp ((n : ℝ) * Real.log 2) ≤
            Real.exp (H (alpha + tau) * (n : ℝ) + (w n + (n : ℝ) * Real.log 2)) := by
          apply Real.exp_le_exp.mpr
          have : 0 ≤ H (alpha + tau) * (n : ℝ) :=
            mul_nonneg hHtar_nn (Nat.cast_nonneg n)
          linarith
        exact le_trans hcard hmono
      · -- large n: peeling argument
        simp only [if_neg hn, add_zero]
        push_neg at hn
        have hn1 : 1 ≤ n := le_trans hNpos hn
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hrange : alpha + beta ≤ 1 / 2 - c0 :=
          hc0 n hn r S alpha beta
          ⟨hvalidD, hbeta, halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩
        have hrange' : alpha + beta ≤ 1 / 2 - c0star := by linarith
        have halpha_half : alpha ≤ 1 / 2 := le_of_lt (lt_of_le_of_lt halpha_max halphaMax_half)
        have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
        have hScard2 : S.card ≤ 2 ^ n := by
          calc S.card ≤ (Finset.univ : Finset (Cube n)).card := Finset.card_le_univ S
            _ = 2 ^ n := by
                rw [Finset.card_univ]
                exact (Fintype.card_finset (α := Fin n)).trans (by rw [Fintype.card_fin])
        -- radius ceiling
        have hr'r : ⌈tau * (n : ℝ)⌉₊ ≤ r := by
          rw [Nat.ceil_le]
          have := htaub
          rw [hbeta, le_div_iff₀ hnR] at this
          exact this
        set r'N := ⌈tau * (n : ℝ)⌉₊ with hr'Ndef
        -- peel
        have hpeel : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
            Real.exp (D.sigma n) * (V n S.card r : ℝ) :=
          V_peel_le S r'N r hr'r (D.sigma n) hnear
        have hVupS : (V n S.card r : ℝ) ≤
            Real.exp (H (alpha + beta) * (n : ℝ) +
              (C_V * (D.cSize * D.sigma n) + volSlack n)) :=
          hVup n r S alpha beta halpha_min halpha_half hbeta hrange' hScard1 hScard2 hsize
        have hcombined : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
            Real.exp (H (alpha + beta) * (n : ℝ) +
              (C_V * (D.cSize * D.sigma n) + volSlack n) + D.sigma n) := by
          calc (V n (neighborhood r'N S).card (r - r'N) : ℝ)
              ≤ Real.exp (D.sigma n) * (V n S.card r : ℝ) := hpeel
            _ ≤ Real.exp (D.sigma n) *
                Real.exp (H (alpha + beta) * (n : ℝ) +
                  (C_V * (D.cSize * D.sigma n) + volSlack n)) :=
                mul_le_mul_of_nonneg_left hVupS (Real.exp_nonneg _)
            _ = Real.exp (H (alpha + beta) * (n : ℝ) +
                  (C_V * (D.cSize * D.sigma n) + volSlack n) + D.sigma n) := by
                rw [← Real.exp_add]; congr 1; ring
        -- exponent comparison
        have hcast_sub : ((r - r'N : ℕ) : ℝ) = (r : ℝ) - (r'N : ℝ) := Nat.cast_sub hr'r
        set a := alpha + tau + ((r - r'N : ℕ) : ℝ) / (n : ℝ) with hadef
        have hbma : alpha + beta - a = (r'N : ℝ) / (n : ℝ) - tau := by
          rw [hadef, hbeta, hcast_sub]; ring
        have htau_le : tau ≤ (r'N : ℝ) / (n : ℝ) := by
          rw [le_div_iff₀ hnR, hr'Ndef]; exact Nat.le_ceil _
        have hbma_nn : 0 ≤ alpha + beta - a := by rw [hbma]; linarith
        have ha_pos : 0 < a := by
          rw [hadef]
          have : 0 ≤ ((r - r'N : ℕ) : ℝ) / (n : ℝ) := by positivity
          linarith
        have hab : a ≤ alpha + beta := by linarith
        have hb_half : alpha + beta ≤ 1 / 2 := by linarith
        have hlo_a : D.alphaMin ≤ a := by
          rw [hadef]
          have : 0 ≤ ((r - r'N : ℕ) : ℝ) / (n : ℝ) := by positivity
          linarith
        have ha_half : a ≤ 1 / 2 := by linarith
        have hslope : Real.log ((1 - a) / a) ≤ Real.log ((1 - D.alphaMin) / D.alphaMin) :=
          log_ratio_upper halphaMin_pos hlo_a ha_half
        have hHdiff : H (alpha + beta) - H a ≤
            (alpha + beta - a) * Real.log ((1 - D.alphaMin) / D.alphaMin) :=
          H_diff_le ha_pos hab hb_half hslope
        have hban_eq : (alpha + beta - a) * (n : ℝ) = (r'N : ℝ) - tau * (n : ℝ) := by
          rw [hbma, sub_mul, div_mul_cancel₀ _ (ne_of_gt hnR)]
        have hban_le : (alpha + beta - a) * (n : ℝ) ≤ 1 := by
          rw [hban_eq, hr'Ndef]
          have := Nat.ceil_lt_add_one (show 0 ≤ tau * (n : ℝ) by positivity)
          linarith
        have hprod : (H (alpha + beta) - H a) * (n : ℝ) ≤
            Real.log ((1 - D.alphaMin) / D.alphaMin) := by
          have h1 : (H (alpha + beta) - H a) * (n : ℝ) ≤
              (alpha + beta - a) * Real.log ((1 - D.alphaMin) / D.alphaMin) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right hHdiff hnR.le
          have h2 : (alpha + beta - a) * Real.log ((1 - D.alphaMin) / D.alphaMin) * (n : ℝ) =
              Real.log ((1 - D.alphaMin) / D.alphaMin) * ((alpha + beta - a) * (n : ℝ)) := by ring
          have h3 : Real.log ((1 - D.alphaMin) / D.alphaMin) * ((alpha + beta - a) * (n : ℝ)) ≤
              Real.log ((1 - D.alphaMin) / D.alphaMin) * 1 :=
            mul_le_mul_of_nonneg_left hban_le hL''nn
          nlinarith [h1, h3]
        have hVbound : (V n (neighborhood r'N S).card (r - r'N) : ℝ) ≤
            Real.exp (H a * (n : ℝ) +
              (D.sigma n + C_V * (D.cSize * D.sigma n) + volSlack n +
                Real.log ((1 - D.alphaMin) / D.alphaMin))) := by
          refine le_trans hcombined (Real.exp_le_exp.mpr ?_)
          nlinarith [hprod]
        -- nonempty and cardinality bound for T
        have hTne : (neighborhood r'N S).Nonempty :=
          hSne.mono (subset_neighborhood_self r'N S)
        have hpow_exp : ((2 ^ n : ℕ) : ℝ) = Real.exp ((n : ℝ) * Real.log 2) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.exp_nat_mul,
            Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        have hk'lt : (neighborhood r'N S).card < 2 ^ n := by
          have hle1 : ((neighborhood r'N S).card : ℝ) ≤ ((neighborhood r S).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (neighborhood_mono_radius hr'r S)
          have hlt2 : Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) <
              Real.exp ((n : ℝ) * Real.log 2) := by
            apply Real.exp_lt_exp.mpr
            have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hd : 0 < D.deltaCap := hvalid.2.1
            nlinarith [mul_pos (mul_pos hd hnR) hlog2]
          have : ((neighborhood r'N S).card : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
            rw [hpow_exp]
            exact lt_of_le_of_lt (le_trans hle1 hcap) hlt2
          exact_mod_cast this
        have hlo_target : D.alphaMin ≤ alpha + tau := by linarith
        have ha_le : a ≤ 1 / 2 - c0star := by linarith
        have hlogk' := hw n (r - r'N) (neighborhood r'N S) (alpha + tau) hTne
          hk'lt hlo_target ha_le hVbound
        have hposc : (0 : ℝ) < ((neighborhood r'N S).card : ℝ) :=
          by exact_mod_cast Finset.card_pos.mpr hTne
        rw [← Real.log_le_iff_le_exp hposc]
        linarith [hlogk']
    · -- S empty
      have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      have hEmpty : neighborhood ⌈tau * (n : ℝ)⌉₊ S = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr ?_
        intro x hx
        rw [mem_neighborhood_iff] at hx
        rcases hx with ⟨u, hu, _⟩
        rw [hSempty] at hu
        exact absurd hu (Finset.notMem_empty u)
      rw [hEmpty, Finset.card_empty]
      simp only [Nat.cast_zero]
      exact le_of_lt (Real.exp_pos _)

lemma r2_downward_pinning (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D) :
    ∃ sigmaDP : ℕ → ℝ, Sublinear sigmaDP ∧
    ∀ n r S alpha beta, classMember D n r S alpha beta →
      ∀ tau : ℝ, 0 < tau → tau ≤ beta →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (min (alpha + tau) (1 / 2)) * (n : ℝ) + sigmaDP n) := by
  obtain ⟨sigmaDP, hsub, hcore⟩ := r2_dp_core hBV hVPlus hVC D hvalid
  refine ⟨sigmaDP, hsub, ?_⟩
  intro n r S alpha beta hmem tau htau htaub
  by_cases hhalf : alpha + tau < 1 / 2
  · rw [min_eq_left hhalf.le]
    exact hcore n r S alpha beta hmem tau htau htaub hhalf
  · -- at or above the equator the cube-size bound is enough
    rw [min_eq_right (not_lt.mp hhalf)]
    have hHhalf : H (1 / 2 : ℝ) = Real.log 2 := by
      unfold H
      rw [show (1/2 : ℝ) = 2⁻¹ by norm_num]
      exact Real.binEntropy_two_inv
    have hcard := cube_card_le_two_pow (neighborhood ⌈tau * (n : ℝ)⌉₊ S)
    have hσ : 0 ≤ sigmaDP n := hsub.1 n
    calc ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ)
        ≤ Real.exp ((n : ℝ) * Real.log 2) := hcard
      _ ≤ Real.exp (H (1 / 2) * (n : ℝ) + sigmaDP n) := by
          apply Real.exp_le_exp.mpr
          rw [hHhalf, mul_comm]
          linarith [hσ]

private lemma validQData_buffered_of_validData (D : StabilityData)
    (hvalid : validData D) (sigmaDP : ℕ → ℝ) (hsubDP : Sublinear sigmaDP) :
    validQData
      { qMin := D.alphaMin
        qMax := D.alphaMax
        s0 := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4)
        mu0 := (1 / 2 - D.alphaMax) / 4
        sigma := fun n => D.cSize * D.sigma n + sigmaDP n } := by
  rcases hvalid with
    ⟨hrho, _hdelta_pos, _hdelta_lt, hcSize, halphaMin_pos, halpha_le,
      halphaMax_lt, hsigma, hlog⟩
  refine ⟨halphaMin_pos, halpha_le, halphaMax_lt, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · linarith
  · have hmin_le : min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4) ≤
        (1 / 2 - D.alphaMax) / 4 := min_le_right _ _
    linarith
  · exact reductions_sublinear_add
      (sublinear_const_mul D.cSize (le_trans zero_le_one hcSize) hsigma)
      hsubDP
  · intro m hm
    have hsigma0 : 0 ≤ D.sigma m := hsigma.1 m
    have hsigmaDP0 : 0 ≤ sigmaDP m := hsubDP.1 m
    have hscaled : D.sigma m ≤ D.cSize * D.sigma m := by
      nlinarith
    linarith [hlog m hm]

private lemma fat_buffered_of_classMember_nonempty (D : StabilityData)
    (hvalid : validData D) (sigmaDP : ℕ → ℝ) (hsubDP : Sublinear sigmaDP)
    {n r : ℕ} {S : Finset (Cube n)} {alpha beta : ℝ}
    (hmem : classMember D n r S alpha beta) (hS : S.Nonempty) :
    fat
      { qMin := D.alphaMin
        qMax := D.alphaMax
        s0 := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4)
        mu0 := (1 / 2 - D.alphaMax) / 4
        sigma := fun n => D.cSize * D.sigma n + sigmaDP n }
      n S alpha := by
  rcases hmem with
    ⟨_hvalidD, _hbeta, halpha_min, halpha_max, _hradius, hsize, _hnear, _hcap⟩
  refine ⟨hS, validQData_buffered_of_validData D hvalid sigmaDP hsubDP,
    halpha_min, halpha_max, ?_⟩
  exact le_trans hsize (by nlinarith [hsubDP.1 n])

private lemma pinned_zero_of_fat {Q : QData} {m : ℕ} {A : Finset (Cube m)}
    {q : ℝ} (hfat : fat Q m A q) :
    ((neighborhood 0 A).card : ℝ) ≤
      Real.exp (H (q + (0 : ℝ) / (m : ℝ)) * (m : ℝ) + Q.sigma m) := by
  classical
  rw [neighborhood_zero_eq]
  have hApos : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hfat.1
  rw [← Real.log_le_iff_le_exp hApos]
  have hsize := hfat.2.2.2.2
  have hupper := (abs_le.mp hsize).2
  simpa [zero_div, add_comm, add_left_comm, add_assoc] using hupper

private lemma pinned_buffered_of_classMember_large (D : StabilityData)
    (hvalid : validData D) (sigmaDP : ℕ → ℝ) (hsubDP : Sublinear sigmaDP)
    (hDP : ∀ n r S alpha beta, classMember D n r S alpha beta →
      ∀ tau : ℝ, 0 < tau → tau ≤ beta →
        ((neighborhood ⌈tau * (n : ℝ)⌉₊ S).card : ℝ) ≤
          Real.exp (H (min (alpha + tau) (1 / 2)) * (n : ℝ) + sigmaDP n))
    {n rTop : ℕ} {S : Finset (Cube n)} {alpha beta : ℝ}
    (hmem : classMember D n rTop S alpha beta)
    (hn : 1 ≤ n)
    (hnrho : (1 : ℝ) / (n : ℝ) ≤ D.rho / 2)
    (hngap : (1 : ℝ) / (n : ℝ) ≤ (1 / 2 - D.alphaMax) / 4) :
    pinned
      { qMin := D.alphaMin
        qMax := D.alphaMax
        s0 := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4)
        mu0 := (1 / 2 - D.alphaMax) / 4
        sigma := fun n => D.cSize * D.sigma n + sigmaDP n }
      n S alpha := by
  classical
  rcases hvalid with
    ⟨hrho, _hdelta_pos, _hdelta_lt, hcSize, _halphaMin_pos, _halpha_le,
      halphaMax_lt, hsigma, _hlog⟩
  rcases hmem with
    ⟨hvalidD, hbeta, _halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    by_cases hS0 : S.card = 0
    · have hSempty : S = ∅ := Finset.card_eq_zero.mp hS0
      rw [hSempty, neighborhood_zero_eq]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · have hS : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hS0)
      simpa using pinned_zero_of_fat
        (fat_buffered_of_classMember_nonempty D
          ⟨hrho, _hdelta_pos, _hdelta_lt, hcSize, _halphaMin_pos, _halpha_le,
            halphaMax_lt, hsigma, _hlog⟩ sigmaDP hsubDP
          ⟨hvalidD, hbeta, _halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩ hS)
  · set tau : ℝ := (r : ℝ) / (n : ℝ) with htau_def
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have htau_pos : 0 < tau := by
      rw [htau_def]
      exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hr0) hnpos
    set s0 : ℝ := min (D.rho / 2) ((1 / 2 - D.alphaMax) / 4) with hs0_def
    have hs0_nonneg : 0 ≤ s0 := by
      rw [hs0_def]
      exact le_of_lt (lt_min (by linarith) (by linarith))
    have hceil_lt : ((Nat.ceil (s0 * (n : ℝ)) : ℕ) : ℝ) <
        s0 * (n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hs0_nonneg hnpos.le)
    have hr_real : (r : ℝ) ≤ (Nat.ceil (s0 * (n : ℝ)) : ℝ) := by
      exact_mod_cast hr
    have htau_le_s0_plus : tau ≤ s0 + (1 : ℝ) / (n : ℝ) := by
      rw [htau_def]
      have hlt : (r : ℝ) < s0 * (n : ℝ) + 1 := lt_of_le_of_lt hr_real hceil_lt
      rw [div_le_iff₀ hnpos]
      have heq : (s0 + (1 : ℝ) / (n : ℝ)) * (n : ℝ) = s0 * (n : ℝ) + 1 := by
        field_simp [ne_of_gt hnpos]
      rw [heq]
      exact hlt.le
    have hs0_le_rho : s0 ≤ D.rho / 2 := by
      rw [hs0_def]
      exact min_le_left _ _
    have hs0_le_gap : s0 ≤ (1 / 2 - D.alphaMax) / 4 := by
      rw [hs0_def]
      exact min_le_right _ _
    have htau_le_rho : tau ≤ D.rho := by
      linarith
    have hbeta_ge_rho : D.rho ≤ beta := by
      rw [hbeta]
      rw [le_div_iff₀ hnpos]
      exact hradius
    have htau_le_beta : tau ≤ beta := le_trans htau_le_rho hbeta_ge_rho
    have htau_le_gap_half : tau ≤ (1 / 2 - D.alphaMax) / 2 := by
      linarith
    have halpha_tau_half : alpha + tau ≤ 1 / 2 := by
      linarith
    have hceil_tau : ⌈tau * (n : ℝ)⌉₊ = r := by
      have hmul : tau * (n : ℝ) = (r : ℝ) := by
        rw [htau_def]
        field_simp [ne_of_gt hnpos]
      rw [hmul]
      simp
    have hDP' := hDP n rTop S alpha beta
      ⟨hvalidD, hbeta, _halpha_min, halpha_max, hradius, hsize, hnear, hcap⟩
      tau htau_pos htau_le_beta
    rw [hceil_tau] at hDP'
    calc ((neighborhood r S).card : ℝ)
        ≤ Real.exp (H (min (alpha + tau) (1 / 2)) * (n : ℝ) + sigmaDP n) := hDP'
      _ = Real.exp (H (alpha + (r : ℝ) / (n : ℝ)) * (n : ℝ) + sigmaDP n) := by
          rw [min_eq_left halpha_tau_half, htau_def]
      _ ≤ Real.exp (H (alpha + (r : ℝ) / (n : ℝ)) * (n : ℝ) +
            (D.cSize * D.sigma n + sigmaDP n)) := by
          apply Real.exp_le_exp.mpr
          have hnonneg : 0 ≤ D.cSize * D.sigma n :=
            mul_nonneg (le_trans zero_le_one hcSize) (hsigma.1 n)
          linarith

/-
Diagonal envelope: given a family of finite thresholds `m0 j` (one per
precision level `1/j`), there is a single sublinear envelope `s` such that
every large `m` admits an achieved level `j` with `m0 j ≤ m` and
`m / j ≤ s m`.  This packages the standard `o(n)`-diagonalization used to
convert `∀ δ ∃ m0(δ)` statements into one sublinear slack.
-/
private lemma sublinear_diag_envelope (m0 : ℕ → ℕ) :
    ∃ s : ℕ → ℝ, Sublinear s ∧
      ∀ m : ℕ, m0 1 ≤ m → 1 ≤ m →
        ∃ j : ℕ, 1 ≤ j ∧ m0 j ≤ m ∧ (m : ℝ) / (j : ℝ) ≤ s m := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ, StrictMono K ∧ ∀ m, K m ≥ m0 (m + 1) + m + 1 := by
    exact ⟨ fun m => Nat.recOn m ( m0 1 + 1 + 1 ) fun n ih => ih + m0 ( n + 2 ) + 2, strictMono_nat_of_lt_succ fun n => by linarith, fun n => Nat.recOn n ( by linarith ) fun n ih => by linarith ⟩;
  refine' ⟨ fun m => ( m : ℝ ) / ( ( Nat.findGreatest ( fun n => K n ≤ m ) m + 1 ) : ℝ ), _, _ ⟩ <;> norm_num [ Sublinear ];
  · refine' ⟨ fun n => by positivity, fun ε hε => ⟨ Nat.ceil ( K ( Nat.ceil ( ε⁻¹ ) ) ), fun n hn => _ ⟩ ⟩;
    rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num at *;
    -- Since $K$ is strictly monotone, we have $Nat.findGreatest (fun n_1 => K n_1 ≤ n) n ≥ ⌈ε⁻¹⌉₊$.
    have h_findGreatest : Nat.findGreatest (fun n_1 => K n_1 ≤ n) n ≥ ⌈ε⁻¹⌉₊ := by
      refine' Nat.le_findGreatest _ _ <;> norm_num [ hn ];
      exact le_trans ( Nat.le_ceil _ ) ( mod_cast hn.trans' ( hK.1.id_le _ ) );
    nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hε ), show ( Nat.findGreatest ( fun n_1 => K n_1 ≤ n ) n : ℝ ) ≥ ⌈ε⁻¹⌉₊ by exact_mod_cast h_findGreatest, mul_nonneg hε.le ( Nat.cast_nonneg n ) ];
  · intro m hm₁ hm₂;
    have := Nat.findGreatest_eq_iff.mp ( rfl : Nat.findGreatest ( fun n => K n ≤ m ) m = _ );
    grind

/-
Parameterized lower range control: the inverse-radius lower bound with the
volume-calculus constants `C_V`, `volSlack` (and their calculus conclusion
`hcalc`, at density `alphaMin` and slack `c0 = (1/2 - alphaMax)/2`) supplied
externally.  This is the body of `r1_range_control_lower` after the internal
`hVC` extraction, so that the constants can be shared across many `sigma`.
-/
lemma r1_range_control_lower_param
    (D : StabilityData) (hvalid : validData D)
    (C_V : ℝ) (hC_V : 1 ≤ C_V) (volSlack : ℕ → ℝ)
    (hcalc : ∀ n k r : ℕ, ∀ alpha beta sizeSlack : ℝ,
        D.alphaMin ≤ alpha → alpha ≤ 1 / 2 → 0 ≤ sizeSlack →
        beta = (r : ℝ) / (n : ℝ) →
        alpha + beta ≤ 1 / 2 - (1 / 2 - D.alphaMax) / 2 →
        1 ≤ k → k ≤ 2 ^ n →
        |Real.log ((k : ℝ)) - H alpha * (n : ℝ)| ≤ sizeSlack →
        |Real.log ((V n k r : ℝ)) - H (alpha + beta) * (n : ℝ)| ≤
            C_V * sizeSlack + volSlack n ∧
        |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + volSlack n) :
    ∀ n, 1 ≤ n → ∀ (t : ℕ) (S : Finset (Cube n)) (alpha : ℝ),
        D.alphaMin ≤ alpha → alpha ≤ D.alphaMax → sizeHyp D n S alpha →
        (ball (∅ : Cube n) t).card ≤ S.card →
        (S.card : ℝ) < ((ball (∅ : Cube n) (t + 1)).card : ℝ) →
        alpha - (C_V * (D.cSize * D.sigma n) + volSlack n + 1) / (n : ℝ) ≤
          (t : ℝ) / (n : ℝ) := by
  refine (fun _ : 1 ≤ C_V => ?_) hC_V
  intro n hn t S alpha halpha_min halpha_max hsize ht_card ht_strict
  have hnpos : 0 < (n : ℝ) := by
    positivity
  have hn_ne : (n : ℝ) ≠ 0 := by
    positivity
  have halpha_half : alpha ≤ 1 / 2 := by
    linarith [ hvalid.2.2.2.2.2.2.1 ]
  have hslack_nonneg : 0 ≤ D.cSize * D.sigma n := by
    exact mul_nonneg ( by linarith [ hvalid.2.2.2.1 ] ) ( by linarith [ hvalid.2.2.2.2.2.2.2.1.1 n ] )
  have hS1 : 1 ≤ S.card := by
    refine' le_trans _ ht_card;
    exact Finset.card_pos.mpr ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simp +decide [ hDist ] ⟩ ⟩
  have hScap : S.card ≤ 2 ^ n := by
    exact le_trans ( Finset.card_le_univ _ ) ( by norm_num [ Cube ] )
  have hrange : alpha + 0 ≤ 1 / 2 - (1 / 2 - D.alphaMax) / 2 := by
    linarith [ hvalid.2.2.2.2.2.2.1 ];
  specialize hcalc n S.card 0 alpha 0 ( D.cSize * D.sigma n ) halpha_min halpha_half hslack_nonneg ; simp_all +decide [ sizeHyp ];
  have hrmin_le_succ : rmin n S.card ≤ t + 1 := by
    unfold rmin; simp +decide [ Finset.min' ] ;
    split_ifs <;> simp_all +decide; all_goals grind;
  rw [ ← add_div, le_div_iff₀ ] <;> norm_num <;> nlinarith [ abs_le.mp hcalc.2, show ( rmin n S.card : ℝ ) ≤ t + 1 by exact_mod_cast hrmin_le_succ ]

/-
Uniform range-or-large-slack dichotomy.  With structural constants fixed
(no dependence on `sigma`), every class member is either in the strictly
sub-equatorial range `alpha + beta ≤ 1/2 - c0`, or the dimension is
controlled by the envelope: `n * log 2 ≤ C * (sigma n + 1)`.  The constants
`c0` and `C` are chosen before `sigma`.
-/
lemma r1_range_control_uniform
    (hBV : BallVolumeTwoSidedStatement) (hVPlus : VPlusStatement)
    (hVC : InteriorVolumeCalculusStatement)
    (rho deltaCap cSize alphaMin alphaMax : ℝ)
    (hrho : 0 < rho) (hdeltaCap : 0 < deltaCap) (hdeltaCap1 : deltaCap < 1)
    (hcSize : 1 ≤ cSize) (halphaMin : 0 < alphaMin) (halpha_le : alphaMin ≤ alphaMax)
    (halphaMax : alphaMax < 1 / 2) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ sigma : ℕ → ℝ, Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
      ∀ (n r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ),
        classMember ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ n r S alpha beta →
        S.Nonempty →
        alpha + beta ≤ 1 / 2 - c0 ∨ (n : ℝ) * Real.log 2 ≤ C * (sigma n + 1) := by
  obtain ⟨cUpper, hcUpper_pos, NUpper, hNUpper1, hupper⟩ := r1_range_control_upper hBV ⟨rho, deltaCap, cSize, alphaMin, alphaMax, fun n => Real.log (n + 2) + 1⟩ (by
  constructor <;> norm_num [ hrho, hdeltaCap, hdeltaCap1, hcSize, halphaMin, halpha_le, halphaMax ];
  refine' ⟨ _, fun n hn => le_add_of_le_of_nonneg ( Real.log_le_log ( by positivity ) ( by linarith ) ) zero_le_one ⟩;
  constructor;
  · exact fun n => add_nonneg ( Real.log_nonneg ( by linarith ) ) zero_le_one;
  · intro ε hε_pos
    have h_log_growth : Filter.Tendsto (fun n : ℕ => (Real.log (n + 2) + 1) / (n : ℝ)) Filter.atTop (nhds 0) := by
      -- We can use the fact that $\frac{\log(n)}{n}$ tends to $0$ as $n$ tends to infinity.
      have h_log_div_n : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      -- We can use the fact that $\frac{\log(n+2)}{n}$ tends to $0$ as $n$ tends to infinity.
      have h_log_div_n_plus_two : Filter.Tendsto (fun n : ℕ => Real.log (n + 2) / (n : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_div_n_plus_two : Filter.Tendsto (fun n : ℕ => (Real.log (n : ℝ) + Real.log (1 + 2 / (n : ℝ))) / (n : ℝ)) Filter.atTop (nhds 0) := by
          simpa [ add_div ] using h_log_div_n.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) ) ( by norm_num ) ) tendsto_natCast_atTop_atTop );
        refine h_log_div_n_plus_two.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ ← Real.log_mul ( by positivity ) ( by positivity ), mul_add, mul_div_cancel₀ _ ( by positivity ), mul_one ] );
      simpa [ add_div ] using h_log_div_n_plus_two.add ( tendsto_inv_atTop_nhds_zero_nat );
    exact Filter.eventually_atTop.mp ( h_log_growth.eventually ( gt_mem_nhds hε_pos ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N + 1, fun n hn ↦ by have := hN n ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩);
  obtain ⟨C_V, hC_V, volSlack, hvolSlack, hcalc⟩ := hVC alphaMin ((1 / 2 - alphaMax) / 2) halphaMin (by linarith);
  obtain ⟨N_v, hN_v⟩ := hvolSlack.2 (cUpper / 4) (by linarith);
  refine' ⟨ cUpper / 2, half_pos hcUpper_pos, ( NUpper + N_v + 1 : ℝ ) * Real.log 2 + ( 4 / cUpper ) * ( C_V * cSize + 1 ) * Real.log 2 + 1, _, _ ⟩;
  · exact le_add_of_nonneg_left ( by positivity );
  · intro sigma hsub hlog n r S alpha beta hmem hSne
    by_cases hnN0 : n < NUpper + N_v + 1;
    · refine Or.inr ?_;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( show sigma n + 1 ≥ 1 from _ ) _ );
      · nlinarith [ show ( n : ℝ ) ≤ NUpper + N_v by norm_cast; linarith, show 0 < Real.log 2 by positivity, show 0 ≤ 4 / cUpper * ( C_V * cSize + 1 ) * Real.log 2 by positivity ];
      · exact le_add_of_nonneg_left ( hsub.1 n );
      · positivity;
    · obtain ⟨t, ht_le, ht_card, htV, ht_strict⟩ := r1_range_control_t_star hVPlus n r S hSne (by
      have := hmem.2.2.2.2.2.2.1;
      contrapose! this;
      have h_contra : (2 ^ n : ℝ) ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ (neighborhood r S).card ∧ (neighborhood r S).card ≤ Real.exp ((1 - deltaCap) * (n : ℝ) * Real.log 2) := by
        exact ⟨ mod_cast this, mod_cast subset_neighborhood_self r S |> Finset.card_le_card, mod_cast hmem.2.2.2.2.2.2.2 ⟩;
      have h_contra : (2 ^ n : ℝ) ≤ Real.exp ((1 - deltaCap) * (n : ℝ) * Real.log 2) := by
        exact le_trans ( mod_cast h_contra.1 ) ( h_contra.2.1.trans h_contra.2.2 );
      have h_contra : (n : ℝ) * Real.log 2 ≤ (1 - deltaCap) * (n : ℝ) * Real.log 2 := by
        simpa using Real.log_le_log ( by positivity ) h_contra;
      nlinarith [ show ( n : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.log_pos one_lt_two ) ]);
      have hball_cap : (ball (∅ : Cube n) (t + r)).card ≤ Real.exp ((1 - deltaCap) * (n : ℝ) * Real.log 2) := by
        refine le_trans htV ?_;
        refine le_trans ( V_le_neighborhood_card r S ) ?_;
        exact hmem.2.2.2.2.2.2.2;
      have hupper_n := hupper n (by linarith) t r hball_cap;
      have hlower_n := r1_range_control_lower_param ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ hmem.1 C_V hC_V volSlack hcalc n (by linarith) t S alpha hmem.2.2.1 hmem.2.2.2.1 hmem.2.2.2.2.2.1 ht_card ht_strict;
      by_cases h_case : (C_V * (cSize * sigma n) + volSlack n + 1) / (n : ℝ) ≤ cUpper / 2;
      · left;
        rw [ hmem.2.1 ] at *;
        ring_nf at *; linarith;
      · have h_case2 : (cUpper / 2) * (n : ℝ) < C_V * (cSize * sigma n) + volSlack n + 1 := by
          rw [ div_le_iff₀ ] at h_case <;> linarith [ show ( n : ℝ ) > 0 by norm_cast; linarith ];
        have h_case2 : (n : ℝ) < (4 / cUpper) * (C_V * cSize + 1) * (sigma n + 1) := by
          field_simp;
          nlinarith [ hN_v n ( by linarith ), hsub.1 n, show ( 0 : ℝ ) ≤ C_V * cSize by positivity, show ( 0 : ℝ ) ≤ C_V * sigma n by exact mul_nonneg ( by positivity ) ( by linarith [ hsub.1 n ] ), show ( 0 : ℝ ) ≤ cSize * sigma n by exact mul_nonneg ( by positivity ) ( by linarith [ hsub.1 n ] ) ];
        exact Or.inr ( by nlinarith [ Real.log_nonneg one_le_two, show ( 0 : ℝ ) ≤ ( NUpper + N_v + 1 ) * Real.log 2 by positivity, show ( 0 : ℝ ) ≤ 4 / cUpper * ( C_V * cSize + 1 ) * Real.log 2 by positivity, hsub.1 n ] )



private lemma r1_sublinear_log_succ : Sublinear (fun n => Real.log ((n : ℝ) + 1)) := by
  constructor <;> norm_num;
  · exact fun n => Real.log_nonneg <| by linarith;
  · have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log (n + 1) / (n : ℝ)) Filter.atTop (nhds 0) := by
      suffices h_log : Filter.Tendsto (fun n : ℕ => (Real.log n + Real.log (1 + 1 / (n : ℝ))) / (n : ℝ)) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ ← Real.log_mul ( by positivity ) ( by positivity ), mul_add, mul_one_div_cancel ( by positivity ), mul_one ] );
      have h_log_n : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      simpa [ add_div ] using h_log_n.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) ( by norm_num ) ) ( tendsto_inv_atTop_nhds_zero_nat ) );
    intro ε hε; have := h_log_growth.eventually ( gt_mem_nhds <| show 0 < ε by positivity ) ; rcases Filter.eventually_atTop.mp this with ⟨ N, hN ⟩ ; exact ⟨ N + 1, fun n hn => by have := hN n ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩

set_option maxHeartbeats 2000000 in
lemma r1_range_control_at (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (D : StabilityData) (hvalid : validData D) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ N : ℕ, 1 ≤ N ∧ ∃ γ : ℝ, 0 < γ ∧
      ∀ n, N ≤ n → D.sigma n ≤ γ * (n : ℝ) →
        ∀ (r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ),
          classMember D n r S alpha beta → alpha + beta ≤ 1 / 2 - c0 := by
  classical
  obtain ⟨cUpper, hcUpper, NUpper, hNUpper1, hupper⟩ :=
    r1_range_control_upper hBV D hvalid
  have halphaMin_pos : 0 < D.alphaMin := hvalid.2.2.2.2.1
  have halphaMax_half : D.alphaMax < 1 / 2 := hvalid.2.2.2.2.2.2.1
  have hcSize_pos : 0 < D.cSize := lt_of_lt_of_le zero_lt_one hvalid.2.2.2.1
  have hc0IVC : (0 : ℝ) < (1 / 2 - D.alphaMax) / 2 := by linarith
  obtain ⟨C_V, hC_V, volSlack, hvolSlack, hcalc⟩ :=
    hVC D.alphaMin ((1 / 2 - D.alphaMax) / 2) halphaMin_pos hc0IVC
  have halphaMin_lt_one : D.alphaMin < 1 := by
    linarith [hvalid.2.2.2.2.2.1, halphaMax_half]
  have hHamin_pos : 0 < H D.alphaMin := by
    unfold H; exact Real.binEntropy_pos halphaMin_pos halphaMin_lt_one
  have hCVcSize_pos : 0 < C_V * D.cSize := mul_pos (by linarith) hcSize_pos
  obtain ⟨N_vs, hN_vs⟩ := hvolSlack.2 (cUpper / 8) (by linarith)
  refine ⟨cUpper / 2, by linarith,
    max (max NUpper N_vs) (max (⌈8 / cUpper⌉₊) 1), ?_,
    min (H D.alphaMin / (2 * D.cSize)) (cUpper / (4 * (C_V * D.cSize + 1))),
    ?_, ?_⟩
  · exact le_trans (le_max_right _ _) (le_max_right _ _)
  · exact lt_min (by positivity) (div_pos hcUpper (by nlinarith [hCVcSize_pos]))
  · intro n hn hsig r S alpha beta hmem
    have hNUpper : NUpper ≤ n :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hNvs : N_vs ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hNlin : ⌈8 / cUpper⌉₊ ≤ n :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hn1 : 1 ≤ n := le_trans hNUpper1 hNUpper
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    rcases hmem with
      ⟨_hvalidD, hbeta, halpha_min, halpha_max, _hradius, hsize, _hnear, hcap⟩
    have halpha_nonneg : 0 ≤ alpha := le_trans halphaMin_pos.le halpha_min
    have halpha_half : alpha ≤ 1 / 2 :=
      le_of_lt (lt_of_le_of_lt halpha_max halphaMax_half)
    have hHalpha_nonneg : 0 ≤ H alpha := by
      unfold H; exact Real.binEntropy_nonneg halpha_nonneg (by linarith)
    have hHamin_le_alpha : H D.alphaMin ≤ H alpha :=
      H_mono_on_half halphaMin_pos.le halpha_min halpha_half
    have hsig_nn : 0 ≤ D.sigma n := hvalid.2.2.2.2.2.2.2.1.1 n
    have hsig_nonempty : D.sigma n ≤ (H D.alphaMin / (2 * D.cSize)) * (n : ℝ) :=
      le_trans hsig (mul_le_mul_of_nonneg_right (min_le_left _ _) hnpos.le)
    have hsig1 : D.sigma n ≤ (cUpper / (4 * (C_V * D.cSize + 1))) * (n : ℝ) :=
      le_trans hsig (mul_le_mul_of_nonneg_right (min_le_right _ _) hnpos.le)
    -- nonempty S (else the size hypothesis forces sigma too large)
    have hS_nonempty : S.Nonempty := by
      have hS_pos_nat : 0 < S.card := by
        by_contra hnot_pos
        have hS0 : S.card = 0 := Nat.eq_zero_of_not_pos hnot_pos
        have hHn_nonneg : 0 ≤ H alpha * (n : ℝ) :=
          mul_nonneg hHalpha_nonneg (Nat.cast_nonneg n)
        have hHn_le : H alpha * (n : ℝ) ≤ D.cSize * D.sigma n := by
          rw [sizeHyp, hS0, Nat.cast_zero, Real.log_zero] at hsize
          simpa [abs_of_nonneg hHn_nonneg] using hsize
        have hc_sigma :
            D.cSize * D.sigma n ≤ (H D.alphaMin / 2) * (n : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left hsig_nonempty hcSize_pos.le
          have heq :
              D.cSize * (H D.alphaMin / (2 * D.cSize) * (n : ℝ)) =
                (H D.alphaMin / 2) * (n : ℝ) := by
            field_simp
          simpa [heq] using hmul
        have hHamin_n_le : H D.alphaMin * (n : ℝ) ≤ H alpha * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hHamin_le_alpha (Nat.cast_nonneg n)
        nlinarith
      exact Finset.card_pos.mp hS_pos_nat
    have hS_not_full : S.card < 2 ^ n := by
      by_contra hnot_lt
      have hpow_le_S : 2 ^ n ≤ S.card := Nat.le_of_not_gt hnot_lt
      have hpow_le_neigh_nat : 2 ^ n ≤ (neighborhood r S).card :=
        le_trans hpow_le_S (Finset.card_le_card (subset_neighborhood_self r S))
      have hpow_le_neigh :
          (((2 ^ n : ℕ) : ℝ) ≤ ((neighborhood r S).card : ℝ)) := by
        exact_mod_cast hpow_le_neigh_nat
      have hpow_exp : ((2 ^ n : ℕ) : ℝ) =
          Real.exp ((n : ℝ) * Real.log 2) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hexp_le :
          Real.exp ((n : ℝ) * Real.log 2) ≤
            Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) := by
        rw [← hpow_exp]
        exact le_trans hpow_le_neigh hcap
      have harg_le := Real.exp_le_exp.mp hexp_le
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hprod_pos : 0 < D.deltaCap * (n : ℝ) * Real.log 2 :=
        mul_pos (mul_pos hvalid.2.1 hnpos) hlog2_pos
      nlinarith
    -- select `t` via V+ and get the cap-side upper bound on `(t+r)/n`
    obtain ⟨t, _ht_le, ht_card, htV, ht_strict⟩ :=
      r1_range_control_t_star hVPlus n r S hS_nonempty hS_not_full
    have hball_cap :
        ((ball (∅ : Cube n) (t + r)).card : ℝ) ≤
          Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) := by
      calc ((ball (∅ : Cube n) (t + r)).card : ℝ)
          ≤ (V n S.card r : ℝ) := htV
        _ ≤ ((neighborhood r S).card : ℝ) := V_le_neighborhood_card r S
        _ ≤ Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2) := hcap
    have hupper_n := hupper n hNUpper t r hball_cap
    rw [div_le_iff₀ hnpos] at hupper_n
    -- interior-volume lower bound (inlined `r1_range_control_lower`)
    have hslack_nonneg : 0 ≤ D.cSize * D.sigma n :=
      mul_nonneg (le_trans zero_le_one hvalid.2.2.2.1) hsig_nn
    have hS1 : 1 ≤ S.card := Finset.card_pos.mpr hS_nonempty
    have hScap : S.card ≤ 2 ^ n := hS_not_full.le
    have hrange0 : alpha + (0 : ℝ) ≤ 1 / 2 - (1 / 2 - D.alphaMax) / 2 := by
      nlinarith [halpha_max, halphaMax_half]
    obtain ⟨_, hrmin⟩ := hcalc n S.card 0 alpha 0 (D.cSize * D.sigma n)
      halpha_min halpha_half hslack_nonneg (by simp) hrange0 hS1 hScap hsize
    have hcard_succ : S.card ≤ (ball (∅ : Cube n) (t + 1)).card := by
      have hstrict_nat : S.card < (ball (∅ : Cube n) (t + 1)).card := by
        exact_mod_cast ht_strict
      exact hstrict_nat.le
    have hrmin_le_succ : rmin n S.card ≤ t + 1 := by
      let vals := (Finset.range (n + 1)).filter
        fun rr => S.card ≤ (ball (∅ : Cube n) rr).card
      by_cases ht_le_n : t + 1 ≤ n
      · have hmem : t + 1 ∈ vals := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ht_le_n), hcard_succ⟩
        have hvals : vals.Nonempty := ⟨t + 1, hmem⟩
        unfold rmin
        change (if h : vals.Nonempty then vals.min' h else n) ≤ t + 1
        rw [dif_pos hvals]
        exact vals.min'_le (t + 1) hmem
      · have hn_le_t : n ≤ t + 1 := Nat.le_of_not_ge ht_le_n
        have hrmin_le_n : rmin n S.card ≤ n := by
          unfold rmin
          change (if h : vals.Nonempty then vals.min' h else n) ≤ n
          by_cases hvals : vals.Nonempty
          · rw [dif_pos hvals]
            exact Nat.lt_succ_iff.mp
              (Finset.mem_range.mp (Finset.mem_filter.mp (vals.min'_mem hvals)).1)
          · rw [dif_neg hvals]
        exact le_trans hrmin_le_n hn_le_t
    have hrmin_le_succ_real : (rmin n S.card : ℝ) ≤ (t : ℝ) + 1 := by
      exact_mod_cast hrmin_le_succ
    have ht_lower :
        alpha * (n : ℝ) - (C_V * (D.cSize * D.sigma n) + volSlack n) - 1 ≤
          (t : ℝ) := by
      have hlow := (abs_le.mp hrmin).1
      linarith
    -- the total lower slack is at most (cUpper/2)·n
    have hvs_bound : volSlack n ≤ (cUpper / 8) * (n : ℝ) := hN_vs n hNvs
    have hone_bound : (1 : ℝ) ≤ (cUpper / 8) * (n : ℝ) := by
      have h8 : (8 : ℝ) / cUpper ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hNlin)
      rw [div_le_iff₀ hcUpper] at h8
      nlinarith [h8]
    have hCVsig_bound :
        C_V * (D.cSize * D.sigma n) ≤ (cUpper / 4) * (n : ℝ) := by
      have hden_pos : (0 : ℝ) < 4 * (C_V * D.cSize + 1) := by
        nlinarith [hCVcSize_pos]
      have hmul :
          C_V * (D.cSize * D.sigma n) ≤
            (C_V * D.cSize) *
              ((cUpper / (4 * (C_V * D.cSize + 1))) * (n : ℝ)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hsig1 hCVcSize_pos.le
      refine le_trans hmul ?_
      rw [show (C_V * D.cSize) *
              ((cUpper / (4 * (C_V * D.cSize + 1))) * (n : ℝ))
            = ((C_V * D.cSize) * cUpper / (4 * (C_V * D.cSize + 1))) * (n : ℝ)
            by ring]
      apply mul_le_mul_of_nonneg_right _ hnpos.le
      rw [div_le_div_iff₀ hden_pos (by norm_num : (0 : ℝ) < 4)]
      nlinarith [hcUpper, hCVcSize_pos]
    -- combine cap-side upper and interior-volume lower bounds
    have hr : beta * (n : ℝ) = (r : ℝ) := by
      rw [hbeta, div_mul_cancel₀ _ (ne_of_gt hnpos)]
    have hkey : (alpha + beta) * (n : ℝ) ≤ (1 / 2 - cUpper / 2) * (n : ℝ) := by
      nlinarith [ht_lower, hupper_n, hvs_bound, hone_bound, hCVsig_bound, hr]
    exact le_of_mul_le_mul_right hkey hnpos

set_option maxHeartbeats 2000000 in
lemma r1_range_control_class_constants (hBV : BallVolumeTwoSidedStatement)
    (hVPlus : VPlusStatement) (hVC : InteriorVolumeCalculusStatement)
    (rho deltaCap cSize alphaMin alphaMax : ℝ)
    (hrho : 0 < rho) (hdeltaCap_pos : 0 < deltaCap) (hdeltaCap_lt : deltaCap < 1)
    (hcSize : 1 ≤ cSize) (halphaMin_pos : 0 < alphaMin)
    (halphaMin_le_max : alphaMin ≤ alphaMax) (halphaMax_half : alphaMax < 1 / 2) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ N : ℕ, 1 ≤ N ∧ ∃ γ : ℝ, 0 < γ ∧
      ∀ sigma, validData ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ →
      ∀ n, N ≤ n → sigma n ≤ γ * (n : ℝ) →
        ∀ (r : ℕ) (S : Finset (Cube n)) (alpha beta : ℝ),
          classMember ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ n r S alpha beta → alpha + beta ≤ 1 / 2 - c0 := by
  classical
  -- Dummy data, sharing all class reals but with a concrete sublinear envelope,
  -- used only to extract the (σ-independent) range-control constants.
  set D0 : StabilityData :=
    ⟨rho, deltaCap, cSize, alphaMin, alphaMax, fun n => Real.log ((n : ℝ) + 1)⟩ with hD0
  have hvalid0 : validData D0 := by
    refine ⟨hrho, hdeltaCap_pos, hdeltaCap_lt, hcSize, halphaMin_pos, halphaMin_le_max,
      halphaMax_half, r1_sublinear_log_succ, ?_⟩
    intro m hm
    have hmpos : 0 < m := hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    exact Real.log_le_log hm0 (by linarith)
  obtain ⟨cUpper, hcUpper, NUpper, hNUpper1, hupper⟩ :=
    r1_range_control_upper hBV D0 hvalid0
  have hcSize_pos : 0 < cSize := lt_of_lt_of_le zero_lt_one hcSize
  have hc0IVC : (0 : ℝ) < (1 / 2 - alphaMax) / 2 := by linarith
  obtain ⟨C_V, hC_V, volSlack, hvolSlack, hcalc⟩ :=
    hVC alphaMin ((1 / 2 - alphaMax) / 2) halphaMin_pos hc0IVC
  have halphaMin_lt_one : alphaMin < 1 := by linarith
  have hHamin_pos : 0 < H alphaMin := by
    unfold H; exact Real.binEntropy_pos halphaMin_pos halphaMin_lt_one
  have hCVcSize_pos : 0 < C_V * cSize := mul_pos (by linarith) hcSize_pos
  obtain ⟨N_vs, hN_vs⟩ := hvolSlack.2 (cUpper / 8) (by linarith)
  refine ⟨cUpper / 2, by linarith,
    max (max NUpper N_vs) (max (⌈8 / cUpper⌉₊) 1), le_trans (le_max_right _ _) (le_max_right _ _),
    min (H alphaMin / (2 * cSize)) (cUpper / (4 * (C_V * cSize + 1))),
    lt_min (by positivity) (div_pos hcUpper (by nlinarith [hCVcSize_pos])), ?_⟩
  intro sigma hvalidS n hn hsig r S alpha beta hmem
  have hNUpper : NUpper ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hNvs : N_vs ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hNlin : ⌈8 / cUpper⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := le_trans hNUpper1 hNUpper
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
  rcases hmem with
    ⟨_hvalidD, hbeta, halpha_min, halpha_max, _hradius, hsize, _hnear, hcap⟩
  have halpha_nonneg : 0 ≤ alpha := le_trans halphaMin_pos.le halpha_min
  have halpha_half : alpha ≤ 1 / 2 :=
    le_of_lt (lt_of_le_of_lt halpha_max halphaMax_half)
  have hHalpha_nonneg : 0 ≤ H alpha := by
    unfold H; exact Real.binEntropy_nonneg halpha_nonneg (by linarith)
  have hHamin_le_alpha : H alphaMin ≤ H alpha :=
    H_mono_on_half halphaMin_pos.le halpha_min halpha_half
  have hsig_nn : 0 ≤ sigma n := hvalidS.2.2.2.2.2.2.2.1.1 n
  have hsig_nonempty : sigma n ≤ (H alphaMin / (2 * cSize)) * (n : ℝ) :=
    le_trans hsig (mul_le_mul_of_nonneg_right (min_le_left _ _) hnpos.le)
  have hsig1 : sigma n ≤ (cUpper / (4 * (C_V * cSize + 1))) * (n : ℝ) :=
    le_trans hsig (mul_le_mul_of_nonneg_right (min_le_right _ _) hnpos.le)
  have hS_nonempty : S.Nonempty := by
    have hS_pos_nat : 0 < S.card := by
      by_contra hnot_pos
      have hS0 : S.card = 0 := Nat.eq_zero_of_not_pos hnot_pos
      have hHn_nonneg : 0 ≤ H alpha * (n : ℝ) :=
        mul_nonneg hHalpha_nonneg (Nat.cast_nonneg n)
      have hHn_le : H alpha * (n : ℝ) ≤ cSize * sigma n := by
        rw [sizeHyp, hS0, Nat.cast_zero, Real.log_zero] at hsize
        simpa [abs_of_nonneg hHn_nonneg] using hsize
      have hc_sigma :
          cSize * sigma n ≤ (H alphaMin / 2) * (n : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hsig_nonempty hcSize_pos.le
        have heq :
            cSize * (H alphaMin / (2 * cSize) * (n : ℝ)) =
              (H alphaMin / 2) * (n : ℝ) := by
          field_simp
        simpa [heq] using hmul
      have hHamin_n_le : H alphaMin * (n : ℝ) ≤ H alpha * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hHamin_le_alpha (Nat.cast_nonneg n)
      nlinarith
    exact Finset.card_pos.mp hS_pos_nat
  have hS_not_full : S.card < 2 ^ n := by
    by_contra hnot_lt
    have hpow_le_S : 2 ^ n ≤ S.card := Nat.le_of_not_gt hnot_lt
    have hpow_le_neigh_nat : 2 ^ n ≤ (neighborhood r S).card :=
      le_trans hpow_le_S (Finset.card_le_card (subset_neighborhood_self r S))
    have hpow_le_neigh :
        (((2 ^ n : ℕ) : ℝ) ≤ ((neighborhood r S).card : ℝ)) := by
      exact_mod_cast hpow_le_neigh_nat
    have hpow_exp : ((2 ^ n : ℕ) : ℝ) =
        Real.exp ((n : ℝ) * Real.log 2) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hexp_le :
        Real.exp ((n : ℝ) * Real.log 2) ≤
          Real.exp ((1 - deltaCap) * (n : ℝ) * Real.log 2) := by
      rw [← hpow_exp]
      exact le_trans hpow_le_neigh hcap
    have harg_le := Real.exp_le_exp.mp hexp_le
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hprod_pos : 0 < deltaCap * (n : ℝ) * Real.log 2 :=
      mul_pos (mul_pos hdeltaCap_pos hnpos) hlog2_pos
    nlinarith
  obtain ⟨t, _ht_le, ht_card, htV, ht_strict⟩ :=
    r1_range_control_t_star hVPlus n r S hS_nonempty hS_not_full
  have hball_cap :
      ((ball (∅ : Cube n) (t + r)).card : ℝ) ≤
        Real.exp ((1 - deltaCap) * (n : ℝ) * Real.log 2) := by
    calc ((ball (∅ : Cube n) (t + r)).card : ℝ)
        ≤ (V n S.card r : ℝ) := htV
      _ ≤ ((neighborhood r S).card : ℝ) := V_le_neighborhood_card r S
      _ ≤ Real.exp ((1 - deltaCap) * (n : ℝ) * Real.log 2) := hcap
  have hupper_n := hupper n hNUpper t r hball_cap
  rw [div_le_iff₀ hnpos] at hupper_n
  have hslack_nonneg : 0 ≤ cSize * sigma n :=
    mul_nonneg (le_trans zero_le_one hcSize) hsig_nn
  have hS1 : 1 ≤ S.card := Finset.card_pos.mpr hS_nonempty
  have hScap : S.card ≤ 2 ^ n := hS_not_full.le
  have hrange0 : alpha + (0 : ℝ) ≤ 1 / 2 - (1 / 2 - alphaMax) / 2 := by
    nlinarith [halpha_max, halphaMax_half]
  obtain ⟨_, hrmin⟩ := hcalc n S.card 0 alpha 0 (cSize * sigma n)
    halpha_min halpha_half hslack_nonneg (by simp) hrange0 hS1 hScap hsize
  have hcard_succ : S.card ≤ (ball (∅ : Cube n) (t + 1)).card := by
    have hstrict_nat : S.card < (ball (∅ : Cube n) (t + 1)).card := by
      exact_mod_cast ht_strict
    exact hstrict_nat.le
  have hrmin_le_succ : rmin n S.card ≤ t + 1 := by
    let vals := (Finset.range (n + 1)).filter
      fun rr => S.card ≤ (ball (∅ : Cube n) rr).card
    by_cases ht_le_n : t + 1 ≤ n
    · have hmem : t + 1 ∈ vals := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ht_le_n), hcard_succ⟩
      have hvals : vals.Nonempty := ⟨t + 1, hmem⟩
      unfold rmin
      change (if h : vals.Nonempty then vals.min' h else n) ≤ t + 1
      rw [dif_pos hvals]
      exact vals.min'_le (t + 1) hmem
    · have hn_le_t : n ≤ t + 1 := Nat.le_of_not_ge ht_le_n
      have hrmin_le_n : rmin n S.card ≤ n := by
        unfold rmin
        change (if h : vals.Nonempty then vals.min' h else n) ≤ n
        by_cases hvals : vals.Nonempty
        · rw [dif_pos hvals]
          exact Nat.lt_succ_iff.mp
            (Finset.mem_range.mp (Finset.mem_filter.mp (vals.min'_mem hvals)).1)
        · rw [dif_neg hvals]
      exact le_trans hrmin_le_n hn_le_t
  have hrmin_le_succ_real : (rmin n S.card : ℝ) ≤ (t : ℝ) + 1 := by
    exact_mod_cast hrmin_le_succ
  have ht_lower :
      alpha * (n : ℝ) - (C_V * (cSize * sigma n) + volSlack n) - 1 ≤
        (t : ℝ) := by
    have hlow := (abs_le.mp hrmin).1
    linarith
  have hvs_bound : volSlack n ≤ (cUpper / 8) * (n : ℝ) := hN_vs n hNvs
  have hone_bound : (1 : ℝ) ≤ (cUpper / 8) * (n : ℝ) := by
    have h8 : (8 : ℝ) / cUpper ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hNlin)
    rw [div_le_iff₀ hcUpper] at h8
    nlinarith [h8]
  have hCVsig_bound :
      C_V * (cSize * sigma n) ≤ (cUpper / 4) * (n : ℝ) := by
    have hden_pos : (0 : ℝ) < 4 * (C_V * cSize + 1) := by
      nlinarith [hCVcSize_pos]
    have hmul :
        C_V * (cSize * sigma n) ≤
          (C_V * cSize) *
            ((cUpper / (4 * (C_V * cSize + 1))) * (n : ℝ)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hsig1 hCVcSize_pos.le
    refine le_trans hmul ?_
    rw [show (C_V * cSize) *
            ((cUpper / (4 * (C_V * cSize + 1))) * (n : ℝ))
          = ((C_V * cSize) * cUpper / (4 * (C_V * cSize + 1))) * (n : ℝ)
          by ring]
    apply mul_le_mul_of_nonneg_right _ hnpos.le
    rw [div_le_div_iff₀ hden_pos (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hcUpper, hCVcSize_pos]
  have hr : beta * (n : ℝ) = (r : ℝ) := by
    rw [hbeta, div_mul_cancel₀ _ (ne_of_gt hnpos)]
  have hkey : (alpha + beta) * (n : ℝ) ≤ (1 / 2 - cUpper / 2) * (n : ℝ) := by
    nlinarith [ht_lower, hupper_n, hvs_bound, hone_bound, hCVsig_bound, hr]
  exact le_of_mul_le_mul_right hkey hnpos

end HarperStability
