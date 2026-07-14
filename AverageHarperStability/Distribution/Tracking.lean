import AverageHarperStability.Distribution.CertificateAssembly
import AverageHarperStability.Interface.Statements

open Filter Topology Set

namespace AverageHarperStability

  -- (err_val definitions were moved to Certificate.lean)

theorem eventMass_mono {n : ℕ} {mu : Cube n → ℝ} {E F : Cube n → Prop}
    [DecidablePred E] [DecidablePred F]
    (hmu : IsLaw mu) (hEF : ∀ x, E x → F x) :
    eventMass mu E ≤ eventMass mu F := by
  unfold eventMass
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hE hF
  · rfl
  · exact (hF (hEF x hE)).elim
  · exact hmu.1 x
  · rfl

theorem eventMass_le_one {n : ℕ} {mu : Cube n → ℝ} {E : Cube n → Prop} [DecidablePred E]
    (hmu : IsLaw mu) : eventMass mu E ≤ 1 := by
  unfold eventMass
  rw [← hmu.2]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with h
  · exact le_refl _
  · exact hmu.1 x

theorem hDist_le_dim {n : ℕ} (x y : Cube n) : hDist x y ≤ n := by
  simpa [hDist] using (Finset.card_le_univ (symmDiff x y))

theorem eventMass_hDist_gt_eq_zero {n : ℕ} (mu : Cube n → ℝ) (D : Cube n → Cube n)
    {radius : ℝ} (hradius : (n : ℝ) ≤ radius) :
    eventMass mu (fun x => radius < (hDist x (D x) : ℝ)) = 0 := by
  unfold eventMass
  apply Finset.sum_eq_zero
  intro x _
  apply if_neg
  have hdist : (hDist x (D x) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hDist_le_dim x (D x)
  linarith

theorem eventMass_markov {n : ℕ} {mu : Cube n → ℝ} {Z : Cube n → ℝ}
    {t a : ℝ} [DecidablePred fun x => t ≤ Z x]
    (hmu : IsLaw mu) (hZ : ∀ x, 0 ≤ Z x) (ht : 0 < t)
    (hEZ : ∑ x, mu x * Z x ≤ a) :
    eventMass mu (fun x => t ≤ Z x) ≤ a / t := by
  have H : eventMass mu (fun x => t ≤ Z x) * t ≤ ∑ x, mu x * Z x := by
    unfold eventMass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    split_ifs with h
    · have h1 := mul_le_mul_of_nonneg_right h (hmu.1 x)
      rw [mul_comm (Z x), mul_comm t] at h1
      exact h1
    · rw [zero_mul]
      exact mul_nonneg (hmu.1 x) (hZ x)
  calc
    eventMass mu (fun x => t ≤ Z x) ≤ (∑ x, mu x * Z x) / t := (le_div_iff₀ ht).mpr H
    _ ≤ a / t := div_le_div_of_nonneg_right hEZ (le_of_lt ht)

/-- Exponential Markov inequality for the finite mass-function model. -/
theorem eventMass_exp_markov {n : ℕ} {mu : Cube n → ℝ} {Z : Cube n → ℝ}
    {t lambda : ℝ} [DecidablePred fun x => t ≤ Z x]
    (hmu : IsLaw mu) (hlambda : 0 < lambda) :
    eventMass mu (fun x => t ≤ Z x) ≤
      Real.exp (-lambda * t) * ∑ x, mu x * Real.exp (lambda * Z x) := by
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · have hexp : 1 ≤ Real.exp (lambda * (Z x - t)) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      mu x = mu x * 1 := by ring
      _ ≤ mu x * Real.exp (lambda * (Z x - t)) :=
        mul_le_mul_of_nonneg_left hexp (hmu.1 x)
      _ = Real.exp (-lambda * t) * (mu x * Real.exp (lambda * Z x)) := by
        rw [show lambda * (Z x - t) = -lambda * t + lambda * Z x by ring,
          Real.exp_add]
        ring
  · exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hmu.1 x) (Real.exp_nonneg _))

/-- Max-entropy bound: the entropy of any law on the `n`-cube is at most `n log 2`
(the cube has `2 ^ n` points; equality for the uniform law). Proved by Jensen's
inequality for the concave `negMulLog` with uniform weights `1 / 2 ^ n`. -/
theorem entropy_le_card_log {n : ℕ} {mu : Cube n → ℝ} (hmu : IsLaw mu) :
    entropy mu ≤ (n : ℝ) * Real.log 2 := by
  classical
  have hcard : (Finset.univ : Finset (Cube n)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  set N : ℝ := (2 : ℝ) ^ n with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  -- Jensen with uniform weights `1 / N`.
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset (Cube n)))
    (w := fun _ => (1 / N))
    (p := mu)
    (fun i _ => by positivity)
    (by
      rw [Finset.sum_const, hcard, nsmul_eq_mul, hN]
      push_cast
      rw [mul_one_div, div_self (by positivity)])
    (fun i _ => hmu.1 i)
  simp only [smul_eq_mul] at hjensen
  have hlhs : (∑ i : Cube n, (1 / N) * Real.negMulLog (mu i)) = (1 / N) * entropy mu := by
    unfold entropy
    rw [Finset.mul_sum]
  have hrhs : (∑ i : Cube n, (1 / N) * mu i) = 1 / N := by
    rw [← Finset.mul_sum, hmu.2, mul_one]
  rw [hlhs, hrhs] at hjensen
  have hlog : Real.negMulLog (1 / N) = (1 / N) * Real.log N := by
    rw [Real.negMulLog, one_div, Real.log_inv]; ring
  rw [hlog] at hjensen
  have hcancel : entropy mu ≤ Real.log N :=
    le_of_mul_le_mul_left hjensen (by positivity)
  rw [hN, Real.log_pow] at hcancel
  exact hcancel

/-- The identity label map leaves the mass untouched. -/
theorem mapMass_id {n : ℕ} (mu : Cube n → ℝ) : mapMass mu id = mu := by
  funext d
  simp only [mapMass, id_eq]
  rw [Finset.sum_ite_eq' Finset.univ d mu]
  simp

/-- The pushforward label distribution is again a law. -/
theorem mapMass_isLaw {n : ℕ} {mu : Cube n → ℝ} (D : Cube n → Cube n) (hmu : IsLaw mu) :
    IsLaw (mapMass mu D) := by
  refine ⟨?_, ?_⟩
  · intro d
    apply Finset.sum_nonneg
    intro x _
    split_ifs with h
    · exact hmu.1 x
    · exact le_refl 0
  · unfold mapMass
    rw [Finset.sum_comm]
    have h1 : ∀ x : Cube n, (∑ d : Cube n, if D x = d then mu x else 0) = mu x := by
      intro x; simp
    simp only [h1]
    exact hmu.2

/-- Entropy of a law is nonnegative (every mass lies in `[0,1]`). -/
theorem entropy_nonneg {n : ℕ} {mu : Cube n → ℝ} (hmu : IsLaw mu) : 0 ≤ entropy mu := by
  unfold entropy
  apply Finset.sum_nonneg
  intro x _
  apply Real.negMulLog_nonneg (hmu.1 x)
  have hle : mu x ≤ ∑ y, mu y := Finset.single_le_sum (fun y _ => hmu.1 y) (Finset.mem_univ x)
  rw [hmu.2] at hle
  exact hle

/-- A constant deterministic label has zero entropy. -/
theorem entropy_mapMass_const {n : ℕ} {mu : Cube n → ℝ} (c : Cube n)
    (hmu : IsLaw mu) : entropy (mapMass mu fun _ => c) = 0 := by
  unfold entropy mapMass
  apply Finset.sum_eq_zero
  intro d _
  by_cases hcd : c = d
  · simp only [hcd, ↓reduceIte, hmu.2, Real.negMulLog_one]
  · simp only [hcd, ↓reduceIte, Finset.sum_const_zero, Real.negMulLog_zero]

theorem label_concentration {n : ℕ} {mu : Cube n → ℝ} (D : Cube n → Cube n)
    (hmu : IsLaw mu) {K : ℝ} (hK : 0 < K) (hn : 1 ≤ n) :
    eventMass (mapMass mu D) (fun d => mapMass mu D d < Real.exp (-(K * n))) ≤
      entropy (mapMass mu D) / (K * (n : ℝ)) := by
  set nu := mapMass mu D
  have hnu_law : IsLaw nu := mapMass_isLaw D hmu
  have H : eventMass nu (fun d => nu d < Real.exp (-(K * n))) * (K * (n : ℝ)) ≤ entropy nu := by
    unfold eventMass entropy
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d _
    split_ifs with h
    · have hnu_nonneg := hnu_law.1 d
      rcases eq_or_lt_of_le hnu_nonneg with h0 | hp
      · rw [← h0, Real.negMulLog_zero]
        simp
      · have hlog : Real.log (nu d) < -(K * (n : ℝ)) := by
          rwa [← Real.log_exp (-(K * n)), Real.log_lt_log_iff hp (Real.exp_pos _)]
        have h1 : nu d * Real.log (nu d) ≤ nu d * -(K * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_of_lt hlog) (le_of_lt hp)
        have h2 : nu d * (K * (n : ℝ)) ≤ -nu d * Real.log (nu d) := by linarith
        unfold Real.negMulLog
        exact h2
    · have hle : nu d ≤ ∑ y, nu y := Finset.single_le_sum (fun y _ => hnu_law.1 y) (Finset.mem_univ d)
      rw [hnu_law.2] at hle
      have h3 : 0 ≤ Real.negMulLog (nu d) := Real.negMulLog_nonneg (hnu_law.1 d) hle
      calc
        0 * (K * ↑n) = 0 := MulZeroClass.zero_mul _
        _ ≤ Real.negMulLog (nu d) := h3
  have hpos : 0 < K * (n : ℝ) := mul_pos hK (by positivity)
  calc
    eventMass nu (fun d => nu d < Real.exp (-(K * n))) ≤ entropy nu / (K * (n : ℝ)) :=
      (le_div_iff₀ hpos).mpr H

theorem negMulLog_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.negMulLog (f i) := by
  set S := ∑ i ∈ s, f i
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg hf
  rcases eq_or_lt_of_le hS_nonneg with hS | hS
  · have hz : ∀ i ∈ s, f i = 0 := by
      intro i hi
      have h1 : 0 ≤ f i := hf i hi
      have h2 : f i ≤ S := Finset.single_le_sum hf hi
      have hS' : S = 0 := hS.symm
      rw [hS'] at h2
      exact le_antisymm h2 h1
    have hs1 : Real.negMulLog S = 0 := by
      have hS' : S = 0 := hS.symm
      rw [hS', Real.negMulLog_zero]
    have hs2 : ∑ i ∈ s, Real.negMulLog (f i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hz i hi, Real.negMulLog_zero]
    rw [hs1, hs2]
  · have h_le : ∀ i ∈ s, f i * Real.log (f i) ≤ f i * Real.log S := by
      intro i hi
      rcases eq_or_lt_of_le (hf i hi) with hfi | hfi
      · rw [← hfi]; simp
      · have h_le_S : f i ≤ S := Finset.single_le_sum hf hi
        have h_log_le : Real.log (f i) ≤ Real.log S := Real.log_le_log hfi h_le_S
        exact mul_le_mul_of_nonneg_left h_log_le (le_of_lt hfi)
    have H1 : ∑ i ∈ s, f i * Real.log (f i) ≤ ∑ i ∈ s, f i * Real.log S :=
      Finset.sum_le_sum h_le
    have H2 : ∑ i ∈ s, f i * Real.log S = S * Real.log S := by rw [← Finset.sum_mul]
    rw [H2] at H1
    have H3 : -(S * Real.log S) ≤ - ∑ i ∈ s, f i * Real.log (f i) := neg_le_neg H1
    have H4 : ∑ i ∈ s, Real.negMulLog (f i) = - ∑ i ∈ s, f i * Real.log (f i) := by
      unfold Real.negMulLog
      have eq1 : (∑ i ∈ s, -f i * Real.log (f i)) = ∑ i ∈ s, -(f i * Real.log (f i)) := by
        apply Finset.sum_congr rfl; intro x _
        simp only [neg_mul]
      rw [eq1, Finset.sum_neg_distrib]
    rw [← H4] at H3
    have h_lhs : -(S * Real.log S) = Real.negMulLog S := by
      unfold Real.negMulLog
      simp only [neg_mul]
    rw [h_lhs] at H3
    exact H3

theorem entropy_mapMass_le {n : ℕ} {mu : Cube n → ℝ} (D : Cube n → Cube n)
    (hmu : IsLaw mu) : entropy (mapMass mu D) ≤ entropy mu := by
  unfold entropy mapMass
  have H : ∀ d, Real.negMulLog (∑ x : Cube n, if D x = d then mu x else 0) ≤
    ∑ x : Cube n, if D x = d then Real.negMulLog (mu x) else 0 := by
    intro d
    have h_nonneg : ∀ x ∈ Finset.univ, 0 ≤ if D x = d then mu x else 0 := by
      intro x _
      split_ifs
      · exact hmu.1 x
      · rfl
    have h1 := negMulLog_sum_le Finset.univ (fun x => if D x = d then mu x else 0) h_nonneg
    have h2 : (∑ x : Cube n, Real.negMulLog (if D x = d then mu x else 0)) =
      ∑ x : Cube n, if D x = d then Real.negMulLog (mu x) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs
      · rfl
      · rw [Real.negMulLog_zero]
    rw [h2] at h1
    exact h1
  have H_sum := Finset.sum_le_sum (s := Finset.univ) (fun d _ => H d)
  have H_swap : (∑ d : Cube n, ∑ x : Cube n, if D x = d then Real.negMulLog (mu x) else 0) =
    ∑ x : Cube n, Real.negMulLog (mu x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp
  rw [H_swap] at H_sum
  exact H_sum



/-
Maximum-entropy bound: a law whose mean Hamming weight is at most `m·n`
(with `m ≤ 1/2`) has entropy at most `n·Hb m`.
-/
theorem entropy_le_of_mean_card
    {n : ℕ} {nu : Cube n → ℝ} (hnu : IsLaw nu)
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1 / 2)
    (hmean : ∑ x, nu x * (x.card : ℝ) ≤ m * n) :
    entropy nu ≤ (n : ℝ) * Hb m := by
  by_cases hm : m = 0;
  · -- Since $\sum x, nu x * x.card \leq 0$ and $nu x \geq 0$, it follows that $nu x = 0$ for all $x$ with $x.card > 0$.
    have h_zero : ∀ x, x ≠ ∅ → nu x = 0 := by
      intro x hx_ne; contrapose! hmean; simp_all +decide [ IsLaw ] ;
      exact lt_of_lt_of_le ( mul_pos ( lt_of_le_of_ne ( hnu.1 x ) ( Ne.symm hmean ) ) ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hx_ne ) ) ) ) ( Finset.single_le_sum ( fun a _ => mul_nonneg ( hnu.1 a ) ( Nat.cast_nonneg ( Finset.card a ) ) ) ( Finset.mem_univ x ) );
    unfold entropy Hb; simp_all +decide [ Finset.sum_eq_single ∅ ] ;
    have := hnu.2; rw [ Finset.sum_eq_single ∅ ] at this <;> aesop;
  · -- Apply Gibbs' inequality with the reference measure $q(x) = m^{x.card} * (1-m)^{n-x.card}$.
    have h_gibbs : ∑ x, nu x * Real.log (m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card)) ≤ ∑ x, nu x * Real.log (nu x) := by
      have h_gibbs : ∀ x, nu x > 0 → nu x * Real.log (m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card)) ≤ nu x * Real.log (nu x) + (m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card)) - nu x := by
        intros x hx_pos
        have h_gibbs_step : Real.log (m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card)) ≤ Real.log (nu x) + (m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card)) / nu x - 1 := by
          have := Real.log_le_sub_one_of_pos ( show 0 < ( m ^ ( x.card : ℝ ) * ( 1 - m ) ^ ( n - x.card : ℝ ) ) / nu x from div_pos ( mul_pos ( Real.rpow_pos_of_pos ( lt_of_le_of_ne hm0 ( Ne.symm hm ) ) _ ) ( Real.rpow_pos_of_pos ( sub_pos.mpr ( lt_of_le_of_lt hm1 ( by norm_num ) ) ) _ ) ) hx_pos );
          rw [ Real.log_div ( mul_ne_zero ( ne_of_gt ( Real.rpow_pos_of_pos ( lt_of_le_of_ne hm0 ( Ne.symm hm ) ) _ ) ) ( ne_of_gt ( Real.rpow_pos_of_pos ( sub_pos.mpr ( lt_of_le_of_lt hm1 ( by norm_num ) ) ) _ ) ) ) hx_pos.ne' ] at this ; linarith;
        nlinarith [ mul_div_cancel₀ ( m ^ ( x.card : ℝ ) * ( 1 - m ) ^ ( n - x.card : ℝ ) ) hx_pos.ne' ];
      have h_sum_gibbs : ∑ x, nu x * Real.log (m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card)) ≤ ∑ x, (nu x * Real.log (nu x) + (m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card)) - nu x) := by
        apply Finset.sum_le_sum;
        intro x hx; by_cases hx' : nu x = 0 <;> simp_all +decide [ IsLaw ] ;
        · exact mul_nonneg ( pow_nonneg hm0 _ ) ( Real.rpow_nonneg ( sub_nonneg.2 <| hm1.trans <| by norm_num ) _ );
        · grind;
      have h_sum_q : ∑ x : Cube n, m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card) = 1 := by
        have h_sum_q : ∑ x : Finset (Fin n), m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card) = (∑ x : Finset (Fin n), m ^ x.card * (1 - m) ^ (n - x.card)) := by
          exact Finset.sum_congr rfl fun x hx => by rw [ ← Nat.cast_sub ( show x.card ≤ n from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; norm_cast;
        have h_sum_q : ∑ x : Finset (Fin n), m ^ x.card * (1 - m) ^ (n - x.card) = (m + (1 - m)) ^ n := by
          exact?;
        aesop;
      simp_all +decide [ Finset.sum_add_distrib, Finset.sum_sub_distrib ];
      linarith [ hnu.2 ];
    -- Simplify the sum $\sum x, nu x * \log(m^{x.card} * (1-m)^{n-x.card})$.
    have h_simplify : ∑ x, nu x * Real.log (m ^ (x.card : ℝ) * (1 - m) ^ ((n : ℝ) - x.card)) = (∑ x, nu x * (x.card : ℝ)) * Real.log m + (n - ∑ x, nu x * (x.card : ℝ)) * Real.log (1 - m) := by
      rw [ Finset.sum_congr rfl fun x hx => by rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( by linarith ) _ ) ), Real.log_rpow ( by positivity ), Real.log_rpow ( by linarith ) ] ];
      simp +decide [ mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, hnu.2 ];
      simp +decide [ sub_mul, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hnu.2 ];
    unfold entropy Hb;
    unfold Real.binEntropy;
    simp_all +decide [ Real.negMulLog ];
    nlinarith [ Real.log_le_sub_one_of_pos ( show 0 < m by positivity ), Real.log_le_log ( by linarith [ show 0 < m by positivity ] ) ( show 1 - m ≥ m by norm_num at *; linarith ) ]

/-
The scalar Hoeffding log-mgf bound: for `p ∈ [0,1]` the Bernoulli log-mgf
centred at its mean is dominated by `t²/8`.  This is the analytic core of
Hoeffding's lemma.
-/
theorem hoeffding_logmgf_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    -p * t + Real.log (1 - p + p * Real.exp t) ≤ t ^ 2 / 8 := by
  -- Consider the function $g(t) = L(t) - t^2/8$ and show that it is concave.
  set g : ℝ → ℝ := fun t => -p * t + Real.log (1 - p + p * Real.exp t) - t^2 / 8
  have hg_concave : ConcaveOn ℝ Set.univ g := by
    apply_rules [ concaveOn_of_deriv2_nonpos, convex_univ ];
    · refine' ContinuousOn.sub ( ContinuousOn.add ( continuousOn_const.mul continuousOn_id ) ( ContinuousOn.log ( continuousOn_const.add ( continuousOn_const.mul ( Real.continuousOn_exp ) ) ) _ ) ) ( continuousOn_id.pow 2 |> ContinuousOn.div_const <| 8 );
      exact fun x _ => by cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos x ] ;
    · apply_rules [ DifferentiableOn.sub, DifferentiableOn.add, DifferentiableOn.mul, differentiableOn_id, differentiableOn_const, DifferentiableOn.log ];
      · exact Differentiable.differentiableOn Real.differentiable_exp;
      · exact fun x _ => by cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos x ] ;
    · refine' DifferentiableOn.congr _ _;
      use fun t => -p + p * Real.exp t / (1 - p + p * Real.exp t) - t / 4;
      · refine' DifferentiableOn.sub _ _ <;> norm_num [ Real.differentiable_exp, mul_comm p ];
        · exact DifferentiableOn.div ( DifferentiableOn.mul ( Real.differentiable_exp.differentiableOn ) ( differentiableOn_const _ ) ) ( DifferentiableOn.add ( differentiableOn_const _ ) ( DifferentiableOn.mul ( Real.differentiable_exp.differentiableOn ) ( differentiableOn_const _ ) ) ) fun x hx => by cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos x ] ;
        · exact differentiableOn_id.div_const _;
      · intro x hx; norm_num [ g, Real.differentiableAt_exp, mul_comm p, show ( 1 - p + p * Real.exp x ) ≠ 0 from by cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos x ] ] ; ring;
        norm_num [ Real.differentiableAt_exp, show ( 1 - p + p * Real.exp x ) ≠ 0 from by cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos x ] ] ; ring;
    · -- Let's calculate the second derivative of $g(t)$.
      have hg'' : ∀ t, deriv^[2] g t = (p * (1 - p) * Real.exp t) / (1 - p + p * Real.exp t)^2 - 1 / 4 := by
        have hg'' : ∀ t, deriv^[2] g t = deriv (fun t => -p + (p * Real.exp t) / (1 - p + p * Real.exp t) - t / 4) t := by
          intro t; refine' Filter.EventuallyEq.deriv_eq _ ; filter_upwards [ ] with t ; norm_num [ Real.differentiableAt_exp, mul_comm p, ne_of_gt ( show 0 < 1 - p + p * Real.exp t from by cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos t ] ) ] ; ring;
          convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.add ( HasDerivAt.const_mul ( -p ) ( hasDerivAt_id t ) ) ( HasDerivAt.log ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_exp t ) ) ) _ ) ) ( HasDerivAt.div_const ( hasDerivAt_pow 2 t ) _ ) ) using 1 <;> norm_num ; ring;
          cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos t ];
        intro t; rw [ hg'' ] ; norm_num [ Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - p + p * Real.exp t from by cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos t ] ) ] ; ring;
      intro t ht; rw [ hg'' t ] ; rw [ sub_nonpos ] ; rw [ div_le_iff₀ ] <;> norm_num;
      · nlinarith [ sq_nonneg ( 1 - p - p * Real.exp t ), Real.exp_pos t ];
      · exact sq_pos_of_pos ( by cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos t ] );
  -- Since $g$ is concave, we have $g(t) \leq g(0) + g'(0)t$ for all $t$.
  have hg_le : ∀ t, g t ≤ g 0 + deriv g 0 * t := by
    have hg_le : ∀ t, g t ≤ g 0 + deriv g 0 * t := by
      intro t
      have h_deriv : ∀ t, HasDerivAt g (deriv g t) t := by
        intro t; exact hasDerivAt_deriv_iff.mpr (by
        apply_rules [ DifferentiableAt.sub, DifferentiableAt.add, DifferentiableAt.mul, DifferentiableAt.log, differentiableAt_id, differentiableAt_const ];
        · exact Real.differentiableAt_exp;
        · cases lt_or_eq_of_le hp0 <;> cases lt_or_eq_of_le hp1 <;> nlinarith [ Real.exp_pos t ])
      have := hg_concave.2 ( Set.mem_univ 0 ) ( Set.mem_univ t );
      -- Apply the definition of concavity.
      have h_concave_def : ∀ h ∈ Set.Ioo 0 1, g (h * t) ≥ (1 - h) * g 0 + h * g t := by
        intro h hh; specialize this ( show 0 ≤ 1 - h by linarith [ hh.1, hh.2 ] ) ( show 0 ≤ h by linarith [ hh.1, hh.2 ] ) ( by linarith [ hh.1, hh.2 ] ) ; aesop;
      -- Apply the definition of the derivative to get the inequality.
      have h_deriv_ineq : Filter.Tendsto (fun h => (g (h * t) - g 0) / h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv g 0 * t)) := by
        have h_deriv_ineq : HasDerivAt (fun h => g (h * t)) (deriv g 0 * t) 0 := by
          convert HasDerivAt.comp 0 ( h_deriv _ ) ( hasDerivAt_mul_const t ) using 1 ; norm_num;
        simpa [ div_eq_inv_mul ] using h_deriv_ineq.tendsto_slope_zero_right;
      have h_deriv_ineq : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), (g (h * t) - g 0) / h ≥ g t - g 0 := by
        filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with h hh using by rw [ ge_iff_le ] ; rw [ le_div_iff₀ hh.1 ] ; linarith [ h_concave_def h hh ] ;
      have := le_of_tendsto_of_tendsto tendsto_const_nhds ‹_› h_deriv_ineq; norm_num at *; linarith;
    exact hg_le;
  simp +zetaDelta at *;
  norm_num [ Real.differentiableAt_exp, mul_comm p ] at *;
  linarith [ hg_le t ]

/-
Finite Hoeffding step: the weighted exponential moment of a mean-zero
bounded family is controlled by `exp (λ²(b-a)²/8)`.
-/
theorem finite_hoeffding_step
    {ι : Type*} (s : Finset ι) (w Y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hwsum : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * Y i = 0)
    {a b lambda : ℝ}
    (hY : ∀ i ∈ s, Y i ∈ Set.Icc a b) :
    ∑ i ∈ s, w i * Real.exp (lambda * Y i) ≤
      Real.exp (lambda^2 * (b - a)^2 / 8) := by
  by_cases h : b ≤ a;
  · simp_all +decide [ le_antisymm h ( by linarith [ Set.mem_Icc.mp ( hY _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by aesop_cat : s ≠ ∅ ) ) ) ) ] ) ];
    simp_all +decide [ ← Finset.sum_mul _ _ _ ];
  · -- Apply Jensen's inequality to the exponential function.
    have h_jensen : ∑ i ∈ s, w i * Real.exp (lambda * Y i) ≤ ∑ i ∈ s, w i * ((b - Y i) / (b - a)) * Real.exp (lambda * a) + ∑ i ∈ s, w i * ((Y i - a) / (b - a)) * Real.exp (lambda * b) := by
      have h_jensen : ∀ i ∈ s, Real.exp (lambda * Y i) ≤ ((b - Y i) / (b - a)) * Real.exp (lambda * a) + ((Y i - a) / (b - a)) * Real.exp (lambda * b) := by
        have h_convex : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
          exact convexOn_exp;
        intro i hi; have := h_convex.2 ( Set.mem_univ ( lambda * a ) ) ( Set.mem_univ ( lambda * b ) ) ; simp_all +decide [ div_eq_inv_mul ] ;
        convert @this ( ( b - Y i ) / ( b - a ) ) ( ( Y i - a ) / ( b - a ) ) ( div_nonneg ( by linarith [ hY i hi ] ) ( by linarith [ hY i hi ] ) ) ( div_nonneg ( by linarith [ hY i hi ] ) ( by linarith [ hY i hi ] ) ) ( by rw [ ← add_div, div_eq_iff ] <;> linarith [ hY i hi ] ) using 1 ; ring;
        · grind;
        · ring;
      simpa only [ mul_assoc, mul_add, Finset.sum_add_distrib ] using Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( h_jensen i hi ) ( hw i hi );
    -- Simplify the expression using the fact that $\sum_{i \in s} w_i = 1$ and $\sum_{i \in s} w_i Y_i = 0$.
    have h_simplify : ∑ i ∈ s, w i * ((b - Y i) / (b - a)) * Real.exp (lambda * a) + ∑ i ∈ s, w i * ((Y i - a) / (b - a)) * Real.exp (lambda * b) = (b / (b - a)) * Real.exp (lambda * a) - (a / (b - a)) * Real.exp (lambda * b) := by
      simp +decide [ ← Finset.sum_mul _ _ _, ← Finset.mul_sum, ← Finset.sum_div, hwsum, hmean, sub_mul, mul_sub, div_eq_mul_inv ];
      simp +decide [ ← mul_assoc, ← Finset.sum_mul, hmean ];
      ring;
    -- Apply the scalar bound from `hoeffding_logmgf_bound`.
    have h_scalar_bound : (b / (b - a)) * Real.exp (lambda * a) - (a / (b - a)) * Real.exp (lambda * b) ≤ Real.exp (lambda ^ 2 * (b - a) ^ 2 / 8) := by
      have hp : 0 ≤ -a / (b - a) ∧ -a / (b - a) ≤ 1 := by
        have h_bounds : a ≤ 0 ∧ 0 ≤ b := by
          have h_bounds : ∑ i ∈ s, w i * Y i ≥ ∑ i ∈ s, w i * a ∧ ∑ i ∈ s, w i * Y i ≤ ∑ i ∈ s, w i * b := by
            exact ⟨ Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( hY i hi |>.1 ) ( hw i hi ), Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( hY i hi |>.2 ) ( hw i hi ) ⟩;
          simp_all +decide [ ← Finset.sum_mul _ _ _ ];
        exact ⟨ div_nonneg ( by linarith ) ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ) ⟩
      have := hoeffding_logmgf_bound hp.1 hp.2 ( lambda * ( b - a ) );
      rw [ show b / ( b - a ) = 1 - ( -a / ( b - a ) ) by rw [ one_sub_div ( by linarith ) ] ; ring, show a / ( b - a ) = - ( -a / ( b - a ) ) by rw [ neg_div' ] ; ring ] ; ring_nf at *;
      convert Real.exp_le_exp.mpr this using 1;
      rw [ Real.exp_add, Real.exp_log ];
      · rw [ show a * b * ( -a + b ) ⁻¹ *lambda - a ^ 2 * ( -a + b ) ⁻¹ *lambda = a *lambda by nlinarith [ mul_inv_cancel_left₀ ( by linarith : ( -a + b ) ≠ 0 ) ( a *lambda ) ] ] ; ring;
        simpa only [ mul_assoc, ← Real.exp_add ] using by ring;
      · by_cases ha : a = 0;
        · simp [ha];
        · cases lt_or_gt_of_ne ha <;> nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( -a + b ) ≠ 0 ) a, Real.exp_pos ( - ( a * lambda ) + b * lambda ) ];
    linarith

theorem distribution_stability_core {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) (n : ℕ) (mu : Cube n → ℝ) (delta : ℝ)
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta) (hd1 : delta ≤ delta0_val tau zeta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤ (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ)) :
    distributionStabilityConclusion (err_val tau zeta delta) mu := by
  -- Split on whether the (worker-chosen) error budget already dominates the
  -- maximal possible entropy `n log 2`.  If it does, the identity label map is a
  -- valid witness: its pushforward is `mu` itself (entropy `≤ n log 2 ≤ err n`),
  -- and every point sits at distance `0` from its label so the far-mass is `0`.
  -- This discharges the whole large-`delta` end of the range; the genuine L0-L9 +
  -- Azuma argument is only needed once `err < log 2`.
  by_cases hbig : Real.log 2 ≤ err_val tau zeta delta
  · refine ⟨id, ?_, ?_⟩
    · rw [mapMass_id]
      calc entropy mu ≤ (n : ℝ) * Real.log 2 := entropy_le_card_log hmu
        _ ≤ (n : ℝ) * err_val tau zeta delta :=
            mul_le_mul_of_nonneg_left hbig (by positivity)
        _ = err_val tau zeta delta * (n : ℝ) := by ring
    · have hpos : (0 : ℝ) ≤
          (hbInv (entropyRate n mu) + err_val tau zeta delta +
            Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ) := by
        have h1 : (0 : ℝ) ≤ hbInv (entropyRate n mu) := le_trans (le_of_lt hz0) hzeta1
        have h2 : (0 : ℝ) < err_val tau zeta delta := err_val_pos ht0 ht1 hz0 hz1 hd0
        have h3 : (0 : ℝ) ≤ Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ)) := Real.sqrt_nonneg _
        apply mul_nonneg _ (by positivity)
        linarith
      have hzero : eventMass mu (fun x =>
          (hbInv (entropyRate n mu) + err_val tau zeta delta +
            Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ) <
            (hDist x (id x) : ℝ)) = 0 := by
        unfold eventMass
        apply Finset.sum_eq_zero
        intro x _
        have hdxx : (hDist x (id x) : ℝ) = 0 := by
          simp only [id_eq]
          have hxx : hDist x x = 0 := by simp [hDist, symmDiff_self]
          rw [hxx]; simp
        have hfalse : ¬ ((hbInv (entropyRate n mu) + err_val tau zeta delta +
            Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ) <
            (hDist x (id x) : ℝ)) := by
          rw [hdxx]; linarith
        exact if_neg hfalse
      rw [hzero]
      have h2 : (0 : ℝ) < err_val tau zeta delta := err_val_pos ht0 ht1 hz0 hz1 hd0
      have h5 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith
  · -- Genuine hard case: `err_val tau zeta delta < log 2` (small `delta`).
    push_neg at hbig
    by_cases htail : 1 ≤ err_val tau zeta delta + 1 / (n : ℝ)
    · -- If the permitted exceptional mass is already at least one, a constant
      -- label suffices: its entropy is zero and every event has mass at most one.
      refine ⟨fun _ => (∅ : Cube n), ?_, ?_⟩
      · rw [entropy_mapMass_const (∅ : Cube n) hmu]
        exact mul_nonneg (le_of_lt (err_val_pos ht0 ht1 hz0 hz1 hd0)) (by positivity)
      · exact (eventMass_le_one hmu).trans htail
    · -- A radius at least the diameter of the cube also makes a constant label
      -- sufficient, independently of the exceptional-mass budget.
      push_neg at htail
      by_cases hradius : (n : ℝ) ≤
          (hbInv (entropyRate n mu) + err_val tau zeta delta +
            Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ)
      · refine ⟨fun _ => (∅ : Cube n), ?_, ?_⟩
        · rw [entropy_mapMass_const (∅ : Cube n) hmu]
          exact mul_nonneg (le_of_lt (err_val_pos ht0 ht1 hz0 hz1 hd0)) (by positivity)
        · rw [eventMass_hDist_gt_eq_zero mu (fun _ => (∅ : Cube n)) hradius]
          have herr : 0 < err_val tau zeta delta := err_val_pos ht0 ht1 hz0 hz1 hd0
          have hninv : 0 ≤ 1 / (n : ℝ) := by positivity
          linarith
      · -- Genuine hard case: small error, nontrivial tail budget, and radius
        -- below the cube diameter.  This is the full L0--L9 tracking plus the
        -- corrected Azuma/Markov argument.
        push_neg at hradius
        have herr : 0 < err_val tau zeta delta :=
          err_val_pos ht0 ht1 hz0 hz1 hd0
        rcases near_mgl_to_tracking_certificate ht0 ht1 hz0 hz1 hn hmu hd0
            hzeta1 hzeta2 h_ent herr hbig le_rfl with ⟨C⟩
        have hAzuma := tracking_certificate_azuma hn hmu C
        exact tracking_certificate_to_conclusion hn hmu herr C hAzuma

end AverageHarperStability
