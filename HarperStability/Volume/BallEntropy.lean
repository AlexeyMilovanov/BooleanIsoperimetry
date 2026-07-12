import HarperStability.Interface

/-!
# Binomial-prefix entropy sandwich for Hamming balls

This file contains the pure real/combinatorial estimates used to prove
`BallVolumeTwoSidedStatement`.  The key object is the (unnormalized) binomial
term `binTerm p n i = C(n,i) · p^i · (1-p)^(n-i)`.  The Bernoulli-mode argument
gives, for `p = t/n`, that the term at `i = t` is the maximum and hence at
least `1/(n+1)` of the total mass `1`; combined with the exponential form of
the binary entropy this yields the two-sided entropy bounds on the ball volume
`∑_{i≤t} C(n,i)`.
-/

namespace HarperStability

open Finset

attribute [local instance] Classical.propDecidable

/-- Unnormalized binomial term `C(n,i) · p^i · (1-p)^(n-i)` (natural powers). -/
noncomputable def binTerm (p : ℝ) (n i : ℕ) : ℝ :=
  (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

/-
Each binomial term is nonnegative on `[0,1]`.
-/
lemma binTerm_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n i : ℕ) :
    0 ≤ binTerm p n i := by
  exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp0 _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) _ )

/-
The binomial terms sum to `1` (binomial theorem with `p + (1-p) = 1`).
-/
lemma binTerm_sum (p : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), binTerm p n i = 1 := by
  unfold binTerm;
  have := add_pow p ( 1 - p ) n;
  simpa [ mul_assoc, mul_comm, mul_left_comm ] using this.symm

/-
With `p = t/n`, the term at the mode `i = t` dominates every other term.
-/
lemma binTerm_le_mode {n t : ℕ} (hn : 1 ≤ n) (ht : t ≤ n) (i : ℕ) :
    binTerm ((t : ℝ) / n) n i ≤ binTerm ((t : ℝ) / n) n t := by
  have h_r_decreasing : ∀ i ≥ t, binTerm ((t : ℝ) / n) n (i + 1) ≤ binTerm ((t : ℝ) / n) n i ∨ i = n := by
    intro i hi;
    by_cases hi' : i < n <;> simp_all +decide [ binTerm ];
    · -- By simplifying, we can see that the inequality holds.
      have h_simp : (n.choose (i + 1) : ℝ) * (t : ℝ) ≤ (n.choose i : ℝ) * (n - t) := by
        norm_cast;
        nlinarith [ Nat.add_one_mul_choose_eq n i, Nat.choose_succ_succ n i, Nat.sub_add_cancel ht ];
      field_simp;
      rw [ show n - i = n - ( i + 1 ) + 1 by omega ] ; ring_nf at *;
      exact Or.inl ( by nlinarith [ show 0 ≤ ( t : ℝ ) ^ i * ( n : ℝ ) ⁻¹ * ( n : ℝ ) ⁻¹ ^ i * ( - ( t * ( n : ℝ ) ⁻¹ ) + n * ( n : ℝ ) ⁻¹ ) ^ ( n - ( 1 + i ) ) by exact mul_nonneg ( mul_nonneg ( mul_nonneg ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ) ( pow_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) _ ) ) ( pow_nonneg ( by nlinarith [ show ( t : ℝ ) ≤ n by norm_cast, show ( i : ℝ ) < n by norm_cast, mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ) ] ) _ ) ] );
    · cases hi'.eq_or_lt <;> simp_all +decide [ Nat.choose_eq_zero_of_lt ];
  by_cases hi : t ≤ i;
  · induction' hi with i hi ih <;> norm_num at *;
    cases h_r_decreasing i hi <;> simp_all +decide [ binTerm ];
    · lia;
    · exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by positivity ) _ ) ) ( pow_nonneg ( sub_nonneg.2 <| div_le_one_of_le₀ ( by norm_cast ) <| by positivity ) _ );
  · have h_r_increasing : ∀ i < t, binTerm ((t : ℝ) / n) n i ≤ binTerm ((t : ℝ) / n) n (i + 1) := by
      intro i hi
      have h_r_increasing_step : (n.choose i : ℝ) * (1 - (t : ℝ) / n) ≤ (n.choose (i + 1) : ℝ) * ((t : ℝ) / n) := by
        field_simp;
        norm_cast;
        have := Nat.choose_succ_right_eq n i;
        nlinarith [ Nat.sub_add_cancel ( by linarith : i ≤ n ), Nat.sub_add_cancel ( by linarith : t ≤ n ) ];
      convert mul_le_mul_of_nonneg_right h_r_increasing_step ( show 0 ≤ ( t / n : ℝ ) ^ i * ( 1 - t / n ) ^ ( n - ( i + 1 ) ) by exact mul_nonneg ( pow_nonneg ( by positivity ) _ ) ( pow_nonneg ( sub_nonneg.2 <| div_le_one_of_le₀ ( mod_cast by linarith ) <| by positivity ) _ ) ) using 1 ; ring;
      · unfold binTerm; ring;
        rw [ show n - i = n - ( 1 + i ) + 1 by omega ] ; ring;
      · unfold binTerm; ring;
    have h_r_increasing_seq : ∀ k, i ≤ k → k ≤ t → binTerm ((t : ℝ) / n) n i ≤ binTerm ((t : ℝ) / n) n k := by
      intro k hk₁ hk₂; induction hk₁ <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
      exact le_trans ( by solve_by_elim [ Nat.le_of_lt ] ) ( h_r_increasing _ hk₂ );
    exact h_r_increasing_seq t ( by linarith ) ( by linarith )

/-
The mode term is at least `1/(n+1)` (there are `n+1` terms summing to `1`).
-/
lemma mode_ge_inv {n t : ℕ} (hn : 1 ≤ n) (ht : t ≤ n) :
    1 / ((n : ℝ) + 1) ≤ binTerm ((t : ℝ) / n) n t := by
  have h_sum_le : ∑ i ∈ Finset.range (n + 1), binTerm ((t : ℝ) / n) n i ≤ (n + 1) * binTerm ((t : ℝ) / n) n t := by
    convert Finset.sum_le_card_nsmul _ _ _ _;
    · ext; simp [Finset.card_range];
    · infer_instance;
    · exact fun i hi => binTerm_le_mode hn ht i;
  rw [ div_le_iff₀ ] <;> linarith [ binTerm_sum ( ( t : ℝ ) / n ) n ]

/-
For `p ≤ 1/2` and `i ≤ t`, the mode's power weight `p^t(1-p)^(n-t)` is at
most the `i`-th weight `p^i(1-p)^(n-i)`, hence `C(n,i)·P ≤ binTerm p n i`.
-/
lemma choose_mul_modeWeight_le {n t i : ℕ} (hi : i ≤ t) (ht : t ≤ n)
    (hp : (t : ℝ) / n ≤ 1 / 2) :
    (n.choose i : ℝ) *
        (((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t)) ≤
      binTerm ((t : ℝ) / n) n i := by
  unfold binTerm; ring_nf; norm_num;
  rw [ show t = i + ( t - i ) by rw [ Nat.add_sub_cancel' hi ], pow_add ] ; ring_nf ;
  by_cases hn : n = 0 <;> simp_all +decide [ mul_assoc, mul_left_comm, mul_comm ];
  rw [ show n - i = ( n - t ) + ( t - i ) by omega, pow_add ] ; ring_nf ; norm_num [ hn ];
  -- Cancel out the common terms on both sides.
  suffices h_cancel : (1 / (n : ℝ)) ^ (t - i) * t ^ (t - i) ≤ (1 - (t : ℝ) / n) ^ (t - i) by
    convert mul_le_mul_of_nonneg_right h_cancel ( show 0 ≤ ( n ^ i : ℝ ) ⁻¹ * t ^ i * n.choose i * ( 1 - ( n : ℝ ) ⁻¹ * t ) ^ ( n - t ) by exact mul_nonneg ( mul_nonneg ( mul_nonneg ( inv_nonneg.2 ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( Nat.cast_nonneg _ ) ) ( pow_nonneg ( sub_nonneg.2 <| by rw [ inv_mul_le_iff₀ <| by positivity ] ; norm_num; linarith ) _ ) ) using 1 <;> ring;
  rw [ ← mul_pow ];
  exact pow_le_pow_left₀ ( by positivity ) ( by ring_nf at *; linarith ) _

/-
Exponential form of the binary entropy for an interior mode `1 ≤ t < n`.
-/
lemma exp_H_eq {n t : ℕ} (h1 : 1 ≤ t) (h2 : t + 1 ≤ n) :
    Real.exp (H ((t : ℝ) / n) * (n : ℝ)) =
      (((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t))⁻¹ := by
  convert Real.exp_log ?_ using 1;
  · unfold H;
    rw [ Real.log_inv, Real.log_mul ] <;> norm_num;
    · unfold Real.binEntropy; rw [ Nat.cast_sub ( by linarith ) ] ; ring;
      by_cases hn : n = 0 <;> simp_all +decide [ Real.log_mul, ne_of_gt ( zero_lt_one.trans_le h1 ) ] ; ring;
    · grind;
    · exact fun h => absurd h <| sub_ne_zero_of_ne <| Ne.symm <| by rw [ Ne.eq_def, div_eq_iff ] <;> norm_cast <;> linarith;
  · exact inv_pos.mpr ( mul_pos ( pow_pos ( by exact div_pos ( by positivity ) ( by norm_cast; linarith ) ) _ ) ( pow_pos ( sub_pos.mpr ( by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) ) _ ) )

/-
`n ↦ log (n+1)` is a sublinear envelope.
-/
lemma sublinear_log_succ : Sublinear (fun n => Real.log ((n : ℝ) + 1)) := by
  constructor <;> norm_num;
  · exact fun n => Real.log_nonneg <| by linarith;
  · -- We'll use the fact that $\log(n+1) \leq \epsilon n$ for sufficiently large $n$.
    have h_log_growth : Filter.Tendsto (fun n : ℕ => Real.log (n + 1) / (n : ℝ)) Filter.atTop (nhds 0) := by
      -- We can use the fact that $\log(n+1) = \log(n) + \log\left(1 + \frac{1}{n}\right)$.
      suffices h_log : Filter.Tendsto (fun n : ℕ => (Real.log n + Real.log (1 + 1 / (n : ℝ))) / (n : ℝ)) Filter.atTop (nhds 0) by
        refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ ← Real.log_mul ( by positivity ) ( by positivity ), mul_add, mul_one_div_cancel ( by positivity ), mul_one ] );
      -- We can use the fact that $\frac{\log n}{n}$ tends to $0$ as $n$ tends to infinity.
      have h_log_n : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      simpa [ add_div ] using h_log_n.add ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) ( by norm_num ) ) ( tendsto_inv_atTop_nhds_zero_nat ) );
    intro ε hε; have := h_log_growth.eventually ( gt_mem_nhds <| show 0 < ε by positivity ) ; rcases Filter.eventually_atTop.mp this with ⟨ N, hN ⟩ ; exact ⟨ N + 1, fun n hn => by have := hN n ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩ ;

end HarperStability