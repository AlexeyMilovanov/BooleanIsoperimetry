import HarperStability.Interface
import HarperStability.Volume.BallEntropy

namespace HarperStability

attribute [local instance] Classical.propDecidable

/-!
Volume calculus and the bridge to the formalized Harper theorem.
-/

lemma hDist_eq_zero_iff {n : ℕ} (x y : Cube n) : hDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    rw [hDist, Finset.card_eq_zero, Finset.symmDiff_eq_empty] at h
    exact h
  · intro h
    subst h
    simp [hDist]

lemma hDist_self {n : ℕ} (x : Cube n) : hDist x x = 0 := by
  simpa using (hDist_eq_zero_iff x x).2 rfl

lemma hDist_triangle {n : ℕ} (x y z : Cube n) :
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

lemma hDist_comm {n : ℕ} (x y : Cube n) : hDist x y = hDist y x := by
  unfold hDist
  congr 1
  ext i
  simp [Finset.mem_symmDiff, and_comm, or_comm]

lemma neighborhood_zero_eq {n : ℕ} (A : Finset (Cube n)) :
    neighborhood 0 A = A := by
  ext v
  constructor
  · intro hv
    rw [mem_neighborhood_iff] at hv
    rcases hv with ⟨u, hu, huv⟩
    have huv0 : hDist u v = 0 := Nat.eq_zero_of_le_zero huv
    simpa [(hDist_eq_zero_iff u v).1 huv0] using hu
  · intro hv
    rw [mem_neighborhood_iff]
    exact ⟨v, hv, by simp [hDist_self]⟩

lemma neighborhood_one_neighborhood_subset {n r : ℕ} (A : Finset (Cube n)) :
    neighborhood 1 (neighborhood r A) ⊆ neighborhood (r + 1) A := by
  intro v hv
  rw [mem_neighborhood_iff] at hv ⊢
  rcases hv with ⟨w, hw, hwv⟩
  rw [mem_neighborhood_iff] at hw
  rcases hw with ⟨u, hu, huw⟩
  exact ⟨u, hu, le_trans (hDist_triangle u w v) (Nat.add_le_add huw hwv)⟩

lemma ball_subset_ball_of_le {n r s : ℕ} {a : Cube n} (hrs : r ≤ s) :
    ball a r ⊆ ball a s := by
  intro x hx
  simp [ball] at hx ⊢
  exact hx.trans hrs

lemma ball_empty_top (n : ℕ) : ball (∅ : Cube n) n = Finset.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hx_card : x.card ≤ n := by
      simpa using Finset.card_le_univ x
    have hx_dist : hDist x (∅ : Cube n) = x.card := by
      have hsymm : symmDiff x (∅ : Cube n) = x := by
        ext i
        simp [Finset.mem_symmDiff]
      simp [hDist, hsymm]
    simp [ball, hx_dist, hx_card]

lemma neighborhood_subset_ball_add_of_subset_empty {n t r : ℕ}
    {A : Finset (Cube n)} (hA : A ⊆ ball (∅ : Cube n) t) :
    neighborhood r A ⊆ ball (∅ : Cube n) (t + r) := by
  intro v hv
  rw [mem_neighborhood_iff] at hv
  rcases hv with ⟨u, hu, huv⟩
  have hu_ball : hDist u (∅ : Cube n) ≤ t := by
    simpa [ball] using hA hu
  have hvu : hDist v u ≤ r := by
    simpa [hDist_comm] using huv
  have hv_dist : hDist v (∅ : Cube n) ≤ t + r := by
    have htri := hDist_triangle v u (∅ : Cube n)
    omega
  simpa [ball] using hv_dist

private noncomputable def HIter (n r k : ℕ) : ℕ :=
  ((_root_.H n)^[r]) k

lemma HIter_zero (n k : ℕ) : HIter n 0 k = k := by
  rfl

lemma HIter_succ (n r k : ℕ) : HIter n (r + 1) k = _root_.H n (HIter n r k) := by
  simp [HIter, Function.iterate_succ_apply']

lemma harper_iter_lower_bound {n r : ℕ} (A : Finset (Cube n)) :
    HIter n r A.card ≤ (neighborhood r A).card := by
  induction r with
  | zero =>
      simp [HIter_zero, neighborhood_zero_eq]
  | succ r ih =>
      have hmono : _root_.H n (HIter n r A.card) ≤ _root_.H n (neighborhood r A).card := H_mono ih
      have hharper : _root_.H n (neighborhood r A).card ≤
          (neighborhood 1 (neighborhood r A)).card := by
        simpa [_root_.H] using
          harper_theorem n (neighborhood r A) (neighborhood r A).card rfl
      have hsubset : (neighborhood 1 (neighborhood r A)).card ≤
          (neighborhood (r + 1) A).card :=
        Finset.card_le_card (neighborhood_one_neighborhood_subset A)
      simpa [HIter_succ] using hmono.trans (hharper.trans hsubset)

lemma ball_empty_card_eq_binomPrefix (n t : ℕ) :
    (ball (∅ : Cube n) t).card = binomPrefix n (t + 1) := by
  rw [BooleanIsoperimetry.binomPrefix_eq_card_lt n (t + 1)]
  congr 1
  ext x
  have hx : hDist x (∅ : Cube n) = x.card := by
    have hsymm : symmDiff x (∅ : Cube n) = x := by
      ext i
      simp [Finset.mem_symmDiff]
    simp [hDist, hsymm]
  simp [ball, hx]

lemma H_ball_empty_card (n t : ℕ) :
    _root_.H n (ball (∅ : Cube n) t).card = (ball (∅ : Cube n) (t + 1)).card := by
  rw [ball_empty_card_eq_binomPrefix n t, ball_empty_card_eq_binomPrefix n (t + 1)]
  exact H_binomPrefix n (t + 1) (by omega)

lemma ball_card_le_HIter {n k t r : ℕ}
    (hkt : (ball (∅ : Cube n) t).card ≤ k) :
    (ball (∅ : Cube n) (t + r)).card ≤ HIter n r k := by
  induction r with
  | zero =>
      simpa [HIter_zero] using hkt
  | succ r ih =>
      have hmono : _root_.H n (ball (∅ : Cube n) (t + r)).card ≤
          _root_.H n (HIter n r k) := H_mono ih
      calc
        (ball (∅ : Cube n) (t + (r + 1))).card
            = (ball (∅ : Cube n) (t + r + 1)).card := by rw [Nat.add_assoc]
        _ = _root_.H n (ball (∅ : Cube n) (t + r)).card := by
          rw [H_ball_empty_card]
        _ ≤ _root_.H n (HIter n r k) := hmono
        _ = HIter n (r + 1) k := (HIter_succ n r k).symm

lemma V_ge_HIter (n k r : ℕ) (hk : k ≤ 2 ^ n) :
    HIter n r k ≤ V n k r := by
  classical
  unfold V
  set fams := (Finset.univ : Finset (Cube n)).powerset.filter
    (fun A : Finset (Cube n) => A.card = k) with hfams
  set vals := fams.image fun A => (neighborhood r A).card with hvals
  have hinit_card : (simplicialInitSeg n k).card = k := by
    rw [card_simplicialInitSeg, min_eq_left hk]
  have hinit_mem : simplicialInitSeg n k ∈ fams := by
    rw [hfams]
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by intro x hx; exact Finset.mem_univ x),
      hinit_card⟩
  have hvals_nonempty : vals.Nonempty := by
    rw [hvals]
    exact ⟨(neighborhood r (simplicialInitSeg n k)).card,
      Finset.mem_image.mpr ⟨simplicialInitSeg n k, hinit_mem, rfl⟩⟩
  rw [dif_pos hvals_nonempty]
  refine Finset.le_min' vals hvals_nonempty (HIter n r k) ?_
  intro y hy
  rw [hvals] at hy
  rcases Finset.mem_image.mp hy with ⟨A, hAfams, rfl⟩
  have hAcard : A.card = k := by
    rw [hfams] at hAfams
    exact (Finset.mem_filter.mp hAfams).2
  simpa [hAcard] using harper_iter_lower_bound (n := n) (r := r) A

lemma rmin_candidates_nonempty {n k : ℕ} (hk : k ≤ 2 ^ n) :
    ((Finset.range (n + 1)).filter fun r => k ≤ (ball (∅ : Cube n) r).card).Nonempty := by
  classical
  refine ⟨n, ?_⟩
  rw [Finset.mem_filter]
  constructor
  · exact Finset.mem_range.mpr (Nat.lt_succ_self n)
  · have hcard_univ : (Finset.univ : Finset (Cube n)).card = 2 ^ n := by
      simp +decide [Finset.card_univ]
    rw [ball_empty_top, hcard_univ]
    exact hk

lemma rmin_spec {n k : ℕ} (hk : k ≤ 2 ^ n) :
    k ≤ (ball (∅ : Cube n) (rmin n k)).card := by
  classical
  let vals := (Finset.range (n + 1)).filter fun r => k ≤ (ball (∅ : Cube n) r).card
  have hvals : vals.Nonempty := rmin_candidates_nonempty (n := n) (k := k) hk
  have hmem : vals.min' hvals ∈ vals := Finset.min'_mem vals hvals
  unfold rmin
  change k ≤ (ball (∅ : Cube n) (if h : vals.Nonempty then vals.min' h else n)).card
  rw [dif_pos hvals]
  exact (Finset.mem_filter.mp hmem).2

lemma rmin_le_of_ball_card {n k t : ℕ} (ht : t ≤ n)
    (hcard : k ≤ (ball (∅ : Cube n) t).card) :
    rmin n k ≤ t := by
  classical
  let vals := (Finset.range (n + 1)).filter fun r => k ≤ (ball (∅ : Cube n) r).card
  have hk : k ≤ 2 ^ n := hcard.trans (card_cube_le (ball (∅ : Cube n) t))
  have hvals : vals.Nonempty := rmin_candidates_nonempty (n := n) (k := k) hk
  have ht_mem : t ∈ vals := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ht), hcard⟩
  unfold rmin
  change (if h : vals.Nonempty then vals.min' h else n) ≤ t
  rw [dif_pos hvals]
  exact vals.min'_le t ht_mem

lemma rmin_le_n (n k : ℕ) : rmin n k ≤ n := by
  classical
  let vals := (Finset.range (n + 1)).filter fun r => k ≤ (ball (∅ : Cube n) r).card
  unfold rmin
  change (if h : vals.Nonempty then vals.min' h else n) ≤ n
  by_cases hvals : vals.Nonempty
  · rw [dif_pos hvals]
    exact Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.min'_mem vals hvals)).1)
  · rw [dif_neg hvals]

lemma ball_card_lt_of_lt_rmin {n k t : ℕ} (ht : t < rmin n k) :
    (ball (∅ : Cube n) t).card < k := by
  by_contra hnot
  exact ht.not_ge (rmin_le_of_ball_card (n := n) (k := k) (t := t)
    (ht.le.trans (rmin_le_n n k))
    (Nat.le_of_not_gt hnot))

lemma V_le_ball_rmin_add (n k r : ℕ) (hk : k ≤ 2 ^ n) :
    V n k r ≤ (ball (∅ : Cube n) (rmin n k + r)).card := by
  classical
  obtain ⟨A, hA_sub, hA_card⟩ :=
    Finset.exists_subset_card_eq (s := ball (∅ : Cube n) (rmin n k)) (rmin_spec (n := n) (k := k) hk)
  unfold V
  set fams := (Finset.univ : Finset (Cube n)).powerset.filter
    (fun A : Finset (Cube n) => A.card = k) with hfams
  set vals := fams.image fun A => (neighborhood r A).card with hvals
  have hA_fams : A ∈ fams := by
    rw [hfams]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (by intro x hx; exact Finset.mem_univ x), hA_card⟩
  have hA_val : (neighborhood r A).card ∈ vals := by
    rw [hvals]
    exact Finset.mem_image.mpr ⟨A, hA_fams, rfl⟩
  have hvals_nonempty : vals.Nonempty := ⟨(neighborhood r A).card, hA_val⟩
  rw [dif_pos hvals_nonempty]
  exact (vals.min'_le (neighborhood r A).card hA_val).trans
    (Finset.card_le_card (neighborhood_subset_ball_add_of_subset_empty hA_sub))

theorem ball_volume_two_sided_skeleton : BallVolumeTwoSidedStatement := by
  refine' ⟨ fun n => Real.log ( ( n : ℝ ) + 1 ), sublinear_log_succ, _ ⟩;
  intro n t ht
  by_cases ht0 : t = 0;
  · simp +decide [ ht0, ball ];
    simp +decide [ hDist_eq_zero_iff, Real.exp_add, Real.exp_sub, Real.exp_log ( Nat.cast_add_one_pos _ ) ];
    unfold H; norm_num [ Finset.filter_eq' ] ;
    exact inv_le_one_of_one_le₀ <| by linarith;
  · constructor;
    · have h_ball_ge_choose : (ball (∅ : Cube n) t).card ≥ (n.choose t : ℝ) := by
        rw [ ball_empty_card_eq_binomPrefix ];
        exact_mod_cast Finset.single_le_sum ( fun x _ => Nat.zero_le ( Nat.choose n x ) ) ( Finset.mem_range.mpr ( Nat.lt_succ_self t ) );
      have h_choose_ge_exp : (n.choose t : ℝ) ≥ (Real.exp (H ((t : ℝ) / n) * (n : ℝ))) / (n + 1) := by
        have h_choose_ge_exp : (n.choose t : ℝ) * ((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t) ≥ 1 / (n + 1) := by
          have h_choose_ge_exp : (n.choose t : ℝ) * ((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t) ≥ binTerm ((t : ℝ) / n) n t := by
            unfold binTerm; ring_nf; norm_num;
          exact le_trans ( mode_ge_inv ( Nat.pos_of_ne_zero ( by aesop ) ) ( by omega ) ) h_choose_ge_exp;
        have h_exp_eq : Real.exp (H ((t : ℝ) / n) * (n : ℝ)) = (((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t))⁻¹ := by
          convert exp_H_eq ( Nat.pos_of_ne_zero ht0 ) ( by omega : t + 1 ≤ n ) using 1;
        field_simp;
        rw [ mul_comm, h_exp_eq, inv_eq_one_div, div_le_iff₀ ];
        · rw [ ge_iff_le, div_le_iff₀ ] at h_choose_ge_exp <;> first | positivity | linarith;
        · exact mul_pos ( pow_pos ( div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ht0 ) ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ) _ ) ( pow_pos ( sub_pos.mpr ( by rw [ div_lt_iff₀ ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n 2, Nat.pos_of_ne_zero ht0 ] ) ) _ );
      rw [ Real.exp_sub, Real.exp_log ( by positivity ) ] ; linarith;
    · -- For $t \geq 1$, we use the binomial term bounds.
      have h_binom : (ball (∅ : Cube n) t).card * ((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t) ≤ 1 := by
        have h_binom : (ball (∅ : Cube n) t).card * ((t : ℝ) / n) ^ t * (1 - (t : ℝ) / n) ^ (n - t) ≤ ∑ i ∈ Finset.range (t + 1), binTerm ((t : ℝ) / n) n i := by
          convert Finset.sum_le_sum fun i hi => choose_mul_modeWeight_le ( Finset.mem_range_succ_iff.mp hi ) ( by linarith [ Nat.div_mul_le_self n 2 ] ) ( show ( t : ℝ ) / n ≤ 1 / 2 from by rw [ div_le_div_iff₀ ] <;> norm_cast <;> linarith [ Nat.div_mul_le_self n 2, Nat.pos_of_ne_zero ht0 ] ) using 1 ; norm_num [ mul_assoc, Finset.sum_mul _ _ _ ];
          rw [ ball_empty_card_eq_binomPrefix ];
          unfold binomPrefix; norm_num [ Finset.sum_mul _ _ _ ] ;
        exact h_binom.trans ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.succ_le_succ ( show t ≤ n from ht.trans ( Nat.div_le_self _ _ ) ) ) ) fun _ _ _ => binTerm_nonneg ( by positivity ) ( by exact div_le_one_of_le₀ ( by norm_cast; linarith [ Nat.div_mul_le_self n 2 ] ) ( by positivity ) ) _ _ ) ( by rw [ binTerm_sum ] ) );
      by_cases hn : n = 0 <;> simp_all +decide [ mul_assoc ];
      rw [ Real.exp_add, Real.exp_log ( by positivity ) ];
      rw [ exp_H_eq ];
      · rw [ inv_mul_eq_div, le_div_iff₀ ];
        · exact h_binom.trans ( by norm_cast; linarith );
        · exact mul_pos ( pow_pos ( by positivity ) _ ) ( pow_pos ( sub_pos.mpr ( by rw [ div_lt_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n 2, Nat.pos_of_ne_zero ht0 ] ) ) _ );
      · exact Nat.pos_of_ne_zero ht0;
      · omega

theorem vplus_skeleton : VPlusStatement := by
  intro n k r hk1 hk2
  classical
  let candidates := (Finset.range (n + 1)).filter
    fun t : ℕ => (ball (∅ : Cube n) t).card ≤ k
  have hball_zero : (ball (∅ : Cube n) 0).card = 1 := by
    simp [ball_empty_card_eq_binomPrefix, binomPrefix]
  have hzero_mem : 0 ∈ candidates := by
    simp [candidates, hball_zero, hk1]
  let t := candidates.max' ⟨0, hzero_mem⟩
  have ht_mem : t ∈ candidates := Finset.max'_mem candidates ⟨0, hzero_mem⟩
  have ht_range : t ∈ Finset.range (n + 1) := (Finset.mem_filter.mp ht_mem).1
  have ht_le_n : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht_range)
  have ht_card : (ball (∅ : Cube n) t).card ≤ k := (Finset.mem_filter.mp ht_mem).2
  refine ⟨t, ht_le_n, ht_card, ?_, ?_⟩
  · intro t' ht'_le hcard
    have ht'_mem : t' ∈ candidates := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ht'_le), hcard⟩
    exact candidates.le_max' t' ht'_mem
  · exact_mod_cast (ball_card_le_HIter (n := n) (k := k) (t := t) (r := r) ht_card).trans
      (V_ge_HIter n k r hk2)

theorem interior_v_skeleton : InteriorVStatement := by
  intro n t r _htr
  have hk : (ball (∅ : Cube n) t).card ≤ 2 ^ n := card_cube_le (ball (∅ : Cube n) t)
  exact_mod_cast (ball_card_le_HIter (n := n) (k := (ball (∅ : Cube n) t).card)
    (t := t) (r := r) le_rfl).trans (V_ge_HIter n (ball (∅ : Cube n) t).card r hk)

/-
On a compact interval `[lo, hi]` bounded away from the endpoints `0` and
`1`, the binary entropy `H` is Lipschitz continuous.
-/
lemma entropy_lipschitz (lo hi : ℝ) (hlo : 0 < lo) (hhi : hi < 1)
    (hlohi : lo ≤ hi) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi →
      |H x - H y| ≤ L * |x - y| := by
        -- Since $H$ is differentiable on $(0, 1)$, we can apply the mean value theorem to $H$ on the interval $[lo, hi]$.
        have h_diff : ∀ x ∈ Set.Icc lo hi, HasDerivAt H (Real.log (1 - x) - Real.log x) x := by
          intro x hx;
          exact Real.hasDerivAt_binEntropy ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] );
        -- By the mean value theorem, for any $x, y \in [lo, hi]$, there exists $c \in (x, y)$ such that $H(x) - H(y) = H'(c)(x - y)$.
        have h_mvt : ∀ x y : ℝ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi → x < y → ∃ c ∈ Set.Ioo x y, H x - H y = (Real.log (1 - c) - Real.log c) * (x - y) := by
          intros x y hx hy hx' hy' hxy
          have h_mean_value : ∃ c ∈ Set.Ioo x y, deriv H c = (H y - H x) / (y - x) := by
            apply_rules [ exists_deriv_eq_slope ];
            · exact continuousOn_of_forall_continuousAt fun z hz => HasDerivAt.continuousAt ( h_diff z ⟨ by linarith [ hz.1 ], by linarith [ hz.2 ] ⟩ );
            · exact fun z hz => ( h_diff z ⟨ by linarith [ hz.1 ], by linarith [ hz.2 ] ⟩ |> HasDerivAt.differentiableAt |> DifferentiableAt.differentiableWithinAt );
          obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_value; exact ⟨ c, hc₁, by have := h_diff c ⟨ by linarith [ hc₁.1 ], by linarith [ hc₁.2 ] ⟩ ; have := this.deriv; rw [ eq_div_iff ] at hc₂ <;> nlinarith ⟩ ;
        -- Let $L$ be an upper bound for $|H'(c)|$ on $[lo, hi]$.
        obtain ⟨L, hL⟩ : ∃ L, ∀ c ∈ Set.Icc lo hi, |Real.log (1 - c) - Real.log c| ≤ L := by
          exact IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) ( show ContinuousOn ( fun x => Real.log ( 1 - x ) - Real.log x ) ( Set.Icc lo hi ) from ContinuousOn.sub ( ContinuousOn.log ( continuousOn_const.sub continuousOn_id ) fun x hx => by linarith [ hx.1, hx.2 ] ) ( ContinuousOn.log continuousOn_id fun x hx => by linarith [ hx.1, hx.2 ] ) );
        refine' ⟨ L, _, _ ⟩;
        · exact le_trans ( abs_nonneg _ ) ( hL lo ⟨ le_rfl, hlohi ⟩ );
        · intro x y hx hy hx' hy'; rcases lt_trichotomy x y with ( H | rfl | H ) <;> norm_num at *;
          · obtain ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ := h_mvt x y hx hy hx' hy' H ; rw [ hcd, abs_mul ] ; exact mul_le_mul_of_nonneg_right ( hL c ( by linarith ) ( by linarith ) ) ( abs_nonneg _ );
          · obtain ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ := h_mvt y x hx' hy' hx hy H ; rw [ abs_le ] ; constructor <;> cases abs_cases ( x - y ) <;> nlinarith [ abs_le.mp ( hL c ( by linarith ) ( by linarith ) ) ]

/-
On a compact interval `[lo, hi]` with `0 < lo` and `hi < 1/2`, the binary
entropy `H` is strictly increasing with a derivative bounded below, hence its
inverse is Lipschitz: `|x - y| ≤ C * |H x - H y|`.
-/
lemma entropy_inversion_compact (lo hi : ℝ) (hlo : 0 < lo) (hhi : hi < 1 / 2)
    (hlohi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi →
      |x - y| ≤ C * |H x - H y| := by
        -- By the mean value theorem, for any $x, y \in [lo, hi]$ with $x < y$, there exists $c \in (x, y)$ such that $H(y) - H(x) = (Real.log (1 - c) - Real.log c) * (y - x)$.
        have h_mean_value : ∀ x y : ℝ, lo ≤ x → x < y → y ≤ hi → ∃ c ∈ Set.Ioo x y, H y - H x = (Real.log (1 - c) - Real.log c) * (y - x) := by
          intros x y hx hy hxy;
          have := exists_deriv_eq_slope ( f := fun x => Real.binEntropy x ) hy;
          -- The binary entropy function is differentiable on (0,1) with derivative log(1-p) - log(p).
          have h_diff : ∀ p ∈ Set.Ioo 0 1, HasDerivAt (fun x => Real.binEntropy x) (Real.log (1 - p) - Real.log p) p := by
            intro p hp; convert Real.hasDerivAt_binEntropy hp.1.ne' hp.2.ne using 1;
          norm_num +zetaDelta at *;
          exact this ( continuousOn_of_forall_continuousAt fun p hp => HasDerivAt.continuousAt ( h_diff p ( by linarith [ hp.1 ] ) ( by linarith [ hp.2 ] ) ) ) ( fun p hp => DifferentiableAt.differentiableWithinAt ( h_diff p ( by linarith [ hp.1 ] ) ( by linarith [ hp.2 ] ) |> HasDerivAt.differentiableAt ) ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ eq_div_iff ] at hc₂ <;> norm_num [ H, h_diff c ( by linarith ) ( by linarith ) |> HasDerivAt.deriv ] at * <;> linarith ⟩;
        -- Since $c < y \leq hi < 1/2$, we have $c < 1 - c$, and $c \leq hi$, so $Real.log (1 - c) - Real.log c \geq Real.log (1 - hi) - Real.log hi = m$ (because $t \mapsto Real.log (1 - t) - Real.log t$ is decreasing).
        have h_deriv_bound : ∀ x y : ℝ, lo ≤ x → x < y → y ≤ hi → H y - H x ≥ (Real.log (1 - hi) - Real.log hi) * (y - x) := by
          intros x y hx hy hxy
          obtain ⟨c, hc⟩ := h_mean_value x y hx hy hxy
          have h_deriv_bound : Real.log (1 - c) - Real.log c ≥ Real.log (1 - hi) - Real.log hi := by
            exact sub_le_sub ( Real.log_le_log ( by linarith [ hc.1.1, hc.1.2 ] ) ( by linarith [ hc.1.1, hc.1.2 ] ) ) ( Real.log_le_log ( by linarith [ hc.1.1, hc.1.2 ] ) ( by linarith [ hc.1.1, hc.1.2 ] ) );
          nlinarith;
        refine' ⟨ ( Real.log ( 1 - hi ) - Real.log hi ) ⁻¹, _, _ ⟩;
        · exact inv_pos.mpr ( sub_pos.mpr ( Real.log_lt_log ( by linarith ) ( by linarith ) ) );
        · intro x y hx hy hx' hy'; rcases lt_trichotomy x y with ( H | rfl | H ) <;> norm_num at *;
          · rw [ inv_mul_eq_div, le_div_iff₀ ] <;> cases abs_cases ( x - y ) <;> cases abs_cases ( HarperStability.H x - HarperStability.H y ) <;> nlinarith [ h_deriv_bound x y hx H hy', show Real.log ( 1 - hi ) - Real.log hi > 0 from sub_pos.mpr <| Real.log_lt_log ( by linarith ) <| by linarith ];
          · rw [ inv_mul_eq_div, le_div_iff₀ ];
            · cases abs_cases ( x - y ) <;> cases abs_cases ( HarperStability.H x - HarperStability.H y ) <;> nlinarith [ h_deriv_bound y x hx' H hy ];
            · exact sub_pos_of_lt ( Real.log_lt_log ( by linarith ) ( by linarith ) )

/-- The constant function `c ≥ 0` is sublinear. -/
lemma Sublinear_const {c : ℝ} (hc : 0 ≤ c) : Sublinear (fun _ => c) := by
  refine ⟨fun _ => hc, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_ge (c / ε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : c / ε ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  rw [div_le_iff₀ hε] at h1
  linarith [h1]

/-- Sum of two sublinear functions is sublinear. -/
lemma Sublinear_add {s t : ℕ → ℝ} (hs : Sublinear s) (ht : Sublinear t) :
    Sublinear (fun n => s n + t n) := by
  refine ⟨fun n => add_nonneg (hs.1 n) (ht.1 n), fun ε hε => ?_⟩
  obtain ⟨N1, hN1⟩ := hs.2 (ε/2) (by linarith)
  obtain ⟨N2, hN2⟩ := ht.2 (ε/2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 := hN2 n (le_trans (le_max_right _ _) hn)
  simp only
  linarith

/-- A nonnegative scalar multiple of a sublinear function is sublinear. -/
lemma Sublinear_smul {c : ℝ} (hc : 0 ≤ c) {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (fun n => c * s n) := by
  refine ⟨fun n => mul_nonneg hc (hs.1 n), fun ε hε => ?_⟩
  rcases eq_or_lt_of_le hc with h | h
  · exact ⟨0, fun n _ => by simp [← h]; positivity⟩
  · obtain ⟨N, hN⟩ := hs.2 (ε/c) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h2 : c * s n ≤ c * (ε/c * (n:ℝ)) := by nlinarith [hN n hn]
    have h3 : c * (ε/c * (n:ℝ)) = ε * n := by field_simp
    show c * s n ≤ ε * n
    rw [← h3]; exact h2

/-- A nonnegative function dominated pointwise by a sublinear function is
sublinear. -/
lemma Sublinear_of_le {s t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (hle : ∀ n, t n ≤ s n) (hs : Sublinear s) : Sublinear t := by
  refine ⟨ht0, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hs.2 ε hε
  exact ⟨N, fun n hn => (hle n).trans (hN n hn)⟩

/-- A nonnegative function that vanishes for all large enough `n` is
sublinear. -/
lemma Sublinear_of_eventually_zero {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (N : ℕ) (hN : ∀ n, N ≤ n → f n = 0) : Sublinear f := by
  refine ⟨hf0, fun ε hε => ?_⟩
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn]
  positivity

/-- Every centered Hamming ball is nonempty (it contains its center `∅`). -/
lemma ball_card_pos (n t : ℕ) : 0 < (ball (∅ : Cube n) t).card := by
  apply Finset.card_pos.mpr
  exact ⟨∅, by simp [ball, hDist_self]⟩

/-- Monotonicity of `H` on `[0, 1/2]`. -/
lemma H_le_H {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    H x ≤ H y :=
  Real.binEntropy_strictMonoOn.monotoneOn ⟨hx, by norm_num; linarith⟩
    ⟨by linarith, by norm_num; linarith⟩ hxy

/-- Strict monotonicity of `H` on `[0, 1/2]`. -/
lemma H_lt_H {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1 / 2) :
  H x < H y :=
  Real.binEntropy_strictMonoOn ⟨hx, by norm_num; linarith⟩
    ⟨by linarith, by norm_num; linarith⟩ hxy

/-
Clean-regime upper estimate for `rmin`: in the interior regime where the
target radius fits below the equator (`hfit`), `rmin n k` is bounded above by
`alpha*n` plus a slack.
-/
lemma rmin_clean_upper {n k : ℕ} {alpha sizeSlack C0 vn lo hi : ℝ}
    (hn : 1 ≤ n) (hC0 : 0 < C0) (hk1 : 1 ≤ k) (_hk2 : k ≤ 2 ^ n)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hhi : hi < 1 / 2)
    (halpha_lo : lo ≤ alpha) (halpha_hi : alpha ≤ hi)
    (hs0 : 0 ≤ sizeSlack) (hvn : 0 ≤ vn)
    (hinv : ∀ x y : ℝ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi → |x - y| ≤ C0 * |H x - H y|)
    (hballL : ∀ t : ℕ, t ≤ n / 2 →
      Real.exp (H ((t : ℝ) / n) * n - vn) ≤ ((ball (∅ : Cube n) t).card : ℝ))
    (hlogk : Real.log k ≤ H alpha * n + sizeSlack)
    (hfit : alpha * n + C0 * sizeSlack + C0 * vn + 1 ≤ hi * n) :
    (rmin n k : ℝ) ≤ alpha * n + C0 * sizeSlack + C0 * vn + 1 := by
      -- Let `X := alpha * n + C0 * (sizeSlack + vn)` and `t := Nat.ceil X`.
      set X := alpha * n + C0 * (sizeSlack + vn)
      set t := Nat.ceil X
      generalize_proofs at *; (
      -- From `hinv (t/n) alpha`, we get `|(t:ℝ)/n - alpha| ≤ C0 * |H ((t:ℝ)/n) - H alpha|`.
      have h_inv : (t : ℝ) / n - alpha ≤ C0 * (H ((t : ℝ) / n) - H alpha) := by
        have h_inv : (t : ℝ) / n ∈ Set.Icc lo hi := by
          constructor <;> nlinarith [ Nat.le_ceil X, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( t : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ), show ( t : ℝ ) ≥ X by exact Nat.le_ceil X, show ( t : ℝ ) ≤ X + 1 by exact Nat.ceil_lt_add_one ( show 0 ≤ X by exact add_nonneg ( mul_nonneg ( by linarith ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg hC0.le ( add_nonneg hs0 hvn ) ) ) |> le_of_lt ] ;
        generalize_proofs at *; (
        have h_inv : (t : ℝ) / n ≥ alpha := by
          rw [ ge_iff_le, le_div_iff₀ ] <;> norm_num <;> nlinarith [ Nat.le_ceil ( alpha * n + C0 * ( sizeSlack + vn ) ), show ( n : ℝ ) ≥ 1 by norm_cast ] ;
        generalize_proofs at *; (
        have h_inv : H alpha ≤ H ((t : ℝ) / n) := by
          apply H_le_H; exact (by linarith [Set.mem_Icc.mp ‹_›]) ; exact (by linarith [Set.mem_Icc.mp ‹_›]) ; exact (by linarith [Set.mem_Icc.mp ‹_›]) ;
        generalize_proofs at *; (
        have := hinv ( t / n ) alpha ( by linarith [ Set.mem_Icc.mp ‹_› ] ) ( by linarith [ Set.mem_Icc.mp ‹_› ] ) ( by linarith [ Set.mem_Icc.mp ‹_› ] ) ( by linarith [ Set.mem_Icc.mp ‹_› ] ) ; rw [ abs_of_nonneg, abs_of_nonneg ] at this <;> linarith;)))
      generalize_proofs at *; (
      -- Therefore, `H ((t:ℝ)/n) * n ≥ H alpha * n + sizeSlack + vn`.
      have h_exp : H ((t : ℝ) / n) * n ≥ H alpha * n + sizeSlack + vn := by
        rw [ div_sub', div_le_iff₀ ] at h_inv <;> nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, Nat.le_ceil X, show ( t : ℝ ) ≥ X by exact Nat.le_ceil X, mul_div_cancel₀ ( C0 : ℝ ) hC0.ne' ] ;
      generalize_proofs at *; (
      -- Therefore, `k ≤ (ball ∅ t).card`.
      have h_card : k ≤ (ball (∅ : Cube n) t).card := by
        have h_card : (k : ℝ) ≤ Real.exp (H ((t : ℝ) / n) * n - vn) := by
          rw [ ← Real.log_le_iff_le_exp ( by positivity ) ] ; linarith [ Real.log_le_log ( by positivity ) ( by linarith : ( k : ℝ ) ≤ k ) ] ;
        generalize_proofs at *; (
        exact_mod_cast h_card.trans ( hballL t ( Nat.le_div_iff_mul_le zero_lt_two |>.2 <| by rw [ ← @Nat.cast_le ℝ ] ; push_cast; nlinarith [ Nat.ceil_lt_add_one <| show 0 ≤ alpha * n + C0 * ( sizeSlack + vn ) by exact add_nonneg ( mul_nonneg ( by linarith ) <| Nat.cast_nonneg _ ) <| mul_nonneg hC0.le <| add_nonneg hs0 hvn ] ) ))
      generalize_proofs at *; (
      -- By `rmin_le_of_ball_card (t ≤ n) this`, `rmin n k ≤ t`.
      have h_rmin_le_t : rmin n k ≤ t := by
        apply rmin_le_of_ball_card (by
        exact Nat.ceil_le.mpr ( by nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] )) h_card
      generalize_proofs at *; (
      exact le_trans ( Nat.cast_le.mpr h_rmin_le_t ) ( by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ alpha * n + C0 * ( sizeSlack + vn ) by exact add_nonneg ( mul_nonneg ( by linarith ) ( Nat.cast_nonneg _ ) ) ( mul_nonneg hC0.le ( add_nonneg hs0 hvn ) ) ) ] ) ;)))))

/-
Clean-regime lower estimate for `rmin`. The gap hypothesis `hgap`
(with `lo < alphaMin ≤ alpha`) rules out `rmin n k` being far below `alpha*n`.
-/
lemma rmin_clean_lower {n k : ℕ} {alpha sizeSlack C0 vn lo hi alphaMin : ℝ}
    (hn : 1 ≤ n) (hC0 : 0 < C0) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 ^ n)
    (hlo : 0 < lo) (_hlohi : lo ≤ hi) (hhi : hi < 1 / 2)
    (halpha_lo : lo ≤ alpha) (halpha_hi : alpha ≤ hi)
    (hs0 : 0 ≤ sizeSlack) (hvn : 0 ≤ vn)
    (hinv : ∀ x y : ℝ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi → |x - y| ≤ C0 * |H x - H y|)
    (hballU : ∀ t : ℕ, t ≤ n / 2 →
      ((ball (∅ : Cube n) t).card : ℝ) ≤ Real.exp (H ((t : ℝ) / n) * n + vn))
    (hlogk : H alpha * n - sizeSlack ≤ Real.log k)
    (hlo_lt_aM : lo < alphaMin) (haM_le_alpha : alphaMin ≤ alpha)
    (_haM_half : alphaMin ≤ 1 / 2)
    (hgap : sizeSlack + vn < (H alphaMin - H lo) * n) :
    alpha * n - (C0 * sizeSlack + C0 * vn) ≤ (rmin n k : ℝ) := by
      -- Let's consider the two cases: $\alpha n \leq rmin n k$ and $rmin n k < \alpha n$.
      by_cases h_case : alpha * n ≤ rmin n k;
      · exact le_trans ( sub_le_self _ ( by positivity ) ) h_case;
      · -- Since $rmin n k < \alpha * n$, we have $(rmin n k : ℝ) / n < \alpha$.
        have h_rmin_lt_alpha : (rmin n k : ℝ) / n < alpha := by
          rw [ div_lt_iff₀ ] <;> first | positivity | linarith;
        -- Since $rmin n k < \alpha * n$, we have $rmin n k \leq n / 2$.
        have h_rmin_le_half : rmin n k ≤ n / 2 := by
          rw [ Nat.le_div_iff_mul_le ] <;> norm_num at *;
          exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] );
        -- By `hlogk` and `hballU`, we have `(H alpha - H ((rmin n k : ℝ) / n)) * n ≤ sizeSlack + vn`.
        have h_diff_le : (H alpha - H ((rmin n k : ℝ) / n)) * n ≤ sizeSlack + vn := by
          have h_diff_le : Real.log k ≤ H ((rmin n k : ℝ) / n) * n + vn := by
            have hlogk' : (k : ℝ) ≤ (ball (∅ : Cube n) (rmin n k)).card := by
              exact_mod_cast rmin_spec hk2;
            exact le_trans ( Real.log_le_log ( by positivity ) hlogk' ) ( by simpa using Real.log_le_log ( Nat.cast_pos.mpr <| ball_card_pos _ _ ) <| hballU _ h_rmin_le_half );
          linarith;
        by_cases h_case2 : (rmin n k : ℝ) / n < lo;
        · -- Since $rmin n k < lo * n$, we have $H ((rmin n k : ℝ) / n) \leq H lo$.
          have h_H_le_Hlo : H ((rmin n k : ℝ) / n) ≤ H lo := by
            apply H_le_H;
            · positivity;
            · grind;
            · linarith;
          -- Since $alphaMin \leq alpha$, we have $H alphaMin \leq H alpha$.
          have h_H_alphaMin_le_H_alpha : H alphaMin ≤ H alpha := by
            apply_rules [ H_le_H ];
            · linarith;
            · grobner;
          nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast ];
        · have := hinv alpha ( ( rmin n k : ℝ ) / n ) ?_ ?_ ?_ ?_ <;> norm_num at *;
          · rw [ abs_of_nonneg, abs_of_nonneg ] at this <;> nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( rmin n k : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ), H_le_H ( show 0 ≤ ( rmin n k : ℝ ) / n by positivity ) ( show ( rmin n k : ℝ ) / n ≤ alpha by linarith ) ( show alpha ≤ 1 / 2 by linarith ) ];
          · grind;
          · grobner;
          · grind;
          · exact le_trans h_rmin_lt_alpha.le halpha_hi

set_option maxHeartbeats 1600000 in
lemma interior_rmin_slack_exists :
  ∀ alphaMin c0 : ℝ, 0 < alphaMin → 0 < c0 →
    ∃ C_V : ℝ, 1 ≤ C_V ∧
    ∃ volumeSlack : ℕ → ℝ, Sublinear volumeSlack ∧
      ∀ n k r : ℕ, ∀ alpha beta sizeSlack : ℝ,
        alphaMin ≤ alpha → alpha ≤ 1 / 2 →
        0 ≤ sizeSlack →
        beta = (r : ℝ) / (n : ℝ) →
        alpha + beta ≤ 1 / 2 - c0 →
        1 ≤ k → k ≤ 2 ^ n →
        |Real.log ((k : ℝ)) - H alpha * (n : ℝ)| ≤ sizeSlack →
        |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + volumeSlack n := by
  intro alphaMin c0 halphaMin hc0
  by_cases hcase : alphaMin ≤ 1 / 2 - c0
  · -- Main interior case.
    set lo := alphaMin / 2 with hlo_def
    set hi := 1 / 2 - c0 / 2 with hhi_def
    have hlo_pos : 0 < lo := by rw [hlo_def]; linarith
    have hhi_lt : hi < 1 / 2 := by rw [hhi_def]; linarith
    have hlohi : lo ≤ hi := by rw [hlo_def, hhi_def]; linarith
    have hc0_half : c0 < 1 / 2 := by linarith
    obtain ⟨C0, hC0_pos, hinv⟩ := entropy_inversion_compact lo hi hlo_pos hhi_lt hlohi
    obtain ⟨vol0, hvol0_sub, hvol0⟩ := ball_volume_two_sided_skeleton
    set δ := H alphaMin - H lo with hδ_def
    have hδ_pos : 0 < δ := by
      rw [hδ_def]; apply sub_pos.mpr
      exact H_lt_H hlo_pos.le (by rw [hlo_def]; linarith) (by linarith)
    set M := min (c0 / (4 * C0)) (δ / 2) with hM_def
    have hM_pos : 0 < M := lt_min (by positivity) (by linarith)
    have hM_le1 : M ≤ c0 / (4 * C0) := min_le_left _ _
    have hM_le2 : M ≤ δ / 2 := min_le_right _ _
    set C_V := max 1 (max (1 / M) C0) with hCV_def
    have hCV1 : (1 : ℝ) ≤ C_V := le_max_left _ _
    have hCV_invM : 1 / M ≤ C_V := le_trans (le_max_left _ _) (le_max_right _ _)
    have hCV_C0 : C0 ≤ C_V := le_trans (le_max_right _ _) (le_max_right _ _)
    obtain ⟨NA, hNA⟩ := hvol0_sub.2 (c0 / (8 * C0)) (by positivity)
    obtain ⟨NB, hNB⟩ := hvol0_sub.2 (M / 4) (by positivity)
    obtain ⟨NC, hNC⟩ := exists_nat_ge (8 / c0)
    set N0 := max (max NA NB) (max NC 1) + 1 with hN0_def
    have hN0_ge1 : 1 ≤ N0 := by omega
    have hN0_props : ∀ n : ℕ, N0 ≤ n →
        C0 * vol0 n + 1 ≤ (c0 / 4) * n ∧ vol0 n ≤ (M / 4) * n := by
      intro n hn
      have hnA : NA ≤ n := by omega
      have hnB : NB ≤ n := by omega
      have hnC : NC ≤ n := by omega
      have hvA : vol0 n ≤ (c0 / (8 * C0)) * n := hNA n hnA
      have hvB : vol0 n ≤ (M / 4) * n := hNB n hnB
      have hcn : (8 : ℝ) / c0 ≤ (n : ℝ) := le_trans hNC (by exact_mod_cast hnC)
      have h1 : (1 : ℝ) ≤ (c0 / 8) * n := by
        rw [div_le_iff₀ hc0] at hcn; nlinarith
      refine ⟨?_, hvB⟩
      have hC0ne : C0 ≠ 0 := hC0_pos.ne'
      have hstep : C0 * vol0 n ≤ (c0 / 8) * n := by
        have h := mul_le_mul_of_nonneg_left hvA hC0_pos.le
        have heq : C0 * (c0 / (8 * C0) * (n : ℝ)) = (c0 / 8) * n := by
          field_simp
        rw [heq] at h; exact h
      linarith
    refine ⟨C_V, hCV1,
      fun n => C0 * vol0 n + 1 + (if n < N0 then (n : ℝ) else 0), ?_, ?_⟩
    · -- Sublinearity of the chosen volume slack.
      apply Sublinear_add
      · apply Sublinear_add
        · exact Sublinear_smul hC0_pos.le hvol0_sub
        · exact Sublinear_const (by norm_num)
      · refine Sublinear_of_eventually_zero (fun n => ?_) N0 (fun n hn => by simp [Nat.not_lt.mpr hn])
        split_ifs with h
        · positivity
        · exact le_refl 0
    · intro n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hbeta0 : 0 ≤ beta := by rw [h_beta]; positivity
      have h_alpha_le : alpha ≤ 1 / 2 - c0 := by linarith
      have h_alpha_lo : lo ≤ alpha := by rw [hlo_def]; linarith
      have h_alpha_hi : alpha ≤ hi := by rw [hhi_def]; linarith
      set s := rmin n k with hs_def
      set E := C_V * sizeSlack + (C0 * vol0 n + 1 + (if n < N0 then (n : ℝ) else 0)) with hE_def
      show |(s : ℝ) - alpha * n| ≤ E
      have hs_le_n : (s : ℝ) ≤ n := by exact_mod_cast rmin_le_n n k
      have hs_nn : (0 : ℝ) ≤ (s : ℝ) := by positivity
      have h_an_0 : 0 ≤ alpha * n := mul_nonneg (by linarith) hn_nn
      have h_an_n : alpha * n ≤ n := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - alpha by linarith) hn_nn]
      have hvol0n : 0 ≤ vol0 n := hvol0_sub.1 n
      have hCVs0 : 0 ≤ C_V * sizeSlack := mul_nonneg (by linarith) h_s0
      have h_triv : |(s : ℝ) - alpha * n| ≤ n := by
        rw [abs_le]; constructor <;> linarith
      by_cases hn_small : n < N0
      · have hbump : (if n < N0 then (n : ℝ) else 0) = (n : ℝ) := if_pos hn_small
        have hEn : (n : ℝ) ≤ E := by
          rw [hE_def, hbump]; nlinarith [hCVs0, mul_nonneg hC0_pos.le hvol0n]
        linarith [h_triv, hEn]
      · have hnN0 : N0 ≤ n := Nat.not_lt.mp hn_small
        have hn1 : 1 ≤ n := le_trans hN0_ge1 hnN0
        obtain ⟨hA, hB⟩ := hN0_props n hnN0
        have hbump0 : (if n < N0 then (n : ℝ) else 0) = 0 := if_neg hn_small
        have hE_eq : E = C_V * sizeSlack + (C0 * vol0 n + 1) := by rw [hE_def, hbump0]; ring
        by_cases hslack : M * n ≤ sizeSlack
        · have hEn : (n : ℝ) ≤ E := by
            have h1 : (n : ℝ) ≤ C_V * sizeSlack := by
              have h2 : (1 / M) * (M * n) ≤ C_V * sizeSlack :=
                mul_le_mul hCV_invM hslack (by positivity) (by linarith)
              have h3 : (1 / M) * (M * (n : ℝ)) = n := by field_simp
              linarith [h2, h3.ge, h3.le]
            rw [hE_eq]; nlinarith [mul_nonneg hC0_pos.le hvol0n]
          linarith [h_triv, hEn]
        · push_neg at hslack
          have hlogU : Real.log k ≤ H alpha * n + sizeSlack := by
            have := (abs_le.mp h_log).2; linarith
          have hlogL : H alpha * n - sizeSlack ≤ Real.log k := by
            have := (abs_le.mp h_log).1; linarith
          have hCs : C0 * sizeSlack ≤ (c0 / 4) * n := by
            have hs_le : sizeSlack ≤ (c0 / (4 * C0)) * n :=
              le_trans hslack.le (mul_le_mul_of_nonneg_right hM_le1 hn_nn)
            have hmul := mul_le_mul_of_nonneg_left hs_le hC0_pos.le
            rw [show C0 * ((c0 / (4 * C0)) * (n : ℝ)) = (c0 / 4) * n by field_simp] at hmul
            linarith
          have halpha_mul : alpha * n ≤ (1 / 2 - c0) * n :=
            mul_le_mul_of_nonneg_right h_alpha_le hn_nn
          have hfit : alpha * n + C0 * sizeSlack + C0 * vol0 n + 1 ≤ hi * n := by
            rw [hhi_def]; nlinarith [hA, hCs, halpha_mul]
          have hgap : sizeSlack + vol0 n < δ * n := by
            have h1 : sizeSlack < (δ / 2) * n :=
              lt_of_lt_of_le hslack (mul_le_mul_of_nonneg_right hM_le2 hn_nn)
            have h2 : vol0 n ≤ (δ / 8) * n :=
              le_trans hB (mul_le_mul_of_nonneg_right (by linarith) hn_nn)
            have h3 : (δ / 2) * n + (δ / 8) * n ≤ δ * n := by nlinarith [mul_nonneg hδ_pos.le hn_nn]
            linarith
          have hUp := rmin_clean_upper (n := n) (k := k) (alpha := alpha)
            (sizeSlack := sizeSlack) (C0 := C0) (vn := vol0 n) (lo := lo) (hi := hi)
            hn1 hC0_pos hk1 hk2 hlo_pos hlohi hhi_lt h_alpha_lo h_alpha_hi h_s0 hvol0n
            hinv (fun t ht => (hvol0 n t ht).1) hlogU hfit
          have hLo := rmin_clean_lower (n := n) (k := k) (alpha := alpha)
            (sizeSlack := sizeSlack) (C0 := C0) (vn := vol0 n) (lo := lo) (hi := hi)
            (alphaMin := alphaMin)
            hn1 hC0_pos hk1 hk2 hlo_pos hlohi hhi_lt h_alpha_lo h_alpha_hi h_s0 hvol0n
            hinv (fun t ht => (hvol0 n t ht).2) hlogL (by rw [hlo_def]; linarith) h_aM
            (by linarith) (by rw [← hδ_def]; exact hgap)
          rw [abs_le, hE_eq]
          have hCsCV : C0 * sizeSlack ≤ C_V * sizeSlack :=
            mul_le_mul_of_nonneg_right hCV_C0 h_s0
          exact ⟨by linarith [hLo, hCsCV], by linarith [hUp, hCsCV]⟩
  · -- Degenerate case: no admissible `alpha` exists.
    refine ⟨1, le_refl 1, fun _ => 0, Sublinear_const (le_refl 0), ?_⟩
    intro n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
    exfalso
    apply hcase
    have hbeta0 : 0 ≤ beta := by rw [h_beta]; positivity
    linarith

/-
If `Real.log` of a ball cardinality is within `vol` of `H(m/n)*n`, and `H`
is `L`-Lipschitz on `[lo,hi]` containing both `m/n` and `gamma`, then
`Real.log` of the ball is within `L*|m - gamma*n| + vol` of `H gamma * n`.
-/
lemma log_ball_approx {n m : ℕ} {gamma vol L lo hi : ℝ}
    (hn : 1 ≤ n) (_hL0 : 0 ≤ L)
    (hlip : ∀ x y : ℝ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi → |H x - H y| ≤ L * |x - y|)
    (hballL : H ((m : ℝ) / n) * n - vol ≤ Real.log ((ball (∅ : Cube n) m).card))
    (hballU : Real.log ((ball (∅ : Cube n) m).card) ≤ H ((m : ℝ) / n) * n + vol)
    (hm_lo : lo ≤ (m : ℝ) / n) (hm_hi : (m : ℝ) / n ≤ hi)
    (hg_lo : lo ≤ gamma) (hg_hi : gamma ≤ hi) :
    |Real.log ((ball (∅ : Cube n) m).card) - H gamma * n| ≤
      L * |(m : ℝ) - gamma * n| + vol := by
        have := hlip ( m / n ) gamma hm_lo hm_hi hg_lo hg_hi;
        rw [ abs_le ] at *;
        rw [ show ( m : ℝ ) - gamma * n = n * ( m / n - gamma ) by rw [ mul_sub, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; rw [ abs_mul, abs_of_nonneg ( by positivity : ( 0 :ℝ ) ≤ n ) ] ; constructor <;> nlinarith [ show ( n :ℝ ) ≥ 1 by norm_cast ] ;

/-
Trivial two-sided bound: `Real.log (V n k r)` and `H gamma * n` both lie in
`[0, n * log 2]`, so their difference is at most `n * log 2`.
-/
lemma V_log_trivial {n k r : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 2 ^ n) {gamma : ℝ}
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    |Real.log ((V n k r : ℝ)) - H gamma * n| ≤ (n : ℝ) * Real.log 2 := by
      rw [ abs_sub_le_iff ];
      constructor;
      · have hV_le : (V n k r : ℝ) ≤ 2 ^ n := by
          convert V_le_ball_rmin_add n k r hk2 |> le_trans <| card_cube_le _ using 1;
          norm_cast;
        have := Real.log_le_log ( Nat.cast_pos.mpr <| show 0 < V n k r from ?_ ) hV_le;
        · rw [ Real.log_pow ] at this ; nlinarith [ show 0 ≤ H gamma by exact Real.binEntropy_nonneg hg0 hg1 ];
        · obtain ⟨ t, ht ⟩ := vplus_skeleton n k r hk1 hk2;
          exact Nat.cast_pos.mp ( lt_of_lt_of_le ( Nat.cast_pos.mpr ( ball_card_pos _ _ ) ) ht.2.2.2 );
      · refine' le_trans ( sub_le_self _ ( Real.log_nonneg _ ) ) _;
        · have := vplus_skeleton n k r hk1 hk2;
          exact_mod_cast this.choose_spec.2.2.2.trans' ( Nat.cast_le.mpr ( ball_card_pos _ _ ) );
        · rw [ mul_comm ];
          exact mul_le_mul_of_nonneg_left ( Real.binEntropy_le_log_two ) ( Nat.cast_nonneg _ )

set_option maxHeartbeats 3200000 in
lemma interior_v_slack_exists :
  ∀ alphaMin c0 : ℝ, 0 < alphaMin → 0 < c0 →
    ∃ C_V : ℝ, 1 ≤ C_V ∧
    ∃ volumeSlack : ℕ → ℝ, Sublinear volumeSlack ∧
      ∀ n k r : ℕ, ∀ alpha beta sizeSlack : ℝ,
        alphaMin ≤ alpha → alpha ≤ 1 / 2 →
        0 ≤ sizeSlack →
        beta = (r : ℝ) / (n : ℝ) →
        alpha + beta ≤ 1 / 2 - c0 →
        1 ≤ k → k ≤ 2 ^ n →
        |Real.log ((k : ℝ)) - H alpha * (n : ℝ)| ≤ sizeSlack →
        |Real.log ((V n k r : ℝ)) - H (alpha + beta) * (n : ℝ)| ≤
            C_V * sizeSlack + volumeSlack n := by
  intro alphaMin c0 halphaMin hc0
  by_cases hcase : alphaMin ≤ 1 / 2 - c0
  ·
    set lo := alphaMin / 2 with hlo_def
    set hi := 1 / 2 - c0 / 2 with hhi_def
    have hlo_pos : 0 < lo := by rw [hlo_def]; linarith
    have hhi_lt1 : hi < 1 := by rw [hhi_def]; linarith
    have hlohi : lo ≤ hi := by rw [hlo_def, hhi_def]; linarith
    obtain ⟨C1, hC1, vol1, hvol1_sub, hrmin⟩ :=
      interior_rmin_slack_exists alphaMin c0 halphaMin hc0
    have hC1pos : 0 < C1 := by linarith
    obtain ⟨L, hL0, hlip⟩ := entropy_lipschitz lo hi hlo_pos hhi_lt1 hlohi
    obtain ⟨vol0, hvol0_sub, hvol0⟩ := ball_volume_two_sided_skeleton
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hHaM_pos : 0 < H alphaMin := Real.binEntropy_pos halphaMin (by
      rw [hlo_def] at hlohi; linarith)
    set η := min (c0 / 2) (alphaMin / 2) with hη_def
    have hη_pos : 0 < η := lt_min (by linarith) (by linarith)
    have hη_le1 : η ≤ c0 / 2 := min_le_left _ _
    have hη_le2 : η ≤ alphaMin / 2 := min_le_right _ _
    set C_V := max 1 (max (L * C1) (max (2 * C1 * Real.log 2 / η) (Real.log 2 / H alphaMin)))
      with hCV_def
    have hCV1 : (1 : ℝ) ≤ C_V := le_max_left _ _
    have hCV_LC1 : L * C1 ≤ C_V :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hCV_slack : 2 * C1 * Real.log 2 / η ≤ C_V :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hCV_logHaM : Real.log 2 / H alphaMin ≤ C_V :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    obtain ⟨NA, hNA⟩ := hvol1_sub.2 (η / 4) (by linarith)
    obtain ⟨NC, hNC⟩ := exists_nat_ge (4 / η)
    set N0 := max NA (max NC 1) + 1 with hN0_def
    have hN0_ge1 : 1 ≤ N0 := by omega
    have hN0v : ∀ n : ℕ, N0 ≤ n → vol1 n + 1 ≤ (η / 2) * n := by
      intro n hn
      have hnA : NA ≤ n := by omega
      have hnC : NC ≤ n := by omega
      have hv : vol1 n ≤ (η / 4) * n := hNA n hnA
      have hcn : (4 : ℝ) / η ≤ (n : ℝ) := le_trans hNC (by exact_mod_cast hnC)
      have h1 : (1 : ℝ) ≤ (η / 4) * n := by
        rw [div_le_iff₀ hη_pos] at hcn; nlinarith
      linarith
    refine ⟨C_V, hCV1,
      fun n => L * vol1 n + vol0 n + (L + 1) + (if n < N0 then (n : ℝ) * Real.log 2 else 0),
      ?_, ?_⟩
    · apply Sublinear_add
      · apply Sublinear_add
        · apply Sublinear_add
          · exact Sublinear_smul hL0 hvol1_sub
          · exact hvol0_sub
        · exact Sublinear_const (by linarith)
      · refine Sublinear_of_eventually_zero (fun n => ?_) N0 (fun n hn => by simp [Nat.not_lt.mpr hn])
        split_ifs with h
        · positivity
        · exact le_refl 0
    · intro n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hbeta0 : 0 ≤ beta := by rw [h_beta]; positivity
      have hab_le : alpha + beta ≤ 1 / 2 - c0 := h_sum
      have hab0 : 0 ≤ alpha + beta := by linarith
      have hab1 : alpha + beta ≤ 1 := by linarith
      have hab_lo : lo ≤ alpha + beta := by rw [hlo_def]; linarith
      have hab_hi : alpha + beta ≤ hi := by rw [hhi_def]; linarith
      set s := rmin n k with hs_def
      set G := H (alpha + beta) * (n : ℝ) with hG_def
      set U := Real.log ((V n k r : ℝ)) with hU_def
      set volS := L * vol1 n + vol0 n + (L + 1) + (if n < N0 then (n : ℝ) * Real.log 2 else 0)
        with hvolS_def
      show |U - G| ≤ C_V * sizeSlack + volS
      -- V is between `1` and `2^n`.
      have hVle : V n k r ≤ (ball (∅ : Cube n) (s + r)).card := V_le_ball_rmin_add n k r hk2
      obtain ⟨t, ht_le, ht_ball_le, ht_max, ht_lower⟩ := vplus_skeleton n k r hk1 hk2
      have hV_ge1 : (1 : ℝ) ≤ (V n k r : ℝ) :=
        le_trans (by exact_mod_cast ball_card_pos n (t + r)) ht_lower
      have hVpos : (0 : ℝ) < (V n k r : ℝ) := by linarith
      have htriv : |U - G| ≤ (n : ℝ) * Real.log 2 := V_log_trivial hk1 hk2 hab0 hab1
      have hvolS_nn : 0 ≤ volS := by
        rw [hvolS_def]
        have : 0 ≤ (if n < N0 then (n : ℝ) * Real.log 2 else 0) := by
          split_ifs with h
          · positivity
          · exact le_refl 0
        have := hvol1_sub.1 n; have := hvol0_sub.1 n
        nlinarith [mul_nonneg hL0 (hvol1_sub.1 n)]
      have hCVs0 : 0 ≤ C_V * sizeSlack := mul_nonneg (by linarith) h_s0
      by_cases hn_small : n < N0
      · -- Burn-in regime: the trivial bound is absorbed by the bump term.
        have hbump : (if n < N0 then (n : ℝ) * Real.log 2 else 0) = (n : ℝ) * Real.log 2 :=
          if_pos hn_small
        have : (n : ℝ) * Real.log 2 ≤ volS := by
          rw [hvolS_def, hbump]
          nlinarith [mul_nonneg hL0 (hvol1_sub.1 n), hvol0_sub.1 n, hL0]
        linarith [htriv, this]
      · have hnN0 : N0 ≤ n := Nat.not_lt.mp hn_small
        have hn1 : 1 ≤ n := le_trans hN0_ge1 hnN0
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
        have hbump0 : (if n < N0 then (n : ℝ) * Real.log 2 else 0) = 0 := if_neg hn_small
        have hvolS_eq : volS = L * vol1 n + vol0 n + (L + 1) := by rw [hvolS_def, hbump0]; ring
        have hN0prop : vol1 n + 1 ≤ (η / 2) * n := hN0v n hnN0
        by_cases hs0case : s = 0
        · -- `rmin n k = 0` forces `k = 1`, so the size slack itself dominates.
          have hb0 : (ball (∅ : Cube n) 0).card = 1 := by
            simp [ball_empty_card_eq_binomPrefix, binomPrefix]
          have hk_le1 : k ≤ 1 := by
            have := rmin_spec hk2; rw [← hs_def, hs0case, hb0] at this; exact this
          have hk_eq : k = 1 := le_antisymm hk_le1 hk1
          have hlogk0 : Real.log ((k : ℝ)) = 0 := by rw [hk_eq]; simp
          have hHan : H alpha * n ≤ sizeSlack := by
            have := (abs_le.mp h_log).1; rw [hlogk0] at this; linarith
          have hHaM_le : H alphaMin ≤ H alpha := H_le_H (by linarith) h_aM h_ah
          have h1 : H alphaMin * n ≤ sizeSlack :=
            le_trans (mul_le_mul_of_nonneg_right hHaM_le hn_nn) hHan
          have h3 : (n : ℝ) * Real.log 2 ≤ (Real.log 2 / H alphaMin) * sizeSlack := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hHaM_pos]; nlinarith [h1, hlog2_pos]
          have h4 : (Real.log 2 / H alphaMin) * sizeSlack ≤ C_V * sizeSlack :=
            mul_le_mul_of_nonneg_right hCV_logHaM h_s0
          linarith [htriv, h3, h4, hvolS_nn]
        · have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0case
          have herr : |(s : ℝ) - alpha * n| ≤ C1 * sizeSlack + vol1 n :=
            hrmin n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
          set errRHS := C1 * sizeSlack + vol1 n with herrRHS_def
          by_cases hclean : errRHS + 1 ≤ η * n
          · -- Clean interior regime.
            have hbetan : beta * (n : ℝ) = r := by rw [h_beta]; field_simp
            have herr' := abs_le.mp herr
            -- Location of `(s+r)/n` and `(s-1+r)/n` inside `[lo, hi]`.
            have hsr_ratio_hi : ((s + r : ℕ) : ℝ) / n ≤ hi := by
              rw [div_le_iff₀ hnpos]; push_cast
              rw [hhi_def]; nlinarith [herr'.2, hbetan, hη_le1]
            have hsr_ratio_lo : lo ≤ ((s + r : ℕ) : ℝ) / n := by
              rw [le_div_iff₀ hnpos]; push_cast
              rw [hlo_def]; nlinarith [herr'.1, hbetan, hη_le2]
            have hs1r_ratio_hi : ((s - 1 + r : ℕ) : ℝ) / n ≤ hi := by
              rw [div_le_iff₀ hnpos]
              rw [Nat.cast_add, Nat.cast_sub hs1, Nat.cast_one]
              rw [hhi_def]; nlinarith [herr'.2, hbetan, hη_le1]
            have hs1r_ratio_lo : lo ≤ ((s - 1 + r : ℕ) : ℝ) / n := by
              rw [le_div_iff₀ hnpos]
              rw [Nat.cast_add, Nat.cast_sub hs1, Nat.cast_one]
              rw [hlo_def]; nlinarith [herr'.1, hbetan, hη_le2]
            have hsr_half : s + r ≤ n / 2 := by
              rw [Nat.le_div_iff_mul_le (by norm_num)]
              have : ((s + r : ℕ) : ℝ) ≤ hi * n := by
                rw [← div_le_iff₀ hnpos]; exact hsr_ratio_hi
              have h2 : ((s + r : ℕ) : ℝ) * 2 < n := by nlinarith [hhi_lt1, hhi_def, this]
              exact_mod_cast le_of_lt (by exact_mod_cast h2)
            have hs1r_half : s - 1 + r ≤ n / 2 := le_trans (by omega) hsr_half
            -- Logarithmic two-sided ball bounds.
            have logball : ∀ m : ℕ, m ≤ n / 2 →
                H ((m : ℝ) / n) * n - vol0 n ≤ Real.log ((ball (∅ : Cube n) m).card) ∧
                Real.log ((ball (∅ : Cube n) m).card) ≤ H ((m : ℝ) / n) * n + vol0 n := by
              intro m hm
              obtain ⟨hlo', hhi'⟩ := hvol0 n m hm
              refine ⟨?_, ?_⟩
              · calc H ((m : ℝ) / n) * n - vol0 n
                    = Real.log (Real.exp (H ((m : ℝ) / n) * n - vol0 n)) := (Real.log_exp _).symm
                  _ ≤ Real.log ((ball (∅ : Cube n) m).card) :=
                      Real.log_le_log (Real.exp_pos _) hlo'
              · calc Real.log ((ball (∅ : Cube n) m).card)
                    ≤ Real.log (Real.exp (H ((m : ℝ) / n) * n + vol0 n)) :=
                      Real.log_le_log (by exact_mod_cast ball_card_pos n m) hhi'
                  _ = H ((m : ℝ) / n) * n + vol0 n := Real.log_exp _
            -- Upper bound on `U`.
            obtain ⟨hbL_u, hbU_u⟩ := logball (s + r) hsr_half
            have hUp := log_ball_approx (n := n) (m := s + r) (gamma := alpha + beta)
              (vol := vol0 n) (L := L) (lo := lo) (hi := hi) hn1 hL0 hlip hbL_u hbU_u
              hsr_ratio_lo hsr_ratio_hi hab_lo hab_hi
            have heq_u : |((s + r : ℕ) : ℝ) - (alpha + beta) * n| = |(s : ℝ) - alpha * n| := by
              congr 1; push_cast; rw [add_mul, hbetan]; ring
            rw [heq_u] at hUp
            have hlogVle : U ≤ Real.log ((ball (∅ : Cube n) (s + r)).card) := by
              rw [hU_def]; exact Real.log_le_log hVpos (by exact_mod_cast hVle)
            -- Lower bound on `U`.
            obtain ⟨hbL_l, hbU_l⟩ := logball (s - 1 + r) hs1r_half
            have hLo := log_ball_approx (n := n) (m := s - 1 + r) (gamma := alpha + beta)
              (vol := vol0 n) (L := L) (lo := lo) (hi := hi) hn1 hL0 hlip hbL_l hbU_l
              hs1r_ratio_lo hs1r_ratio_hi hab_lo hab_hi
            have heq_l : |((s - 1 + r : ℕ) : ℝ) - (alpha + beta) * n| = |(s : ℝ) - 1 - alpha * n| := by
              congr 1; rw [Nat.cast_add, Nat.cast_sub hs1, Nat.cast_one, add_mul, hbetan]; ring
            rw [heq_l] at hLo
            have hs1_le_t : s - 1 ≤ t :=
              ht_max (s - 1) (by omega)
                (le_of_lt (ball_card_lt_of_lt_rmin (by omega : s - 1 < s)))
            have hball_mono : (ball (∅ : Cube n) (s - 1 + r)).card ≤ (ball (∅ : Cube n) (t + r)).card :=
              Finset.card_le_card (ball_subset_ball_of_le (by omega))
            have hlogVge : Real.log ((ball (∅ : Cube n) (s - 1 + r)).card) ≤ U := by
              rw [hU_def]
              exact Real.log_le_log (by exact_mod_cast ball_card_pos n (s - 1 + r))
                (le_trans (by exact_mod_cast hball_mono) ht_lower)
            -- Shift bound: `|s - 1 - alpha*n| ≤ errRHS + 1`.
            have hshift : |(s : ℝ) - 1 - alpha * n| ≤ errRHS + 1 := by
              rw [abs_le]; rw [herrRHS_def]; constructor <;> linarith [herr'.1, herr'.2]
            -- Combine into a two-sided estimate.
            have habs : |U - G| ≤ L * (errRHS + 1) + vol0 n := by
              rw [abs_le]
              refine ⟨?_, ?_⟩
              · have h1 : Real.log ((ball (∅ : Cube n) (s - 1 + r)).card) - G ≥
                    -(L * (errRHS + 1) + vol0 n) := by
                  have := (abs_le.mp hLo).1
                  have hle : L * |(s : ℝ) - 1 - alpha * n| ≤ L * (errRHS + 1) :=
                    mul_le_mul_of_nonneg_left hshift hL0
                  rw [hG_def]; linarith
                linarith [hlogVge]
              · have hle : L * |(s : ℝ) - alpha * n| ≤ L * (errRHS + 1) :=
                  mul_le_mul_of_nonneg_left (by rw [herrRHS_def]; linarith [herr'.1, herr'.2, abs_le.mpr ⟨herr'.1, herr'.2⟩]) hL0
                have := (abs_le.mp hUp).2
                rw [hG_def]; linarith [hlogVle]
            -- Absorb into `C_V * sizeSlack + volS`.
            have hfinal : L * (errRHS + 1) + vol0 n ≤ C_V * sizeSlack + volS := by
              rw [hvolS_eq, herrRHS_def]
              have hmul : L * C1 * sizeSlack ≤ C_V * sizeSlack :=
                mul_le_mul_of_nonneg_right hCV_LC1 h_s0
              nlinarith [hmul, hL0]
            exact le_trans habs hfinal
          · -- Non-clean regime with `n ≥ N0`: the size slack is large.
            push_neg at hclean
            have hbig : (η / 2) * n < C1 * sizeSlack := by
              rw [herrRHS_def] at hclean; linarith [hN0prop]
            have hss : (η / (2 * C1)) * n < sizeSlack := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hbig]
            have hcoef_nn : 0 ≤ 2 * C1 * Real.log 2 / η := by positivity
            have hb2 : (2 * C1 * Real.log 2 / η) * ((η / (2 * C1)) * n) ≤
                (2 * C1 * Real.log 2 / η) * sizeSlack :=
              mul_le_mul_of_nonneg_left hss.le hcoef_nn
            have hb3 : (2 * C1 * Real.log 2 / η) * ((η / (2 * C1)) * n) = (n : ℝ) * Real.log 2 := by
              field_simp
            have hb4 : (2 * C1 * Real.log 2 / η) * sizeSlack ≤ C_V * sizeSlack :=
              mul_le_mul_of_nonneg_right hCV_slack h_s0
            have : (n : ℝ) * Real.log 2 ≤ C_V * sizeSlack := by
              rw [← hb3]; linarith [hb2, hb4]
            linarith [htriv, this, hvolS_nn]
  · -- Degenerate case: no admissible `alpha` exists.
    refine ⟨1, le_refl 1, fun _ => 0, Sublinear_const (le_refl 0), ?_⟩
    intro n k r alpha beta sizeSlack h_aM h_ah h_s0 h_beta h_sum hk1 hk2 h_log
    exfalso
    apply hcase
    have hbeta0 : 0 ≤ beta := by rw [h_beta]; positivity
    linarith

theorem interior_volume_calculus_skeleton : InteriorVolumeCalculusStatement := by
  intro alphaMin c0 halphaMin hc0
  obtain ⟨C_V1, hC_V1, volumeSlack1, hSub1, hV⟩ := interior_v_slack_exists alphaMin c0 halphaMin hc0
  obtain ⟨C_V2, hC_V2, volumeSlack2, hSub2, hrmin⟩ := interior_rmin_slack_exists alphaMin c0 halphaMin hc0
  use max C_V1 C_V2
  constructor
  · exact le_max_of_le_left hC_V1
  · use fun n => volumeSlack1 n + volumeSlack2 n
    constructor
    · constructor
      · intro n
        exact add_nonneg (hSub1.1 n) (hSub2.1 n)
      · intro ε hε
        obtain ⟨N1, hN1⟩ := hSub1.2 (ε / 2) (half_pos hε)
        obtain ⟨N2, hN2⟩ := hSub2.2 (ε / 2) (half_pos hε)
        use max N1 N2
        intro n hn
        have hn1 : n ≥ N1 := le_trans (le_max_iff.mpr (Or.inl le_rfl)) hn
        have hn2 : n ≥ N2 := le_trans (le_max_iff.mpr (Or.inr le_rfl)) hn
        linarith [hN1 n hn1, hN2 n hn2]
    · intro n k r alpha beta sizeSlack halpha1 halpha2 hsizeSlack hbeta hsum hk1 hk2 hlog
      constructor
      · exact (hV n k r alpha beta sizeSlack halpha1 halpha2 hsizeSlack hbeta hsum hk1 hk2 hlog).trans (by
          have h1 : C_V1 * sizeSlack ≤ max C_V1 C_V2 * sizeSlack := mul_le_mul_of_nonneg_right (le_max_left C_V1 C_V2) hsizeSlack
          have h2 : volumeSlack1 n ≤ volumeSlack1 n + volumeSlack2 n := le_add_of_nonneg_right (hSub2.1 n)
          linarith)
      · exact (hrmin n k r alpha beta sizeSlack halpha1 halpha2 hsizeSlack hbeta hsum hk1 hk2 hlog).trans (by
          have h1 : C_V2 * sizeSlack ≤ max C_V1 C_V2 * sizeSlack := mul_le_mul_of_nonneg_right (le_max_right C_V1 C_V2) hsizeSlack
          have h2 : volumeSlack2 n ≤ volumeSlack1 n + volumeSlack2 n := le_add_of_nonneg_left (hSub1.1 n)
          linarith)

end HarperStability
