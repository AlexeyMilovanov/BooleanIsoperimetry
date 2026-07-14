import HarperStability.Entropy

namespace HarperStability

/-!
Core layer: S5--S7.

This worker uses the shared entropy toolkit and receives upstream
process/reduction stages as hypotheses.
-/

theorem predictableCenter_mem_iff {m : ℕ} (A : Finset (Cube m)) (x : Cube m)
    (t : Fin m) :
    t ∈ predictableCenter A x ↔
      (1 / 2 : ℝ) < rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x) := by
  simp [predictableCenter]

theorem averageBadStepsLE_mono_slack {m : ℕ} (A : Finset (Cube m))
    {q eps massSlack massSlack' : ℝ}
    (hSlack : massSlack ≤ massSlack') :
    averageBadStepsLE A q eps massSlack →
      averageBadStepsLE A q eps massSlack' := by
  unfold averageBadStepsLE
  intro h
  exact le_trans h (mul_le_mul_of_nonneg_right hSlack (by positivity))

theorem predictableCenter_not_mem_iff {m : ℕ} (A : Finset (Cube m)) (x : Cube m)
    (t : Fin m) :
    t ∉ predictableCenter A x ↔
      rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x) ≤ (1 / 2 : ℝ) := by
  rw [predictableCenter_mem_iff]
  exact not_lt

noncomputable def badStepSet {m : ℕ} (A : Finset (Cube m)) (q eps : ℝ)
    (x : Cube m) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter fun t =>
    eps ≤ |fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) - q|

theorem averageBadStepsLE_of_forall_badSteps_le {m : ℕ} (A : Finset (Cube m))
    (q eps K : ℝ)
    (hK : ∀ x ∈ A, ((badStepSet A q eps x).card : ℝ) ≤ K) :
    averageBadStepsLE A q eps K := by
  unfold averageBadStepsLE
  unfold badStepSet at hK
  have hsum :
      (∑ x ∈ A,
        (((Finset.univ : Finset (Fin m)).filter fun t =>
          eps ≤ |fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) - q|
        ).card : ℝ)) ≤ ∑ x ∈ A, K := by
    exact Finset.sum_le_sum (fun x hx => hK x hx)
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

theorem averageBadStepsLE_zero_of_forall_good {m : ℕ} (A : Finset (Cube m))
    (q eps : ℝ)
    (hgood : ∀ x ∈ A, ∀ t : Fin m,
      |fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) - q| < eps) :
    averageBadStepsLE A q eps 0 := by
  refine averageBadStepsLE_of_forall_badSteps_le A q eps 0 ?_
  intro x hx
  have hnone : (badStepSet A q eps x).card = 0 := by
    rw [badStepSet, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _
    exact not_le_of_gt (hgood x hx t)
  simp [hnone]

theorem heavyBallConclusion_of_log_card_le_slack {n : ℕ} {S : Finset (Cube n)}
    {massSlack : ℝ} (radiusSlack : ℕ)
    (hS : S.Nonempty) (hlog : Real.log (S.card : ℝ) ≤ massSlack) :
    heavyBallConclusion n S massSlack radiusSlack := by
  rcases hS with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hmass : Real.exp (-massSlack) * (S.card : ℝ) ≤ 1 := by
    have hcard_pos : 0 < (S.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨a, ha⟩)
    have hcard_le_exp : (S.card : ℝ) ≤ Real.exp massSlack := by
      exact (Real.log_le_iff_le_exp hcard_pos).mp hlog
    have hmul :
        Real.exp (-massSlack) * (S.card : ℝ) ≤
          Real.exp (-massSlack) * Real.exp massSlack := by
      exact mul_le_mul_of_nonneg_left hcard_le_exp (le_of_lt (Real.exp_pos _))
    have hexp : Real.exp (-massSlack) * Real.exp massSlack = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    simpa [hexp] using hmul
  have hmem : a ∈ S.filter (fun x => hDist x a ≤ rmin n S.card + radiusSlack) := by
    simp [ha, hDist]
  have hfilter_pos :
      0 < (S.filter fun x => hDist x a ≤ rmin n S.card + radiusSlack).card :=
    Finset.card_pos.mpr ⟨a, hmem⟩
  have hfilter_ge_one :
      (1 : ℝ) ≤
        (((S.filter fun x => hDist x a ≤ rmin n S.card + radiusSlack).card : ℕ) : ℝ) := by
    exact_mod_cast hfilter_pos
  exact hmass.trans hfilter_ge_one

theorem badStepSet_subset_of_eps_le {m : ℕ} (A : Finset (Cube m))
    {q eps eps' : ℝ} (x : Cube m) (heps : eps ≤ eps') :
    badStepSet A q eps' x ⊆ badStepSet A q eps x := by
  intro t ht
  simp only [badStepSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  exact heps.trans ht

theorem badStepSet_card_mono_eps {m : ℕ} (A : Finset (Cube m))
    {q eps eps' : ℝ} (x : Cube m) (heps : eps ≤ eps') :
    ((badStepSet A q eps' x).card : ℝ) ≤ ((badStepSet A q eps x).card : ℝ) := by
  have hcard :
      (badStepSet A q eps' x).card ≤ (badStepSet A q eps x).card :=
    Finset.card_le_card (badStepSet_subset_of_eps_le A x heps)
  exact_mod_cast hcard

theorem averageBadStepsLE_mono_eps {m : ℕ} (A : Finset (Cube m))
    {q eps eps' massSlack : ℝ} (heps : eps ≤ eps') :
    averageBadStepsLE A q eps massSlack →
      averageBadStepsLE A q eps' massSlack := by
  unfold averageBadStepsLE
  change
    (∑ x ∈ A, ((badStepSet A q eps x).card : ℝ)) ≤
        massSlack * (A.card : ℝ) →
      (∑ x ∈ A, ((badStepSet A q eps' x).card : ℝ)) ≤
        massSlack * (A.card : ℝ)
  intro h
  have hsum :
      (∑ x ∈ A, ((badStepSet A q eps' x).card : ℝ)) ≤
        ∑ x ∈ A, ((badStepSet A q eps x).card : ℝ) := by
    exact Finset.sum_le_sum fun x _ => badStepSet_card_mono_eps A x heps
  exact hsum.trans h

theorem badStepSet_card_le_dim {m : ℕ} (A : Finset (Cube m)) (q eps : ℝ)
    (x : Cube m) :
    ((badStepSet A q eps x).card : ℝ) ≤ (m : ℝ) := by
  have hcard : (badStepSet A q eps x).card ≤ m := by
    simpa [Fintype.card_fin] using (badStepSet A q eps x).card_le_univ
  exact_mod_cast hcard

theorem averageBadStepsLE_dim_bound {m : ℕ} (A : Finset (Cube m))
    (q eps : ℝ) :
    averageBadStepsLE A q eps (m : ℝ) := by
  refine averageBadStepsLE_of_forall_badSteps_le A q eps (m : ℝ) ?_
  intro x _
  exact badStepSet_card_le_dim A q eps x

theorem hDist_self_eq_zero {m : ℕ} (x : Cube m) :
    hDist x x = 0 := by
  simp [hDist]

theorem hDist_eq_card_filter_mem_ne {m : ℕ} (x y : Cube m) :
    hDist x y =
      ((Finset.univ : Finset (Fin m)).filter fun t => (t ∈ x) ≠ (t ∈ y)).card := by
  unfold hDist
  apply congrArg Finset.card
  ext t
  by_cases hx : t ∈ x <;> by_cases hy : t ∈ y <;>
    simp [Finset.mem_symmDiff, hx, hy]

theorem hDist_predictableCenter_eq_card_filter {m : ℕ} (A : Finset (Cube m))
    (x : Cube m) :
    hDist x (predictableCenter A x) =
      ((Finset.univ : Finset (Fin m)).filter fun t =>
        (t ∈ x) ≠
          ((1 / 2 : ℝ) <
            rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))).card := by
  rw [hDist_eq_card_filter_mem_ne]
  apply congrArg Finset.card
  ext t
  simp [predictableCenter_mem_iff]

theorem proj_eq_of_subset {m : ℕ} {I J : Finset (Fin m)} {x y : Cube m}
    (hIJ : I ⊆ J) (hxy : proj J x = proj J y) :
    proj I x = proj I y := by
  unfold proj at hxy ⊢
  ext t
  by_cases htI : t ∈ I
  · have htJ : t ∈ J := hIJ htI
    have hmem := congrArg (fun z : Cube m => t ∈ z) hxy
    simpa [htI, htJ] using hmem
  · simp [htI]

theorem dependsOnWindow_pi {m : ℕ} {B : Type*} {I : Finset (Fin m)}
    (F : Cube m → Fin m → B)
    (hcoord : ∀ t : Fin m, dependsOnWindow I (fun x => F x t)) :
    dependsOnWindow I F := by
  intro x y hxy
  funext t
  exact hcoord t x y hxy

theorem cube_eq_of_forall_coord_eq {m : ℕ} {x y : Cube m}
    (hcoord : ∀ t : Fin m, coord t x = coord t y) :
    x = y := by
  ext t
  specialize hcoord t
  dsimp only [coord] at hcoord
  by_cases hx : t ∈ x <;> by_cases hy : t ∈ y <;>
    simp [hx, hy] at hcoord ⊢

theorem cube_eq_iff_forall_coord_eq {m : ℕ} {x y : Cube m} :
    x = y ↔ ∀ t : Fin m, coord t x = coord t y := by
  constructor
  · intro h t
    rw [h]
  · exact cube_eq_of_forall_coord_eq

theorem binnedFoldField_coord_dependsOnWindow {m : ℕ} (A : Finset (Cube m))
    (w o : ℝ) (t : Fin m) :
    dependsOnWindow (below (Finset.univ : Finset (Fin m)) t)
      (fun x => binnedFoldField A w o x t) := by
  intro x y hxy
  unfold binnedFoldField
  simp [hxy]

theorem binnedFoldField_coord_dependsOnWindow_of_below_subset {m : ℕ}
    (A : Finset (Cube m)) (w o : ℝ) {I : Finset (Fin m)} (t : Fin m)
    (hbelow : below (Finset.univ : Finset (Fin m)) t ⊆ I) :
    dependsOnWindow I (fun x => binnedFoldField A w o x t) := by
  intro x y hxy
  exact binnedFoldField_coord_dependsOnWindow A w o t x y
    (proj_eq_of_subset hbelow hxy)

theorem predictableCenter_coord_dependsOnWindow {m : ℕ} (A : Finset (Cube m))
    (t : Fin m) :
    dependsOnWindow (below (Finset.univ : Finset (Fin m)) t)
      (fun x => coord t (predictableCenter A x)) := by
  intro x y hxy
  dsimp only [coord]
  simp only [predictableCenter_mem_iff, hxy]

theorem predictableCenter_coord_dependsOnWindow_of_below_subset {m : ℕ}
    (A : Finset (Cube m)) {I : Finset (Fin m)} (t : Fin m)
    (hbelow : below (Finset.univ : Finset (Fin m)) t ⊆ I) :
    dependsOnWindow I (fun x => coord t (predictableCenter A x)) := by
  intro x y hxy
  exact predictableCenter_coord_dependsOnWindow A t x y
    (proj_eq_of_subset hbelow hxy)

lemma uH_predictableCenter_le_coordField {m : ℕ} (A : Finset (Cube m)) :
  uH A (predictableCenter A) ≤
    uH A (fun x : Cube m => fun t : Fin m => coord t (predictableCenter A x)) := by
  classical
  let centerField : Cube m → Fin m → Bool :=
    fun x t => coord t (predictableCenter A x)
  let recover : (Fin m → Bool) → Cube m :=
    fun f => (Finset.univ : Finset (Fin m)).filter fun t => f t = true
  have hrecover : (fun x => recover (centerField x)) = predictableCenter A := by
    funext x
    ext t
    simp [recover, centerField, coord]
  calc
    uH A (predictableCenter A) = uH A (fun x => recover (centerField x)) := by
      rw [hrecover]
    _ ≤ uH A centerField := uH_comp_le A centerField recover

/-- `fold x = min x (1 - x) ≤ 1/2` for every real `x`, since
`min a b ≤ (a + b)/2`. -/
lemma fold_le_half (x : ℝ) : fold x ≤ 1 / 2 := by
  unfold fold
  rcases le_total x (1 - x) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-
Hamming distance as a sum of coordinate mismatch indicators.
-/
lemma hDist_eq_sum_indicator {m : ℕ} (x y : Cube m) :
    (hDist x y : ℝ)
      = ∑ t : Fin m, if coord t x = coord t y then (0 : ℝ) else 1 := by
  unfold hDist coord; simp +decide [ Finset.sum_ite ] ;
  exact congr_arg Finset.card ( by ext; simp +decide [ symmDiff ] ; tauto )

/-
Fiber-counting identity: within any fiber `F`, the number of points whose
`t`-coordinate disagrees with the majority prediction `decide (1/2 < pOn F (coord t) true)`
equals `|F| · fold (pOn F (coord t) true)`.  (Majority prediction errs with probability
`min(r, 1-r) = fold r`.)
-/
lemma fiber_error_card_eq {m : ℕ} (F : Finset (Cube m)) (t : Fin m) :
    ((F.filter fun x =>
        coord t x ≠ decide ((1 / 2 : ℝ) < pOn F (coord t) true)).card : ℝ)
      = (F.card : ℝ) * fold (pOn F (coord t) true) := by
  by_cases h : 1 / 2 < pOn F ( coord t ) true <;> simp +decide;
  · rw [ show fold ( pOn F ( coord t ) true ) = 1 - pOn F ( coord t ) true from _ ];
    · simp +decide [ coord, pOn ] at *;
      by_cases hF : F = ∅ <;> simp_all +decide [ mul_sub, mul_div_cancel₀ ];
      rw [ eq_sub_iff_add_eq', ← Nat.cast_add, Finset.card_filter_add_card_filter_not ];
    · exact min_eq_right ( by linarith );
  · simp_all +decide [ fold ];
    rw [ min_eq_left ];
    · rw [ mul_comm, pOn ];
      by_cases hF : F = ∅ <;> simp_all +decide;
      rw [ Finset.filter_congr fun x hx => by rw [ decide_eq_false ] ; aesop ];
      grind;
    · grind

/-
Per-coordinate averaging identity: summing the mismatch indicator against the
predictable center over `A` equals summing the fold of the prefix bias, via the
fiber-counting identity `fiber_error_card_eq` grouped over prefix windows.
-/
lemma sum_indicator_eq_sum_fold {m : ℕ} (A : Finset (Cube m)) (t : Fin m) :
    (∑ x ∈ A, if coord t x = coord t (predictableCenter A x) then (0 : ℝ) else 1)
      = ∑ x ∈ A,
          fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) := by
  -- Apply `fiber_error_card_eq` to each term in the sum.
  have h_fiber : ∀ w ∈ A.image (proj (below Finset.univ t)), (∑ x ∈ A.filter (fun x => proj (below Finset.univ t) x = w), (if coord t x = coord t (predictableCenter A x) then (0 : ℝ) else 1)) = (A.filter (fun x => proj (below Finset.univ t) x = w)).card * fold (rho A t w) := by
    intro w hw
    have h_fiber : ∀ x ∈ A.filter (fun x => proj (below Finset.univ t) x = w), coord t (predictableCenter A x) = decide ((1 / 2 : ℝ) < rho A t w) := by
      simp +contextual [ coord, predictableCenter_mem_iff ];
    have h_fiber_card : ((A.filter (fun x => proj (below Finset.univ t) x = w)).filter (fun x => coord t x ≠ decide ((1 / 2 : ℝ) < rho A t w))).card = (A.filter (fun x => proj (below Finset.univ t) x = w)).card * fold (pOn (A.filter (fun x => proj (below Finset.univ t) x = w)) (coord t) true) := by
      convert fiber_error_card_eq ( A.filter ( fun x => proj ( below Finset.univ t ) x = w ) ) t using 1;
    convert h_fiber_card using 1;
    simp +contextual [ Finset.sum_ite, h_fiber ];
  convert Finset.sum_congr rfl h_fiber using 1;
  · rw [ Finset.sum_image' ] ; aesop;
  · rw [ Finset.sum_image' ];
    intro x hx; rw [ Finset.sum_congr rfl fun y hy => by rw [ Finset.mem_filter.mp hy |>.2 ] ] ; simp +decide [ Finset.sum_const, nsmul_eq_mul ] ;

/-
Expected distance to the predictable center equals the expected total fold of
the prefix bias process.
-/
lemma uE_hDist_predictableCenter_eq_sum_fold {m : ℕ} (A : Finset (Cube m)) :
    uE A (fun x => (hDist x (predictableCenter A x) : ℝ))
      = uE A (fun x => ∑ t : Fin m,
          fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))) := by
  unfold uE;
  rw [ Finset.sum_congr rfl fun x hx => hDist_eq_sum_indicator x ( predictableCenter A x ) ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun t ht => sum_indicator_eq_sum_fold A t, Finset.sum_comm ]

/-
Per-point bound: the total fold over all coordinates is at most
`(q+eps)·m` plus the number of `eps`-bad coordinates.  Good coordinates satisfy
`fold < q+eps`; bad coordinates satisfy the crude bound
`fold ≤ 1/2 ≤ (q+eps)+1`.
-/
lemma sum_fold_le_add_badSteps {m : ℕ} (A : Finset (Cube m)) {q eps : ℝ}
    (hq : 0 ≤ q) (heps : 0 ≤ eps) (x : Cube m) :
    (∑ t : Fin m,
        fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)))
      ≤ (q + eps) * (m : ℝ)
        + (((Finset.univ : Finset (Fin m)).filter fun t =>
            eps ≤ |fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
              - q|).card : ℝ) := by
  convert Finset.sum_le_sum fun i _ => ?_ using 1;
  rotate_left;
  use fun i => ( q + eps ) + if eps ≤ |fold ( rho A i ( proj ( below Finset.univ i ) x ) ) - q| then 1 else 0;
  · infer_instance;
  · split_ifs <;> cases abs_cases ( fold ( rho A i ( proj ( below Finset.univ i ) x ) ) - q ) <;> linarith [ fold_le_half ( rho A i ( proj ( below Finset.univ i ) x ) ) ];
  · simp +decide [ Finset.sum_add_distrib ];
    ring
/- Corrected distance-to-center bound.  Compared with the rejected earlier leaf,
this adds the faithful hypotheses `0 ≤ q` and `0 ≤ eps` (without which the
statement is false).  Proof: rewrite the expectation via
`uE_hDist_predictableCenter_eq_sum_fold`, bound each point via
`sum_fold_le_add_badSteps`, and use `hPF` (with `b ≥ 0` deduced from the
nonnegative left-hand side of `averageBadStepsLE`).
-/
lemma uE_hDist_predictableCenter_le_of_averageBadStepsLE {m : ℕ} (A : Finset (Cube m))
  {q eps b : ℝ}
  (hA : A.Nonempty) (hq : 0 ≤ q) (heps : 0 ≤ eps) (_hqeps : q + eps ≤ 1 / 2)
  (hPF : averageBadStepsLE A q eps b) :
  uE A (fun x => (hDist x (predictableCenter A x) : ℝ)) ≤
    (q + eps) * (m : ℝ) + b := by
  rw [ HarperStability.uE_hDist_predictableCenter_eq_sum_fold A ];
  convert div_le_div_of_nonneg_right ( show ( ∑ x ∈ A, ∑ t : Fin m, fold ( rho A t ( proj ( below Finset.univ t ) x ) ) ) ≤ ( q + eps ) * m * A.card + b * A.card from ?_ ) ( Nat.cast_nonneg _ ) using 1;
  · rw [ eq_div_iff ] <;> ring_nf ; aesop;
  · refine' le_trans ( Finset.sum_le_sum fun x hx => HarperStability.sum_fold_le_add_badSteps A hq heps x ) _;
    unfold averageBadStepsLE at hPF; simp_all +decide [ Finset.sum_add_distrib, mul_comm ] ;

/-
The chosen prefix-branch probability of a coordinate equals the ratio of
prefix-fiber cardinalities (agreement up to and including `t` over agreement
below `t`).  Valid for any finite set `S` containing the reference point `x`,
so both fibers are nonempty.
-/
lemma rho_choose_eq_card_ratio {m : ℕ} (S : Finset (Cube m)) (t : Fin m) (x : Cube m)
    (hx : x ∈ S) :
    (if coord t x then rho S t (proj (below (Finset.univ : Finset (Fin m)) t) x)
      else 1 - rho S t (proj (below (Finset.univ : Finset (Fin m)) t) x))
    = ((S.filter (fun y => ∀ u : Fin m, u ≤ t → coord u y = coord u x)).card : ℝ)
      / ((S.filter (fun y => ∀ u : Fin m, u < t → coord u y = coord u x)).card : ℝ) := by
  split_ifs <;> simp_all +decide [ rho, pOn ];
  · congr! 3;
    · ext y; simp [proj, below];
      simp +decide [ Finset.ext_iff, coord ] at *;
      grind;
    · ext y; simp [proj, below];
      simp +decide [ Finset.ext_iff, coord ];
  · rw [ one_sub_div, div_eq_div_iff ];
    · rw [ show ( Finset.filter ( fun y => ∀ u ≤ t, coord u y = coord u x ) S ) = Finset.filter ( fun y => ∀ u < t, coord u y = coord u x ) S \ Finset.filter ( fun y => coord t y = true ) ( Finset.filter ( fun y => ∀ u < t, coord u y = coord u x ) S ) from ?_, Finset.card_sdiff ];
      · rw [ Nat.cast_sub ];
        · simp +decide [ Finset.filter_filter, Finset.inter_comm ];
          simp +decide [ Finset.filter_filter, Finset.filter_inter, Finset.inter_filter, Finset.ext_iff, proj, below ];
          simp +decide [ coord ];
        · exact Finset.card_le_card fun x hx => by aesop;
      · grind;
    · exact ne_of_gt <| Nat.cast_pos.mpr <| Finset.card_pos.mpr ⟨ x, by aesop ⟩;
    · exact ne_of_gt <| Nat.cast_pos.mpr <| Finset.card_pos.mpr ⟨ x, by aesop ⟩;
    · exact ne_of_gt <| Nat.cast_pos.mpr <| Finset.card_pos.mpr ⟨ x, by aesop ⟩

/-
Per-point telescoping of the log-likelihood ratio along the revelation
order: for `x ∈ B ⊆ A` the prefix-branch ratios multiply to `|A|/|B|`.
-/
lemma llr_telescope {m : ℕ} (A B : Finset (Cube m)) (hB : B ⊆ A)
    (hB_nonempty : B.Nonempty) (x : Cube m) (hxB : x ∈ B) :
    (∑ t : Fin m, Real.log (
      (((B.filter (fun y => ∀ u : Fin m, u ≤ t → coord u y = coord u x)).card : ℝ)
        / ((B.filter (fun y => ∀ u : Fin m, u < t → coord u y = coord u x)).card : ℝ))
      / (((A.filter (fun y => ∀ u : Fin m, u ≤ t → coord u y = coord u x)).card : ℝ)
        / ((A.filter (fun y => ∀ u : Fin m, u < t → coord u y = coord u x)).card : ℝ))))
    = Real.log ((A.card : ℝ) / (B.card : ℝ)) := by
  rw [ ← Real.log_prod ] <;> norm_num;
  · congr 1;
    rw [ div_div_div_comm, div_eq_div_iff ];
    · rw [ div_mul_eq_mul_div, mul_div, div_eq_div_iff ];
      · have h_telescope : ∀ (n : ℕ), n ≤ m → (∏ t ∈ Finset.univ.filter (fun t : Fin m => t.val < n), ((B.filter (fun y => ∀ u : Fin m, u < t → coord u y = coord u x)).card : ℝ)) * ((B.filter (fun y => ∀ u : Fin m, u.val < n → coord u y = coord u x)).card : ℝ) = (∏ t ∈ Finset.univ.filter (fun t : Fin m => t.val < n), ((B.filter (fun y => ∀ u : Fin m, u ≤ t → coord u y = coord u x)).card : ℝ)) * (B.card : ℝ) := by
          intro n hn;
          induction' n with n ih;
          · simp +decide ;
          · rw [ show ( Finset.univ.filter fun t : Fin m => ( t : ℕ ) < n + 1 ) = Finset.univ.filter ( fun t : Fin m => ( t : ℕ ) < n ) ∪ { ⟨ n, by linarith ⟩ } from ?_, Finset.prod_union ] <;> norm_num; all_goals grind;
        have h_telescope_A : ∀ (n : ℕ), n ≤ m → (∏ t ∈ Finset.univ.filter (fun t : Fin m => t.val < n), ((A.filter (fun y => ∀ u : Fin m, u < t → coord u y = coord u x)).card : ℝ)) * ((A.filter (fun y => ∀ u : Fin m, u.val < n → coord u y = coord u x)).card : ℝ) = (∏ t ∈ Finset.univ.filter (fun t : Fin m => t.val < n), ((A.filter (fun y => ∀ u : Fin m, u ≤ t → coord u y = coord u x)).card : ℝ)) * (A.card : ℝ) := by
          intro n hn
          induction' n with n ih;
          · simp +decide ;
          · rw [ show ( Finset.univ.filter fun t : Fin m => ( t : ℕ ) < n + 1 ) = Finset.univ.filter ( fun t : Fin m => ( t : ℕ ) < n ) ∪ { ⟨ n, by linarith ⟩ } from ?_, Finset.prod_union ] <;> norm_num;
            · convert congr_arg ( · * ( Finset.card ( Finset.filter ( fun y => ∀ u : Fin m, u ≤ ⟨ n, by linarith ⟩ → coord u y = coord u x ) A ) : ℝ ) ) ( ih ( Nat.le_of_succ_le hn ) ) using 1 ; ring!;
            · grind;
        have h_filter_eq : (B.filter (fun y => ∀ u : Fin m, u.val < m → coord u y = coord u x)) = {x} ∧ (A.filter (fun y => ∀ u : Fin m, u.val < m → coord u y = coord u x)) = {x} := by
          constructor <;> ext y <;> simp +decide [ Finset.mem_filter, Finset.mem_singleton ];
          · exact ⟨ fun h => cube_eq_of_forall_coord_eq h.2, fun h => h.symm ▸ ⟨ hxB, fun u => rfl ⟩ ⟩;
          · exact ⟨ fun h => cube_eq_of_forall_coord_eq h.2, fun h => h.symm ▸ ⟨ hB hxB, fun u => rfl ⟩ ⟩;
        specialize h_telescope m le_rfl; specialize h_telescope_A m le_rfl; simp_all +decide ;
        ring;
      · exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr ⟨ x, by aesop ⟩;
      · exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr ⟨ x, Finset.mem_filter.mpr ⟨ hB hxB, fun u hu => rfl ⟩ ⟩;
    · simp +zetaDelta at *;
      exact ⟨ Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr ⟨ x, by aesop ⟩, Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr ⟨ x, by aesop ⟩ ⟩;
    · exact Nat.cast_ne_zero.mpr hB_nonempty.card_pos.ne';
  · exact fun t => ⟨ ⟨ ⟨ x, hxB, fun u hu => rfl ⟩, ⟨ x, hxB, fun u hu => rfl ⟩ ⟩, ⟨ ⟨ x, hB hxB, fun u hu => rfl ⟩, ⟨ x, hB hxB, fun u hu => rfl ⟩ ⟩ ⟩

/-
Fiber-summed identity: summing over all `x ∈ B` (for a fixed coordinate
`t`) converts the fiber-averaged Bernoulli KL term into the log-likelihood
ratio using each point's own coordinate.  The pointwise equality is FALSE; it
only holds after summing over each prefix fiber.
-/
set_option maxHeartbeats 4000000 in
lemma fiber_sum_kl_eq_llr {m : ℕ} (A B : Finset (Cube m)) (hB : B ⊆ A) (t : Fin m) :
    (∑ x ∈ B,
      (let p := rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x)
       let q := rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
       p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))))
    = ∑ x ∈ B, Real.log (
        (((B.filter (fun y => ∀ u : Fin m, u ≤ t → coord u y = coord u x)).card : ℝ)
          / ((B.filter (fun y => ∀ u : Fin m, u < t → coord u y = coord u x)).card : ℝ))
        / (((A.filter (fun y => ∀ u : Fin m, u ≤ t → coord u y = coord u x)).card : ℝ)
          / ((A.filter (fun y => ∀ u : Fin m, u < t → coord u y = coord u x)).card : ℝ))) := by
  by_contra h_contra;
  have h_fiber_sum : ∀ w ∈ Finset.image (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x) B, ∑ x ∈ B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w), (let p := rho B t w; let q := rho A t w; p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) = ∑ x ∈ B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w), Real.log ((if coord t x then rho B t w else 1 - rho B t w) / (if coord t x then rho A t w else 1 - rho A t w)) := by
    intro w hw
    have h_fiber_sum : (let p := rho B t w; let q := rho A t w; p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) * (B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w)).card = ∑ x ∈ B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w), Real.log ((if coord t x then rho B t w else 1 - rho B t w) / (if coord t x then rho A t w else 1 - rho A t w)) := by
      have h_fiber_sum : (let p := rho B t w; let q := rho A t w; p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) * (B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w)).card = (B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w ∧ coord t x)).card * Real.log (rho B t w / rho A t w) + (B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w ∧ ¬coord t x)).card * Real.log ((1 - rho B t w) / (1 - rho A t w)) := by
        have h_fiber_sum : (rho B t w) * (B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w)).card = (B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w ∧ coord t x)).card := by
          unfold rho pOn;
          by_cases h : Finset.card ( Finset.filter ( fun x => proj ( below Finset.univ t ) x = w ) B ) = 0 <;> simp_all +decide [ Finset.filter_filter ];
          · exact False.elim <| h hw.choose_spec.1 hw.choose_spec.2;
          · convert rfl;
        have h_fiber_sum : (1 - rho B t w) * (B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w)).card = (B.filter (fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w ∧ ¬coord t x)).card := by
          rw [ sub_mul, one_mul, h_fiber_sum ];
          rw [ sub_eq_iff_eq_add ] ; norm_cast ; rw [ ← Finset.card_union_of_disjoint ] ; congr ; ext ; by_cases h : coord t ‹_› <;> aesop;
          exact Finset.disjoint_filter.mpr ( by aesop );
        grind;
      convert h_fiber_sum using 1;
      rw [ Finset.card_filter, Finset.card_filter ];
      push_cast [ Finset.sum_filter ];
      rw [ Finset.sum_mul, Finset.sum_mul ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> aesop;
    simp_all +decide ;
    linarith;
  convert h_contra ?_;
  convert Finset.sum_congr rfl h_fiber_sum using 1;
  · rw [ Finset.sum_image' ];
    exact fun x hx => Finset.sum_congr rfl fun y hy => by aesop;
  · rw [ Finset.sum_image' ];
    intro x hx; refine' Finset.sum_congr rfl fun y hy => _; simp_all +decide ;
    rw [ ← hy.2, rho_choose_eq_card_ratio B t y hy.1, rho_choose_eq_card_ratio A t y ( hB hy.1 ) ]

lemma event_kl_chain_rule {m : ℕ} (A B : Finset (Cube m))
    (hB : B ⊆ A) (hB_nonempty : B.Nonempty) :
    (∑ t : Fin m, uE B (fun x =>
      let p := rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x)
      let q := rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))))
    ≤ Real.log ((A.card : ℝ) / (B.card : ℝ)) := by
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hB_nonempty
  have key :
      (∑ t : Fin m, uE B (fun x =>
        let p := rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x)
        let q := rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
        p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))))
      = Real.log ((A.card : ℝ) / (B.card : ℝ)) := by
    unfold uE
    rw [← Finset.sum_div]
    rw [Finset.sum_congr rfl (fun t _ => fiber_sum_kl_eq_llr A B hB t)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x hx => llr_telescope A B hB hB_nonempty x hx)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_assoc,
      div_self (ne_of_gt hBpos), mul_one]
  exact le_of_eq key

/-
Analytic Bernoulli Pinsker inequality: the Bernoulli relative entropy of
`p` w.r.t. an interior `q` dominates `2 (p - q)²`.
-/
set_option maxHeartbeats 4000000 in
lemma bernoulli_pinsker (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  -- Let's define the function $f(p) = p \log(p/q) + (1-p) \log((1-p)/(1-q)) - 2(p-q)^2$.
  set f : ℝ → ℝ := fun p => p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) - 2 * (p - q) ^ 2;
  -- We'll use the fact that $f(p)$ is convex on $[0, 1]$ and that $f(q) = 0$ and $f'(q) = 0$.
  have h_convex : ConvexOn ℝ (Set.Icc 0 1) f := by
    apply_rules [ convexOn_of_deriv2_nonneg, convex_Icc ];
    · refine' ContinuousOn.sub _ _;
      · refine' ContinuousOn.add _ _;
        · have h_cont : ContinuousOn (fun p => p * Real.log p - p * Real.log q) (Set.Icc 0 1) := by
            exact ContinuousOn.sub ( Real.continuous_mul_log.continuousOn ) ( continuousOn_id.mul continuousOn_const );
          refine' h_cont.congr fun x hx => _;
          by_cases hx' : x = 0 <;> simp +decide [ hx', Real.log_div, hq0.ne' ] ; ring;
        · refine' continuousOn_of_forall_continuousAt fun p hp => _;
          by_cases h : 1 - p = 0 <;> simp_all +decide [ ContinuousAt ];
          · have := Real.continuous_mul_log.tendsto ( 0 : ℝ );
            convert this.comp ( show Filter.Tendsto ( fun p : ℝ => ( 1 - p ) / ( 1 - q ) ) ( nhds p ) ( nhds 0 ) from Continuous.tendsto' ( by continuity ) _ _ <| by norm_num [ show p = 1 by linarith ] ) |> Filter.Tendsto.mul_const ( 1 - q ) using 2 <;> norm_num ; ring_nf;
            grind;
          · exact Filter.Tendsto.mul ( tendsto_const_nhds.sub Filter.tendsto_id ) ( Filter.Tendsto.log ( Filter.Tendsto.div_const ( tendsto_const_nhds.sub Filter.tendsto_id ) _ ) ( div_ne_zero h ( by linarith ) ) );
      · exact Continuous.continuousOn ( by continuity );
    · norm_num +zetaDelta at *;
      exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.sub ( DifferentiableAt.add ( DifferentiableAt.mul differentiableAt_id ( DifferentiableAt.log ( differentiableAt_id.div_const _ ) ( by exact div_ne_zero hx.1.ne' hq0.ne' ) ) ) ( DifferentiableAt.mul ( differentiableAt_id.const_sub _ ) ( DifferentiableAt.log ( by exact DifferentiableAt.div ( differentiableAt_id.const_sub _ ) ( differentiableAt_const _ ) ( by linarith ) ) ( by exact div_ne_zero ( by linarith [ hx.1, hx.2 ] ) ( by linarith ) ) ) ) ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( by norm_num ) ) ) ;
    · -- Let's calculate the first derivative of $f$.
      have h_deriv : ∀ p ∈ Set.Ioo 0 1, deriv f p = Real.log (p / q) - Real.log ((1 - p) / (1 - q)) - 4 * (p - q) := by
        intro p hp; norm_num [ f, hp.1.ne', hp.2.ne', hq0.ne', hq1.ne', sub_ne_zero, mul_comm, div_eq_mul_inv ] ; ring_nf;
        norm_num [ show p ≠ 0 by linarith [ hp.1 ], show p ≠ 1 by linarith [ hp.2 ], show q ≠ 0 by linarith, show q ≠ 1 by linarith, show ( 1 - q ) ≠ 0 by linarith, show ( - ( p * ( 1 - q ) ⁻¹ ) + ( 1 - q ) ⁻¹ ) ≠ 0 by nlinarith [ hp.1, hp.2, mul_inv_cancel₀ ( by linarith : ( 1 - q ) ≠ 0 ) ] ] ; ring_nf;
        grind;
      norm_num +zetaDelta at *;
      exact DifferentiableOn.congr ( fun x hx => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.sub ( DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id.div_const _ ) <| by exact ne_of_gt <| div_pos hx.1 hq0 ) <| DifferentiableAt.log ( DifferentiableAt.div ( differentiableAt_id.const_sub _ ) ( differentiableAt_const _ ) <| by linarith ) <| by exact ne_of_gt <| div_pos ( by linarith [ hx.2 ] ) <| by linarith ) <| DifferentiableAt.mul ( differentiableAt_const _ ) <| differentiableAt_id.sub_const _ ) fun x hx => h_deriv x hx.1 hx.2;
    · -- Let's calculate the first derivative of $f$.
      have h_deriv : ∀ x ∈ Set.Ioo 0 1, deriv f x = Real.log (x / q) - Real.log ((1 - x) / (1 - q)) - 4 * (x - q) := by
        intro x hx; norm_num [ f, hx.1.ne', hx.2.ne', hq0.ne', hq1.ne', sub_ne_zero, mul_comm, div_eq_mul_inv ] ; ring_nf;
        norm_num [ show x ≠ 0 by linarith [ hx.1 ], show x ≠ 1 by linarith [ hx.2 ], show q ≠ 0 by linarith, show q ≠ 1 by linarith, show ( 1 - q ) ≠ 0 by linarith, show ( - ( x * ( 1 - q ) ⁻¹ ) + ( 1 - q ) ⁻¹ ) ≠ 0 by nlinarith [ hx.1, hx.2, mul_inv_cancel₀ ( by linarith : ( 1 - q ) ≠ 0 ) ] ] ; ring_nf;
        grind;
      -- Let's calculate the second derivative of $f$.
      have h_deriv2 : ∀ x ∈ Set.Ioo 0 1, deriv^[2] f x = 1 / x + 1 / (1 - x) - 4 := by
        intro x hx; refine' HasDerivAt.deriv _ ; convert HasDerivAt.congr_of_eventuallyEq _ ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hx.1 hx.2 ) fun y hy => h_deriv y hy ) using 1 ; ring_nf;
        convert HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.neg ( HasDerivAt.mul ( hasDerivAt_id x ) ( hasDerivAt_const _ _ ) ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.sub ( HasDerivAt.log ( HasDerivAt.mul ( hasDerivAt_id x ) ( hasDerivAt_const _ _ ) ) _ ) ( HasDerivAt.log ( HasDerivAt.add ( HasDerivAt.neg ( HasDerivAt.mul ( hasDerivAt_id x ) ( hasDerivAt_const _ _ ) ) ) ( hasDerivAt_const _ _ ) ) _ ) ) using 1 <;> norm_num <;> ring_nf <;> try nlinarith [ hx.1, hx.2, mul_inv_cancel₀ ( by linarith : ( 1 - q ) ≠ 0 ) ] ;
        · grind;
        · exact ⟨ hx.1.ne', hq0.ne' ⟩
      generalize_proofs at *; (
      simp +zetaDelta at *;
      exact fun x hx₁ hx₂ => h_deriv2 x hx₁ hx₂ ▸ by nlinarith [ inv_pos.2 hx₁, inv_pos.2 ( sub_pos.2 hx₂ ), mul_inv_cancel₀ ( ne_of_gt hx₁ ), mul_inv_cancel₀ ( ne_of_gt ( sub_pos.2 hx₂ ) ), sq_nonneg ( x - 1 / 2 ) ] ;)
  have h_min : ∀ p ∈ Set.Icc 0 1, f p ≥ f q := by
    have h_min : ∀ p ∈ Set.Icc 0 1, f p ≥ f q + deriv f q * (p - q) := by
      intros p hp
      have h_subgradient : ∀ t ∈ Set.Ioo 0 1, f (t * p + (1 - t) * q) ≤ t * f p + (1 - t) * f q := by
        exact fun t ht => h_convex.2 hp ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩ ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] );
      have h_subgradient : Filter.Tendsto (fun t => (f (q + t * (p - q)) - f q) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv f q * (p - q))) := by
        have h_subgradient : HasDerivAt (fun t => f (q + t * (p - q))) (deriv f q * (p - q)) 0 := by
          convert HasDerivAt.comp 0 ( show HasDerivAt f _ _ from hasDerivAt_deriv_iff.mpr ?_ ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id 0 ) ( hasDerivAt_const _ _ ) ) ) using 1 <;> norm_num;
          apply_rules [ DifferentiableAt.sub, DifferentiableAt.add, DifferentiableAt.mul, DifferentiableAt.log, differentiableAt_id, differentiableAt_const ] <;> norm_num [ hq0.ne', hq1.ne' ];
          linarith;
        simpa [ div_eq_inv_mul ] using h_subgradient.tendsto_slope_zero_right;
      have h_subgradient : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), (f (q + t * (p - q)) - f q) / t ≤ f p - f q := by
        filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with t ht using by have := ‹∀ t ∈ Set.Ioo 0 1, f ( t * p + ( 1 - t ) * q ) ≤ t * f p + ( 1 - t ) * f q› t ht; rw [ div_le_iff₀ ht.1 ] ; ring_nf at *; linarith;
      have := le_of_tendsto_of_tendsto ‹_› tendsto_const_nhds h_subgradient; norm_num at *; linarith;
    convert h_min using 3;
    simp +zetaDelta at *;
    ring_nf;
    norm_num [ show q ≠ 0 by linarith, show 1 - q ≠ 0 by linarith, show - ( q * ( 1 - q ) ⁻¹ ) + ( 1 - q ) ⁻¹ ≠ 0 by nlinarith [ mul_inv_cancel₀ ( by linarith : ( 1 - q ) ≠ 0 ) ] ] ; ring_nf;
    field_simp;
    rw [ show ( -q + 1 ) / ( 1 - q ) = 1 by rw [ div_eq_iff ] <;> linarith ] ; norm_num ; ring_nf ;
    grind
  have h_zero : f q = 0 := by
    simp +zetaDelta at *
  have h_deriv_zero : deriv f q = 0 := by
    refine' IsLocalMin.deriv_eq_zero _;
    filter_upwards [ Icc_mem_nhds hq0 hq1 ] with p hp using h_min p hp
  have h_final : f p ≥ 0 := by
    exact h_zero ▸ h_min p ⟨ hp0, hp1 ⟩
  linarith [h_final]

/-
Support monotonicity of the prefix bias for `B ⊆ A` at a point of `B`:
if the `A`-branch is deterministic then so is the `B`-branch.
-/
lemma rho_subset_support {m : ℕ} (A B : Finset (Cube m)) (hB : B ⊆ A) (t : Fin m)
    (x : Cube m) (hxB : x ∈ B) :
    (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x) = 0 →
       rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x) = 0) ∧
    (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x) = 1 →
       rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x) = 1) := by
  constructor <;> intro h <;> simp_all +decide [ rho, pOn ];
  · exact Or.imp ( fun h => fun y hy hy' => h ( hB hy ) hy' ) ( fun h => fun y hy hy' => h ( hB hy ) hy' ) h;
  · rw [ div_eq_iff ] at * <;> norm_cast at * <;> simp_all +decide [ Finset.ext_iff ];
    · refine' le_antisymm _ _;
      · grind +locals;
      · refine' Finset.card_le_card _;
        contrapose! h;
        refine' ne_of_lt ( Finset.card_lt_card _ );
        simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        exact ⟨ h.choose, hB h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2 ⟩;
    · exact ⟨ x, hB hxB, fun _ => Iff.rfl ⟩;
    · exact ⟨ x, hxB, fun _ => Iff.rfl ⟩

/-
Pointwise Pinsker for the prefix-bias process at a point of `B`,
including the boundary cases handled by `rho_subset_support`.
-/
lemma rho_pinsker_pointwise {m : ℕ} (A B : Finset (Cube m)) (hB : B ⊆ A) (t : Fin m)
    (x : Cube m) (hxB : x ∈ B) :
    2 * (rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x)
        - rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) ^ 2
    ≤ (let p := rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x)
       let q := rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
       p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) := by
  by_cases hq : rho A t (proj (below Finset.univ t) x) = 0 ∨ rho A t (proj (below Finset.univ t) x) = 1;
  · have := rho_subset_support A B hB t x hxB; aesop;
  · apply bernoulli_pinsker;
    · exact rho_nonneg _ _ _;
    · exact HarperStability.rho_le_one B t ( proj ( below Finset.univ t ) x );
    · exact lt_of_le_of_ne ( rho_nonneg A t _ ) ( Ne.symm <| by tauto );
    · exact lt_of_le_of_ne ( rho_le_one _ _ _ ) fun h => hq <| Or.inr h

/-
Sum of square roots bound (Cauchy–Schwarz): `∑ √ f ≤ √(|s| · ∑ f)`.
-/
lemma sum_sqrt_le_sqrt_card_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, Real.sqrt (f i) ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, f i) := by
  refine' Real.le_sqrt_of_sq_le _;
  convert ( Finset.sum_mul_sq_le_sq_mul_sq s ( fun _ => 1 ) ( fun i => Real.sqrt ( f i ) ) ) using 1 <;> norm_num [ hf ];
  exact Or.inl ( Finset.sum_congr rfl fun i hi => by rw [ Real.sq_sqrt ( hf i hi ) ] )

/-
Per-coordinate Pinsker: the mean L¹ gap is at most `√(mean KL / 2)`.
-/
lemma pinsker_per_coord {m : ℕ} (A B : Finset (Cube m)) (hB : B ⊆ A)
    (hB_nonempty : B.Nonempty) (t : Fin m) :
    uE B (fun x => |rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x)
        - rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)|)
    ≤ Real.sqrt ((uE B (fun x =>
        let p := rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x)
        let q := rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
        p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)))) / 2) := by
  obtain ⟨x, hx⟩ := hB_nonempty;
  refine Real.le_sqrt_of_sq_le ?_;
  unfold uE; norm_num;
  have h_cauchy_schwarz : (∑ x ∈ B, |rho B t (proj (below Finset.univ t) x) - rho A t (proj (below Finset.univ t) x)|) ^ 2 ≤ (B.card : ℝ) * (∑ x ∈ B, (rho B t (proj (below Finset.univ t) x) - rho A t (proj (below Finset.univ t) x)) ^ 2) := by
    have h_cauchy_schwarz : ∀ (u v : Cube m → ℝ), (∑ x ∈ B, u x * v x) ^ 2 ≤ (∑ x ∈ B, u x ^ 2) * (∑ x ∈ B, v x ^ 2) := by
      exact fun u v => Finset.sum_mul_sq_le_sq_mul_sq B u v
    simpa using h_cauchy_schwarz 1 ( fun x => |rho B t ( proj ( below Finset.univ t ) x ) - rho A t ( proj ( below Finset.univ t ) x )| );
  rw [ div_pow, div_div, div_le_div_iff₀ ] ;
  · have h_pinsker : ∑ x ∈ B, (rho B t (proj (below Finset.univ t) x) - rho A t (proj (below Finset.univ t) x)) ^ 2 ≤ (1 / 2) * ∑ x ∈ B, (rho B t (proj (below Finset.univ t) x) * Real.log (rho B t (proj (below Finset.univ t) x) / rho A t (proj (below Finset.univ t) x)) + (1 - rho B t (proj (below Finset.univ t) x)) * Real.log ((1 - rho B t (proj (below Finset.univ t) x)) / (1 - rho A t (proj (below Finset.univ t) x)))) := by
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun x hx => by linarith [ rho_pinsker_pointwise A B hB t x hx ] ;
    nlinarith [ show ( B.card : ℝ ) ≥ 1 by exact_mod_cast Finset.card_pos.mpr ⟨ x, hx ⟩ ];
  · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ x, hx ⟩ ) );
  · exact mul_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ x, hx ⟩ ) ) zero_lt_two

lemma finite_pinsker_rho_subset {m : ℕ} (A B : Finset (Cube m))
    (hB : B ⊆ A) (hB_nonempty : B.Nonempty) :
    ∑ t : Fin m, uE B (fun x =>
      |rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x) -
       rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)|)
    ≤ Real.sqrt (m / 2 * ∑ t : Fin m, uE B (fun x =>
        let p := rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x)
        let q := rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
        p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)))) := by
  have step1 : ∀ t : Fin m, 0 ≤ uE B (fun x => (let p := rho B t (proj (below Finset.univ t) x); let q := rho A t (proj (below Finset.univ t) x); p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)))) := by
    intro t;
    refine' div_nonneg ( Finset.sum_nonneg fun x hx => _ ) ( Nat.cast_nonneg _ );
    exact le_trans ( by positivity ) ( rho_pinsker_pointwise A B hB t x hx );
  refine' le_trans ( Finset.sum_le_sum fun t _ => _ ) _;
  use fun t => Real.sqrt ( uE B ( fun x => ( let p := rho B t ( proj ( below Finset.univ t ) x ); let q := rho A t ( proj ( below Finset.univ t ) x ); p * Real.log ( p / q ) + ( 1 - p ) * Real.log ( ( 1 - p ) / ( 1 - q ) ) ) ) / 2 );
  · convert pinsker_per_coord A B hB hB_nonempty t using 1;
  · convert sum_sqrt_le_sqrt_card_mul_sum Finset.univ ( fun t => uE B ( fun x => ( let p := rho B t ( proj ( below Finset.univ t ) x ); let q := rho A t ( proj ( below Finset.univ t ) x ); p * Real.log ( p / q ) + ( 1 - p ) * Real.log ( ( 1 - p ) / ( 1 - q ) ) ) ) / 2 ) ( fun t ht => div_nonneg ( step1 t ) zero_le_two ) using 1 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]

lemma kl_tilt_l1_bound {m : ℕ} (A B : Finset (Cube m))
    (hB : B ⊆ A) (hB_nonempty : B.Nonempty) :
    ∑ t : Fin m, uE B (fun x =>
      |rho B t (proj (below (Finset.univ : Finset (Fin m)) t) x) -
       rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)|)
    ≤ Real.sqrt (m / 2 * Real.log ((A.card : ℝ) / (B.card : ℝ))) := by
  have h_kl := event_kl_chain_rule A B hB hB_nonempty
  have h_pinsker := finite_pinsker_rho_subset A B hB hB_nonempty
  exact le_trans h_pinsker (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h_kl (by positivity)))

lemma same_bin_separation_lemma (qMin qMax eps : ℝ)
    (hqMin : 0 ≤ qMin) (hqMax : qMax < 1 / 2) (_hq_le : qMin ≤ qMax)
    (heps : 0 < eps) :
    ∃ Delta_eps > 0, ∀ q' ∈ Set.Icc qMin qMax, ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ),
      |y - q'| ≥ 3 * eps / 4 →
      Delta_eps ≤ |H y - H q'| := by
  classical
  let d : ℝ := 3 * eps / 4
  have hd : 0 < d := by positivity
  by_cases hne : ∃ q' ∈ Set.Icc qMin qMax, ∃ y ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ),
      d ≤ |y - q'|
  · let K : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc qMin qMax ∧
        p.2 ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) ∧ d ≤ |p.2 - p.1|}
    let f : ℝ × ℝ → ℝ := fun p => |H p.2 - H p.1|
    have hK_ne : K.Nonempty := by
      rcases hne with ⟨q', hq', y, hy, hdist⟩
      exact ⟨(q', y), by simpa [K] using And.intro hq' (And.intro hy hdist)⟩
    have hclosed_sep : IsClosed {p : ℝ × ℝ | d ≤ |p.2 - p.1|} := by
      have hcont : Continuous fun p : ℝ × ℝ => |p.2 - p.1| := by
        exact (continuous_snd.sub continuous_fst).abs
      simpa using isClosed_le continuous_const hcont
    have hK_comp : IsCompact K := by
      have hrect : IsCompact (Set.Icc (qMin, (0 : ℝ)) (qMax, (1 / 2 : ℝ))) :=
        isCompact_Icc
      have hK_eq : K = Set.Icc (qMin, (0 : ℝ)) (qMax, (1 / 2 : ℝ)) ∩
          {p : ℝ × ℝ | d ≤ |p.2 - p.1|} := by
        ext p
        simp [K, Set.mem_Icc, Prod.le_def, and_assoc, and_left_comm]
      rw [hK_eq]
      exact hrect.inter_right hclosed_sep
    have hf_cont : ContinuousOn f K := by
      have hcont : Continuous f := by
        dsimp [f, H]
        exact ((Real.binEntropy_continuous.comp continuous_snd).sub
          (Real.binEntropy_continuous.comp continuous_fst)).abs
      exact hcont.continuousOn
    rcases hK_comp.exists_isMinOn hK_ne hf_cont with ⟨p0, hp0K, hp0min⟩
    have hp0_q : p0.1 ∈ Set.Icc qMin qMax := hp0K.1
    have hp0_y : p0.2 ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := hp0K.2.1
    have hp0_dist : d ≤ |p0.2 - p0.1| := hp0K.2.2
    have hp0_q_half : p0.1 ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := by
      exact ⟨le_trans hqMin hp0_q.1, le_of_lt (lt_of_le_of_lt hp0_q.2 hqMax)⟩
    have hp0_q_half' : p0.1 ∈ Set.Icc (0 : ℝ) (2⁻¹ : ℝ) := by
      simpa using hp0_q_half
    have hp0_y' : p0.2 ∈ Set.Icc (0 : ℝ) (2⁻¹ : ℝ) := by
      simpa using hp0_y
    have hp0_coord_ne : p0.2 ≠ p0.1 := by
      intro h
      have : d ≤ 0 := by simpa [h] using hp0_dist
      linarith
    have hp0_H_ne : H p0.2 ≠ H p0.1 := by
      rcases lt_or_gt_of_ne hp0_coord_ne with hlt | hgt
      · have hstrict : H p0.2 < H p0.1 := by
          simpa [H] using Real.binEntropy_strictMonoOn hp0_y' hp0_q_half' hlt
        exact ne_of_lt hstrict
      · have hstrict : H p0.1 < H p0.2 := by
          simpa [H] using Real.binEntropy_strictMonoOn hp0_q_half' hp0_y' hgt
        exact ne_of_gt hstrict
    have hf_pos : 0 < f p0 := by
      dsimp [f]
      exact abs_pos.mpr (sub_ne_zero.mpr hp0_H_ne)
    refine ⟨f p0 / 2, by positivity, ?_⟩
    intro q' hq' y hy hdist
    have hp : (q', y) ∈ K := by
      dsimp [K]
      exact ⟨hq', hy, by simpa [d] using hdist⟩
    have hmin : f p0 ≤ f (q', y) := (isMinOn_iff.mp hp0min) (q', y) hp
    dsimp [f] at hmin ⊢
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro q' hq' y hy hdist
    exfalso
    exact hne ⟨q', hq', y, hy, by simpa [d] using hdist⟩

lemma varOn_nonneg {m : ℕ} (F : Finset (Cube m)) (rho : Cube m → ℝ) :
    0 ≤ varOn F rho := by
  unfold varOn uE
  positivity

lemma varOn_ge_pOn_mul_sq_of_forall {m : ℕ} (F : Finset (Cube m))
    (rho : Cube m → ℝ) (P : Cube m → Prop) [DecidablePred P] (c : ℝ)
    (hge : ∀ x ∈ F, P x → c ≤ (rho x - uE F rho) ^ 2) :
    pOn F (fun x => decide (P x)) true * c ≤ varOn F rho := by
  let μ := uE F rho
  have hfilter_sum : ((F.filter P).card : ℝ) * c ≤
      ∑ x ∈ F.filter P, (rho x - μ) ^ 2 := by
    calc
      ((F.filter P).card : ℝ) * c = ∑ x ∈ F.filter P, c := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ F.filter P, (rho x - μ) ^ 2 := by
        exact Finset.sum_le_sum fun x hx => by
          dsimp [μ]
          exact hge x (Finset.mem_of_mem_filter x hx) (Finset.mem_filter.mp hx).2
  have hsubset : F.filter P ⊆ F := Finset.filter_subset _ _
  have hsum_le : ∑ x ∈ F.filter P, (rho x - μ) ^ 2 ≤
      ∑ x ∈ F, (rho x - μ) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro x _ _
      exact sq_nonneg _)
  have hnum : ((F.filter P).card : ℝ) * c ≤
      ∑ x ∈ F, (rho x - μ) ^ 2 := hfilter_sum.trans hsum_le
  unfold pOn varOn
  rw [show uE F rho = μ by rfl]
  unfold uE
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by simpa using hnum) (Nat.cast_nonneg _)

lemma pOn_bool_le_add_of_imp {m : ℕ} (F : Finset (Cube m))
    (P Q R : Cube m → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (himp : ∀ x ∈ F, P x → Q x ∨ R x) :
    pOn F (fun x => decide (P x)) true ≤
      pOn F (fun x => decide (Q x)) true + pOn F (fun x => decide (R x)) true := by
  have hsub : F.filter P ⊆ F.filter Q ∪ F.filter R := by
    intro x hx
    have hxF : x ∈ F := Finset.mem_of_mem_filter x hx
    have hxP : P x := (Finset.mem_filter.mp hx).2
    rcases himp x hxF hxP with hQ | hR
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxF, hQ⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxF, hR⟩)
  have hcard_nat : (F.filter P).card ≤ (F.filter Q).card + (F.filter R).card := by
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hcard_real : ((F.filter P).card : ℝ) ≤
      ((F.filter Q).card : ℝ) + ((F.filter R).card : ℝ) := by
    exact_mod_cast hcard_nat
  have hden : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg _
  have hfrac : ((F.filter P).card : ℝ) / (F.card : ℝ) ≤
      ((F.filter Q).card : ℝ) / (F.card : ℝ) +
        ((F.filter R).card : ℝ) / (F.card : ℝ) := by
    calc
      ((F.filter P).card : ℝ) / (F.card : ℝ)
          ≤ (((F.filter Q).card : ℝ) + ((F.filter R).card : ℝ)) / (F.card : ℝ) :=
            div_le_div_of_nonneg_right hcard_real hden
      _ = ((F.filter Q).card : ℝ) / (F.card : ℝ) +
          ((F.filter R).card : ℝ) / (F.card : ℝ) := by
            rw [add_div]
  simpa [pOn] using hfrac

lemma one_sub_pOn_bool_eq_not {m : ℕ} (F : Finset (Cube m))
    (P : Cube m → Prop) [DecidablePred P] (hF : F.Nonempty) :
    1 - pOn F (fun x => decide (P x)) true =
      pOn F (fun x => decide (¬ P x)) true := by
  have hcard_pos : 0 < (F.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hF
  have hcard_ne : (F.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hsum :
      ((F.filter P).card : ℝ) + ((F.filter fun x => ¬ P x).card : ℝ) =
        (F.card : ℝ) := by
    rw [← Nat.cast_add]
    congr
    exact Finset.card_filter_add_card_filter_not (s := F) P
  have hfrac : 1 - ((F.filter P).card : ℝ) / (F.card : ℝ) =
      ((F.filter fun x => ¬ P x).card : ℝ) / (F.card : ℝ) := by
    calc
      1 - ((F.filter P).card : ℝ) / (F.card : ℝ)
          = ((F.card : ℝ) - ((F.filter P).card : ℝ)) / (F.card : ℝ) := by
            rw [sub_div]
            simp [hcard_ne]
      _ = ((F.filter fun x => ¬ P x).card : ℝ) / (F.card : ℝ) := by
            rw [← hsum]
            ring
  simpa [pOn] using hfrac

lemma two_cluster_lemma {m : ℕ} (F : Finset (Cube m))
    (rho : Cube m → ℝ) (q qMax eps gap : ℝ)
    (_hrho0 : ∀ x ∈ F, 0 ≤ rho x)
    (_hrho1 : ∀ x ∈ F, rho x ≤ 1)
    (hq_le : q ≤ qMax)
    (_hqMax : qMax < 1 / 2)
    (_heps : 0 < eps)
    (hgap : 0 < gap)
    (hgap_le : qMax + eps ≤ 1 / 2 - gap) :
    let beta := pOn F (fun x => decide (eps ≤ |fold (rho x) - q|)) true
    let gamma := pOn F (fun x => decide (1 / 2 < rho x)) true
    let delta := min gamma (1 - gamma)
    delta ≤ (4 / gap ^ 2) * varOn F rho + 2 * beta := by
  by_cases hF : F.Nonempty
  · let bad : Cube m → Prop := fun x => eps ≤ |fold (rho x) - q|
    let upper : Cube m → Prop := fun x => (1 / 2 : ℝ) < rho x
    let goodUpper : Cube m → Prop := fun x => ¬ bad x ∧ upper x
    let goodLower : Cube m → Prop := fun x => ¬ bad x ∧ ¬ upper x
    let beta := pOn F (fun x => decide (bad x)) true
    let gamma := pOn F (fun x => decide (upper x)) true
    let μ := uE F rho
    have hqe : q + eps ≤ 1 / 2 - gap := by linarith
    have hgap_sq_pos : 0 < gap ^ 2 := sq_pos_of_pos hgap
    have hvar_nonneg : 0 ≤ varOn F rho := varOn_nonneg F rho
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact pOn_nonneg F (fun x => decide (bad x)) true
    have hUpperProb : gamma ≤ pOn F (fun x => decide (goodUpper x)) true + beta := by
      dsimp [gamma, beta]
      exact pOn_bool_le_add_of_imp F upper goodUpper bad (by
        intro x hxF hxU
        by_cases hb : bad x
        · exact Or.inr hb
        · exact Or.inl ⟨hb, hxU⟩)
    have hLowerProb : 1 - gamma ≤ pOn F (fun x => decide (goodLower x)) true + beta := by
      have hnot := pOn_bool_le_add_of_imp F (fun x => ¬ upper x) goodLower bad (by
        intro x hxF hxU
        by_cases hb : bad x
        · exact Or.inr hb
        · exact Or.inl ⟨hb, hxU⟩)
      have hcomp : 1 - gamma = pOn F (fun x => decide (¬ upper x)) true := by
        dsimp [gamma]
        exact one_sub_pOn_bool_eq_not F upper hF
      simpa [beta, hcomp] using hnot
    have hlast (base : ℝ) (hbase_nonneg : 0 ≤ base) :
        base + beta ≤ 4 * base + 2 * beta := by
      nlinarith
    by_cases hmu : μ ≤ 1 / 2
    · have hmass_var :
          pOn F (fun x => decide (goodUpper x)) true * gap ^ 2 ≤ varOn F rho := by
        apply varOn_ge_pOn_mul_sq_of_forall F rho goodUpper (gap ^ 2)
        intro x hxF hxGU
        have hnotbad : ¬ bad x := hxGU.1
        have hupper : upper x := hxGU.2
        have hfold : fold (rho x) = 1 - rho x := by
          unfold fold
          exact min_eq_right (by linarith)
        have habs : |fold (rho x) - q| < eps := lt_of_not_ge hnotbad
        have hlt : 1 - rho x - q < eps := by
          have := (abs_lt.mp habs).2
          rwa [hfold] at this
        have hrho_lower : 1 / 2 + gap ≤ rho x := by
          linarith
        have hdist : gap ≤ rho x - μ := by
          linarith
        nlinarith [sq_nonneg ((rho x - μ) - gap)]
      have hgood_le :
          pOn F (fun x => decide (goodUpper x)) true ≤ varOn F rho / gap ^ 2 := by
        rw [le_div_iff₀ hgap_sq_pos]
        simpa [mul_comm] using hmass_var
      have hbase_nonneg : 0 ≤ varOn F rho / gap ^ 2 :=
        div_nonneg hvar_nonneg (le_of_lt hgap_sq_pos)
      have hmain : gamma ≤ varOn F rho / gap ^ 2 + beta := by
        linarith
      calc
        min gamma (1 - gamma) ≤ gamma := min_le_left _ _
        _ ≤ varOn F rho / gap ^ 2 + beta := hmain
        _ ≤ 4 * (varOn F rho / gap ^ 2) + 2 * beta := hlast _ hbase_nonneg
        _ = (4 / gap ^ 2) * varOn F rho + 2 * beta := by ring
    · have hmu_ge : 1 / 2 ≤ μ := le_of_lt (lt_of_not_ge hmu)
      have hmass_var :
          pOn F (fun x => decide (goodLower x)) true * gap ^ 2 ≤ varOn F rho := by
        apply varOn_ge_pOn_mul_sq_of_forall F rho goodLower (gap ^ 2)
        intro x hxF hxGL
        have hnotbad : ¬ bad x := hxGL.1
        have hnotupper : ¬ upper x := hxGL.2
        have hrho_half : rho x ≤ 1 / 2 := le_of_not_gt hnotupper
        have hfold : fold (rho x) = rho x := by
          unfold fold
          exact min_eq_left (by linarith)
        have habs : |fold (rho x) - q| < eps := lt_of_not_ge hnotbad
        have hlt : rho x - q < eps := by
          have := (abs_lt.mp habs).2
          rwa [hfold] at this
        have hrho_upper : rho x ≤ 1 / 2 - gap := by
          linarith
        have hdist : gap ≤ μ - rho x := by
          linarith
        nlinarith [sq_nonneg ((μ - rho x) - gap)]
      have hgood_le :
          pOn F (fun x => decide (goodLower x)) true ≤ varOn F rho / gap ^ 2 := by
        rw [le_div_iff₀ hgap_sq_pos]
        simpa [mul_comm] using hmass_var
      have hbase_nonneg : 0 ≤ varOn F rho / gap ^ 2 :=
        div_nonneg hvar_nonneg (le_of_lt hgap_sq_pos)
      have hmain : 1 - gamma ≤ varOn F rho / gap ^ 2 + beta := by
        linarith
      calc
        min gamma (1 - gamma) ≤ 1 - gamma := min_le_right _ _
        _ ≤ varOn F rho / gap ^ 2 + beta := hmain
        _ ≤ 4 * (varOn F rho / gap ^ 2) + 2 * beta := hlast _ hbase_nonneg
        _ = (4 / gap ^ 2) * varOn F rho + 2 * beta := by ring
  · have hF_eq : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [hF_eq, pOn, varOn, uE]

lemma two_cluster_mean_threshold_error_lemma {m : ℕ} (F : Finset (Cube m))
    (rho : Cube m → ℝ) (q qMax eps gap : ℝ)
    (_hrho0 : ∀ x ∈ F, 0 ≤ rho x)
    (_hrho1 : ∀ x ∈ F, rho x ≤ 1)
    (hq_le : q ≤ qMax)
    (_hqMax : qMax < 1 / 2)
    (_heps : 0 < eps)
    (hgap : 0 < gap)
    (hgap_le : qMax + eps ≤ 1 / 2 - gap) :
    uE F (fun x =>
      if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < uE F rho) then
        (0 : ℝ)
      else
        1)
      ≤ (4 / gap ^ 2) * varOn F rho +
        2 * pOn F (fun x => decide (eps ≤ |fold (rho x) - q|)) true := by
  by_cases hF : F.Nonempty
  · let bad : Cube m → Prop := fun x => eps ≤ |fold (rho x) - q|
    let upper : Cube m → Prop := fun x => (1 / 2 : ℝ) < rho x
    let goodUpper : Cube m → Prop := fun x => ¬ bad x ∧ upper x
    let goodLower : Cube m → Prop := fun x => ¬ bad x ∧ ¬ upper x
    let beta := pOn F (fun x => decide (bad x)) true
    let gamma := pOn F (fun x => decide (upper x)) true
    let μ := uE F rho
    have hqe : q + eps ≤ 1 / 2 - gap := by linarith
    have hgap_sq_pos : 0 < gap ^ 2 := sq_pos_of_pos hgap
    have hvar_nonneg : 0 ≤ varOn F rho := varOn_nonneg F rho
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact pOn_nonneg F (fun x => decide (bad x)) true
    have hUpperProb : gamma ≤ pOn F (fun x => decide (goodUpper x)) true + beta := by
      dsimp [gamma, beta]
      exact pOn_bool_le_add_of_imp F upper goodUpper bad (by
        intro x hxF hxU
        by_cases hb : bad x
        · exact Or.inr hb
        · exact Or.inl ⟨hb, hxU⟩)
    have hLowerProb : 1 - gamma ≤ pOn F (fun x => decide (goodLower x)) true + beta := by
      have hnot := pOn_bool_le_add_of_imp F (fun x => ¬ upper x) goodLower bad (by
        intro x hxF hxU
        by_cases hb : bad x
        · exact Or.inr hb
        · exact Or.inl ⟨hb, hxU⟩)
      have hcomp : 1 - gamma = pOn F (fun x => decide (¬ upper x)) true := by
        dsimp [gamma]
        exact one_sub_pOn_bool_eq_not F upper hF
      simpa [beta, hcomp] using hnot
    have hlast (base : ℝ) (hbase_nonneg : 0 ≤ base) :
        base + beta ≤ 4 * base + 2 * beta := by
      nlinarith
    by_cases hmu : μ ≤ 1 / 2
    · have hdec : decide ((1 / 2 : ℝ) < uE F rho) = false := by
        exact decide_eq_false (not_lt.mpr (by simpa [μ] using hmu))
      have hnot_mu : ¬ (1 / 2 : ℝ) < uE F rho := by
        exact not_lt.mpr (by simpa [μ] using hmu)
      have hnot_mu_raw :
          ¬ (1 / 2 : ℝ) < (∑ x ∈ F, rho x) / (F.card : ℝ) := by
        simpa [uE] using hnot_mu
      have herr :
          uE F (fun x =>
            if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < uE F rho) then
              (0 : ℝ)
            else
              1) = gamma := by
        let rawMean : ℝ := (∑ x ∈ F, rho x) / (F.card : ℝ)
        have hnot_raw : ¬ (1 / 2 : ℝ) < rawMean := by
          dsimp [rawMean]
          simpa using hnot_mu_raw
        have hnot_raw_inv : ¬ (2⁻¹ : ℝ) < rawMean := by
          simpa using hnot_raw
        have hdec_raw : decide ((1 / 2 : ℝ) < rawMean) = false :=
          decide_eq_false hnot_raw
        have hsum :
            (∑ x ∈ F,
              (if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < rawMean) then
                (0 : ℝ)
              else
                1)) =
              ((F.filter fun x => (1 / 2 : ℝ) < rho x).card : ℝ) := by
          calc
            (∑ x ∈ F,
              (if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < rawMean) then
                (0 : ℝ)
              else
                1))
                = ∑ x ∈ F, (if (1 / 2 : ℝ) < rho x then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  by_cases hxupper : (2⁻¹ : ℝ) < rho x
                  · simp [hxupper, hnot_raw_inv]
                  · simp [hxupper, hnot_raw_inv]
            _ = ((F.filter fun x => (1 / 2 : ℝ) < rho x).card : ℝ) := by
                  simp
        unfold uE
        dsimp [rawMean] at hsum
        rw [hsum]
        dsimp [gamma, upper]
        unfold pOn
        simp
      have hmass_var :
          pOn F (fun x => decide (goodUpper x)) true * gap ^ 2 ≤ varOn F rho := by
        apply varOn_ge_pOn_mul_sq_of_forall F rho goodUpper (gap ^ 2)
        intro x hxF hxGU
        have hnotbad : ¬ bad x := hxGU.1
        have hupper : upper x := hxGU.2
        have hfold : fold (rho x) = 1 - rho x := by
          unfold fold
          exact min_eq_right (by linarith)
        have habs : |fold (rho x) - q| < eps := lt_of_not_ge hnotbad
        have hlt : 1 - rho x - q < eps := by
          have := (abs_lt.mp habs).2
          rwa [hfold] at this
        have hrho_lower : 1 / 2 + gap ≤ rho x := by
          linarith
        have hdist : gap ≤ rho x - μ := by
          linarith
        nlinarith [sq_nonneg ((rho x - μ) - gap)]
      have hgood_le :
          pOn F (fun x => decide (goodUpper x)) true ≤ varOn F rho / gap ^ 2 := by
        rw [le_div_iff₀ hgap_sq_pos]
        simpa [mul_comm] using hmass_var
      have hbase_nonneg : 0 ≤ varOn F rho / gap ^ 2 :=
        div_nonneg hvar_nonneg (le_of_lt hgap_sq_pos)
      have hmain : gamma ≤ varOn F rho / gap ^ 2 + beta := by
        linarith
      calc
        uE F (fun x =>
            if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < uE F rho) then
              (0 : ℝ)
            else
              1) = gamma := herr
        _ ≤ varOn F rho / gap ^ 2 + beta := hmain
        _ ≤ 4 * (varOn F rho / gap ^ 2) + 2 * beta := hlast _ hbase_nonneg
        _ = (4 / gap ^ 2) * varOn F rho + 2 * beta := by ring
    · have hmu_ge : 1 / 2 ≤ μ := le_of_lt (lt_of_not_ge hmu)
      have hdec : decide ((1 / 2 : ℝ) < uE F rho) = true := by
        exact decide_eq_true (by simpa [μ] using lt_of_not_ge hmu)
      have hgt_mu : (1 / 2 : ℝ) < uE F rho := by
        exact by simpa [μ] using lt_of_not_ge hmu
      have hgt_mu_raw :
          (1 / 2 : ℝ) < (∑ x ∈ F, rho x) / (F.card : ℝ) := by
        simpa [uE] using hgt_mu
      have herr :
          uE F (fun x =>
            if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < uE F rho) then
              (0 : ℝ)
            else
              1) = 1 - gamma := by
        have hnot :
            uE F (fun x =>
              if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < uE F rho) then
                (0 : ℝ)
              else
                1) = pOn F (fun x => decide (¬ upper x)) true := by
          let rawMean : ℝ := (∑ x ∈ F, rho x) / (F.card : ℝ)
          have hgt_raw : (1 / 2 : ℝ) < rawMean := by
            dsimp [rawMean]
            simpa using hgt_mu_raw
          have hgt_raw_inv : (2⁻¹ : ℝ) < rawMean := by
            simpa using hgt_raw
          have hdec_raw : decide ((1 / 2 : ℝ) < rawMean) = true :=
            decide_eq_true hgt_raw
          have hsum :
              (∑ x ∈ F,
                (if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < rawMean) then
                  (0 : ℝ)
                else
                  1)) =
                ((F.filter fun x => ¬ (1 / 2 : ℝ) < rho x).card : ℝ) := by
            calc
              (∑ x ∈ F,
                (if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < rawMean) then
                  (0 : ℝ)
                else
                  1))
                  = ∑ x ∈ F, (if ¬ (1 / 2 : ℝ) < rho x then (1 : ℝ) else 0) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    by_cases hxupper : (2⁻¹ : ℝ) < rho x
                    · have hxnotle : ¬ rho x ≤ (2⁻¹ : ℝ) := not_le.mpr hxupper
                      simp [hxupper, hgt_raw_inv]
                    · have hxle : rho x ≤ (2⁻¹ : ℝ) := le_of_not_gt hxupper
                      simp [hxupper, hgt_raw_inv]
              _ = ((F.filter fun x => ¬ (1 / 2 : ℝ) < rho x).card : ℝ) := by
                    simp
          unfold uE
          dsimp [rawMean] at hsum
          rw [hsum]
          dsimp [upper]
          unfold pOn
          simp
        have hcomp : 1 - gamma = pOn F (fun x => decide (¬ upper x)) true := by
          dsimp [gamma]
          exact one_sub_pOn_bool_eq_not F upper hF
        rw [hnot, ← hcomp]
      have hmass_var :
          pOn F (fun x => decide (goodLower x)) true * gap ^ 2 ≤ varOn F rho := by
        apply varOn_ge_pOn_mul_sq_of_forall F rho goodLower (gap ^ 2)
        intro x hxF hxGL
        have hnotbad : ¬ bad x := hxGL.1
        have hnotupper : ¬ upper x := hxGL.2
        have hrho_half : rho x ≤ 1 / 2 := le_of_not_gt hnotupper
        have hfold : fold (rho x) = rho x := by
          unfold fold
          exact min_eq_left (by linarith)
        have habs : |fold (rho x) - q| < eps := lt_of_not_ge hnotbad
        have hlt : rho x - q < eps := by
          have := (abs_lt.mp habs).2
          rwa [hfold] at this
        have hrho_upper : rho x ≤ 1 / 2 - gap := by
          linarith
        have hdist : gap ≤ μ - rho x := by
          linarith
        nlinarith [sq_nonneg ((μ - rho x) - gap)]
      have hgood_le :
          pOn F (fun x => decide (goodLower x)) true ≤ varOn F rho / gap ^ 2 := by
        rw [le_div_iff₀ hgap_sq_pos]
        simpa [mul_comm] using hmass_var
      have hbase_nonneg : 0 ≤ varOn F rho / gap ^ 2 :=
        div_nonneg hvar_nonneg (le_of_lt hgap_sq_pos)
      have hmain : 1 - gamma ≤ varOn F rho / gap ^ 2 + beta := by
        linarith
      calc
        uE F (fun x =>
            if decide ((1 / 2 : ℝ) < rho x) = decide ((1 / 2 : ℝ) < uE F rho) then
              (0 : ℝ)
            else
              1) = 1 - gamma := herr
        _ ≤ varOn F rho / gap ^ 2 + beta := hmain
        _ ≤ 4 * (varOn F rho / gap ^ 2) + 2 * beta := hlast _ hbase_nonneg
        _ = (4 / gap ^ 2) * varOn F rho + 2 * beta := by ring
  · have hF_eq : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [hF_eq, pOn, varOn, uE]

/-
Hoeffding's lemma for a Bernoulli(`p`) variable centered at its mean:
the centered exponential moment is at most `exp (lam^2/8)`.
-/
set_option maxHeartbeats 4000000 in
lemma hoeffding_bernoulli_mgf (p lam : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (lam * (-p))
      ≤ Real.exp (lam ^ 2 / 8) := by
  by_contra h_contra;
  have h_taylor : ∀ t : ℝ, -t * p + Real.log (1 - p + p * Real.exp t) ≤ t^2 / 8 := by
    intro t
    by_cases hp : p = 0 ∨ p = 1;
    · cases hp <;> simp_all +decide; all_goals positivity;
    · -- Let's define the function $g(t) = \frac{t^2}{8} - (-t * p + \log(1 - p + p * \exp(t)))$ and show that $g(t) \geq 0$ for all $t$.
      set g : ℝ → ℝ := fun t => t^2 / 8 - (-t * p + Real.log (1 - p + p * Real.exp t));
      -- We'll use the fact that $g(t)$ is convex and has a minimum at $t = 0$.
      have hg_convex : ConvexOn ℝ Set.univ g := by
        apply_rules [ convexOn_of_deriv2_nonneg, convex_univ ];
        · exact ContinuousOn.sub ( ContinuousOn.div_const ( continuousOn_id.pow 2 ) _ ) ( ContinuousOn.add ( ContinuousOn.mul ( continuousOn_id.neg ) continuousOn_const ) ( ContinuousOn.log ( continuousOn_const.add ( continuousOn_const.mul ( Real.continuousOn_exp ) ) ) fun x hx => by cases lt_or_gt_of_ne ( mt Or.inl hp ) <;> cases lt_or_gt_of_ne ( mt Or.inr hp ) <;> nlinarith [ Real.exp_pos x ] ) );
        · exact DifferentiableOn.sub ( DifferentiableOn.div_const ( differentiableOn_id.pow 2 ) _ ) ( DifferentiableOn.add ( differentiableOn_id.neg.mul_const _ ) ( DifferentiableOn.log ( DifferentiableOn.add ( differentiableOn_const _ ) ( differentiableOn_id.exp.const_mul _ ) ) ( by intro x hx; exact ne_of_gt ( by cases lt_or_gt_of_ne ( mt Or.inl hp ) <;> cases lt_or_gt_of_ne ( mt Or.inr hp ) <;> nlinarith [ Real.exp_pos x ] ) ) ) );
        · refine' DifferentiableOn.congr _ _;
          use fun t => t / 4 - ( -p + p * Real.exp t / ( 1 - p + p * Real.exp t ) );
          · exact DifferentiableOn.sub ( differentiableOn_id.div_const _ ) ( DifferentiableOn.add ( differentiableOn_const _ ) ( DifferentiableOn.div ( DifferentiableOn.mul ( differentiableOn_const _ ) ( Real.differentiable_exp.differentiableOn ) ) ( DifferentiableOn.add ( differentiableOn_const _ ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( Real.differentiable_exp.differentiableOn ) ) ) ( by intro t ht; exact ne_of_gt ( by cases lt_or_gt_of_ne ( mt Or.inl hp ) <;> cases lt_or_gt_of_ne ( mt Or.inr hp ) <;> nlinarith [ Real.exp_pos t ] ) ) ) );
          · intro x hx; norm_num [ g, Real.differentiableAt_exp, show ( 1 - p + p * Real.exp x ) ≠ 0 from by cases lt_or_gt_of_ne ( mt Or.inl hp ) <;> cases lt_or_gt_of_ne ( mt Or.inr hp ) <;> nlinarith [ Real.exp_pos x ] ] ; ring;
        · -- Let's calculate the second derivative of $g(t)$.
          have hg'' : ∀ t, deriv^[2] g t = 1 / 4 - p * (1 - p) * Real.exp t / (1 - p + p * Real.exp t)^2 := by
            have hg'' : ∀ t, deriv^[2] g t = deriv (fun t => t / 4 - (-p + p * Real.exp t / (1 - p + p * Real.exp t))) t := by
              intro t; refine' Filter.EventuallyEq.deriv_eq _ ; filter_upwards [ ] with t ; norm_num [ Real.differentiableAt_exp, mul_comm p, show ( 1 - p + p * Real.exp t ) ≠ 0 from by cases lt_or_gt_of_ne ( mt Or.inl hp ) <;> cases lt_or_gt_of_ne ( mt Or.inr hp ) <;> nlinarith [ Real.exp_pos t ] ] ; ring_nf;
              norm_num +zetaDelta at *;
              norm_num [ Real.differentiableAt_exp, show ( 1 - p + p * Real.exp t ) ≠ 0 from by cases lt_or_gt_of_ne hp.1 <;> cases lt_or_gt_of_ne hp.2 <;> nlinarith [ Real.exp_pos t ] ] ; ring;
            intro t; rw [ hg'' ] ; norm_num [ Real.differentiableAt_exp, ne_of_gt ( show 0 < 1 - p + p * Real.exp t from by cases lt_or_gt_of_ne ( mt Or.inl hp ) <;> cases lt_or_gt_of_ne ( mt Or.inr hp ) <;> nlinarith [ Real.exp_pos t ] ) ] ; ring;
          simp_all +decide [ not_or ];
          intro x; rw [ div_le_iff₀ ] <;> norm_num <;> nlinarith [ sq_nonneg ( 1 - p - p * Real.exp x ), Real.exp_pos x, mul_self_pos.2 ( sub_ne_zero.2 hp.1 ), mul_self_pos.2 ( sub_ne_zero.2 hp.2 ), Real.exp_pos x, mul_pos ( lt_of_le_of_ne hp0 ( Ne.symm hp.1 ) ) ( Real.exp_pos x ) ] ;
      have hg_min : ∀ t : ℝ, g t ≥ g 0 + deriv g 0 * (t - 0) := by
        intro t; have := hg_convex.2 ( Set.mem_univ 0 ) ( Set.mem_univ t ) ; simp_all +decide [ ConvexOn ] ;
        have hg_min : Filter.Tendsto (fun h => (g (h * t) - g 0) / h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv g 0 * t)) := by
          have hg_min : HasDerivAt (fun h => g (h * t)) (deriv g 0 * t) 0 := by
            convert HasDerivAt.comp 0 ( show HasDerivAt g _ _ from hasDerivAt_deriv_iff.mpr ?_ ) ( hasDerivAt_mul_const t ) using 1 <;> norm_num;
            exact DifferentiableAt.sub ( by norm_num ) ( DifferentiableAt.add ( DifferentiableAt.mul ( differentiableAt_id.neg ) ( differentiableAt_const _ ) ) ( DifferentiableAt.log ( by norm_num [ Real.differentiableAt_exp ] ) ( by cases lt_or_gt_of_ne hp.1 <;> cases lt_or_gt_of_ne hp.2 <;> nlinarith [ Real.exp_pos 0 ] ) ) );
          simpa [ div_eq_inv_mul ] using hg_min.tendsto_slope_zero_right;
        have hg_min : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), (g (h * t) - g 0) / h ≤ g t - g 0 := by
          filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with h hh using by have := this ( show 0 ≤ 1 - h by linarith [ hh.1, hh.2 ] ) ( show 0 ≤ h by linarith [ hh.1, hh.2 ] ) ( by linarith [ hh.1, hh.2 ] ) ; rw [ div_le_iff₀ hh.1 ] ; nlinarith [ hh.1, hh.2 ] ;
        have := le_of_tendsto_of_tendsto ‹_› tendsto_const_nhds hg_min; norm_num at *; linarith;
      simp +zetaDelta at *;
      norm_num [ Real.differentiableAt_exp, show ( 1 - p + p * Real.exp 0 ) ≠ 0 from by cases lt_or_gt_of_ne hp.1 <;> cases lt_or_gt_of_ne hp.2 <;> nlinarith [ Real.exp_pos 0 ] ] at * ; linarith [ hg_min t ];
  have := h_taylor lam;
  -- Exponentiate both sides of the inequality to remove the logarithm.
  have h_exp : (1 - p + p * Real.exp lam) ≤ Real.exp (lam^2 / 8 + lam * p) := by
    rw [ ← Real.log_le_iff_le_exp ( by nlinarith [ Real.exp_pos lam, show p * Real.exp lam ≥ 0 by positivity ] ) ] ; linarith;
  convert h_contra _ using 1;
  convert mul_le_mul_of_nonneg_right h_exp ( Real.exp_nonneg ( lam * -p ) ) using 1 <;> ring_nf;
  · rw [ Real.exp_add ] ; ring;
  · rw [ ← Real.exp_add ] ; ring_nf

/-
Fiber MGF bound: within any fiber `F`, the mean centered exponential
moment of the majority-mismatch indicator is at most `exp (lam²/8)`.
-/
lemma fiber_mgf_le {m : ℕ} (F : Finset (Cube m)) (t : Fin m) (lam : ℝ) :
    (∑ y ∈ F, Real.exp (lam * ((if coord t y = decide ((1 / 2 : ℝ) < pOn F (coord t) true)
        then (0 : ℝ) else 1) - fold (pOn F (coord t) true))))
      ≤ (F.card : ℝ) * Real.exp (lam ^ 2 / 8) := by
  convert mul_le_mul_of_nonneg_left ( hoeffding_bernoulli_mgf ( fold ( pOn F ( coord t ) true ) ) lam ?_ ?_ ) ( Nat.cast_nonneg F.card ) using 1;
  · have h_split : (∑ y ∈ F, Real.exp (lam * ((if coord t y = decide (1 / 2 < pOn F (coord t) true) then 0 else 1) - fold (pOn F (coord t) true)))) =
      (∑ y ∈ F.filter (fun y => coord t y ≠ decide (1 / 2 < pOn F (coord t) true)), Real.exp (lam * (1 - fold (pOn F (coord t) true)))) +
      (∑ y ∈ F.filter (fun y => coord t y = decide (1 / 2 < pOn F (coord t) true)), Real.exp (lam * (-fold (pOn F (coord t) true)))) := by
        rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> ring_nf;
        contradiction;
    have := fiber_error_card_eq F t; simp_all +decide ;
    rw [ show ( Finset.filter ( fun y => coord t y = decide ( 2⁻¹ < pOn F ( coord t ) true ) ) F ).card = F.card - ( Finset.filter ( fun y => ¬coord t y = decide ( 2⁻¹ < pOn F ( coord t ) true ) ) F ).card from eq_tsub_of_add_eq <| by rw [ Finset.card_filter_add_card_filter_not ] ] ; rw [ Nat.cast_sub <| Finset.card_filter_le _ _ ] ; norm_num ; ring_nf;
    grind;
  · exact le_min ( pOn_nonneg _ _ _ ) ( sub_nonneg.2 ( pOn_le_one _ _ _ ) );
  · exact le_trans ( fold_le_half _ ) ( by norm_num )

/-
The centered mismatch increment at coordinate `t` depends only on the
prefix window `{u | u.val < n}` whenever `t.val < n`: two points agreeing on
that window give the same increment.
-/
lemma delta_eq_of_prefix {m : ℕ} (A : Finset (Cube m)) (t : Fin m) (n : ℕ) (ht : t.val < n)
    (x y : Cube m)
    (hxy : proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x
         = proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) y) :
    (if coord t x = coord t (predictableCenter A x) then (0 : ℝ) else 1)
       - fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
    = (if coord t y = coord t (predictableCenter A y) then (0 : ℝ) else 1)
       - fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) y)) := by
  have h_eq : coord t x = coord t y := by
    unfold coord at *; simp_all +decide [ Finset.ext_iff, proj ] ;
  have h_eq_proj : proj (below Finset.univ t) x = proj (below Finset.univ t) y := by
    apply_rules [ proj_eq_of_subset ];
    exact fun u hu => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, lt_of_lt_of_le ( Finset.mem_filter.mp hu |>.2 ) ht.le ⟩
  have h_eq_rho : rho A t (proj (below Finset.univ t) x) = rho A t (proj (below Finset.univ t) y) := by
    rw [h_eq_proj]
  have h_eq_predictableCenter : coord t (predictableCenter A x) = coord t (predictableCenter A y) := by
    simp_all +decide [ predictableCenter, coord ]
  simp [h_eq, h_eq_proj, h_eq_predictableCenter]

/-
MGF telescoping over the revelation order: the total exponential moment of
the centered mismatch process is at most `|A| * exp (lam^2 m /8)`.
-/
set_option maxHeartbeats 4000000 in
lemma mgf_telescope {m : ℕ} (A : Finset (Cube m)) (lam : ℝ) :
    (∑ x ∈ A, Real.exp (lam * ∑ t : Fin m,
        ((if coord t x = coord t (predictableCenter A x) then (0 : ℝ) else 1)
          - fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)))))
      ≤ (A.card : ℝ) * Real.exp (lam ^ 2 * (m : ℝ) / 8) := by
  -- We prove by induction on n ≤ m:
  -- P(n): ∑_{x∈A} exp(lam * ∑_{t : Fin m, t.val < n} δ x t) ≤ |A| * exp(lam^2 * n / 8).
  have h_ind : ∀ n : ℕ, n ≤ m →
    (∑ x ∈ A, Real.exp (lam * (∑ t : Fin m, if t.val < n then
      ((if coord t x = coord t (predictableCenter A x) then 0 else 1) -
       fold (rho A t (proj (below Finset.univ t) x))) else 0)))
    ≤ (A.card : ℝ) * Real.exp (lam ^ 2 * n / 8) := by
      intro n hn;
      induction' n with n ih;
      · norm_num;
      · -- Split the sum into the sum over the prefix and the sum over the suffix.
        have h_split : ∑ x ∈ A, Real.exp (lam * (∑ t : Fin m, if t.val < n + 1 then
          ((if coord t x = coord t (predictableCenter A x) then 0 else 1) -
           fold (rho A t (proj (below Finset.univ t) x))) else 0)) =
          ∑ w ∈ Finset.image (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x) A,
          ∑ x ∈ A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w),
          Real.exp (lam * (∑ t : Fin m, if t.val < n then
            ((if coord t x = coord t (predictableCenter A x) then 0 else 1) -
             fold (rho A t (proj (below Finset.univ t) x))) else 0)) *
          Real.exp (lam * ((if coord ⟨n, by linarith⟩ x = coord ⟨n, by linarith⟩ (predictableCenter A x) then 0 else 1) -
           fold (rho A ⟨n, by linarith⟩ (proj (below Finset.univ ⟨n, by linarith⟩) x)))) := by
             rw [ Finset.sum_image' ];
             intro x hx; refine' Finset.sum_congr rfl fun y hy => _; simp +decide [ Finset.sum_ite ] ;
             rw [ ← Real.exp_add ] ; congr 1 ; ring_nf;
             rw [ show ( Finset.filter ( fun x : Fin m => ( x : ℕ ) ≤ n ) Finset.univ ) = Finset.filter ( fun x : Fin m => ( x : ℕ ) < n ) Finset.univ ∪ { ⟨ n, by linarith ⟩ } from ?_, Finset.sum_union ] <;> norm_num;
             · split_ifs <;> simp_all +decide [ Finset.filter_insert ] <;> ring;
             · grind +splitImp;
        -- Apply the induction hypothesis to each term in the sum.
        have h_ind_step : ∀ w ∈ Finset.image (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x) A,
          ∑ x ∈ A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w),
            Real.exp (lam * ((if coord ⟨n, by linarith⟩ x = coord ⟨n, by linarith⟩ (predictableCenter A x) then 0 else 1) -
             fold (rho A ⟨n, by linarith⟩ (proj (below Finset.univ ⟨n, by linarith⟩) x)))) ≤
            (A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w)).card * Real.exp (lam ^ 2 / 8) := by
              intro w hw;
              convert fiber_mgf_le ( A.filter ( fun x => proj ( Finset.filter ( fun u : Fin m => u.val < n ) Finset.univ ) x = w ) ) ⟨ n, by linarith ⟩ lam using 1;
              refine' Finset.sum_congr rfl fun x hx => _;
              congr! 2;
              congr! 2;
              · simp +decide [ predictableCenter_mem_iff, coord ];
                unfold rho pOn; simp +decide [ Finset.filter_filter ] ;
                congr! 2;
                · congr! 2;
                  ext; simp [below];
                  grind;
                · congr! 2;
                  ext; simp [below];
                  grind;
              · unfold rho pOn;
                congr! 2;
                · congr! 2;
                  ext; simp [below];
                  grind;
                · congr! 2;
                  ext; simp +decide [ Finset.ext_iff, below ] ;
                  grind +qlia;
        -- Apply the induction hypothesis to each term in the sum and simplify.
        have h_ind_step_simplified : ∑ w ∈ Finset.image (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x) A,
            ∑ x ∈ A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w),
            Real.exp (lam * (∑ t : Fin m, if t.val < n then
              ((if coord t x = coord t (predictableCenter A x) then 0 else 1) -
               fold (rho A t (proj (below Finset.univ t) x))) else 0)) *
            Real.exp (lam * ((if coord ⟨n, by linarith⟩ x = coord ⟨n, by linarith⟩ (predictableCenter A x) then 0 else 1) -
             fold (rho A ⟨n, by linarith⟩ (proj (below Finset.univ ⟨n, by linarith⟩) x)))) ≤
            Real.exp (lam ^ 2 / 8) * ∑ x ∈ A,
            Real.exp (lam * (∑ t : Fin m, if t.val < n then
              ((if coord t x = coord t (predictableCenter A x) then 0 else 1) -
               fold (rho A t (proj (below Finset.univ t) x))) else 0)) := by
                 have h_ind_step_simplified : ∀ w ∈ Finset.image (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x) A,
                     ∑ x ∈ A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w),
                       Real.exp (lam * (∑ t : Fin m, if t.val < n then
                         ((if coord t x = coord t (predictableCenter A x) then 0 else 1) -
                          fold (rho A t (proj (below Finset.univ t) x))) else 0)) *
                       Real.exp (lam * ((if coord ⟨n, by linarith⟩ x = coord ⟨n, by linarith⟩ (predictableCenter A x) then 0 else 1) -
                        fold (rho A ⟨n, by linarith⟩ (proj (below Finset.univ ⟨n, by linarith⟩) x)))) ≤
                       Real.exp (lam ^ 2 / 8) * ∑ x ∈ A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w),
                       Real.exp (lam * (∑ t : Fin m, if t.val < n then
                         ((if coord t x = coord t (predictableCenter A x) then 0 else 1) -
                          fold (rho A t (proj (below Finset.univ t) x))) else 0)) := by
                            intros w hw
                            have h_const : ∀ x ∈ A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w), ∀ y ∈ A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w), (∑ t : Fin m, if t.val < n then ((if coord t x = coord t (predictableCenter A x) then 0 else 1) - fold (rho A t (proj (below Finset.univ t) x))) else 0) = (∑ t : Fin m, if t.val < n then ((if coord t y = coord t (predictableCenter A y) then 0 else 1) - fold (rho A t (proj (below Finset.univ t) y))) else 0) := by
                              grind +suggestions;
                            obtain ⟨x, hx⟩ : ∃ x ∈ A.filter (fun x => proj (Finset.filter (fun u : Fin m => u.val < n) Finset.univ) x = w), True := by
                              rw [ Finset.mem_image ] at hw; obtain ⟨ x, hx, rfl ⟩ := hw; exact ⟨ x, Finset.mem_filter.mpr ⟨ hx, rfl ⟩, trivial ⟩ ;
                            convert mul_le_mul_of_nonneg_left ( h_ind_step w hw ) ( Real.exp_nonneg ( lam * ( ∑ t : Fin m, if t.val < n then ( if coord t x = coord t ( predictableCenter A x ) then 0 else 1 ) - fold ( rho A t ( proj ( below Finset.univ t ) x ) ) else 0 ) ) ) using 1;
                            · rw [ Finset.mul_sum _ _ _ ];
                              exact Finset.sum_congr rfl fun y hy => by rw [ h_const y hy x hx.1 ] ;
                            · rw [ Finset.sum_congr rfl fun y hy => by rw [ h_const y hy x hx.1 ] ] ; norm_num ; ring;
                 refine' le_trans ( Finset.sum_le_sum h_ind_step_simplified ) _;
                 rw [ ← Finset.mul_sum _ _ _ ];
                 rw [ Finset.sum_image' ];
                 exact fun _ _ => rfl;
        convert h_ind_step_simplified.trans ( mul_le_mul_of_nonneg_left ( ih ( Nat.le_of_succ_le hn ) ) ( Real.exp_nonneg _ ) ) using 1 ; push_cast ; ring_nf;
        rw [ Real.exp_add ] ; ring;
  simpa using h_ind m le_rfl

lemma azuma_center_distance {m : ℕ} (A : Finset (Cube m)) (hA : A.Nonempty) (eps : ℝ)
    (heps : 0 ≤ eps) :
    let c := predictableCenter A
    let r_t := fun x t => fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
    pOn A (fun x => decide (eps * (m : ℝ) ≤ (hDist x (c x) : ℝ) - ∑ t : Fin m, r_t x t)) true
      ≤ Real.exp (-eps ^ 2 * (m : ℝ) / 2) := by
  -- Set lambda = 4 * eps and apply Markov's inequality.
  set lam : ℝ := 4 * eps
  have h_markov : (∑ x ∈ A, Real.exp (lam * (hDist x (predictableCenter A x) - ∑ t, fold (rho A t (proj (below Finset.univ t) x))))) ≥ (∑ x ∈ A.filter (fun x => eps * m ≤ hDist x (predictableCenter A x) - ∑ t, fold (rho A t (proj (below Finset.univ t) x))), Real.exp (lam * (eps * m))) := by
    refine' le_trans ( Finset.sum_le_sum fun x hx => Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left ( Finset.mem_filter.mp hx |>.2 ) <| by positivity ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Real.exp_nonneg _ );
  -- By dividing both sides of the inequality by $|A|$, we obtain the desired result.
  have h_div : (A.filter (fun x => eps * m ≤ hDist x (predictableCenter A x) - ∑ t, fold (rho A t (proj (below Finset.univ t) x)))).card / A.card ≤ Real.exp (lam^2 * m / 8) / Real.exp (lam * eps * m) := by
    rw [ div_le_div_iff₀ ] <;> try positivity;
    convert h_markov.trans _ using 1;
    · norm_num [ mul_assoc ];
    · convert mgf_telescope A lam using 1 ; ring_nf;
      · simp +decide [ ← mul_sub, hDist_eq_sum_indicator ];
      · ring;
  convert h_div.trans _ using 1;
  · unfold pOn; aesop;
  · rw [ ← Real.exp_sub ] ; ring_nf ; norm_num;
    nlinarith [ show 0 ≤ eps ^ 2 * m by positivity ]

-- ============================================================================
-- S6 Leaves (Entropy Compression)
-- ============================================================================

lemma bool_center_coord_image_le_two {m : ℕ} (A : Finset (Cube m)) (t : Fin m) :
    ((A.image (fun x => coord t (predictableCenter A x))).card : ℝ) ≤ 2 := by
  have hcard :
      (A.image (fun x => coord t (predictableCenter A x))).card ≤ 2 := by
    simpa using
      (Finset.card_le_univ (s := A.image (fun x => coord t (predictableCenter A x))))
  exact_mod_cast hcard

noncomputable def centerMajorityEstimator {m : ℕ} (A : Finset (Cube m))
    (J : Finset (Fin m)) (x : Cube m) (t : Fin m) : Bool :=
  decide (1 / 2 <
    pOn (A.filter fun y => proj (below J t) y = proj (below J t) x)
      (fun y => coord t (predictableCenter A y)) true)

lemma center_majority_estimator_dependsOnWindow {m : ℕ} (A : Finset (Cube m))
    (J : Finset (Fin m)) :
    dependsOnWindow J (centerMajorityEstimator A J) := by
  intro x y hxy
  funext t
  have hbelow : below J t ⊆ J := Finset.filter_subset _ _
  have hproj : proj (below J t) x = proj (below J t) y :=
    proj_eq_of_subset hbelow hxy
  simp [centerMajorityEstimator, hproj]

lemma sublinear_eventual_le_linear (f : ℕ → ℝ) (hf : Sublinear f) (eps : ℝ) (heps : 0 < eps) :
    ∃ N, ∀ n ≥ N, f n ≤ eps * n := by
  exact hf.2 eps heps

lemma dist_le_ceil_q_four_eps {m : ℕ} (x y : Cube m) {q eps : ℝ}
    (heps : 0 ≤ eps)
    (hdist : (hDist x y : ℝ) ≤ (q + 3 * eps) * (m : ℝ)) :
    hDist x y ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ)) := by
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hle : (hDist x y : ℝ) ≤ (q + 4 * eps) * (m : ℝ) := by
    nlinarith
  have hceil : (hDist x y : ℝ) ≤
      (Nat.ceil ((q + 4 * eps) * (m : ℝ)) : ℝ) :=
    hle.trans (Nat.le_ceil _)
  exact_mod_cast hceil

lemma blockRegularFamily_from_R3 (Q : QData) (_hR3 : R3Statement)
    (hQ : validQData Q) :
    ∃ sFam : ℝ → ℕ → ℝ, (∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (sFam pLow)) ∧
      ∀ m A q, A.Nonempty → fat Q m A q → pinned Q m A q →
        blockRegularFamily m A q sFam := by
  classical
  let sFam : ℝ → ℕ → ℝ := fun pLow =>
    if h : 0 < pLow ∧ pLow ≤ 1 / 2 then
      Classical.choose (_hR3 Q pLow hQ h.1 h.2)
    else
      fun _ => 0
  refine ⟨sFam, ?_, ?_⟩
  · intro pLow hpLow hpLow_le
    have h : 0 < pLow ∧ pLow ≤ 1 / 2 := ⟨hpLow, hpLow_le⟩
    dsimp [sFam]
    rw [dif_pos h]
    exact (Classical.choose_spec (_hR3 Q pLow hQ hpLow hpLow_le)).1
  · intro m A q hA hfat hpinned pLow hpLow hpLow_le
    have h : 0 < pLow ∧ pLow ≤ 1 / 2 := ⟨hpLow, hpLow_le⟩
    dsimp [sFam]
    rw [dif_pos h]
    exact (Classical.choose_spec (_hR3 Q pLow hQ hpLow hpLow_le)).2
      m A q hA hfat hpinned

/-- Local (Core-scoped) copies of the sublinearity toolkit (the originals live
in the `Volume` layer, which `Core` may not import). -/
lemma core_Sublinear_const {c : ℝ} (hc : 0 ≤ c) : Sublinear (fun _ => c) := by
  refine ⟨fun _ => hc, fun ε hε => ?_⟩
  refine ⟨Nat.ceil (c / ε), fun n hn => ?_⟩
  have h1 : c / ε ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [div_le_iff₀ hε] at h1
  linarith [h1]

lemma core_Sublinear_add {s t : ℕ → ℝ} (hs : Sublinear s) (ht : Sublinear t) :
    Sublinear (fun n => s n + t n) := by
  refine ⟨fun n => add_nonneg (hs.1 n) (ht.1 n), fun ε hε => ?_⟩
  obtain ⟨N1, hN1⟩ := hs.2 (ε/2) (by linarith)
  obtain ⟨N2, hN2⟩ := ht.2 (ε/2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 := hN2 n (le_trans (le_max_right _ _) hn)
  simp only
  linarith

lemma core_Sublinear_smul {c : ℝ} (hc : 0 ≤ c) {s : ℕ → ℝ} (hs : Sublinear s) :
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

lemma core_Sublinear_of_le {s t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (hle : ∀ n, t n ≤ s n) (hs : Sublinear s) : Sublinear t := by
  refine ⟨ht0, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hs.2 ε hε
  exact ⟨N, fun n hn => (hle n).trans (hN n hn)⟩

lemma core_Sublinear_of_eventually_zero {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (N : ℕ) (hN : ∀ n, N ≤ n → f n = 0) : Sublinear f := by
  refine ⟨hf0, fun ε hε => ⟨N, fun n hn => ?_⟩⟩
  rw [hN n hn]; positivity

/-
The geometric mean of a sublinear function with the identity is sublinear:
if `s = o(m)` then `sqrt((s m + 1)(m + 1)) = o(m)`.
-/
lemma core_Sublinear_geomMean {s : ℕ → ℝ} (hs : Sublinear s) :
    Sublinear (fun m => Real.sqrt ((s m + 1) * ((m : ℝ) + 1))) := by
  constructor;
  · exact fun n => Real.sqrt_nonneg _;
  · intro ε hε;
    -- Since `s` is sublinear, apply `hs.2 (ε^2/4)` to get `N0` with `s m ≤ (ε^2/4)*m` for `m ≥ N0`.
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ m ≥ N0, s m ≤ (ε^2 / 4) * m := by
      exact hs.2 ( ε ^ 2 / 4 ) ( by positivity );
    refine' ⟨ N0 + ⌈4 / ε ^ 2⌉₊ + 1, fun n hn => Real.sqrt_le_iff.mpr ⟨ by positivity, _ ⟩ ⟩;
    have := hN0 n ( by linarith );
    nlinarith [ show ( n : ℝ ) ≥ ⌈4 / ε ^ 2⌉₊ + 1 by norm_cast; linarith, Nat.le_ceil ( 4 / ε ^ 2 ), mul_div_cancel₀ 4 ( ne_of_gt ( sq_pos_of_pos hε ) ), pow_two_nonneg ( ε * n - 2 ), pow_two_nonneg ( ε * n + 2 ), hs.1 n ]

/-
sqrt algebra: `sqrt((a+1)/(n+1)) * n ≤ sqrt((a+1)(n+1))`.
-/
lemma core_geomMean_mul_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt ((a + 1) / ((n : ℝ) + 1)) * (n : ℝ)
      ≤ Real.sqrt ((a + 1) * ((n : ℝ) + 1)) := by
  convert Real.le_sqrt_of_sq_le _ using 1;
  rw [ mul_pow, Real.sq_sqrt <| by positivity, div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ sq ( n : ℝ ) ]

/-
sqrt algebra: `a / sqrt((a+1)/(n+1)) ≤ sqrt((a+1)(n+1))`.
-/
lemma core_div_geomMean_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    a / Real.sqrt ((a + 1) / ((n : ℝ) + 1))
      ≤ Real.sqrt ((a + 1) * ((n : ℝ) + 1)) := by
  rw [ div_le_iff₀ ( Real.sqrt_pos.mpr <| by positivity ) ];
  rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.le_sqrt_of_sq_le <| by nlinarith [ sq_nonneg a, mul_div_cancel₀ ( a + 1 ) ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ] ;

/-
Window inclusion (lower): for `m ≥ 30`, `(1/6) m ≤ ⌊m/5⌋`.
-/
lemma core_window_floor_lower (m : ℕ) (hm : 30 ≤ m) :
    (1 / 6 : ℝ) * (m : ℝ) ≤ ((m / 5 : ℕ) : ℝ) := by
  rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast ; linarith [ Nat.div_add_mod m 5, Nat.mod_lt m ( by decide : 5 > 0 ) ]

/-
Window inclusion (upper): for `m ≥ 30`, `m - ⌊m/5⌋ ≤ (5/6) m`.
-/
lemma core_window_floor_upper (m : ℕ) (hm : 30 ≤ m) :
    (m : ℝ) - ((m / 5 : ℕ) : ℝ) ≤ (1 - 1 / 6 : ℝ) * (m : ℝ) := by
  convert sub_le_sub_left ( core_window_floor_lower m hm ) ( m : ℝ ) using 1 ; ring

/-
Variance of a `[0,1]`-valued statistic is at most `1`.
-/
lemma core_varOn_le_one {m : ℕ} (A : Finset (Cube m)) (f : Cube m → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : varOn A f ≤ 1 := by
  refine' div_le_one_of_le₀ _ _;
  · refine' le_trans ( Finset.sum_le_sum fun x hx => show ( f x - ( ∑ x ∈ A, f x ) / A.card ) ^ 2 ≤ 1 by nlinarith only [ hf0 x, hf1 x, show ( ∑ x ∈ A, f x ) / A.card ≥ 0 by exact div_nonneg ( Finset.sum_nonneg fun _ _ => hf0 _ ) ( Nat.cast_nonneg _ ), show ( ∑ x ∈ A, f x ) / A.card ≤ 1 by exact div_le_one_of_le₀ ( le_trans ( Finset.sum_le_sum fun _ _ => hf1 _ ) ( by norm_num ) ) ( Nat.cast_nonneg _ ) ] ) ( by norm_num );
  · positivity

/-
Conditional variance of a `[0,1]`-valued statistic is at most `1`.
-/
lemma core_uCondVar_le_one {m : ℕ} {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (f : Cube m → ℝ) (g : Cube m → B)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : uCondVar A f g ≤ 1 := by
  unfold uCondVar;
  refine' le_trans ( Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left ( core_varOn_le_one _ _ ( fun x => hf0 x ) ( fun x => hf1 x ) ) ( _ ) ) _;
  · exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
  · by_cases hA : A.Nonempty <;> simp_all +decide [ pOn ];
    rw [ ← Finset.sum_div _ _ _, div_le_iff₀ ] <;> norm_cast <;> simp_all +decide ;
    grind +suggestions

/-
Trivial dimension bound for the variance budget.
-/
lemma core_varianceBudgetLE_dim {m : ℕ} (A : Finset (Cube m)) (pLow : ℝ) :
    varianceBudgetLE A pLow (m : ℝ) := by
  intro W hW1 hW2;
  refine' le_trans ( Finset.sum_le_sum fun t ht => core_uCondVar_le_one A _ _ ( fun x => rho_nonneg A t _ ) ( fun x => rho_le_one A t _ ) ) _;
  simpa using Finset.card_le_univ W

lemma varianceFamily_from_R3_S1_S2 (Q : QData) (_hR3 : R3Statement) (_hS1 : S1Statement) (_hS2 : S2Statement)
    (hQ : validQData Q) :
    ∃ vFam : ℝ → ℕ → ℝ, (∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow)) ∧
      ∀ m A q, A.Nonempty → fat Q m A q → pinned Q m A q →
        ∀ pLow, 0 < pLow → pLow ≤ 1 / 2 → varianceBudgetLE A pLow (vFam pLow m) := by
  revert _hR3 _hS1 _hS2;
  intro _hR3 _hS1 _hS2
  obtain ⟨sFam, hsFam_sub, hsFam⟩ := blockRegularFamily_from_R3 Q _hR3 hQ
  set sslack := fun m => sFam (1/6) m + Q.sigma m with h_sslack
  set epsm := fun m => Real.sqrt ((sslack m + 1) / ((m : ℝ) + 1)) with h_epsm
  set vFam := fun pLow m => (sFam pLow m + epsm m * (m : ℝ) + (12 * (sslack m / epsm m) + 4) * Real.log 2) / 2 + (if m < 30 then (m : ℝ) else 0) with h_vFam
  use vFam
  constructor
  intro pLow hpLow hpLow_le
  have h_sslack_sub : Sublinear sslack := by
    exact core_Sublinear_add ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) ) hQ.2.2.2.2.2.2.1
  have h_epsm_sub : Sublinear (fun m => epsm m * (m : ℝ)) := by
    convert core_Sublinear_of_le ( fun n => by positivity ) ( fun n => core_geomMean_mul_le ( sslack n ) ( ?_ ) n ) ( core_Sublinear_geomMean h_sslack_sub ) using 1;
    exact add_nonneg ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) |>.1 n ) ( hQ.2.2.2.2.2.2.1 |>.1 n )
  have h_div_sub : Sublinear (fun m => sslack m / epsm m) := by
    apply core_Sublinear_of_le (fun n => by
      apply div_nonneg;
      · exact add_nonneg ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) |>.1 n ) ( hQ.2.2.2.2.2.2.1.1 n );
      · exact Real.sqrt_nonneg _) (fun n => by
      convert core_div_geomMean_le ( sslack n ) ( show 0 ≤ sslack n from _ ) n using 1;
      exact add_nonneg ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) |> fun h => h.1 n ) ( hQ.2.2.2.2.2.2.1 |> fun h => h.1 n )) (core_Sublinear_geomMean h_sslack_sub)
  have h_log_sub : Sublinear (fun m => (12 * (sslack m / epsm m) + 4) * Real.log 2) := by
    convert core_Sublinear_smul ( show 0 ≤ Real.log 2 by positivity ) ( core_Sublinear_add ( core_Sublinear_smul ( show 0 ≤ 12 by norm_num ) h_div_sub ) ( core_Sublinear_const ( show 0 ≤ 4 by norm_num ) ) ) using 1 ; ext m ; ring
  have h_vFam_sub : Sublinear (fun m => (sFam pLow m + epsm m * (m : ℝ) + (12 * (sslack m / epsm m) + 4) * Real.log 2) / 2) := by
    convert core_Sublinear_smul ( show 0 ≤ 1 / 2 by norm_num ) ( core_Sublinear_add ( core_Sublinear_add ( hsFam_sub pLow hpLow hpLow_le ) h_epsm_sub ) h_log_sub ) using 1 ; ext ; ring;
  apply core_Sublinear_add h_vFam_sub;
  apply core_Sublinear_of_eventually_zero (fun n => by positivity) 30 (fun n hn => by simp [Nat.not_lt.mpr hn])
  intro m A q hA hfat hpinned pLow hpLow hpLow_le
  by_cases hm : m < 30
  simp [vFam, hm] at *;
  · refine' fun W h1 h2 => le_trans ( core_varianceBudgetLE_dim A pLow W h1 h2 ) _;
    exact le_add_of_nonneg_left ( div_nonneg ( add_nonneg ( add_nonneg ( hsFam_sub pLow hpLow hpLow_le |>.1 m ) ( mul_nonneg ( Real.sqrt_nonneg _ ) ( Nat.cast_nonneg _ ) ) ) ( mul_nonneg ( add_nonneg ( mul_nonneg ( by norm_num ) ( div_nonneg ( add_nonneg ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) |>.1 m ) ( hQ.2.2.2.2.2.2.1.1 m ) ) ( Real.sqrt_nonneg _ ) ) ) ( by norm_num ) ) ( Real.log_nonneg ( by norm_num ) ) ) ) zero_le_two );
  · -- Set `sS := sslack m`, `epsS := epsm m` (`>0`), `kappa := H q`.
    set sS := sslack m with h_sS
    set epsS := epsm m with h_epsS
    set kappa := H q with h_kappa;
    -- Build S1 flatness `hflat` and lower bound `hlow`.
    have hflat : ∀ I : Finset (Fin m), ((m / 5 : ℕ) : ℝ) ≤ I.card → I.card ≤ (m : ℝ) - ((m / 5 : ℕ) : ℝ) → uH A (proj I) ≤ kappa * I.card + sS := by
      intros I hI₁ hI₂
      have hI₃ : (1 / 6 : ℝ) * m ≤ I.card := by
        exact le_trans ( by rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast ; linarith [ Nat.div_add_mod m 5, Nat.mod_lt m ( by decide : 5 > 0 ) ] ) hI₁
      have hI₄ : I.card ≤ (1 - 1 / 6 : ℝ) * m := by
        exact le_trans hI₂ ( by linarith [ show ( m : ℝ ) ≥ 30 by norm_cast; linarith, show ( m / 5 : ℕ ) ≥ ( m : ℝ ) / 5 - 1 by exact sub_le_iff_le_add.mpr <| by rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ Nat.div_add_mod m 5, Nat.mod_lt m ( by norm_num : 5 > 0 ) ] ] )
      have hI₅ : |uH A (proj I) - kappa * I.card| ≤ sFam (1 / 6) m := by
        exact hsFam m A q hA hfat hpinned ( 1 / 6 ) ( by norm_num ) ( by norm_num ) |>.2.2 I hI₃ hI₄
      have hI₆ : uH A (proj I) ≤ kappa * I.card + sS := by
        linarith [ abs_le.mp hI₅, show 0 ≤ Q.sigma m from hQ.2.2.2.2.2.2.1.1 m ]
      exact hI₆
    have hlow : kappa * (m : ℝ) - sS ≤ uH A (proj Finset.univ) := by
      have hlow : kappa * (m : ℝ) - Q.sigma m ≤ uH A (proj Finset.univ) := by
        have := hfat.2.2.2.2;
        rw [ uH_proj_univ A hA ] ; linarith [ abs_le.mp this ];
      linarith [ show 0 ≤ sFam ( 1 / 6 ) m from ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) ).1 m ];
    -- Apply S1 to get the bound on the number of bad steps.
    obtain ⟨count, hcount⟩ : ∃ count : ℕ, ((Finset.univ.filter (fun t => epsS ≤ |hstep A t - H q|)).card : ℝ) ≤ count ∧ count ≤ 12 * sS / epsS + 4 := by
      have := _hS1 m A kappa sS epsS hA (by
      exact add_nonneg ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) |>.1 m ) ( hQ.2.2.2.2.2.2.1.1 m )) (by
      exact Real.sqrt_pos.mpr ( div_pos ( add_pos_of_nonneg_of_pos ( add_nonneg ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) |>.1 m ) ( hQ.2.2.2.2.2.2.1.1 m ) ) zero_lt_one ) ( by positivity ) )) hflat hlow;
      exact ⟨ _, le_rfl, this ⟩;
    have := _hS2 m A q pLow ( sFam pLow m ) epsS count hA hpLow hpLow_le ( hsFam_sub pLow hpLow hpLow_le |>.1 m ) ( Real.sqrt_pos.mpr <| div_pos ( add_pos_of_nonneg_of_pos ( add_nonneg ( hsFam_sub ( 1 / 6 ) ( by norm_num ) ( by norm_num ) |>.1 m ) ( hQ.2.2.2.2.2.2.1.1 m ) ) zero_lt_one ) ( by positivity ) ) ( by positivity ) ( hsFam m A q hA hfat hpinned pLow hpLow hpLow_le ) ( by linarith ) ; simp_all +decide [ varianceBudgetLE ] ;
    intro W hW₁ hW₂; specialize this W hW₁ hW₂; split_ifs <;> simp_all +decide [ mul_div_assoc ] ;
    · grind;
    · exact this.trans ( by gcongr ; linarith )

-- ============================================================================
-- S5 Leaves (Heavy Atom Infrastructure)
-- ============================================================================

lemma validQData_sigma_add_sublinear (Q : QData) (G : ℕ → ℝ)
    (hQ : validQData Q) (hG : Sublinear G) :
    validQData { Q with sigma := fun m => Q.sigma m + G m } := by
  rcases hQ with ⟨hqMin_pos, hqMin_le, hqMax_lt, hs0_pos, hmu0_pos,
    hreg, hsigma, hlog⟩
  refine ⟨hqMin_pos, hqMin_le, hqMax_lt, hs0_pos, hmu0_pos, hreg, ?_, ?_⟩
  · refine ⟨fun n => add_nonneg (hsigma.1 n) (hG.1 n), ?_⟩
    intro eps heps
    obtain ⟨N1, hN1⟩ := hsigma.2 (eps / 2) (by linarith)
    obtain ⟨N2, hN2⟩ := hG.2 (eps / 2) (by linarith)
    refine ⟨max N1 N2, ?_⟩
    intro n hn
    have h1 := hN1 n (le_trans (Nat.le_max_left N1 N2) hn)
    have h2 := hN2 n (le_trans (Nat.le_max_right N1 N2) hn)
    linarith
  · intro m hm
    have hG_nonneg := hG.1 m
    linarith [hlog m hm]


lemma binnedFoldField_same_atom_interval {m : ℕ} (A : Finset (Cube m)) (w o : ℝ) (hw : 0 < w) (t : Fin m) (x y : Cube m)
    (h_same : binnedFoldField A w o x t = binnedFoldField A w o y t) :
    |fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) - fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) y))| < w := by
  have h1 := h_same
  dsimp [binnedFoldField] at h1
  have hw_pos : 0 < w := hw
  have hw_ne_zero : w ≠ 0 := ne_of_gt hw
  let fx := fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
  let fy := fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) y))
  change |fx - fy| < w
  have h_le_x := Int.floor_le ((fx - o) / w)
  have h_lt_x := Int.lt_floor_add_one ((fx - o) / w)
  have h_le_y := Int.floor_le ((fy - o) / w)
  have h_lt_y := Int.lt_floor_add_one ((fy - o) / w)
  rw [h1] at h_le_x h_lt_x
  rw [abs_lt]
  constructor
  · have h2 : (fy - o) / w < (fx - o) / w + 1 := by linarith
    have h3 : (fy - o) / w < (fx - o + w) / w := by
      calc
        (fy - o) / w < (fx - o) / w + 1 := h2
        _ = (fx - o) / w + w / w := by rw [div_self hw_ne_zero]
        _ = (fx - o + w) / w := by ring
    have h4 : fy - o < fx - o + w := (div_lt_div_iff_of_pos_right hw_pos).mp h3
    linarith
  · have h2 : (fx - o) / w < (fy - o) / w + 1 := by linarith
    have h3 : (fx - o) / w < (fy - o + w) / w := by
      calc
        (fx - o) / w < (fy - o) / w + 1 := h2
        _ = (fy - o) / w + w / w := by rw [div_self hw_ne_zero]
        _ = (fy - o + w) / w := by ring
    have h4 : fx - o < fy - o + w := (div_lt_div_iff_of_pos_right hw_pos).mp h3
    linarith

end HarperStability
