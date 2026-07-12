import HarperStability.Core.Basic


namespace HarperStability

open Finset

attribute [local instance] Classical.propDecidable

lemma majority_error_uE_eq_min_pOn {m : ℕ} (F : Finset (Cube m))
    (P : Cube m → Prop) [DecidablePred P] :
    uE F (fun x =>
      if decide (P x) = decide (1 / 2 < pOn F (fun x => decide (P x)) true)
        then (0 : ℝ) else 1)
      = min (pOn F (fun x => decide (P x)) true)
          (1 - pOn F (fun x => decide (P x)) true) := by
  by_cases hmaj : 1 / 2 < pOn F (fun x => decide (P x)) true
  · have hF : F.Nonempty := by
      by_contra h
      have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [hFempty, pOn] at hmaj
      norm_num at hmaj
    have hcomp := one_sub_pOn_bool_eq_not F P hF
    have hdec :
        decide (1 / 2 < pOn F (fun x => decide (P x)) true) = true :=
      decide_eq_true hmaj
    have herr :
        uE F (fun x =>
          if decide (P x) = decide (1 / 2 < pOn F (fun x => decide (P x)) true)
            then (0 : ℝ) else 1)
          = pOn F (fun x => decide (¬ P x)) true := by
      rw [hdec]
      unfold uE pOn
      simp +decide [Finset.sum_ite]
    have hmin :
        min (pOn F (fun x => decide (P x)) true)
          (1 - pOn F (fun x => decide (P x)) true)
          = 1 - pOn F (fun x => decide (P x)) true := by
      rw [min_eq_right]
      linarith
    rw [herr, ← hcomp, hmin]
  · have hle : pOn F (fun x => decide (P x)) true ≤ 1 / 2 := le_of_not_gt hmaj
    have hdec :
        decide (1 / 2 < pOn F (fun x => decide (P x)) true) = false :=
      decide_eq_false hmaj
    have herr :
        uE F (fun x =>
          if decide (P x) = decide (1 / 2 < pOn F (fun x => decide (P x)) true)
            then (0 : ℝ) else 1)
          = pOn F (fun x => decide (P x)) true := by
      rw [hdec]
      unfold uE pOn
      simp +decide
    have hmin :
        min (pOn F (fun x => decide (P x)) true)
          (1 - pOn F (fun x => decide (P x)) true)
          = pOn F (fun x => decide (P x)) true := by
      rw [min_eq_left]
      linarith
    rw [herr, hmin]

-- Decomposed leaf 1: Error bound on a single fiber
lemma center_majority_fiber_error {m : ℕ} (A : Finset (Cube m))
    (q qMax eps gap : ℝ) (hq_le : q ≤ qMax) (hqMax : qMax < 1 / 2)
    (heps : 0 < eps) (hgap : 0 < gap) (hgap_le : qMax + eps ≤ 1 / 2 - gap)
    (J : Finset (Fin m)) (t : Fin m) (w : Cube m) :
    let F := A.filter (fun y => proj (below J t) y = w)
    let rho_y := fun y => rho A t (proj (below (univ : Finset (Fin m)) t) y)
    let c_y := fun y => coord t (predictableCenter A y)
    let bad_y := fun y => decide (eps ≤ |fold (rho_y y) - q|)
    let err_y := fun y => if c_y y = decide (1 / 2 < pOn F c_y true) then (0 : ℝ) else 1
    uE F err_y ≤ (4 / gap ^ 2) * varOn F rho_y + 2 * pOn F bad_y true := by
  dsimp only
  let F := A.filter (fun y => proj (below J t) y = w)
  let rho_y : Cube m → ℝ :=
    fun y => rho A t (proj (below (univ : Finset (Fin m)) t) y)
  let c_y : Cube m → Bool := fun y => coord t (predictableCenter A y)
  have hc : c_y = fun y => decide ((1 / 2 : ℝ) < rho_y y) := by
    funext y
    dsimp [c_y, rho_y, coord]
    simp [predictableCenter_mem_iff]
  have htc := two_cluster_lemma F rho_y q qMax eps gap
    (fun x _ => rho_nonneg A t (proj (below (univ : Finset (Fin m)) t) x))
    (fun x _ => rho_le_one A t (proj (below (univ : Finset (Fin m)) t) x))
    hq_le hqMax heps hgap hgap_le
  change
    uE F (fun y => if c_y y = decide (1 / 2 < pOn F c_y true) then (0 : ℝ) else 1)
      ≤ (4 / gap ^ 2) * varOn F rho_y +
        2 * pOn F (fun y => decide (eps ≤ |fold (rho_y y) - q|)) true
  rw [hc]
  rw [majority_error_uE_eq_min_pOn F (fun y => (1 / 2 : ℝ) < rho_y y)]
  simpa [hc, rho_y] using htc

lemma averageBadStepsLE_sum_pOn {m : ℕ} (A : Finset (Cube m))
    (q eps massSlack : ℝ) (hA : A.Nonempty)
    (h_bad : averageBadStepsLE A q eps massSlack) :
    (∑ t : Fin m,
      pOn A (fun x =>
        decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
        true) ≤ massSlack := by
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have h_sum_delta :
      (∑ t : Fin m,
        pOn A (fun x =>
          decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
          true)
        =
      uE A (fun x =>
        (((univ : Finset (Fin m)).filter fun t =>
          eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|).card : ℝ)) := by
    unfold pOn uE
    simp +decide only [Finset.card_filter]
    simp +decide only [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop)
  rw [h_sum_delta]
  unfold averageBadStepsLE at h_bad
  unfold uE
  rw [div_le_iff₀ hApos]
  exact h_bad

-- Top-level target 1 (reconstructed via fiber summation)
lemma uE_eq_sum_uE_fiber {m : ℕ} {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (f : Cube m → ℝ) (g : Cube m → B) :
    uE A f = ∑ b ∈ image g A, pOn A g b * uE (A.filter (fun x => g x = b)) f := by
  by_cases hA : A.Nonempty
  · unfold uE pOn
    have Hsum : ∑ b ∈ image g A, ∑ i ∈ A.filter (fun x => g x = b), f i = ∑ i ∈ A, f i :=
      sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem g hi) f
    rw [← Hsum, sum_div]
    apply sum_congr rfl
    intro b _
    by_cases hF : (A.filter (fun x => g x = b)).Nonempty
    · have hFpos : (0 : ℝ) < ((A.filter (fun x => g x = b)).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
      have hFpos_ne : ((A.filter (fun x => g x = b)).card : ℝ) ≠ 0 := ne_of_gt hFpos
      rw [mul_comm]
      convert (@div_mul_div_cancel₀ ℝ _ (∑ x ∈ A.filter (fun x => g x = b), f x) ((A.filter (fun x => g x = b)).card : ℝ) (A.card : ℝ) hFpos_ne).symm
    · have hFempty : A.filter (fun x => g x = b) = ∅ := not_nonempty_iff_eq_empty.mp hF
      simp [hFempty]
  · have hAempty : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    simp [hAempty, uE]

lemma pOn_eq_sum_pOn_fiber {m : ℕ} {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (f : Cube m → Bool) (b_bool : Bool) (g : Cube m → B) :
    pOn A f b_bool = ∑ b ∈ image g A, pOn A g b * pOn (A.filter (fun x => g x = b)) f b_bool := by
  classical
  have hpOn_eq_uE :
      ∀ (S : Finset (Cube m)) (h : Cube m → Bool) (b : Bool),
        pOn S h b = uE S (fun x => if h x = b then (1 : ℝ) else 0) := by
    intro S h b
    norm_num [pOn, uE]
    apply congrArg (fun n : ℕ => (n : ℝ) / (S.card : ℝ))
    apply congrArg Finset.card
    ext x
    simp
  calc
    pOn A f b_bool
        = uE A (fun x => if f x = b_bool then (1 : ℝ) else 0) := by
          rw [hpOn_eq_uE]
    _ = ∑ b ∈ image g A,
          pOn A g b *
            uE (A.filter (fun x => g x = b))
              (fun x => if f x = b_bool then (1 : ℝ) else 0) := by
          exact uE_eq_sum_uE_fiber A
            (fun x => if f x = b_bool then (1 : ℝ) else 0) g
    _ = ∑ b ∈ image g A,
          pOn A g b * pOn (A.filter (fun x => g x = b)) f b_bool := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [hpOn_eq_uE]

lemma center_majority_error_le_twoCluster {m : ℕ} (A : Finset (Cube m))
    (q qMax eps gap : ℝ) (hq_le : q ≤ qMax) (hqMax : qMax < 1 / 2)
    (heps : 0 < eps) (hgap : 0 < gap) (hgap_le : qMax + eps ≤ 1 / 2 - gap)
    (J : Finset (Fin m)) (t : Fin m) :
    uE A (fun x => if coord t (predictableCenter A x) = centerMajorityEstimator A J x t then (0 : ℝ) else 1)
    ≤ (4 / gap ^ 2) * uCondVar A (fun x => rho A t (proj (below (univ : Finset (Fin m)) t) x)) (proj (below J t))
      + 2 * pOn A (fun x => decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|)) true := by
  classical
  let g : Cube m → Cube m := proj (below J t)
  let rho_y : Cube m → ℝ :=
    fun x => rho A t (proj (below (univ : Finset (Fin m)) t) x)
  let c_y : Cube m → Bool := fun x => coord t (predictableCenter A x)
  let bad_y : Cube m → Bool := fun x => decide (eps ≤ |fold (rho_y x) - q|)
  let err_y : Cube m → ℝ :=
    fun x => if c_y x = centerMajorityEstimator A J x t then (0 : ℝ) else 1
  let C : ℝ := 4 / gap ^ 2
  have hfiber :
      ∀ w ∈ image g A,
        uE (A.filter (fun x => g x = w)) err_y ≤
          C * varOn (A.filter (fun x => g x = w)) rho_y +
            2 * pOn (A.filter (fun x => g x = w)) bad_y true := by
    intro w _
    let F := A.filter (fun x => g x = w)
    have hcenter :
        uE F err_y =
          uE F (fun y =>
            if c_y y = decide (1 / 2 < pOn F c_y true) then (0 : ℝ) else 1) := by
      unfold uE
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxw : g x = w := (Finset.mem_filter.mp hx).2
      have hest :
          centerMajorityEstimator A J x t =
            decide (1 / 2 < pOn F c_y true) := by
        simp [centerMajorityEstimator, F, g, c_y, hxw]
      simp [err_y, hest]
    have hleaf := center_majority_fiber_error A q qMax eps gap hq_le hqMax
      heps hgap hgap_le J t w
    rw [hcenter]
    simpa [F, g, rho_y, c_y, bad_y, C] using hleaf
  have hsum :
      uE A err_y =
        ∑ w ∈ image g A, pOn A g w * uE (A.filter (fun x => g x = w)) err_y :=
    uE_eq_sum_uE_fiber A err_y g
  have hweighted :
      ∑ w ∈ image g A, pOn A g w * uE (A.filter (fun x => g x = w)) err_y
        ≤ ∑ w ∈ image g A,
          pOn A g w *
            (C * varOn (A.filter (fun x => g x = w)) rho_y +
              2 * pOn (A.filter (fun x => g x = w)) bad_y true) := by
    refine Finset.sum_le_sum ?_
    intro w hw
    exact mul_le_mul_of_nonneg_left (hfiber w hw) (pOn_nonneg A g w)
  calc
    uE A (fun x =>
        if coord t (predictableCenter A x) = centerMajorityEstimator A J x t
        then (0 : ℝ) else 1)
        = uE A err_y := by rfl
    _ = ∑ w ∈ image g A,
          pOn A g w * uE (A.filter (fun x => g x = w)) err_y := hsum
    _ ≤ ∑ w ∈ image g A,
          pOn A g w *
            (C * varOn (A.filter (fun x => g x = w)) rho_y +
              2 * pOn (A.filter (fun x => g x = w)) bad_y true) := hweighted
    _ = C * uCondVar A rho_y g + 2 * pOn A bad_y true := by
          rw [pOn_eq_sum_pOn_fiber A bad_y true g]
          unfold uCondVar
          have himage :
              @image (Cube m) (Cube m) (fun a b => Classical.propDecidable (a = b)) g A =
                image g A := by
            ext x
            simp
          rw [himage]
          simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_left_comm]
          apply Finset.sum_congr rfl
          intro w _
          congr 2
          apply congrArg (fun S : Finset (Cube m) => varOn S rho_y)
          ext x
          simp
    _ =
        (4 / gap ^ 2) *
            uCondVar A
              (fun x => rho A t (proj (below (univ : Finset (Fin m)) t) x))
              (proj (below J t)) +
          2 * pOn A
            (fun x =>
              decide
                (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
            true := by
          rfl

-- === Ported/auxiliary machinery for the variance-window conversion ===

-- Ported window-reindexing inequality (Core-local copy).
lemma core_windowProb_reindex_le (m : ℕ) (p : ℝ) (hp0 : 0 < p)
    (φ : Finset (Fin m) → Fin m → ℝ)
    (hφ : ∀ (J : Finset (Fin m)) (t : Fin m), t ∉ J → φ J t = φ (insert t J) t) :
    (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m, φ J t)
      ≤ (1 / p) * ∑ J : Finset (Fin m), windowProb J p * ∑ t ∈ J, φ J t := by
  have h_reindex_step : ∀ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∉ J), windowProb J p * φ J t = ∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * ((1 - p) / p) * φ J t := by
    intro t
    apply Finset.sum_bij (fun J _ => insert t J);
    · grind;
    · simp +contextual [ Finset.ext_iff ];
      grind;
    · exact fun J hJ => ⟨ J.erase t, by aesop ⟩;
    · intro J hJ; rw [ hφ J t ( by simpa using hJ ) ] ; simp +decide [ windowProb, Finset.card_insert_of_notMem ( by simpa using hJ ) ] ; ring;
      field_simp;
      exact Or.inl ( by rw [ ← pow_succ', show m - J.card = m - ( 1 + J.card ) + 1 by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 + J.card ≤ m from by linarith [ show J.card < m from lt_of_lt_of_le ( Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ J, by aesop_cat ⟩ ) ( by simp ) ] ] ] );
  have h_sum_reindex : ∑ J, windowProb J p * ∑ t, φ J t = ∑ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * φ J t + ∑ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∉ J), windowProb J p * φ J t := by
    simp +decide only [Finset.mul_sum _ _ _, ← Finset.sum_add_distrib]
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_filter_add_sum_filter_not ]
  have h_swap : (∑ J : Finset (Fin m), windowProb J p * ∑ t ∈ J, φ J t) = ∑ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * φ J t := by
    simp +decide only [Finset.mul_sum, Finset.sum_filter]
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop
  rw [ h_sum_reindex, h_swap ]
  have h_reindex_sum : (∑ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∉ J), windowProb J p * φ J t) = ∑ t : Fin m, ∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * ((1 - p) / p) * φ J t := by
    apply Finset.sum_congr rfl
    intro t _
    exact h_reindex_step t
  rw [ h_reindex_sum, ← Finset.sum_add_distrib ]
  rw [ Finset.mul_sum ]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro t _
  rw [ ← Finset.sum_add_distrib, Finset.mul_sum ]
  apply Finset.sum_congr rfl
  intro J _
  have : p ≠ 0 := by linarith
  calc
    windowProb J p * φ J t + windowProb J p * ((1 - p) / p) * φ J t
      = (windowProb J p * φ J t) * (1 + (1 - p) / p) := by ring
    _ = (windowProb J p * φ J t) * (1 / p) := by
      congr
      calc
        1 + (1 - p) / p = p / p + (1 - p) / p := by rw [div_self this]
        _ = (p + (1 - p)) / p := by rw [← add_div]
        _ = 1 / p := by ring
    _ = (1 / p) * (windowProb J p * φ J t) := by ring

-- Decomposed leaf 2: Window probability variance conversion.
--
-- NOTE.  The statement previously written here (with the exponentially small
-- tail `(m : ℝ) * Real.exp (- 2 * (p - pLow) ^ 2 * (m : ℝ))` and an overall
-- `4 / gap ^ 2` factor) is FALSE: letting `gap → 0` sends the left-hand side
-- to `+∞` while the tail term stays bounded, so no proof can exist.  The
-- honest, provable content of this step is the variance-budget decomposition
-- below, in which the concentration "tail" is kept as the explicit probability
-- mass of the exceptional (non-typical-density) windows.  The overall
-- `4 / gap ^ 2` factor is applied at the call site instead.
lemma s6_variance_budget_conversion {m : ℕ} (A : Finset (Cube m))
    (p pLow varianceSlack : ℝ) (hVarSlack : 0 ≤ varianceSlack)
    (hp_pos : 0 < p) (hp : p ≤ 1 / 2)
    (h_var : varianceBudgetLE A pLow varianceSlack) :
    (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m,
      uCondVar A (fun x => rho A t (proj (below (univ : Finset (Fin m)) t) x)) (proj (below J t)))
    ≤ varianceSlack / p
      + ((m : ℝ) / p) *
          ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
            ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
            windowProb J p := by
  classical
  have hp_le_one : p ≤ 1 := by linarith
  set φ : Finset (Fin m) → Fin m → ℝ :=
    fun J t => uCondVar A (fun x => rho A t (proj (below (univ : Finset (Fin m)) t) x)) (proj (below J t))
    with hφdef
  have hbelow : ∀ (J : Finset (Fin m)) (t : Fin m), t ∉ J →
      below J t = below (insert t J) t := by
    intro J t _
    unfold below
    ext s
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hsJ, hst⟩; exact ⟨Or.inr hsJ, hst⟩
    · rintro ⟨hs, hst⟩
      refine ⟨?_, hst⟩
      rcases hs with rfl | h
      · exact absurd hst (lt_irrefl _)
      · exact h
  have hφ : ∀ (J : Finset (Fin m)) (t : Fin m), t ∉ J → φ J t = φ (insert t J) t := by
    intro J t ht
    simp only [hφdef, hbelow J t ht]
  have hreindex := core_windowProb_reindex_le m p hp_pos φ hφ
  have hcardm : ∀ J : Finset (Fin m), (J.card : ℝ) ≤ (m : ℝ) := by
    intro J
    have hle : J.card ≤ m := by simpa using Finset.card_le_univ J
    exact_mod_cast hle
  have hgood :
      (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
          pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)),
          windowProb J p * ∑ t ∈ J, φ J t) ≤ varianceSlack := by
    have hstep : ∀ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
        pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)),
        windowProb J p * ∑ t ∈ J, φ J t ≤ windowProb J p * varianceSlack := by
      intro J hJ
      have hPJ := (Finset.mem_filter.mp hJ).2
      have hb : ∑ t ∈ J, φ J t ≤ varianceSlack := h_var J hPJ.1 hPJ.2
      exact mul_le_mul_of_nonneg_left hb (windowProb_nonneg J p hp_pos.le hp_le_one)
    have hsub :
        (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
            pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)),
            windowProb J p) ≤ 1 := by
      calc (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
              pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)),
              windowProb J p)
            ≤ ∑ J : Finset (Fin m), windowProb J p :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun J _ _ => windowProb_nonneg J p hp_pos.le hp_le_one)
        _ = 1 := sum_windowProb_eq_one p hp_pos.le hp_le_one
    calc (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
            pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)),
            windowProb J p * ∑ t ∈ J, φ J t)
          ≤ ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
              pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)),
              windowProb J p * varianceSlack := Finset.sum_le_sum hstep
      _ = (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
              pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)),
              windowProb J p) * varianceSlack := by rw [Finset.sum_mul]
      _ ≤ 1 * varianceSlack := mul_le_mul_of_nonneg_right hsub hVarSlack
      _ = varianceSlack := one_mul _
  have hbad :
      (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
          ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
          windowProb J p * ∑ t ∈ J, φ J t)
      ≤ (m : ℝ) *
          ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
            ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
            windowProb J p := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro J _
    have hb : ∑ t ∈ J, φ J t ≤ (m : ℝ) := by
      calc ∑ t ∈ J, φ J t ≤ ∑ _t ∈ J, (1 : ℝ) := by
            refine Finset.sum_le_sum fun t _ => ?_
            simp only [hφdef]
            exact core_uCondVar_le_one A
              (fun x => rho A t (proj (below (univ : Finset (Fin m)) t) x))
              (proj (below J t))
              (fun x => rho_nonneg A t (proj (below (univ : Finset (Fin m)) t) x))
              (fun x => rho_le_one A t (proj (below (univ : Finset (Fin m)) t) x))
        _ = (J.card : ℝ) := by simp
        _ ≤ (m : ℝ) := hcardm J
    calc windowProb J p * ∑ t ∈ J, φ J t
        ≤ windowProb J p * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hb (windowProb_nonneg J p hp_pos.le hp_le_one)
      _ = (m : ℝ) * windowProb J p := by ring
  have hinner :
      (∑ J : Finset (Fin m), windowProb J p * ∑ t ∈ J, φ J t)
      ≤ varianceSlack + (m : ℝ) *
          ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
            ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
            windowProb J p := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun J : Finset (Fin m) =>
          pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))
        (fun J => windowProb J p * ∑ t ∈ J, φ J t)]
    exact add_le_add hgood hbad
  calc (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m, φ J t)
      ≤ (1 / p) * ∑ J : Finset (Fin m), windowProb J p * ∑ t ∈ J, φ J t := hreindex
    _ ≤ (1 / p) * (varianceSlack + (m : ℝ) *
          ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
            ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
            windowProb J p) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = varianceSlack / p
        + ((m : ℝ) / p) *
          ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
            ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
            windowProb J p := by ring

-- Decomposed leaf 3: Bad steps sum conversion
lemma s6_average_bad_steps_conversion {m : ℕ} (A : Finset (Cube m))
    (q eps p massSlack : ℝ) (hA : A.Nonempty) (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (h_bad : averageBadStepsLE A q eps massSlack) :
    2 * ∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m,
      pOn A (fun x => decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|)) true
    ≤ 2 * (massSlack / p) := by
  have hsumProb : (∑ J : Finset (Fin m), windowProb J p) = 1 :=
    sum_windowProb_eq_one p (le_of_lt hp_pos) hp_le_one
  have hbad_sum := averageBadStepsLE_sum_pOn A q eps massSlack hA h_bad
  have hbad_nonneg :
      0 ≤ ∑ t : Fin m,
        pOn A (fun x =>
          decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
          true := by
    exact Finset.sum_nonneg fun t _ => pOn_nonneg A _ true
  have hmass_nonneg : 0 ≤ massSlack := hbad_nonneg.trans hbad_sum
  have hmain :
      (∑ t : Fin m,
        pOn A (fun x =>
          decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
          true) ≤ massSlack / p := by
    have hmass_le : massSlack ≤ massSlack / p := by
      rw [le_div_iff₀ hp_pos]
      nlinarith
    exact hbad_sum.trans hmass_le
  calc
    2 * (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m,
        pOn A (fun x =>
          decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
          true)
      = 2 * ((∑ J : Finset (Fin m), windowProb J p) *
          ∑ t : Fin m,
            pOn A (fun x =>
              decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
              true) := by
          rw [Finset.sum_mul]
    _ = 2 * (∑ t : Fin m,
            pOn A (fun x =>
              decide (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
              true) := by
          rw [hsumProb, one_mul]
    _ ≤ 2 * (massSlack / p) := by
          exact mul_le_mul_of_nonneg_left hmain (by norm_num)

lemma uE_card_filter_ne_eq_sum_uE_error {m : ℕ} {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (F G : Cube m → Fin m → B) :
    uE A (fun x =>
      (((univ : Finset (Fin m)).filter fun t => F x t ≠ G x t).card : ℝ))
      = ∑ t : Fin m, uE A (fun x => if F x t = G x t then (0 : ℝ) else 1) := by
  classical
  have hpoint :
      ∀ x : Cube m,
        (((univ : Finset (Fin m)).filter fun t => F x t ≠ G x t).card : ℝ)
          = ∑ t : Fin m, if F x t = G x t then (0 : ℝ) else 1 := by
    intro x
    rw [Finset.card_filter]
    simp +decide
  unfold uE
  rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]

-- Top-level target 2 (reconstructed via summation of the above)
set_option maxHeartbeats 1000000 in
lemma s6_expectedEstimatorError_le {m : ℕ} (A : Finset (Cube m))
    (q qMax eps gap p pLow varianceSlack massSlack : ℝ)
    (hA : A.Nonempty) (_hVarSlack : 0 ≤ varianceSlack) (_hmassSlack : 0 ≤ massSlack)
    (hq_le : q ≤ qMax) (hqMax : qMax < 1 / 2)
    (heps : 0 < eps) (hgap : 0 < gap) (hgap_le : qMax + eps ≤ 1 / 2 - gap)
    (hpLow_pos : 0 < pLow) (hpLow_le : pLow ≤ p) (hp : p ≤ 1 / 2)
    (h_var : varianceBudgetLE A pLow varianceSlack)
    (h_bad : averageBadStepsLE A q eps massSlack) :
    expectedEstimatorError A
      (fun x t => coord t (predictableCenter A x))
      (centerMajorityEstimator A) p
    ≤ (4 / gap ^ 2) * (varianceSlack / p) + 2 * (massSlack / p)
      + (4 / gap ^ 2) * (((m : ℝ) / p) *
          ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
            ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
            windowProb J p) := by
  classical
  have hp_pos : 0 < p := lt_of_lt_of_le hpLow_pos hpLow_le
  have hp_le_one : p ≤ 1 := by linarith
  let F : Cube m → Fin m → Bool := fun x t => coord t (predictableCenter A x)
  let G : Finset (Fin m) → Cube m → Fin m → Bool := centerMajorityEstimator A
  let varTerm : Finset (Fin m) → Fin m → ℝ :=
    fun J t =>
      uCondVar A
        (fun x => rho A t (proj (below (univ : Finset (Fin m)) t) x))
        (proj (below J t))
  let badTerm : Fin m → ℝ :=
    fun t =>
      pOn A
        (fun x =>
          decide
            (eps ≤ |fold (rho A t (proj (below (univ : Finset (Fin m)) t) x)) - q|))
        true
  let C : ℝ := 4 / gap ^ 2
  have hperJ :
      ∀ J : Finset (Fin m),
        uE A (fun x =>
          (((univ : Finset (Fin m)).filter fun t => F x t ≠ G J x t).card : ℝ))
          ≤ ∑ t : Fin m, (C * varTerm J t + 2 * badTerm t) := by
    intro J
    rw [uE_card_filter_ne_eq_sum_uE_error A F (G J)]
    refine Finset.sum_le_sum ?_
    intro t _
    have hct := center_majority_error_le_twoCluster A q qMax eps gap hq_le hqMax
      heps hgap hgap_le J t
    simpa [F, G, varTerm, badTerm, C] using hct
  have hmain :
      expectedEstimatorError A F G p
        ≤ C * (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m, varTerm J t) +
            2 * (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m, badTerm t) := by
    unfold expectedEstimatorError
    refine le_trans
      (b := ∑ J : Finset (Fin m),
        windowProb J p * ∑ t : Fin m, (C * varTerm J t + 2 * badTerm t)) ?_ ?_
    · refine Finset.sum_le_sum ?_
      intro J _
      convert
        (mul_le_mul_of_nonneg_left (hperJ J)
          (windowProb_nonneg J p (le_of_lt hp_pos) hp_le_one))
        using 1
      congr 1
      unfold uE
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x _
      apply congrArg (fun S : Finset (Fin m) => (S.card : ℝ))
      ext t
      simp
    · simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_left_comm]
  have hC_nonneg : 0 ≤ C := by positivity
  have hvar :
      (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m, varTerm J t)
      ≤ varianceSlack / p
        + ((m : ℝ) / p) *
            ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
              ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
              windowProb J p := by
    simpa [varTerm] using
      s6_variance_budget_conversion A p pLow varianceSlack _hVarSlack hp_pos hp h_var
  have hbad := s6_average_bad_steps_conversion A q eps p massSlack hA hp_pos hp_le_one h_bad
  calc
    expectedEstimatorError A
        (fun x t => coord t (predictableCenter A x))
        (centerMajorityEstimator A) p
        = expectedEstimatorError A F G p := by rfl
    _ ≤ C * (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m, varTerm J t) +
          2 * (∑ J : Finset (Fin m), windowProb J p * ∑ t : Fin m, badTerm t) := hmain
    _ ≤ C * (varianceSlack / p
            + ((m : ℝ) / p) *
                ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
                  ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
                  windowProb J p)
          + 2 * (massSlack / p) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hvar hC_nonneg) hbad
    _ =
        (4 / gap ^ 2) * (varianceSlack / p) + 2 * (massSlack / p)
          + (4 / gap ^ 2) * (((m : ℝ) / p) *
              ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
                ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
                windowProb J p) := by
          simp only [C]; ring

end HarperStability
