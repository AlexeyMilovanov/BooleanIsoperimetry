import HarperStability.Core.Basic

/-!
# S6 leaf: bad-window mass (binomial Chebyshev)

`s6_badWindow_mass_le` bounds the total `windowProb`-mass of the
windows outside the band `[pLow*m, (1-pLow)*m]` — exactly the deferred
third term in the conclusion of `s6_expectedEstimatorError_le`
(`Core/S6Estimator.lean`).  A Chebyshev bound (`O(1/m)`) suffices: the
consumer (`s6_errorBound` in `Core/S6.lean`) multiplies this mass by
`m/p`, so any `O(1/m)` tail makes the error term constant in `m`, and
the `p → 0` diagonalization absorbs constants.  No exponential
(Hoeffding/Chernoff) bound is needed anywhere.

## Proof route (all finite)

Write `q := 1 - p` and `X J := (J.card : ℝ)`.

1. **Marginal identities** (each by the insert-bijection between
   `{J | t ∉ J}` and `{J | t ∈ J}`, exactly as in
   `core_windowProb_reindex_le` in `Core/S6Estimator.lean`, or by
   `Finset.prod_add` : `∏_{i ∈ s} (x + y) = ∑_{J ⊆ s} x^|J| * y^{|s|-|J|}`):
   * `∑ J, windowProb J p = 1`  (this is `(p + q)^m = 1`);
   * for each `t`:  `∑ J ∈ {J | t ∈ J}, windowProb J p = p`;
   * for `s ≠ t`:  `∑ J ∈ {J | s ∈ J ∧ t ∈ J}, windowProb J p = p^2`.
2. **Second moment.**  `X J - p*m = ∑ t, ((if t ∈ J then 1 else 0) - p)`,
   so expanding the square and applying the identities of step 1
   termwise (cross terms `s ≠ t` contribute `p^2 - 2*p^2 + p^2 = 0`,
   diagonal terms contribute `p - 2*p^2 + p^2 = p*(1-p)`):
   `∑ J, windowProb J p * (X J - p*m)^2 = m * p * (1-p)`.
3. **Chebyshev/Markov.**  On the bad set,
   `|X J - p*m| > (p - pLow) * m`:
   * `X J < pLow*m` gives `p*m - X J > (p - pLow)*m`;
   * `X J > (1-pLow)*m` gives
     `X J - p*m > (1 - pLow - p)*m ≥ (p - pLow)*m`, using `p ≤ 1/2`.
   Hence each bad `J` has
   `windowProb J p ≤ windowProb J p * (X J - p*m)^2 / ((p-pLow)*m)^2`
   (all factors nonneg; `windowProb ≥ 0` since `0 ≤ p ≤ 1`), so
   `∑_{bad} windowProb J p ≤ m*p*(1-p) / ((p-pLow)^2 * m^2)
      = p*(1-p) / ((p-pLow)^2 * m) ≤ p / ((p-pLow)^2 * m)`.
4. **Degenerate `m = 0`:** the only window `J = ∅` satisfies the band
   condition (`0 ≤ 0 ≤ 0`), so the bad sum is empty (`= 0`), and the
   right-hand side is `p / 0 = 0` under Lean's division convention:
   the inequality holds as `0 ≤ 0`.  (Handle this case first, then
   assume `0 < m`.)

Instance gotcha (STATUS.md): use instance-robust `simp only` forms; the
ambient `Finset` sums here are over `Finset (Fin m)` with decidable
filters, so `classical` at the top is fine.
-/

namespace HarperStability

/-- 1a. Marginal identity: sum of all probabilities is 1. -/
lemma s6_windowProb_sum (m : ℕ) (p : ℝ) :
    ∑ J : Finset (Fin m), windowProb J p = 1 := by
  classical
  unfold windowProb
  simpa [Fintype.card_fin] using
    (Fintype.sum_pow_mul_eq_add_pow (Fin m) p (1 - p) :
      (∑ J : Finset (Fin m),
          p ^ J.card * (1 - p) ^ (Fintype.card (Fin m) - J.card)) =
        (p + (1 - p)) ^ Fintype.card (Fin m))

/-- 1b. Marginal identity: probability of including `t` is `p`. -/
lemma s6_windowProb_sum_t (m : ℕ) (p : ℝ) (t : Fin m) :
    ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => t ∈ J), windowProb J p = p := by
  classical
  have h := windowProb_mem_past_independent (m := m) t p (fun _ => (1 : ℝ))
  calc
    (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => t ∈ J), windowProb J p)
        = ∑ J : Finset (Fin m),
            windowProb J p * (if t ∈ J then (1 : ℝ) else 0) := by
          simp [Finset.sum_filter]
    _ = p * (∑ J : Finset (Fin m), windowProb J p * (1 : ℝ)) := by
          simpa using h
    _ = p := by
          simp [s6_windowProb_sum]

/-- 1c. Marginal identity: probability of including `s` and `t` is `p^2`. -/
lemma s6_windowProb_sum_s_t (m : ℕ) (p : ℝ) (s t : Fin m) (hst : s ≠ t) :
    ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => s ∈ J ∧ t ∈ J), windowProb J p = p^2 := by
  classical
  rcases lt_or_gt_of_ne hst with hst_lt | hts_lt
  · have h :=
      windowProb_mem_past_independent (m := m) t p
        (fun K => if s ∈ K then (1 : ℝ) else 0)
    calc
      (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => s ∈ J ∧ t ∈ J),
          windowProb J p)
          = ∑ J : Finset (Fin m),
              windowProb J p *
                (if t ∈ J then
                  (if s ∈ J ∩ below (Finset.univ : Finset (Fin m)) t then (1 : ℝ) else 0)
                else 0) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro J _
            by_cases hsJ : s ∈ J <;> by_cases htJ : t ∈ J <;>
              simp [hsJ, htJ, below, hst_lt]
      _ = p * (∑ J : Finset (Fin m),
              windowProb J p *
                (if s ∈ J ∩ below (Finset.univ : Finset (Fin m)) t then (1 : ℝ) else 0)) := by
            simpa using h
      _ = p * (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => s ∈ J),
              windowProb J p) := by
            congr 1
            simp [Finset.sum_filter, below, hst_lt]
      _ = p ^ 2 := by
            rw [s6_windowProb_sum_t]
            ring
  · have h :=
      windowProb_mem_past_independent (m := m) s p
        (fun K => if t ∈ K then (1 : ℝ) else 0)
    calc
      (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => s ∈ J ∧ t ∈ J),
          windowProb J p)
          = ∑ J : Finset (Fin m),
              windowProb J p *
                (if s ∈ J then
                  (if t ∈ J ∩ below (Finset.univ : Finset (Fin m)) s then (1 : ℝ) else 0)
                else 0) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro J _
            by_cases hsJ : s ∈ J <;> by_cases htJ : t ∈ J <;>
              simp [hsJ, htJ, below, hts_lt]
      _ = p * (∑ J : Finset (Fin m),
              windowProb J p *
                (if t ∈ J ∩ below (Finset.univ : Finset (Fin m)) s then (1 : ℝ) else 0)) := by
            simpa using h
      _ = p * (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => t ∈ J),
              windowProb J p) := by
            congr 1
            simp [Finset.sum_filter, below, hts_lt]
      _ = p ^ 2 := by
            rw [s6_windowProb_sum_t]
            ring

/-- Indicator form of `s6_windowProb_sum_t`. -/
lemma s6_windowProb_sum_indicator (m : ℕ) (p : ℝ) (t : Fin m) :
    (∑ J : Finset (Fin m), windowProb J p * (if t ∈ J then (1 : ℝ) else 0)) = p := by
  classical
  calc
    (∑ J : Finset (Fin m), windowProb J p * (if t ∈ J then (1 : ℝ) else 0))
        = ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => t ∈ J), windowProb J p := by
          simp [Finset.sum_filter]
    _ = p := s6_windowProb_sum_t m p t

/-- Two-indicator form of `s6_windowProb_sum_s_t`. -/
lemma s6_windowProb_sum_indicator_mul (m : ℕ) (p : ℝ) (s t : Fin m) (hst : s ≠ t) :
    (∑ J : Finset (Fin m),
        windowProb J p *
          ((if s ∈ J then (1 : ℝ) else 0) * (if t ∈ J then (1 : ℝ) else 0))) = p ^ 2 := by
  classical
  calc
    (∑ J : Finset (Fin m),
        windowProb J p *
          ((if s ∈ J then (1 : ℝ) else 0) * (if t ∈ J then (1 : ℝ) else 0)))
        = ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => s ∈ J ∧ t ∈ J),
            windowProb J p := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro J _
          by_cases hsJ : s ∈ J <;> by_cases htJ : t ∈ J <;> simp [hsJ, htJ]
    _ = p ^ 2 := s6_windowProb_sum_s_t m p s t hst

/-- Centered indicator covariance under the independent window law. -/
lemma s6_windowProb_centered_indicator_mul (m : ℕ) (p : ℝ) (s t : Fin m) :
    (∑ J : Finset (Fin m),
        windowProb J p *
          (((if s ∈ J then (1 : ℝ) else 0) - p) *
            ((if t ∈ J then (1 : ℝ) else 0) - p)))
      = if s = t then p * (1 - p) else 0 := by
  classical
  by_cases hst : s = t
  · subst t
    have hterm : ∀ J : Finset (Fin m),
        (((if s ∈ J then (1 : ℝ) else 0) - p) *
            ((if s ∈ J then (1 : ℝ) else 0) - p))
          = (1 - 2 * p) * (if s ∈ J then (1 : ℝ) else 0) + p ^ 2 := by
      intro J
      by_cases hsJ : s ∈ J <;> simp [hsJ] <;> ring
    calc
      (∑ J : Finset (Fin m),
          windowProb J p *
            (((if s ∈ J then (1 : ℝ) else 0) - p) *
              ((if s ∈ J then (1 : ℝ) else 0) - p)))
          = ∑ J : Finset (Fin m),
              windowProb J p *
                ((1 - 2 * p) * (if s ∈ J then (1 : ℝ) else 0) + p ^ 2) := by
            exact Finset.sum_congr rfl fun J _ => by rw [hterm J]
      _ = (1 - 2 * p) *
              (∑ J : Finset (Fin m), windowProb J p * (if s ∈ J then (1 : ℝ) else 0)) +
            p ^ 2 * (∑ J : Finset (Fin m), windowProb J p) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_comm]
      _ = p * (1 - p) := by
            rw [s6_windowProb_sum_indicator, s6_windowProb_sum]
            ring
      _ = (if s = s then p * (1 - p) else 0) := by simp
  · have hterm : ∀ J : Finset (Fin m),
        (((if s ∈ J then (1 : ℝ) else 0) - p) *
            ((if t ∈ J then (1 : ℝ) else 0) - p))
          =
            (if s ∈ J then (1 : ℝ) else 0) * (if t ∈ J then (1 : ℝ) else 0)
              - p * (if s ∈ J then (1 : ℝ) else 0)
              - p * (if t ∈ J then (1 : ℝ) else 0)
              + p ^ 2 := by
      intro J
      by_cases hsJ : s ∈ J <;> by_cases htJ : t ∈ J <;> simp [hsJ, htJ] <;> ring
    calc
      (∑ J : Finset (Fin m),
          windowProb J p *
            (((if s ∈ J then (1 : ℝ) else 0) - p) *
              ((if t ∈ J then (1 : ℝ) else 0) - p)))
          = ∑ J : Finset (Fin m),
              windowProb J p *
                ((if s ∈ J then (1 : ℝ) else 0) * (if t ∈ J then (1 : ℝ) else 0)
                  - p * (if s ∈ J then (1 : ℝ) else 0)
                  - p * (if t ∈ J then (1 : ℝ) else 0)
                  + p ^ 2) := by
            exact Finset.sum_congr rfl fun J _ => by rw [hterm J]
      _ =
            (∑ J : Finset (Fin m),
              windowProb J p *
                ((if s ∈ J then (1 : ℝ) else 0) * (if t ∈ J then (1 : ℝ) else 0)))
            - p * (∑ J : Finset (Fin m), windowProb J p * (if s ∈ J then (1 : ℝ) else 0))
            - p * (∑ J : Finset (Fin m), windowProb J p * (if t ∈ J then (1 : ℝ) else 0))
            + p ^ 2 * (∑ J : Finset (Fin m), windowProb J p) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
              mul_add, mul_sub, mul_comm]
      _ = 0 := by
            rw [s6_windowProb_sum_indicator_mul m p s t hst,
              s6_windowProb_sum_indicator, s6_windowProb_sum_indicator,
              s6_windowProb_sum]
            ring
      _ = (if s = t then p * (1 - p) else 0) := by simp [hst]

/-- 2. Second moment of the binomial distribution. -/
lemma s6_windowProb_second_moment (m : ℕ) (p : ℝ) :
    ∑ J : Finset (Fin m), windowProb J p * ((J.card : ℝ) - p * (m : ℝ))^2 = (m : ℝ) * p * (1 - p) := by
  classical
  let a : Finset (Fin m) → Fin m → ℝ :=
    fun J t => (if t ∈ J then (1 : ℝ) else 0) - p
  have hcard : ∀ J : Finset (Fin m),
      (J.card : ℝ) = ∑ t : Fin m, if t ∈ J then (1 : ℝ) else 0 := by
    intro J
    rw [Finset.card_eq_sum_ones]
    simp
  have hcenter : ∀ J : Finset (Fin m),
      (J.card : ℝ) - p * (m : ℝ) = ∑ t : Fin m, a J t := by
    intro J
    dsimp [a]
    rw [Finset.sum_sub_distrib, ← hcard J]
    simp [Fintype.card_fin]
    ring
  have hsquare : ∀ J : Finset (Fin m),
      ((J.card : ℝ) - p * (m : ℝ)) ^ 2 =
        ∑ s : Fin m, ∑ t : Fin m, a J s * a J t := by
    intro J
    rw [hcenter J]
    rw [pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro s _
    rw [Finset.mul_sum]
  calc
    (∑ J : Finset (Fin m), windowProb J p * ((J.card : ℝ) - p * (m : ℝ)) ^ 2)
        = ∑ J : Finset (Fin m),
            windowProb J p * (∑ s : Fin m, ∑ t : Fin m, a J s * a J t) := by
          exact Finset.sum_congr rfl fun J _ => by rw [hsquare J]
    _ = ∑ J : Finset (Fin m), ∑ s : Fin m, ∑ t : Fin m,
          windowProb J p * (a J s * a J t) := by
          refine Finset.sum_congr rfl ?_
          intro J _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [Finset.mul_sum]
    _ = ∑ s : Fin m, ∑ t : Fin m,
          ∑ J : Finset (Fin m), windowProb J p * (a J s * a J t) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [Finset.sum_comm]
    _ = ∑ s : Fin m, ∑ t : Fin m, if s = t then p * (1 - p) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _
          refine Finset.sum_congr rfl ?_
          intro t _
          simpa [a] using s6_windowProb_centered_indicator_mul m p s t
    _ = (m : ℝ) * p * (1 - p) := by
          have hdiag : ∀ s : Fin m,
              (∑ t : Fin m, if s = t then p * (1 - p) else 0) = p * (1 - p) := by
            intro s
            simp
          calc
            (∑ s : Fin m, ∑ t : Fin m, if s = t then p * (1 - p) else 0)
                = ∑ _s : Fin m, p * (1 - p) := by
                  exact Finset.sum_congr rfl fun s _ => hdiag s
            _ = (m : ℝ) * p * (1 - p) := by
                  simp [Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- **Bad-window mass (Chebyshev).**  For `0 < pLow < p ≤ 1/2`, the
`windowProb`-mass of the windows outside `[pLow*m, (1-pLow)*m]` is at
most `p / ((p-pLow)^2 * m)`. -/
lemma s6_badWindow_mass_le (m : ℕ) (p pLow : ℝ)
    (hpLow : 0 < pLow) (hlt : pLow < p) (hp_half : p ≤ 1 / 2) :
    (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) =>
        ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧
          (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ))),
      windowProb J p) ≤ p / ((p - pLow) ^ 2 * (m : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hzero :
        (Finset.univ.filter (fun J : Finset (Fin 0) =>
          ¬ ((0 : ℝ) ≤ (J.card : ℝ) ∧ (J.card : ℝ) ≤ 0))) = ∅ := by
      ext J
      have hJ : J = ∅ := by
        ext t
        exact Fin.elim0 t
      simp [hJ]
    simp only [Nat.cast_zero, mul_zero, div_zero]
    rw [hzero]
    simp
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hp_pos : 0 < p := hpLow.trans hlt
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_le_one : p ≤ 1 := hp_half.trans (by norm_num)
  have hdiff_pos : 0 < p - pLow := sub_pos.mpr hlt
  let bad : Finset (Finset (Fin m)) :=
    Finset.univ.filter (fun J : Finset (Fin m) =>
      ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧
        (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)))
  let D : ℝ := ((p - pLow) * (m : ℝ)) ^ 2
  have hD_pos : 0 < D := by
    dsimp [D]
    exact sq_pos_of_pos (mul_pos hdiff_pos hmR)
  have hpoint :
      ∀ J ∈ bad,
        windowProb J p ≤
          (windowProb J p * ((J.card : ℝ) - p * (m : ℝ)) ^ 2) / D := by
    intro J hJ
    have hbad :
        ¬ (pLow * (m : ℝ) ≤ (J.card : ℝ) ∧
          (J.card : ℝ) ≤ (1 - pLow) * (m : ℝ)) := by
      simpa [bad] using (Finset.mem_filter.mp hJ).2
    have hbad_cases :
        (J.card : ℝ) < pLow * (m : ℝ) ∨
          (1 - pLow) * (m : ℝ) < (J.card : ℝ) := by
      by_cases hlow : pLow * (m : ℝ) ≤ (J.card : ℝ)
      · right
        exact lt_of_not_ge (fun hhigh => hbad ⟨hlow, hhigh⟩)
      · left
        exact lt_of_not_ge hlow
    have hgap_abs :
        |(p - pLow) * (m : ℝ)| ≤ |(J.card : ℝ) - p * (m : ℝ)| := by
      rw [abs_of_nonneg (mul_nonneg (le_of_lt hdiff_pos) (le_of_lt hmR))]
      rcases hbad_cases with hlow | hhigh
      · rw [abs_of_neg]
        · linarith
        · nlinarith
      · rw [abs_of_nonneg]
        · nlinarith [hp_half, hmR]
        · nlinarith [hp_half, hmR]
    have hsq :
        D ≤ ((J.card : ℝ) - p * (m : ℝ)) ^ 2 := by
      dsimp [D]
      exact (sq_le_sq).2 hgap_abs
    have hratio : 1 ≤ (((J.card : ℝ) - p * (m : ℝ)) ^ 2) / D := by
      rw [one_le_div hD_pos]
      exact hsq
    have hwp : 0 ≤ windowProb J p := windowProb_nonneg J p hp_nonneg hp_le_one
    calc
      windowProb J p = windowProb J p * 1 := by ring
      _ ≤ windowProb J p * ((((J.card : ℝ) - p * (m : ℝ)) ^ 2) / D) :=
          mul_le_mul_of_nonneg_left hratio hwp
      _ = (windowProb J p * ((J.card : ℝ) - p * (m : ℝ)) ^ 2) / D := by ring
  have hmarkov :
      (∑ J ∈ bad, windowProb J p) ≤
        (∑ J : Finset (Fin m),
          (windowProb J p * ((J.card : ℝ) - p * (m : ℝ)) ^ 2) / D) := by
    calc
      (∑ J ∈ bad, windowProb J p)
          ≤ ∑ J ∈ bad,
              (windowProb J p * ((J.card : ℝ) - p * (m : ℝ)) ^ 2) / D :=
            Finset.sum_le_sum hpoint
      _ ≤ ∑ J : Finset (Fin m),
              (windowProb J p * ((J.card : ℝ) - p * (m : ℝ)) ^ 2) / D :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun J _ _ =>
                div_nonneg
                  (mul_nonneg (windowProb_nonneg J p hp_nonneg hp_le_one) (sq_nonneg _))
                  (le_of_lt hD_pos))
  have hmoment :
      (∑ J : Finset (Fin m),
          (windowProb J p * ((J.card : ℝ) - p * (m : ℝ)) ^ 2) / D)
        = ((m : ℝ) * p * (1 - p)) / D := by
    rw [← Finset.sum_div]
    rw [s6_windowProb_second_moment]
  have hcheb :
      (∑ J ∈ bad, windowProb J p) ≤ ((m : ℝ) * p * (1 - p)) / D := by
    simpa [hmoment] using hmarkov
  have hrewrite :
      ((m : ℝ) * p * (1 - p)) / D =
        (p * (1 - p)) / ((p - pLow) ^ 2 * (m : ℝ)) := by
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmR
    have hdiff_ne : p - pLow ≠ 0 := ne_of_gt hdiff_pos
    dsimp [D]
    field_simp [hm_ne, hdiff_ne]
  have hlast :
      (p * (1 - p)) / ((p - pLow) ^ 2 * (m : ℝ)) ≤
        p / ((p - pLow) ^ 2 * (m : ℝ)) := by
    have hden_nonneg : 0 ≤ (p - pLow) ^ 2 * (m : ℝ) := by positivity
    have hnum : p * (1 - p) ≤ p := by
      nlinarith [hp_nonneg]
    exact div_le_div_of_nonneg_right hnum hden_nonneg
  simpa [bad] using hcheb.trans (by simpa [hrewrite] using hlast)

end HarperStability
