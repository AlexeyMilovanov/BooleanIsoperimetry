import AverageHarperStability.Distribution.CertificateCore

open scoped BigOperators
open Filter Topology Set Classical

namespace AverageHarperStability

attribute [local instance] Classical.propDecidable

lemma offFlatBudget_mono {n : ℕ} (mu : Cube n → ℝ) (x : Cube n) {err1 err2 : ℝ} (h : err1 ≤ err2) :
    offFlatBudget err2 mu x ≤ offFlatBudget err1 mu x := by
  unfold offFlatBudget
  have hn : 0 ≤ (n : ℝ) := by positivity
  apply max_le_max (le_refl 0)
  have h2 : err1 / 2 * (n : ℝ) ≤ err2 / 2 * (n : ℝ) := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h (by norm_num)) hn
  linarith

/-! ## Reduction of the strong-convexity leaf

The quantitative strong-convexity estimate `mglCurve_bregman_ge_sq` is proved
below from the single elementary logarithm inequality `key_polylog`.  The route
is: a clean pointwise slope-derivative bound (`slope_deriv_ge`, via the novel
`kfun_deriv_ge : deriv kfun x ≥ 1 - 2x`), then `MonotoneOn.convexOn_of_deriv`
and the tangent-line lemmas.  All of the calculus/probability machinery is
discharged here, including the elementary `key_polylog` estimate. -/

section MglBregmanReduction
open Real

/-- The logarithmic slope lower bound `2(1-2x) ≤ log((1-x)/x)`. -/
lemma L_lower_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    2 * (1 - 2 * x) ≤ log ((1 - x) / x) := by
  let z := (1 - 2 * x) / x
  have hz0 : 0 < z := div_pos (by linarith) hx0
  have hlog := Real.lt_log_one_add_of_pos hz0
  have heq1 : 1 + z = (1 - x) / x := by
    dsimp [z]; field_simp; ring
  have heq2 : 2 * z / (z + 2) = 2 * (1 - 2 * x) := by
    dsimp [z]
    have hx_ne_zero : x ≠ 0 := ne_of_gt hx0
    apply mul_right_cancel₀ (by linarith : (1 - 2 * x) / x + 2 ≠ 0)
    field_simp; ring
  rw [← heq1, ← heq2]
  exact hlog.le

/-- `kfun x = x(1-x)/(1-2x) · log((1-x)/x)`, the core monotone quantity from
`mgl_core_inequality`. -/
noncomputable def kfun (x : ℝ) : ℝ := (x * (1 - x)) / (1 - 2 * x) * log ((1 - x) / x)

/-- Derivative of `kfun` (same computation as in `mgl_core_inequality`). -/
lemma kfun_hasDerivAt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    HasDerivAt kfun
      (((1 - 2 * x + 2 * x ^ 2) / (1 - 2 * x) ^ 2) * log ((1 - x) / x) -
        1 / (1 - 2 * x)) x := by
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have hx1' : 1 - x ≠ 0 := by
    apply ne_of_gt; exact sub_pos.mpr (hx1.trans (by norm_num))
  have hxdenpos : 0 < 1 - 2 * x := by linarith
  have hxden : 1 - 2 * x ≠ 0 := ne_of_gt hxdenpos
  have hone : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> norm_num
  have hquot : HasDerivAt (fun y : ℝ => (1 - y) / y) (-1 / x ^ 2) x := by
    have hquot0 : HasDerivAt (fun y : ℝ => (1 - y) / y)
        ((-1 * x - (1 - x) * 1) / x ^ 2) x := by
      simpa only [id_eq] using hone.div (hasDerivAt_id x) hx0'
    convert hquot0 using 1 <;> field_simp <;> ring
  have hlog : HasDerivAt (fun y : ℝ => log ((1 - y) / y))
      (-1 / (x * (1 - x))) x := by
    convert hquot.log (div_ne_zero hx1' hx0') using 1 <;> field_simp <;> ring
  have hrat : HasDerivAt (fun y : ℝ => (y * (1 - y)) / (1 - 2 * y))
      ((1 - 2 * x + 2 * x ^ 2) / (1 - 2 * x) ^ 2) x := by
    have hnum' : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 - 2 * x) x := by
      have hnum0 : HasDerivAt (fun y : ℝ => y * (1 - y))
          (1 * (1 - x) + x * (-1)) x := by
        simpa only [id_eq] using (hasDerivAt_id x).mul hone
      convert hnum0 using 1 <;> ring
    have hden' : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
      convert (hasDerivAt_const x 1).sub ((hasDerivAt_const x 2).mul (hasDerivAt_id x))
        using 1 <;> norm_num
    convert hnum'.div hden' hxden using 1 <;> field_simp <;> ring
  have hk : HasDerivAt kfun
      (((1 - 2 * x + 2 * x ^ 2) / (1 - 2 * x) ^ 2) * log ((1 - x) / x) -
        1 / (1 - 2 * x)) x := by
    unfold kfun
    convert hrat.mul hlog using 1 <;> field_simp <;> ring
  exact hk

/-- **Key new quantitative bound**: the derivative of `kfun` is at least `1 - 2x`.
This is the quantitative strengthening of `mgl_core_inequality` (which only gives
`deriv kfun > 0`).  It follows cleanly from `L_lower_bound`. -/
lemma kfun_deriv_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    1 - 2 * x ≤ deriv kfun x := by
  rw [(kfun_hasDerivAt hx0 hx1).deriv]
  have hd : 0 < 1 - 2 * x := by linarith
  have hL := L_lower_bound hx0 hx1
  set L := log ((1 - x) / x) with hLdef
  have hnum : 0 < 1 - 2 * x + 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hApos : 0 < (1 - 2 * x + 2 * x ^ 2) / (1 - 2 * x) ^ 2 := by positivity
  have step1 : (1 - 2 * x + 2 * x ^ 2) / (1 - 2 * x) ^ 2 * (2 * (1 - 2 * x)) ≤
      (1 - 2 * x + 2 * x ^ 2) / (1 - 2 * x) ^ 2 * L :=
    mul_le_mul_of_nonneg_left hL hApos.le
  have step2 : (1 - 2 * x + 2 * x ^ 2) / (1 - 2 * x) ^ 2 * (2 * (1 - 2 * x)) -
      1 / (1 - 2 * x) = 1 - 2 * x := by
    field_simp
    ring
  linarith

/-- Integrated form: `kfun q - kfun p ≥ (q-p)(1-p-q)`, obtained by integrating
`kfun_deriv_ge` (i.e. showing `κ x = kfun x - x + x²` is monotone). -/
lemma kfun_diff_ge {p q : ℝ} (hp0 : 0 < p) (hpq : p ≤ q) (hq : q < 1 / 2) :
    (q - p) * (1 - p - q) ≤ kfun q - kfun p := by
  set κ : ℝ → ℝ := fun x => kfun x - x + x ^ 2 with hκ
  have hmem : ∀ x ∈ Icc p q, x ∈ Ioo (0 : ℝ) (1 / 2) := by
    intro x hx
    exact ⟨hp0.trans_le hx.1, hx.2.trans_lt hq⟩
  have hκ_hd : ∀ x ∈ Ioo p q, HasDerivAt κ
      (deriv kfun x - 1 + 2 * x) x := by
    intro x hx
    have hxm : x ∈ Ioo (0 : ℝ) (1 / 2) := hmem x (Ioo_subset_Icc_self hx)
    have hkd := kfun_hasDerivAt hxm.1 hxm.2
    have : HasDerivAt κ (deriv kfun x - 1 + 2 * x) x := by
      have h1 : HasDerivAt (fun x : ℝ => kfun x - x) (deriv kfun x - 1) x := by
        rw [hkd.deriv]; exact hkd.sub (hasDerivAt_id x)
      have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      simpa [hκ] using h1.add h2
    exact this
  have hmono : MonotoneOn κ (Icc p q) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc p q)
    · intro x hx
      have hxm := hmem x hx
      exact ((kfun_hasDerivAt hxm.1 hxm.2).sub (hasDerivAt_id x)).add
        (by simpa using hasDerivAt_pow 2 x) |>.continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hκ_hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxm := hmem x (Ioo_subset_Icc_self hx)
      rw [(hκ_hd x hx).deriv]
      have := kfun_deriv_ge hxm.1 hxm.2
      linarith
  have hle := hmono (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq) hpq
  simp only [hκ] at hle
  nlinarith [hle]

/-- The slope of `mglCurve tau` as a function of `p = hbInv u`.  Matches
`deriv (mglCurve tau) u` at `u` with `p = hbInv u` (see `mglCurve_hasDerivAt`). -/
noncomputable def slopeFun (tau p : ℝ) : ℝ :=
  (1 - 2 * tau) *
    (log (1 - (tau + (1 - 2 * tau) * p)) - log (tau + (1 - 2 * tau) * p)) /
    (log (1 - p) - log p)

/-- Derivative of `slopeFun tau` (same computation as in `mglSlope_strictMonoOn`). -/
lemma slopeFun_hasDerivAt {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt (slopeFun tau)
      ((1 - 2 * tau) *
        ((-(1 - 2 * tau) /
            ((tau + (1 - 2 * tau) * p) * (1 - (tau + (1 - 2 * tau) * p)))) *
              (log (1 - p) - log p) -
          (log (1 - (tau + (1 - 2 * tau) * p)) -
              log (tau + (1 - 2 * tau) * p)) * (-1 / (p * (1 - p)))) /
        (log (1 - p) - log p) ^ 2) p := by
  let a := 1 - 2 * tau
  let Q : ℝ → ℝ := fun p => tau + a * p
  let L : ℝ → ℝ := fun p => log (1 - p) - log p
  have ha : 0 < a := by dsimp [a]; linarith
  have hpden : 0 < 1 - 2 * p := by
    have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hp.2
    linarith
  have hgap : 0 < tau * (1 - 2 * p) := mul_pos ht0 hpden
  have hhalf : 0 < a * (1 / 2 - p) := mul_pos ha (sub_pos.mpr hp.2)
  have hqp : Q p ∈ Ioo p (1 / 2) := by
    dsimp [Q, a]; constructor <;> nlinarith
  have hp1 : p < 1 := hp.2.trans (by norm_num)
  have hq1 : Q p < 1 := hqp.2.trans (by norm_num)
  have hLder : ∀ x : ℝ, 0 < x → x < 1 → HasDerivAt L (-1 / (x * (1 - x))) x := by
    intro x hx0 hx1
    dsimp [L]
    have h1 := (Real.hasDerivAt_log (by linarith : 1 - x ≠ 0)).comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    have h2 := Real.hasDerivAt_log (ne_of_gt hx0)
    convert h1.sub h2 using 1 <;>
      field_simp [ne_of_gt hx0, ne_of_gt (sub_pos.mpr hx1)] <;> ring
  have hLpos : 0 < L p := by
    dsimp [L]; rw [sub_pos]; exact Real.log_lt_log hp.1 (by linarith)
  have hQder : HasDerivAt Q a p := by
    dsimp [Q]
    convert (hasDerivAt_const p tau).add ((hasDerivAt_const p a).mul (hasDerivAt_id p))
      using 1 <;> simp only [id_eq] <;> ring
  have hLQ : HasDerivAt (fun x => L (Q x)) (-a / (Q p * (1 - Q p))) p := by
    convert (hLder (Q p) (hp.1.trans hqp.1) hq1).comp p hQder using 1 <;>
      field_simp <;> ring
  have hd : HasDerivAt (slopeFun tau)
      (a * ((-a / (Q p * (1 - Q p))) * L p - L (Q p) * (-1 / (p * (1 - p)))) /
        (L p) ^ 2) p := by
    show HasDerivAt (fun p => a * L (Q p) / L p) _ p
    have hn : HasDerivAt (fun x => a * L (Q x))
        (a * (-a / (Q p * (1 - Q p)))) p := by
      convert (hasDerivAt_const p a).mul hLQ using 1 <;> ring
    convert hn.div (hLder p hp.1 hp1) (ne_of_gt hLpos) using 1 <;> ring
  exact hd

/-- Elementary logarithm inequality used in the quantitative slope bound:
`(log((1-p)/p))³ · p(1-p) ≤ 4(1-2p)³` for `p ∈ (0,1/2)`.
Equivalently, with `t = 1-2p`, `ℓ(t) = log((1+t)/(1-t))`: `(1-t²)ℓ(t)³ ≤ 16t³`.

The proof below splits at `p = 3/20`.  On the central range it uses the first
three terms of the positive power series for
`log ((1+t)/(1-t))`, with `t = 1-2p`.  On the small-`p` tail it uses the
optimized sub-polynomial estimate `log y ≤ (3/e)y^(1/3) ≤ (6/5)y^(1/3)`. -/

lemma polylog_seriesFactor_eq {s : ℝ} (hs1 : s < 1) :
    1 + s / 3 + s ^ 2 / 5 + s ^ 3 / (1 - s) =
      (15 - 10 * s - 2 * s ^ 2 + 12 * s ^ 3) / (15 * (1 - s)) := by
  have hne : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs1)
  field_simp
  ring

lemma polylog_seriesFactor_le_five_four {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 3 / 8) :
    1 + s / 3 + s ^ 2 / 5 + s ^ 3 / (1 - s) ≤ 5 / 4 := by
  have hs1 : s < 1 := hs.trans_lt (by norm_num)
  have hden : 0 < 15 * (1 - s) := mul_pos (by norm_num) (sub_pos.mpr hs1)
  rw [polylog_seriesFactor_eq hs1, div_le_iff₀ hden]
  have h2 : s ^ 2 ≤ (3 / 8 : ℝ) * s := by
    nlinarith [mul_le_mul_of_nonneg_left hs hs0]
  have h3 : s ^ 3 ≤ (3 / 8 : ℝ) * s ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg s)]
  nlinarith

lemma polylog_seriesFactor_le_four_three {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 11 / 27) :
    1 + s / 3 + s ^ 2 / 5 + s ^ 3 / (1 - s) ≤ 4 / 3 := by
  have hs1 : s < 1 := hs.trans_lt (by norm_num)
  have hden : 0 < 15 * (1 - s) := mul_pos (by norm_num) (sub_pos.mpr hs1)
  rw [polylog_seriesFactor_eq hs1, div_le_iff₀ hden]
  have h2 : s ^ 2 ≤ (11 / 27 : ℝ) * s := by
    nlinarith [mul_le_mul_of_nonneg_left hs hs0]
  have h3 : s ^ 3 ≤ (11 / 27 : ℝ) * s ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg s)]
  nlinarith

lemma polylog_seriesFactor_le_three_two {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 49 / 100) :
    1 + s / 3 + s ^ 2 / 5 + s ^ 3 / (1 - s) ≤ 3 / 2 := by
  have hs1 : s < 1 := hs.trans_lt (by norm_num)
  have hden : 0 < 15 * (1 - s) := mul_pos (by norm_num) (sub_pos.mpr hs1)
  rw [polylog_seriesFactor_eq hs1, div_le_iff₀ hden]
  have h2 : s ^ 2 ≤ (49 / 100 : ℝ) * s := by
    nlinarith [mul_le_mul_of_nonneg_left hs hs0]
  have h3 : s ^ 3 ≤ (49 / 100 : ℝ) * s ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg s)]
  nlinarith

lemma polylog_log_ratio_le_seriesFactor {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    log ((1 + t) / (1 - t)) ≤
      2 * t * (1 + t ^ 2 / 3 + (t ^ 2) ^ 2 / 5 + (t ^ 2) ^ 3 / (1 - t ^ 2)) := by
  have h := Real.log_div_le_sum_range_add ht0 ht1 3
  norm_num [Finset.sum_range_succ] at h
  have hden : 1 - t ^ 2 ≠ 0 := by nlinarith
  calc
    log ((1 + t) / (1 - t)) ≤
        2 * (t + t ^ 3 / 3 + t ^ 5 / 5 + t ^ 7 / (1 - t ^ 2)) := by linarith
    _ = 2 * t * (1 + t ^ 2 / 3 + (t ^ 2) ^ 2 / 5 + (t ^ 2) ^ 3 / (1 - t ^ 2)) := by
      field_simp

lemma polylog_log_le_six_fifths_cuberoot {y : ℝ} (hy : 0 < y) :
    log y ≤ (6 / 5) * y ^ (1 / 3 : ℝ) := by
  set r := y ^ (1 / 3 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hy _
  have hz0 : 0 < r / exp 1 := div_pos hr0 (exp_pos 1)
  have hlog := Real.log_le_sub_one_of_pos hz0
  have hlogr : log r = (1 / 3 : ℝ) * log y := by
    rw [hr, Real.log_rpow hy]
  rw [Real.log_div (ne_of_gt hr0) (Real.exp_ne_zero 1), Real.log_exp, hlogr] at hlog
  have he : (5 / 2 : ℝ) ≤ exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 3
    norm_num [Finset.sum_range_succ] at h
    exact h
  have hcoef : 3 / exp 1 ≤ (6 / 5 : ℝ) := by
    rw [div_le_iff₀ (exp_pos 1)]
    nlinarith
  have hopt : log y ≤ 3 / exp 1 * r := by
    have hexp : exp 1 ≠ 0 := Real.exp_ne_zero 1
    field_simp [hexp] at hlog ⊢
    nlinarith [exp_pos 1]
  exact hopt.trans (mul_le_mul_of_nonneg_right hcoef hr0.le)

set_option maxHeartbeats 800000 in
lemma key_polylog {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2) :
    (log (1 - p) - log p) ^ 3 * (p * (1 - p)) ≤ 4 * (1 - 2 * p) ^ 3 := by
  have hp_one : p < 1 := hp1.trans (by norm_num)
  have hL0 : 0 ≤ log (1 - p) - log p := by
    have hlog : log p ≤ log (1 - p) := Real.log_le_log hp0 (by linarith)
    linarith
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
  have ht0 : 0 < 1 - 2 * p := by linarith
  by_cases htail : p ≤ 3 / 20
  · set y := (1 - p) / p with hy
    have hy0 : 0 < y := div_pos (by linarith) hp0
    have hL : log (1 - p) - log p = log y := by
      rw [hy, Real.log_div (by linarith) (ne_of_gt hp0)]
    have hb := polylog_log_le_six_fifths_cuberoot hy0
    rw [← hL] at hb
    have hr0 : 0 ≤ y ^ (1 / 3 : ℝ) := (Real.rpow_pos_of_pos hy0 _).le
    have hcube := pow_le_pow_left₀ hL0 hb 3
    have hry : (y ^ (1 / 3 : ℝ)) ^ 3 = y := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hy0.le]
      norm_num
    have hbudget :
        (log (1 - p) - log p) ^ 3 * (p * (1 - p)) ≤
          (216 / 125 : ℝ) * (1 - p) ^ 2 := by
      calc
        _ ≤ ((6 / 5 : ℝ) * y ^ (1 / 3 : ℝ)) ^ 3 * (p * (1 - p)) :=
          mul_le_mul_of_nonneg_right hcube hpp
        _ = (216 / 125 : ℝ) * (1 - p) ^ 2 := by
          rw [mul_pow, hry, hy]
          field_simp [ne_of_gt hp0]
          ring
    have hpoly : (216 / 125 : ℝ) * (1 - p) ^ 2 ≤ 4 * (1 - 2 * p) ^ 3 := by
      have hp_nonneg : 0 ≤ p := hp0.le
      have hsum : p + 3 / 20 ≤ 3 / 10 := by linarith
      have hquad : 0 ≤ p ^ 2 + p * (3 / 20) + (3 / 20 : ℝ) ^ 2 := by positivity
      have hfactor :
          4 * (1 - 2 * p) ^ 3 - (216 / 125 : ℝ) * (1 - p) ^ 2 -
              (4 * (1 - 2 * (3 / 20 : ℝ)) ^ 3 -
                (216 / 125 : ℝ) * (1 - (3 / 20 : ℝ)) ^ 2) =
            ((3 / 20 : ℝ) - p) *
              ((2568 / 125 : ℝ) - (5784 / 125 : ℝ) * (p + 3 / 20) +
                32 * (p ^ 2 + p * (3 / 20) + (3 / 20 : ℝ) ^ 2)) := by ring
      have hfacnonneg : 0 ≤ (2568 / 125 : ℝ) - (5784 / 125 : ℝ) * (p + 3 / 20) +
                32 * (p ^ 2 + p * (3 / 20) + (3 / 20 : ℝ) ^ 2) := by
        nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr htail) hfacnonneg, hfactor]
    exact hbudget.trans hpoly
  · have hp_lower : 3 / 20 < p := lt_of_not_ge htail
    set t := 1 - 2 * p with ht
    have ht_nonneg : 0 ≤ t := by rw [ht]; linarith
    have ht_lt_one : t < 1 := by rw [ht]; linarith
    have ht_le : t ≤ 7 / 10 := by rw [ht]; linarith
    have hs_le : t ^ 2 ≤ 49 / 100 := by nlinarith [sq_nonneg (t - 7 / 10)]
    have hratio : (1 - p) / p = (1 + t) / (1 - t) := by
      rw [ht]
      field_simp [ne_of_gt hp0]
      ring
    have hL : log (1 - p) - log p = log ((1 + t) / (1 - t)) := by
      rw [← Real.log_div (by linarith) (ne_of_gt hp0), hratio]
    have hseries := polylog_log_ratio_le_seriesFactor ht_nonneg ht_lt_one
    rw [← hL] at hseries
    by_cases hs_small : t ^ 2 ≤ 3 / 8
    · have hA := polylog_seriesFactor_le_five_four (sq_nonneg t) hs_small
      have hbound : log (1 - p) - log p ≤ (5 / 2 : ℝ) * t := by
        have hscale := mul_le_mul_of_nonneg_left hA
          (show 0 ≤ (2 : ℝ) * t by positivity)
        nlinarith [hseries, hscale]
      have hcube := pow_le_pow_left₀ hL0 hbound 3
      have hpp_bound : p * (1 - p) ≤ 1 / 4 := by
        nlinarith [sq_nonneg (p - 1 / 2)]
      nlinarith [mul_le_mul_of_nonneg_right hcube hpp,
        mul_nonneg (pow_nonneg ht_nonneg 3) hpp]
    · have hs_large : 3 / 8 < t ^ 2 := lt_of_not_ge hs_small
      by_cases hs_mid : t ^ 2 ≤ 11 / 27
      · have hA := polylog_seriesFactor_le_four_three (sq_nonneg t) hs_mid
        have hbound : log (1 - p) - log p ≤ (8 / 3 : ℝ) * t := by
          have hscale := mul_le_mul_of_nonneg_left hA
            (show 0 ≤ (2 : ℝ) * t by positivity)
          nlinarith [hseries, hscale]
        have hcube := pow_le_pow_left₀ hL0 hbound 3
        have hpp_bound : p * (1 - p) ≤ 5 / 32 := by
          have hid : p * (1 - p) = (1 - t ^ 2) / 4 := by rw [ht]; ring
          rw [hid]
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hcube hpp,
          mul_nonneg (pow_nonneg ht_nonneg 3) hpp]
      · have hs_upper : 11 / 27 < t ^ 2 := lt_of_not_ge hs_mid
        have hA := polylog_seriesFactor_le_three_two (sq_nonneg t) hs_le
        have hbound : log (1 - p) - log p ≤ 3 * t := by
          have hscale := mul_le_mul_of_nonneg_left hA
            (show 0 ≤ (2 : ℝ) * t by positivity)
          nlinarith [hseries, hscale]
        have hcube := pow_le_pow_left₀ hL0 hbound 3
        have hpp_bound : p * (1 - p) ≤ 4 / 27 := by
          have hid : p * (1 - p) = (1 - t ^ 2) / 4 := by rw [ht]; ring
          rw [hid]
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hcube hpp,
          mul_nonneg (pow_nonneg ht_nonneg 3) hpp]

set_option maxHeartbeats 800000 in
/-- (♦) The slope derivative is at least `c · L(p)`, where `c = (τ(1-2τ))²`.
This is the pointwise strong-convexity estimate, reduced (via `kfun_diff_ge`) to
the single elementary leaf `key_polylog`. -/
lemma slope_deriv_ge {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1 / 2)) :
    (tau * (1 - 2 * tau)) ^ 2 * (log (1 - p) - log p) ≤ deriv (slopeFun tau) p := by
  rw [(slopeFun_hasDerivAt ht0 ht1 hp).deriv]
  have hp0 := hp.1
  have hp12 := hp.2
  have ha : (0 : ℝ) < 1 - 2 * tau := by linarith
  have ht : (0 : ℝ) < 1 - 2 * p := by linarith
  set q := tau + (1 - 2 * tau) * p with hq_def
  have hqmem : q ∈ Ioo p (1 / 2) := by
    rw [hq_def]; constructor <;> nlinarith
  have hq0 : 0 < q := hp0.trans hqmem.1
  have hq12 : q < 1 / 2 := hqmem.2
  have hq0ne : q ≠ 0 := ne_of_gt hq0
  have hq1ne : (1 : ℝ) - q ≠ 0 := by linarith
  have hp0ne : p ≠ 0 := ne_of_gt hp0
  have hp1ne : (1 : ℝ) - p ≠ 0 := by linarith
  set Lp := log (1 - p) - log p with hLp_def
  set Lq := log (1 - q) - log q with hLq_def
  have hLp : 0 < Lp := by rw [hLp_def, sub_pos]; exact Real.log_lt_log hp0 (by linarith)
  have hLq : 0 < Lq := by rw [hLq_def, sub_pos]; exact Real.log_lt_log hq0 (by linarith)
  have hLpne : Lp ≠ 0 := ne_of_gt hLp
  have hP : 0 < p * (1 - p) := by nlinarith
  have hQ : 0 < q * (1 - q) := by nlinarith
  have hQ14 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hNum_id : Lq * (q * (1 - q)) - (1 - 2 * tau) * Lp * (p * (1 - p)) =
      (1 - 2 * tau) * (1 - 2 * p) * (kfun q - kfun p) := by
    have h2q : (1 : ℝ) - 2 * q = (1 - 2 * tau) * (1 - 2 * p) := by rw [hq_def]; ring
    unfold kfun
    rw [Real.log_div hq1ne hq0ne, Real.log_div hp1ne hp0ne, ← hLp_def, ← hLq_def, h2q]
    field_simp
  have hkf : (q - p) * (1 - p - q) ≤ kfun q - kfun p :=
    kfun_diff_ge hp0 (le_of_lt hqmem.1) hq12
  have hpoly : (q - p) * (1 - p - q) = tau * (1 - tau) * (1 - 2 * p) ^ 2 := by
    rw [hq_def]; ring
  have hNum_ge : (1 - 2 * tau) * (tau * (1 - tau)) * (1 - 2 * p) ^ 3 ≤
      Lq * (q * (1 - q)) - (1 - 2 * tau) * Lp * (p * (1 - p)) := by
    rw [hNum_id]
    rw [hpoly] at hkf
    nlinarith [mul_le_mul_of_nonneg_left hkf (mul_nonneg ha.le ht.le)]
  have hkey := key_polylog hp0 hp12
  rw [← hLp_def] at hkey
  have hden : (0 : ℝ) < p * (1 - p) * (q * (1 - q)) * Lp ^ 2 := by positivity
  have hdval : (1 - 2 * tau) *
      ((-(1 - 2 * tau) / (q * (1 - q))) * Lp - Lq * (-1 / (p * (1 - p)))) / Lp ^ 2 =
      (1 - 2 * tau) * (Lq * (q * (1 - q)) - (1 - 2 * tau) * Lp * (p * (1 - p))) /
        (p * (1 - p) * (q * (1 - q)) * Lp ^ 2) := by
    field_simp
    ring
  rw [hdval, le_div_iff₀ hden]
  have hmid : tau * (Lp ^ 3 * (p * (1 - p)) * (q * (1 - q))) ≤
      (1 - tau) * (1 - 2 * p) ^ 3 := by
    have h1 : Lp ^ 3 * (p * (1 - p)) * (q * (1 - q)) ≤ (1 - 2 * p) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_right hkey (le_of_lt hQ), hQ14,
        pow_pos ht 3, mul_pos hP (pow_pos hLp 3)]
    nlinarith [h1, ht0.le, ht1, pow_pos ht 3]
  have e1 : (1 - 2 * tau) ^ 2 * tau * (tau * (Lp ^ 3 * (p * (1 - p)) * (q * (1 - q)))) ≤
      (1 - 2 * tau) ^ 2 * tau * ((1 - tau) * (1 - 2 * p) ^ 3) :=
    mul_le_mul_of_nonneg_left hmid (mul_nonneg (sq_nonneg (1 - 2 * tau)) ht0.le)
  have e2 : (1 - 2 * tau) * ((1 - 2 * tau) * (tau * (1 - tau)) * (1 - 2 * p) ^ 3) ≤
      (1 - 2 * tau) * (Lq * (q * (1 - q)) - (1 - 2 * tau) * Lp * (p * (1 - p))) :=
    mul_le_mul_of_nonneg_left hNum_ge ha.le
  nlinarith [e1, e2]

/-- `H(p) = slope(p) - c·Hb(p)` is monotone on `(0,1/2)` (from `slope_deriv_ge`). -/
lemma H_monotone {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2) :
    MonotoneOn (fun p => slopeFun tau p - (tau * (1 - 2 * tau)) ^ 2 * Hb p)
      (Ioo (0 : ℝ) (1 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 (1 / 2))
  · intro x hx
    have hs := (slopeFun_hasDerivAt ht0 ht1 hx).continuousAt
    have hb : ContinuousAt Hb x := Real.binEntropy_continuous.continuousAt
    exact (hs.sub (continuousAt_const.mul hb)).continuousWithinAt
  · rw [interior_Ioo]
    intro x hx
    have hs := (slopeFun_hasDerivAt ht0 ht1 hx).differentiableAt
    have hbd : HasDerivAt Hb (log (1 - x) - log x) x := by
      simpa [Hb] using
        Real.hasDerivAt_binEntropy (ne_of_gt hx.1) (by linarith [hx.2] : x ≠ 1)
    exact (hs.sub ((differentiableAt_const _).mul hbd.differentiableAt)).differentiableWithinAt
  · rw [interior_Ioo]
    intro x hx
    have hHb : HasDerivAt Hb (log (1 - x) - log x) x := by
      simpa [Hb] using
        Real.hasDerivAt_binEntropy (ne_of_gt hx.1) (by linarith [hx.2] : x ≠ 1)
    have hHd : HasDerivAt (fun p => slopeFun tau p - (tau * (1 - 2 * tau)) ^ 2 * Hb p)
        (deriv (slopeFun tau) x - (tau * (1 - 2 * tau)) ^ 2 * (log (1 - x) - log x)) x :=
      (slopeFun_hasDerivAt ht0 ht1 hx).differentiableAt.hasDerivAt.sub
        (hHb.const_mul ((tau * (1 - 2 * tau)) ^ 2))
    rw [hHd.deriv]
    have := slope_deriv_ge ht0 ht1 hx
    linarith

end MglBregmanReduction

/-! The only genuinely analytic input in this file is the quantitative form of
strict convexity below.  Everything after it is finite Jensen bookkeeping,
binary-entropy branch geometry, and algebra. -/

set_option maxHeartbeats 800000 in
/-- A conservative strong-convexity estimate for the Mrs.-Gerber curve.

The optimal lower bound for the second derivative is larger than the constant
used here.  The deliberately weak `(tau * (1 - 2 * tau))²` constant is enough
for `err_val`, and keeps the endpoint-uniform statement simple.

Proved from the pointwise slope bound `slope_deriv_ge` by convexity of
`φ = mglCurve tau - (c/2)·id²` and the tangent-line inequality. -/
lemma mglCurve_bregman_ge_sq
    {tau u v : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hu : u ∈ Ioo (0 : ℝ) (Real.log 2))
    (hv : v ∈ Icc (0 : ℝ) (Real.log 2)) :
    (tau * (1 - 2 * tau)) ^ 2 / 2 * (v - u) ^ 2 ≤
      mglCurve tau v - mglCurve tau u -
        deriv (mglCurve tau) u * (v - u) := by
  set c := (tau * (1 - 2 * tau)) ^ 2 with hc_def
  set φ : ℝ → ℝ := fun w => mglCurve tau w - c / 2 * w ^ 2 with hφ_def
  have hcont_mgl : ContinuousOn (mglCurve tau) (Icc 0 (Real.log 2)) := by
    unfold mglCurve
    exact Real.binEntropy_continuous.continuousOn.comp
      (continuousOn_const.add (continuousOn_const.mul hbInv_continuousOn))
      (fun _ _ => mem_univ _)
  have hφcont : ContinuousOn φ (Icc 0 (Real.log 2)) := by
    rw [hφ_def]; exact hcont_mgl.sub (continuousOn_const.mul (continuousOn_pow 2))
  have hφdiff : DifferentiableOn ℝ φ (interior (Icc 0 (Real.log 2))) := by
    rw [interior_Icc, hφ_def]
    intro x hx
    exact ((mglCurve_hasDerivAt ht0 ht1 hx).differentiableAt.sub
      ((differentiableAt_const _).mul (differentiableAt_pow 2))).differentiableWithinAt
  have hderivφ : ∀ w ∈ Ioo (0 : ℝ) (Real.log 2),
      deriv φ w = slopeFun tau (hbInv w) - c * Hb (hbInv w) := by
    intro w hw
    have hmgl : HasDerivAt (mglCurve tau) (deriv (mglCurve tau) w) w :=
      (mglCurve_hasDerivAt ht0 ht1 hw).differentiableAt.hasDerivAt
    have hpow : HasDerivAt (fun w => c / 2 * w ^ 2) (c * w) w := by
      have h := (hasDerivAt_pow 2 w).const_mul (c / 2); convert h using 1; ring
    have hφd : HasDerivAt φ (deriv (mglCurve tau) w - c * w) w := by
      rw [hφ_def]; exact hmgl.sub hpow
    rw [hφd.deriv]
    have h1 : deriv (mglCurve tau) w = slopeFun tau (hbInv w) :=
      (mglCurve_hasDerivAt ht0 ht1 hw).deriv
    have h2 : Hb (hbInv w) = w := (hbInv_spec ⟨hw.1.le, hw.2.le⟩).2
    rw [h1, h2]
  have hφmono : MonotoneOn (deriv φ) (Ioo (0 : ℝ) (Real.log 2)) := by
    intro w1 hw1 w2 hw2 h12
    rw [hderivφ w1 hw1, hderivφ w2 hw2]
    have hle : hbInv w1 ≤ hbInv w2 :=
      hbInv_strictMonoOn.monotoneOn ⟨hw1.1.le, hw1.2.le⟩ ⟨hw2.1.le, hw2.2.le⟩ h12
    exact H_monotone ht0 ht1 (hbInv_mem_Ioo hw1) (hbInv_mem_Ioo hw2) hle
  have hφconv : ConvexOn ℝ (Icc 0 (Real.log 2)) φ :=
    MonotoneOn.convexOn_of_deriv (convex_Icc _ _) hφcont hφdiff
      (by rw [interior_Icc]; exact hφmono)
  have huIcc : u ∈ Icc (0 : ℝ) (Real.log 2) := ⟨hu.1.le, hu.2.le⟩
  have hφdiffu : DifferentiableAt ℝ φ u := by
    rw [hφ_def]
    exact (mglCurve_hasDerivAt ht0 ht1 hu).differentiableAt.sub
      ((differentiableAt_const _).mul (differentiableAt_pow 2))
  have hφu : HasDerivAt φ (deriv φ u) u := hφdiffu.hasDerivAt
  have htangent : deriv φ u * (v - u) ≤ φ v - φ u := by
    rcases lt_trichotomy u v with h | h | h
    · have hs := hφconv.le_slope_of_hasDerivAt huIcc hv h hφu
      rw [slope_def_field] at hs
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < v - u)] at hs
      linarith
    · subst h; simp
    · have hs := hφconv.slope_le_of_hasDerivAt hv huIcc h hφu
      rw [slope_def_field] at hs
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < u - v)] at hs
      linarith
  have hdφu : deriv φ u = deriv (mglCurve tau) u - c * u := by
    have hpow : HasDerivAt (fun w => c / 2 * w ^ 2) (c * u) u := by
      have h := (hasDerivAt_pow 2 u).const_mul (c / 2); convert h using 1; ring
    have hh : HasDerivAt φ (deriv (mglCurve tau) u - c * u) u := by
      rw [hφ_def]; exact (mglCurve_hasDerivAt ht0 ht1 hu).differentiableAt.hasDerivAt.sub hpow
    exact hh.deriv
  have hφv : φ v = mglCurve tau v - c / 2 * v ^ 2 := by rw [hφ_def]
  have hφu' : φ u = mglCurve tau u - c / 2 * u ^ 2 := by rw [hφ_def]
  rw [hφv, hφu', hdφu] at htangent
  nlinarith [htangent]

noncomputable def eps_val (tau zeta delta : ℝ) : ℝ :=
  (err_val tau zeta delta / 4) * deriv Hb (1 / 2 - zeta / 2)

/-- Number of coordinates whose conditional entropy is above the global rate
by more than `eps_val`.  Only the upper tail matters for excess mismatch. -/
noncomputable def offFlatCount {n : ℕ} (tau zeta delta : ℝ)
    (mu : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ t, if eps_val tau zeta delta <
      condEntropy mu t x - entropyRate n mu then 1 else 0

lemma conditionalMismatch_mem_Icc_half {n : ℕ} (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (t : Fin n) (x : Cube n) :
    conditionalMismatch mu t x ∈ Icc (0 : ℝ) (1 / 2) := by
  refine ⟨conditionalMismatch_nonneg mu hmu t x, ?_⟩
  unfold conditionalMismatch
  split_ifs with h
  · have hp := condProbOne_le_one mu hmu t x
    linarith
  · linarith

lemma entropyRate_mem_Ioo_of_hbInv_window
    {zeta : ℝ} (hz0 : 0 < zeta) {n : ℕ} {mu : Cube n → ℝ}
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta) :
    entropyRate n mu ∈ Ioo (0 : ℝ) (Real.log 2) := by
  constructor
  · by_contra h
    have hu : entropyRate n mu ≤ 0 := le_of_not_gt h
    rw [hbInv_eq_zero_of_nonpos hu] at hzeta1
    linarith
  · by_contra h
    have hu : Real.log 2 ≤ entropyRate n mu := le_of_not_gt h
    rcases hu.eq_or_lt with hu | hu
    · have hspec := hbInv_spec
          (show entropyRate n mu ∈ Icc (0 : ℝ) (Real.log 2) by
            rw [← hu]
            exact ⟨Real.log_pos (by norm_num) |>.le, le_rfl⟩)
      have hp : hbInv (entropyRate n mu) = 1 / 2 := by
        have htop : Real.binEntropy (hbInv (entropyRate n mu)) =
            Real.log 2 := by
          simpa [Hb] using hspec.2.trans hu.symm
        have := Real.binEntropy_eq_log_two.mp htop
        simpa using this
      rw [hp] at hzeta2
      linarith
    · rw [hbInv_eq_zero_of_gt_log2 hu] at hzeta1
      linarith

lemma condEntropy_mem_Icc {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (x : Cube n) :
    condEntropy mu t x ∈ Icc (0 : ℝ) (Real.log 2) := by
  rw [condEntropy_eq_Hb_conditionalMismatch]
  exact ⟨Real.binEntropy_nonneg
      (conditionalMismatch_mem_Icc_half mu hmu t x).1
      ((conditionalMismatch_mem_Icc_half mu hmu t x).2.trans (by norm_num)),
    Real.binEntropy_le_log_two⟩

/-- The binary-entropy derivative at the edge of the enlarged window is at
least `2*zeta`.  This is the first term of the positive power series for
`log ((1+zeta)/(1-zeta))`. -/
lemma deriv_Hb_window_ge_two_zeta {zeta : ℝ}
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) :
    2 * zeta ≤ deriv Hb (1 / 2 - zeta / 2) := by
  have hzlt : zeta < 1 := hz1.trans_lt (by norm_num)
  have hseries := Real.sum_range_le_log_div hz0.le hzlt 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hseries
  unfold Hb
  rw [Real.deriv_binEntropy]
  have hpos1 : 0 < 1 + zeta := by linarith
  have hpos2 : 0 < 1 - zeta := by linarith
  rw [← Real.log_div (show 1 - (1 / 2 - zeta / 2) ≠ 0 by linarith)
    (show 1 / 2 - zeta / 2 ≠ 0 by linarith)]
  have hratio :
      (1 - (1 / 2 - zeta / 2)) / (1 / 2 - zeta / 2) =
        (1 + zeta) / (1 - zeta) := by
    field_simp
    ring
  rw [hratio]
  linarith

/-- On a lower-branch interval ending before `r`, binary entropy grows at
least at the terminal derivative `deriv Hb r`. -/
lemma Hb_growth_ge_terminal_deriv {p q r : ℝ}
    (hp0 : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r) (hr : r < 1 / 2) :
    deriv Hb r * (q - p) ≤ Hb q - Hb p := by
  have hr0 : 0 < r := hp0.trans_le (hpq.trans hqr)
  have hcont : ContinuousOn Hb (Icc p q) :=
    Real.binEntropy_continuous.continuousOn
  have hdiff : DifferentiableOn ℝ Hb (interior (Icc p q)) := by
    intro x hx
    have hxm := interior_subset hx
    have hx0 : 0 < x := hp0.trans_le hxm.1
    have hx1 : x < 1 := hxm.2.trans hqr |>.trans_lt (hr.trans (by norm_num))
    exact (Real.hasDerivAt_binEntropy (ne_of_gt hx0) (by linarith : x ≠ 1))
      |>.differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc p q), deriv Hb r ≤ deriv Hb x := by
    intro x hx
    have hxm := interior_subset hx
    have hx0 : 0 < x := hp0.trans_le hxm.1
    have hxr : x ≤ r := hxm.2.trans hqr
    unfold Hb
    rw [Real.deriv_binEntropy, Real.deriv_binEntropy]
    have hlog1 : Real.log (1 - r) ≤ Real.log (1 - x) := by
      apply Real.log_le_log
      · linarith
      · linarith
    have hlog2 : Real.log x ≤ Real.log r := Real.log_le_log hx0 hxr
    linarith
  exact (convex_Icc p q).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hderiv p (left_mem_Icc.mpr hpq) q
      (right_mem_Icc.mpr hpq) hpq

/-- The total Jensen gap of all conditional entropies is bounded by the MGL
slack.  This combines the per-coordinate conditional-MGL inequality with the
entropy chain rule. -/
lemma total_condEntropy_mgl_gap_le
    {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hmu : IsLaw mu)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ)) :
    (∑ t, ∑ x, mu x * mglCurve tau (condEntropy mu t x)) -
        (n : ℝ) * mglCurve tau (entropyRate n mu) ≤ delta * (n : ℝ) := by
  have hnoise : IsLaw (noiseMass tau mu) :=
    noiseMass_isLaw ht0.le (by linarith) mu hmu
  have hsum : (∑ t, ∑ x, mu x * mglCurve tau (condEntropy mu t x)) ≤
      entropy (noiseMass tau mu) := by
    rw [entropy_eq_sum_stepEntropy _ hnoise]
    apply Finset.sum_le_sum
    intro t _
    calc
      (∑ x, mu x * mglCurve tau (condEntropy mu t x)) =
          ∑ x, mu x * Hb
            (tau + (1 - 2 * tau) * condProbOne mu t x) := by
        apply Finset.sum_congr rfl
        intro x _
        unfold condEntropy
        rw [mglCurve_Hb_eq_all ht0 ht1
          ⟨condProbOne_nonneg mu hmu t x, condProbOne_le_one mu hmu t x⟩]
      _ ≤ stepEntropy (noiseMass tau mu) t :=
        stepEntropy_noise_ge_condMGL tau mu hmu ht0 ht1 t
  linarith

/-- Quantitative global flatness: the weighted square deviation of all
conditional entropies from the entropy rate is paid for by the MGL slack. -/
lemma condEntropy_sq_deviation_bound
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hmu : IsLaw mu)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ)) :
    (tau * (1 - 2 * tau)) ^ 2 / 2 *
        (∑ t, ∑ x, mu x *
          (condEntropy mu t x - entropyRate n mu) ^ 2) ≤
      delta * (n : ℝ) := by
  let u := entropyRate n mu
  let c := (tau * (1 - 2 * tau)) ^ 2 / 2
  let d := deriv (mglCurve tau) u
  have hu : u ∈ Ioo (0 : ℝ) (Real.log 2) :=
    entropyRate_mem_Ioo_of_hbInv_window hz0 hzeta1 hzeta2
  have hpoint (t : Fin n) (x : Cube n) :
      c * (condEntropy mu t x - u) ^ 2 ≤
        mglCurve tau (condEntropy mu t x) - mglCurve tau u -
          d * (condEntropy mu t x - u) := by
    exact mglCurve_bregman_ge_sq ht0 ht1 hu (condEntropy_mem_Icc mu hmu t x)
  have hweighted :
      c * (∑ t, ∑ x, mu x * (condEntropy mu t x - u) ^ 2) ≤
        ∑ t, ∑ x, mu x *
          (mglCurve tau (condEntropy mu t x) - mglCurve tau u -
            d * (condEntropy mu t x - u)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    convert mul_le_mul_of_nonneg_left (hpoint t x) (hmu.1 x) using 1 <;> ring
  have hlinear :
      (∑ t, ∑ x, mu x *
          (mglCurve tau (condEntropy mu t x) - mglCurve tau u -
            d * (condEntropy mu t x - u))) =
        (∑ t, ∑ x, mu x * mglCurve tau (condEntropy mu t x)) -
          (n : ℝ) * mglCurve tau u := by
    have hstep (t : Fin n) :
        ∑ x, mu x * condEntropy mu t x = stepEntropy mu t := by
      rfl
    have hrate : ∑ t, stepEntropy mu t = (n : ℝ) * u := by
      simpa [u] using sum_stepEntropy_eq_rate mu hmu
    have hdiff_step (t : Fin n) :
        (∑ x, mu x * (condEntropy mu t x - u)) =
          stepEntropy mu t - u := by
      calc
        _ = (∑ x, mu x * condEntropy mu t x) -
            (∑ x, mu x * u) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = stepEntropy mu t - u := by
          rw [hstep, ← Finset.sum_mul, hmu.2, one_mul]
    have hdiff :
        (∑ t, ∑ x, mu x * (condEntropy mu t x - u)) = 0 := by
      simp_rw [hdiff_step]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, hrate]
      ring
    have hconst :
        (∑ _t : Fin n, ∑ x : Cube n, mu x * mglCurve tau u) =
          (n : ℝ) * mglCurve tau u := by
      calc
        _ = ∑ _t : Fin n, mglCurve tau u := by
          apply Finset.sum_congr rfl
          intro t _
          rw [← Finset.sum_mul, hmu.2, one_mul]
        _ = (n : ℝ) * mglCurve tau u := by simp
    have hexpand :
        (∑ t, ∑ x, mu x *
          (mglCurve tau (condEntropy mu t x) - mglCurve tau u -
            d * (condEntropy mu t x - u))) =
          (∑ t, ∑ x, mu x * mglCurve tau (condEntropy mu t x)) -
            (∑ _t : Fin n, ∑ x : Cube n, mu x * mglCurve tau u) -
              d * (∑ t, ∑ x, mu x * (condEntropy mu t x - u)) := by
      calc
        _ = ∑ t, ∑ x,
            (mu x * mglCurve tau (condEntropy mu t x) -
              mu x * mglCurve tau u -
                d * (mu x * (condEntropy mu t x - u))) := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by
          have hinner_expand (t : Fin n) :
              (∑ x, (mu x * mglCurve tau (condEntropy mu t x) -
                mu x * mglCurve tau u -
                  d * (mu x * (condEntropy mu t x - u)))) =
                (∑ x, mu x * mglCurve tau (condEntropy mu t x)) -
                  (∑ x, mu x * mglCurve tau u) -
                    d * (∑ x, mu x * (condEntropy mu t x - u)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum]
          simp_rw [hinner_expand]
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    rw [hexpand, hconst, hdiff, mul_zero, sub_zero]
  rw [hlinear] at hweighted
  exact hweighted.trans
    (total_condEntropy_mgl_gap_le ht0 ht1 hmu h_ent)

/-- In the only nontrivial regime for the positive-part budget, every step
outside the upper entropy tail has mismatch at most `p + err/4`. -/
lemma offFlatBudget_le_half_offFlatCount
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (x : Cube n) :
    offFlatBudget (err_val tau zeta delta) mu x ≤
      offFlatCount tau zeta delta mu x / 2 := by
  let e := err_val tau zeta delta
  let p := hbInv (entropyRate n mu)
  let u := entropyRate n mu
  let r := 1 / 2 - zeta / 2
  let derivR := deriv Hb r
  let eps := e / 4 * derivR
  have he : 0 < e := err_val_pos ht0 ht1 hz0 hz1 hd0
  have hp0 : 0 < p := hz0.trans_le hzeta1
  have hp_half : p ≤ 1 / 2 - zeta := hzeta2
  have hrhalf : r < 1 / 2 := by dsimp [r]; linarith
  have hderiv : 2 * zeta ≤ derivR := by
    simpa [derivR, r] using deriv_Hb_window_ge_two_zeta hz0 hz1
  have hderiv0 : 0 < derivR := lt_of_lt_of_le (by positivity) hderiv
  have heps0 : 0 < eps := by dsimp [eps]; positivity
  have hu := entropyRate_mem_Ioo_of_hbInv_window hz0 hzeta1 hzeta2
  have hHb_p : Hb p = u := (hbInv_spec ⟨hu.1.le, hu.2.le⟩).2
  have hcount0 : 0 ≤ offFlatCount tau zeta delta mu x := by
    unfold offFlatCount
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> norm_num
  by_cases htrivial : 1 / 2 ≤ p + e / 2
  · unfold offFlatBudget
    apply max_le
    · positivity
    · have hqsum : predictableDistance (conditionalMismatch mu) x ≤
          (1 / 2) * (n : ℝ) := by
        unfold predictableDistance
        calc
          (∑ t, conditionalMismatch mu t x) ≤ ∑ _t : Fin n, (1 / 2 : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            exact (conditionalMismatch_mem_Icc_half mu hmu t x).2
          _ = (1 / 2) * (n : ℝ) := by simp [mul_comm]
      change predictableDistance (conditionalMismatch mu) x -
          (p + e / 2) * (n : ℝ) ≤ offFlatCount tau zeta delta mu x / 2
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_right htrivial hn0
      linarith
  · have hnontrivial : p + e / 2 < 1 / 2 := lt_of_not_ge htrivial
    have hq_le_r : p + e / 4 ≤ r := by
      rcases le_total e (2 * zeta) with hez | hez
      · dsimp [r]
        linarith
      · dsimp [r]
        linarith
    have hflat (t : Fin n)
        (ht : ¬ eps < condEntropy mu t x - u) :
        conditionalMismatch mu t x ≤ p + e / 4 := by
      by_contra hq
      have hqgt : p + e / 4 < conditionalMismatch mu t x := lt_of_not_ge hq
      have hq0 : p + e / 4 ≤ conditionalMismatch mu t x := hqgt.le
      have hpq : p ≤ p + e / 4 := by linarith
      have hgrowth := Hb_growth_ge_terminal_deriv hp0 hpq hq_le_r hrhalf
      have hmono : Hb (p + e / 4) < Hb (conditionalMismatch mu t x) := by
        apply Real.binEntropy_strictMonoOn
        · constructor
          · exact hp0.le.trans hpq
          · simpa [one_div] using hq_le_r.trans hrhalf.le
        · have hqm := conditionalMismatch_mem_Icc_half mu hmu t x
          simpa [one_div] using hqm
        · exact hqgt
      have hF : eps < condEntropy mu t x - u := by
        rw [condEntropy_eq_Hb_conditionalMismatch, ← hHb_p]
        dsimp [eps]
        have heq : derivR * (p + e / 4 - p) = e / 4 * derivR := by ring
        rw [heq] at hgrowth
        linarith
      exact ht hF
    have hsum : predictableDistance (conditionalMismatch mu) x ≤
        (p + e / 4) * (n : ℝ) + offFlatCount tau zeta delta mu x / 2 := by
      unfold predictableDistance offFlatCount
      calc
        (∑ t, conditionalMismatch mu t x) ≤
            ∑ t, ((p + e / 4) +
              (if eps < condEntropy mu t x - u then 1 / 2 else 0)) := by
          apply Finset.sum_le_sum
          intro t _
          by_cases ht : eps < condEntropy mu t x - u
          · rw [if_pos ht]
            have hq := (conditionalMismatch_mem_Icc_half mu hmu t x).2
            have hp_nonneg : 0 ≤ p + e / 4 := by positivity
            linarith
          · rw [if_neg ht]
            simpa using hflat t ht
        _ = (p + e / 4) * (n : ℝ) +
            (∑ t, if eps < condEntropy mu t x - u then 1 else 0) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin]
          congr 1
          · ring
          · rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro t _
            split_ifs <;> norm_num
    unfold offFlatBudget
    apply max_le
    · positivity
    · change predictableDistance (conditionalMismatch mu) x -
          (p + e / 2) * (n : ℝ) ≤
        (∑ t, if eps < condEntropy mu t x - u then 1 else 0) / 2
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hreserve : 0 ≤ e / 4 * (n : ℝ) := by positivity
      change predictableDistance (conditionalMismatch mu) x ≤
        (p + e / 4) * (n : ℝ) +
          (∑ t, if eps < condEntropy mu t x - u then 1 else 0) / 2 at hsum
      linarith

/-- The eighth-root error is large enough, in the nontrivial `err < 1`
regime, to absorb the channel/window constants needed by Chebyshev. -/
lemma sixteen_delta_le_channel_err_fourth
    {tau zeta delta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4) (hd0 : 0 < delta)
    (hsmall : err_val tau zeta delta < 1) :
    16 * delta ≤
      (zeta * tau * (1 - 2 * tau)) ^ 2 *
        err_val tau zeta delta ^ 4 := by
  let A := zeta * tau * (1 - 2 * tau)
  let s := Real.sqrt (Real.sqrt (Real.sqrt delta))
  let K := 1 + 1 / A ^ 2
  have ha : 0 < 1 - 2 * tau := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hAhalf : A ≤ 1 / 2 := by
    dsimp [A]
    have hchan0 : 0 ≤ 1 - 2 * tau := ha.le
    calc
      zeta * tau * (1 - 2 * tau) ≤ (1 / 4) * (1 / 2) * 1 := by
        apply mul_le_mul
        · exact mul_le_mul hz1 ht1.le ht0.le (by norm_num)
        · linarith
        · positivity
        · positivity
      _ ≤ 1 / 2 := by norm_num
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hK1 : 1 ≤ K := by
    dsimp [K]
    have : 0 ≤ 1 / A ^ 2 := by positivity
    linarith
  have hKA : 1 / A ^ 2 ≤ K := by dsimp [K]; linarith
  have heq : err_val tau zeta delta = K * s := by rfl
  have hsA : s < A ^ 2 := by
    have hmul : (1 / A ^ 2) * s ≤ err_val tau zeta delta := by
      rw [heq]
      exact mul_le_mul_of_nonneg_right hKA hs0
    have hdiv : s / A ^ 2 < 1 := by
      have heqdiv : s / A ^ 2 = (1 / A ^ 2) * s := by ring
      rw [heqdiv]
      exact hmul.trans_lt hsmall
    rwa [div_lt_one₀ (sq_pos_of_pos hA)] at hdiv
  have hs_sq : s * s = Real.sqrt (Real.sqrt delta) := by
    dsimp [s]
    exact Real.mul_self_sqrt (Real.sqrt_nonneg (Real.sqrt delta))
  have hs4 : s ^ 4 = Real.sqrt delta := by
    calc
      s ^ 4 = (s * s) ^ 2 := by ring
      _ = Real.sqrt (Real.sqrt delta) ^ 2 := by rw [hs_sq]
      _ = Real.sqrt delta := Real.sq_sqrt (Real.sqrt_nonneg delta)
  have hs8 : s ^ 8 = delta := by
    calc
      s ^ 8 = (s ^ 4) ^ 2 := by ring
      _ = Real.sqrt delta ^ 2 := by rw [hs4]
      _ = delta := Real.sq_sqrt hd0.le
  have hA6 : A ^ 6 ≤ (1 / 2 : ℝ) ^ 6 := by gcongr
  have hfactor : 16 * A ^ 6 ≤ 1 := by
    calc
      16 * A ^ 6 ≤ 16 * (1 / 2 : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_left hA6 (by norm_num)
      _ ≤ 1 := by norm_num
  have hs4A : 16 * s ^ 4 ≤ A ^ 2 := by
    have hs4le : s ^ 4 ≤ (A ^ 2) ^ 4 := by gcongr
    calc
      16 * s ^ 4 ≤ 16 * (A ^ 2) ^ 4 :=
        mul_le_mul_of_nonneg_left hs4le (by norm_num)
      _ = A ^ 2 * (16 * A ^ 6) := by ring
      _ ≤ A ^ 2 * 1 := mul_le_mul_of_nonneg_left hfactor (sq_nonneg A)
      _ = A ^ 2 := by ring
  have hse : s ≤ err_val tau zeta delta := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hK1 hs0]
  have hs4e : s ^ 4 ≤ err_val tau zeta delta ^ 4 := by gcongr
  calc
    16 * delta = 16 * s ^ 8 := by rw [hs8]
    _ = (16 * s ^ 4) * s ^ 4 := by ring
    _ ≤ A ^ 2 * s ^ 4 :=
      mul_le_mul hs4A (le_refl _) (by positivity) (sq_nonneg A)
    _ ≤ A ^ 2 * err_val tau zeta delta ^ 4 :=
      mul_le_mul_of_nonneg_left hs4e (sq_nonneg A)

lemma expected_offFlatCount_bound
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ))
    (hsmall : err_val tau zeta delta < 1) :
    ∑ x, mu x * offFlatCount tau zeta delta mu x ≤
      (err_val tau zeta delta ^ 2 / 2) * (n : ℝ) := by
  let e := err_val tau zeta delta
  let eps := eps_val tau zeta delta
  let c := (tau * (1 - 2 * tau)) ^ 2
  let V := ∑ t, ∑ x, mu x *
    (condEntropy mu t x - entropyRate n mu) ^ 2
  let M := ∑ x, mu x * offFlatCount tau zeta delta mu x
  have he : 0 < e := err_val_pos ht0 ht1 hz0 hz1 hd0
  have hderiv := deriv_Hb_window_ge_two_zeta hz0 hz1
  have heps : 0 < eps := by
    dsimp [eps, eps_val, e]
    have : 0 < deriv Hb (1 / 2 - zeta / 2) :=
      lt_of_lt_of_le (by positivity) hderiv
    positivity
  have hc : 0 < c := by
    have ha : 0 < 1 - 2 * tau := by linarith
    dsimp [c]
    positivity
  have hM0 : 0 ≤ M := by
    dsimp [M, offFlatCount]
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (hmu.1 x) (Finset.sum_nonneg fun t _ => by
      split_ifs <;> norm_num)
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg (hmu.1 x) (sq_nonneg _)
  have hcount : eps ^ 2 * M ≤ V := by
    dsimp [M, V, offFlatCount]
    calc
      eps ^ 2 * (∑ x, mu x *
          ∑ t, if eps < condEntropy mu t x - entropyRate n mu then 1 else 0) =
          ∑ x, ∑ t, mu x *
            (eps ^ 2 *
              (if eps < condEntropy mu t x - entropyRate n mu then 1 else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        calc
          eps ^ 2 * (mu x *
              ∑ t, if eps < condEntropy mu t x - entropyRate n mu then 1 else 0) =
              (eps ^ 2 * mu x) *
                ∑ t, if eps < condEntropy mu t x - entropyRate n mu then 1 else 0 := by
            ring
          _ = ∑ t, (eps ^ 2 * mu x) *
              (if eps < condEntropy mu t x - entropyRate n mu then 1 else 0) := by
            rw [Finset.mul_sum]
          _ = ∑ t, mu x *
              (eps ^ 2 *
                (if eps < condEntropy mu t x - entropyRate n mu then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro t _
            ring
      _ =
          ∑ t, ∑ x, mu x *
            (eps ^ 2 *
              (if eps < condEntropy mu t x - entropyRate n mu then 1 else 0)) := by
        exact Finset.sum_comm
      _ ≤ ∑ t, ∑ x, mu x *
          (condEntropy mu t x - entropyRate n mu) ^ 2 := by
        apply Finset.sum_le_sum
        intro t _
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hmu.1 x)
        by_cases h : eps < condEntropy mu t x - entropyRate n mu
        · rw [if_pos h, mul_one]
          nlinarith
        · rw [if_neg h, mul_zero]
          exact sq_nonneg _
  have hvar : c / 2 * V ≤ delta * (n : ℝ) := by
    simpa [c, V] using condEntropy_sq_deviation_bound
      ht0 ht1 hz0 hmu hzeta1 hzeta2 h_ent
  let A := zeta * tau * (1 - 2 * tau)
  have hA : 0 < A := by
    have ha : 0 < 1 - 2 * tau := by linarith
    dsimp [A]
    positivity
  have hdelta : 16 * delta ≤ A ^ 2 * e ^ 4 := by
    simpa [A, e] using sixteen_delta_le_channel_err_fourth
      ht0 ht1 hz0 hz1 hd0 hsmall
  have hcd : 4 * A ^ 2 ≤
      c * deriv Hb (1 / 2 - zeta / 2) ^ 2 := by
    have hsq : (2 * zeta) ^ 2 ≤
        deriv Hb (1 / 2 - zeta / 2) ^ 2 := by
      nlinarith [sq_nonneg
        (deriv Hb (1 / 2 - zeta / 2) - 2 * zeta)]
    dsimp [A, c]
    have hchan : 0 ≤ (tau * (1 - 2 * tau)) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hsq hchan]
  have hnumeric : 4 * delta ≤ c * eps ^ 2 * e ^ 2 := by
    have he4 : 0 ≤ e ^ 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hcd
      (show 0 ≤ e ^ 4 / 16 by positivity)
    dsimp [eps, eps_val]
    dsimp [e] at hmul ⊢
    dsimp [A] at hdelta
    nlinarith
  have hleft : c * eps ^ 2 * M ≤ 2 * delta * (n : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hcount hc.le
    nlinarith [hvar]
  have hright : 2 * delta * (n : ℝ) ≤
      c * eps ^ 2 * ((e ^ 2 / 2) * (n : ℝ)) := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_right hnumeric
      (show 0 ≤ (n : ℝ) / 2 by positivity)
    nlinarith
  change M ≤ (e ^ 2 / 2) * (n : ℝ)
  exact le_of_mul_le_mul_left (hleft.trans hright)
    (mul_pos hc (sq_pos_of_pos heps))

lemma flatness_off_flat_budget_bound
    {tau zeta : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hz0 : 0 < zeta) (hz1 : zeta ≤ 1 / 4)
    {n : ℕ} {mu : Cube n → ℝ} {delta : ℝ}
    (hn : 1 ≤ n) (hmu : IsLaw mu) (hd0 : 0 < delta)
    (hzeta1 : zeta ≤ hbInv (entropyRate n mu))
    (hzeta2 : hbInv (entropyRate n mu) ≤ 1 / 2 - zeta)
    (h_ent : entropy (noiseMass tau mu) ≤
      (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ)) :
    ∑ x, mu x * offFlatBudget (err_val tau zeta delta) mu x ≤
      (err_val tau zeta delta ^ 2 / 4) * (n : ℝ) := by
  let e := err_val tau zeta delta
  let p := hbInv (entropyRate n mu)
  have he : 0 < e := err_val_pos ht0 ht1 hz0 hz1 hd0
  by_cases hsmall : e < 1
  · have hpoint (x : Cube n) := offFlatBudget_le_half_offFlatCount
      ht0 ht1 hz0 hz1 hmu hd0 hzeta1 hzeta2 x
    calc
      (∑ x, mu x * offFlatBudget (err_val tau zeta delta) mu x) ≤
          ∑ x, mu x * (offFlatCount tau zeta delta mu x / 2) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hpoint x) (hmu.1 x)
      _ = (∑ x, mu x * offFlatCount tau zeta delta mu x) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ ((err_val tau zeta delta ^ 2 / 2) * (n : ℝ)) / 2 := by
        exact div_le_div_of_nonneg_right
          (expected_offFlatCount_bound ht0 ht1 hz0 hz1 hn hmu hd0
            hzeta1 hzeta2 h_ent (by simpa [e] using hsmall)) (by norm_num)
      _ = (err_val tau zeta delta ^ 2 / 4) * (n : ℝ) := by ring
  · have he1 : 1 ≤ e := le_of_not_gt hsmall
    have hp0 : 0 ≤ p := (hz0.trans_le hzeta1).le
    have htarget : 1 / 2 ≤ p + e / 2 := by linarith
    have hzero (x : Cube n) : offFlatBudget e mu x = 0 := by
      unfold offFlatBudget
      rw [max_eq_left]
      have hqsum : predictableDistance (conditionalMismatch mu) x ≤
          (1 / 2) * (n : ℝ) := by
        unfold predictableDistance
        calc
          (∑ t, conditionalMismatch mu t x) ≤ ∑ _t : Fin n, (1 / 2 : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            exact (conditionalMismatch_mem_Icc_half mu hmu t x).2
          _ = (1 / 2) * (n : ℝ) := by simp [mul_comm]
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_right htarget hn0
      dsimp [p] at htarget ⊢
      linarith
    have hlhs : ∑ x, mu x * offFlatBudget e mu x = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [hzero x, mul_zero]
    change ∑ x, mu x * offFlatBudget e mu x ≤ (e ^ 2 / 4) * (n : ℝ)
    rw [hlhs]
    positivity

end AverageHarperStability
