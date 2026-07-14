import AverageHarperStability.MGL.Curve

open scoped BigOperators
open Set
open Real

namespace AverageHarperStability

/-!
Exact entropy-slack decomposition and Jensen-flatness layer (L0--L3).
Workers for the distribution section introduce only mathematically explicit
lemmas here; the frozen target they must jointly imply is
`DistributionStabilityStatement`.
-/

lemma mglCurve_slope_cap {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) (log 2)) :
    deriv (mglCurve tau) u ≤ (1 - 2 * tau) ^ 2 := by
  let a : ℝ := 1 - 2 * tau
  let p : ℝ := hbInv u
  let q : ℝ → ℝ := fun x => tau + a * x
  let L : ℝ → ℝ := fun x => log (1 - x) - log x
  let F : ℝ → ℝ := fun x => a * L x - L (q x)
  have ha : 0 < a := by dsimp [a]; linarith
  have hp : p ∈ Ioo (0 : ℝ) (1 / 2) := hbInv_mem_Ioo hu
  have hq_mem (x : ℝ) (hx : x ∈ Icc p (1 / 2)) : q x ∈ Icc x (1 / 2) := by
    have hnonneg : 0 ≤ 1 - 2 * x := by linarith [hx.2]
    constructor
    · dsimp [q, a]
      nlinarith [mul_nonneg ht0.le hnonneg]
    · dsimp [q, a]
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hx.2)]
  have hLder (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
      HasDerivAt L (-1 / (x * (1 - x))) x := by
    dsimp [L]
    have h1 := (Real.hasDerivAt_log (by linarith : 1 - x ≠ 0)).comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    have h2 := Real.hasDerivAt_log (ne_of_gt hx0)
    convert h1.sub h2 using 1 <;>
      field_simp [ne_of_gt hx0, ne_of_gt (sub_pos.mpr hx1)] <;> ring
  have hFder (x : ℝ) (hx : x ∈ Icc p (1 / 2)) :
      HasDerivAt F
        (a * (-1 / (x * (1 - x))) -
          (-a / (q x * (1 - q x)))) x := by
    have hx0 : 0 < x := hp.1.trans_le hx.1
    have hx1 : x < 1 := hx.2.trans_lt (by norm_num)
    have hqx := hq_mem x hx
    have hqx0 : 0 < q x := hx0.trans_le hqx.1
    have hqx1 : q x < 1 := hqx.2.trans_lt (by norm_num)
    have hqder : HasDerivAt q a x := by
      dsimp [q]
      convert (hasDerivAt_const x tau).add
        ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
    have hLq : HasDerivAt (fun y => L (q y))
        (-a / (q x * (1 - q x))) x := by
      convert (hLder (q x) hqx0 hqx1).comp x hqder using 1
      field_simp
    dsimp [F]
    convert ((hasDerivAt_const x a).mul (hLder x hx0 hx1)).sub hLq using 1 <;> ring
  have hFder_nonpos (x : ℝ) (hx : x ∈ Icc p (1 / 2)) :
      a * (-1 / (x * (1 - x))) -
          (-a / (q x * (1 - q x))) ≤ 0 := by
    have hqx := hq_mem x hx
    have hx0 : 0 < x := hp.1.trans_le hx.1
    have hx1 : x < 1 := hx.2.trans_lt (by norm_num)
    have hqx0 : 0 < q x := hx0.trans_le hqx.1
    have hqx1 : q x < 1 := hqx.2.trans_lt (by norm_num)
    have hxprod : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
    have hprod : x * (1 - x) ≤ q x * (1 - q x) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqx.1)
        (by linarith [hqx.2, hx.2] : 0 ≤ 1 - q x - x)]
    have hinv : 1 / (q x * (1 - q x)) ≤ 1 / (x * (1 - x)) :=
      one_div_le_one_div_of_le hxprod hprod
    have hmul := mul_le_mul_of_nonneg_left hinv ha.le
    rw [show a * (-1 / (x * (1 - x))) - (-a / (q x * (1 - q x))) =
        a * (1 / (q x * (1 - q x))) - a * (1 / (x * (1 - x))) by ring]
    exact sub_nonpos.mpr hmul
  have hFcont : ContinuousOn F (Icc p (1 / 2)) := by
    intro x hx
    exact (hFder x hx).continuousAt.continuousWithinAt
  have hFanti : AntitoneOn F (Icc p (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc p (1 / 2)) hFcont
    · intro x hx
      exact (hFder x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact hFder_nonpos x (interior_subset hx)
  have hhalf : (1 / 2 : ℝ) ∈ Icc p (1 / 2) := ⟨hp.2.le, le_rfl⟩
  have hpmem : p ∈ Icc p (1 / 2) := ⟨le_rfl, hp.2.le⟩
  have hFineq : F (1 / 2) ≤ F p := hFanti hpmem hhalf hp.2.le
  have hFhalf : F (1 / 2) = 0 := by
    have hqhalf : q (1 / 2) = 1 / 2 := by dsimp [q, a]; ring
    dsimp [F, L]
    rw [hqhalf]
    ring
  have hLineq : L (q p) ≤ a * L p := by
    rw [hFhalf] at hFineq
    dsimp [F] at hFineq
    linarith
  have hLp : 0 < L p := by
    dsimp [L]
    rw [sub_pos]
    have hpless : p < 1 - p := by nlinarith [hp.2]
    exact Real.log_lt_log hp.1 hpless
  rw [(mglCurve_hasDerivAt ht0 ht1 hu).deriv]
  change a * L (q p) / L p ≤ a ^ 2
  apply (div_le_iff₀ hLp).2
  have hmul := mul_le_mul_of_nonneg_left hLineq ha.le
  nlinarith

lemma hbInv_lipschitz_window {zeta u eps : ℝ} (hz0 : 0 < zeta) (hz1 : zeta ≤ 1/4)
    (hu : Hb zeta ≤ u) (hu2 : u ≤ Hb (1/2 - zeta)) (heps : 0 ≤ eps)
    (hmem : u + eps ≤ Hb (1/2 - zeta/2)) :
    hbInv (u + eps) - hbInv u ≤ eps / deriv Hb (1/2 - zeta/2) := by
  let r : ℝ := 1 / 2 - zeta / 2
  let p : ℝ := hbInv u
  let p' : ℝ := hbInv (u + eps)
  have hz_lt_one : zeta < 1 := hz1.trans_lt (by norm_num)
  have hHb_zeta_pos : 0 < Hb zeta := Real.binEntropy_pos hz0 hz_lt_one
  have hu0 : 0 < u := hHb_zeta_pos.trans_le hu
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hrhalf : r < 1 / 2 := by dsimp [r]; linarith
  have hHb_r_le : Hb r ≤ log 2 := Real.binEntropy_le_log_two
  have hu_mem : u ∈ Icc (0 : ℝ) (log 2) := by
    constructor
    · exact hu0.le
    · exact (le_add_of_nonneg_right heps).trans (hmem.trans hHb_r_le)
  have hue_mem : u + eps ∈ Icc (0 : ℝ) (log 2) :=
    ⟨by linarith, hmem.trans hHb_r_le⟩
  have hp_spec := hbInv_spec hu_mem
  have hp'_spec := hbInv_spec hue_mem
  have hu_lt : u < log 2 := by
    exact hu2.trans_lt (Real.binEntropy_lt_log_two.mpr (by linarith [hz0]))
  have hp0 : 0 < p := by
    dsimp [p]
    exact (hbInv_mem_Ioo ⟨hu0, hu_lt⟩).1
  have hpp' : p ≤ p' := by
    dsimp [p, p']
    exact hbInv_strictMonoOn.monotoneOn hu_mem hue_mem (le_add_of_nonneg_right heps)
  have hr_mem : r ∈ Icc (0 : ℝ) (1 / 2) := ⟨hr0.le, hrhalf.le⟩
  have hp'_le_r : p' ≤ r := by
    have hHb : Hb p' ≤ Hb r := by
      dsimp [p']
      rw [hp'_spec.2]
      exact hmem
    exact (Real.binEntropy_strictMonoOn.le_iff_le
      (by simpa [one_div] using hp'_spec.1)
      (by simpa [one_div] using hr_mem)).mp hHb
  have hp'_lt_one : p' < 1 := hp'_le_r.trans_lt (hrhalf.trans (by norm_num))
  have hderiv_r : deriv Hb r = log (1 - r) - log r := by
    unfold Hb
    exact Real.deriv_binEntropy r
  have hderiv_pos : 0 < deriv Hb r := by
    rw [hderiv_r, sub_pos]
    have hr_lt : r < 1 - r := by nlinarith [hrhalf]
    exact Real.log_lt_log hr0 hr_lt
  have hcont : ContinuousOn Hb (Icc p p') :=
    Real.binEntropy_continuous.continuousOn
  have hdiff : DifferentiableOn ℝ Hb (interior (Icc p p')) := by
    intro x hx
    have hxmem : x ∈ Icc p p' := interior_subset hx
    have hx0 : 0 < x := hp0.trans_le hxmem.1
    have hx1 : x < 1 := hxmem.2.trans_lt hp'_lt_one
    exact (Real.hasDerivAt_binEntropy (ne_of_gt hx0) (by linarith : x ≠ 1)).differentiableAt.differentiableWithinAt
  have hderiv_lower : ∀ x ∈ interior (Icc p p'), deriv Hb r ≤ deriv Hb x := by
    intro x hx
    have hxmem : x ∈ Icc p p' := interior_subset hx
    have hx0 : 0 < x := hp0.trans_le hxmem.1
    have hxr : x ≤ r := hxmem.2.trans hp'_le_r
    have hlog_one : log (1 - r) ≤ log (1 - x) := by
      apply Real.log_le_log
      · linarith [hrhalf]
      · linarith
    have hlog_x : log x ≤ log r := Real.log_le_log hx0 hxr
    rw [hderiv_r]
    unfold Hb
    rw [Real.deriv_binEntropy]
    linarith
  have hgrowth := (convex_Icc p p').mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hderiv_lower p (left_mem_Icc.mpr hpp') p' (right_mem_Icc.mpr hpp') hpp'
  have hentropy_diff : Hb p' - Hb p = eps := by
    dsimp [p, p']
    rw [hp'_spec.2, hp_spec.2]
    ring
  rw [hentropy_diff] at hgrowth
  change p' - p ≤ eps / deriv Hb r
  exact (le_div_iff₀ hderiv_pos).2 (by simpa [mul_comm] using hgrowth)

/-- Missing glue: `Var(τ + (1-2τ)p) = (1-2τ)²·Var(p)` -/
lemma var_linear_transform {ι : Type*} (s : Finset ι) (w p : ι → ℝ)
    (_hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1) (tau : ℝ) :
    let pbar := ∑ i ∈ s, w i * p i
    let b i := tau + (1 - 2 * tau) * p i
    let bbar := ∑ i ∈ s, w i * b i
    ∑ i ∈ s, w i * (b i - bbar)^2 = (1 - 2 * tau)^2 * ∑ i ∈ s, w i * (p i - pbar)^2 := by
  dsimp
  have hbbar :
      (∑ i ∈ s, w i * (tau + (1 - 2 * tau) * p i)) =
        tau + (1 - 2 * tau) * ∑ i ∈ s, w i * p i := by
    calc
      (∑ i ∈ s, w i * (tau + (1 - 2 * tau) * p i)) =
          ∑ i ∈ s, (w i * tau +
            (1 - 2 * tau) * (w i * p i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ =
          (∑ i ∈ s, w i) * tau +
            (1 - 2 * tau) * ∑ i ∈ s, w i * p i := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, ← Finset.mul_sum]
      _ = tau + (1 - 2 * tau) * ∑ i ∈ s, w i * p i := by
        rw [hwsum, one_mul]
  rw [hbbar]
  calc
    (∑ i ∈ s, w i *
        (tau + (1 - 2 * tau) * p i -
          (tau + (1 - 2 * tau) * ∑ j ∈ s, w j * p j)) ^ 2) =
        ∑ i ∈ s, (1 - 2 * tau) ^ 2 *
          (w i * (p i - ∑ j ∈ s, w j * p j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (1 - 2 * tau) ^ 2 *
        ∑ i ∈ s, w i * (p i - ∑ j ∈ s, w j * p j) ^ 2 := by
      rw [Finset.mul_sum]

/-- Weighted variance as half the expected squared difference of two
independent samples. -/
lemma weighted_variance_eq_pairwise {ι : Type*} (s : Finset ι) (w p : ι → ℝ)
    (hwsum : ∑ i ∈ s, w i = 1) :
    let pbar := ∑ i ∈ s, w i * p i
    ∑ i ∈ s, w i * (p i - pbar)^2 =
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * (p i - p j)^2 := by
  dsimp
  set m : ℝ := ∑ i ∈ s, w i * p i
  have hm : ∑ i ∈ s, w i * p i = m := rfl
  have hleft :
      (∑ i ∈ s, w i * (p i - m) ^ 2) =
        (∑ i ∈ s, w i * p i ^ 2) - m ^ 2 := by
    calc
      (∑ i ∈ s, w i * (p i - m) ^ 2) =
          ∑ i ∈ s, (w i * p i ^ 2 -
            2 * m * (w i * p i) + m ^ 2 * w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ =
          (∑ i ∈ s, w i * p i ^ 2) -
            2 * m * (∑ i ∈ s, w i * p i) +
              m ^ 2 * (∑ i ∈ s, w i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (∑ i ∈ s, w i * p i ^ 2) - m ^ 2 := by
        rw [hm, hwsum]
        ring
  rw [hleft]
  rw [show (∑ i ∈ s, ∑ j ∈ s, w i * w j * (p i - p j) ^ 2) =
      2 * ((∑ i ∈ s, w i * p i ^ 2) - m ^ 2) by
    calc
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * (p i - p j) ^ 2) =
          ∑ i ∈ s, (w i * p i ^ 2 * (∑ j ∈ s, w j) -
            2 * (w i * p i) * (∑ j ∈ s, w j * p j) +
              w i * (∑ j ∈ s, w j * p j ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (∑ j ∈ s, w i * w j * (p i - p j) ^ 2) =
              ∑ j ∈ s, (w i * p i ^ 2 * w j -
                2 * (w i * p i) * (w j * p j) +
                  w i * (w j * p j ^ 2)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = w i * p i ^ 2 * (∑ j ∈ s, w j) -
              2 * (w i * p i) * (∑ j ∈ s, w j * p j) +
                w i * (∑ j ∈ s, w j * p j ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ =
          (∑ i ∈ s, w i * p i ^ 2) * (∑ j ∈ s, w j) -
            (∑ i ∈ s, 2 * (w i * p i)) * (∑ j ∈ s, w j * p j) +
              (∑ i ∈ s, w i) * (∑ j ∈ s, w j * p j ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      _ =
          (∑ i ∈ s, w i * p i ^ 2) * (∑ j ∈ s, w j) -
            2 * (∑ i ∈ s, w i * p i) * (∑ j ∈ s, w j * p j) +
              (∑ i ∈ s, w i) * (∑ j ∈ s, w j * p j ^ 2) := by
        have hfactor : (∑ i ∈ s, 2 * (w i * p i)) =
            2 * ∑ i ∈ s, w i * p i := by
          rw [Finset.mul_sum]
        rw [hfactor]
      _ = 2 * ((∑ i ∈ s, w i * p i ^ 2) - m ^ 2) := by
        rw [hm, hwsum]
        ring]
  ring

/-- Two-cluster variance lower bound. -/
lemma two_cluster_variance {ι : Type*} (s : Finset ι) (w p : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1) (zeta p_minus p_plus : ℝ)
    (hzeta : 0 < zeta) (hsep : zeta ≤ p_plus - p_minus)
    (s1 s0 : Finset ι) (hs1 : s1 ⊆ s) (hs0 : s0 ⊆ s) (hdisj : Disjoint s1 s0)
    (hp1 : ∀ i ∈ s1, p_plus ≤ p i) (hp0 : ∀ i ∈ s0, p i ≤ p_minus) :
    let pbar := ∑ i ∈ s, w i * p i
    let m1 := ∑ i ∈ s1, w i
    let m0 := ∑ i ∈ s0, w i
    zeta^2 * m1 * m0 ≤ ∑ i ∈ s, w i * (p i - pbar)^2 := by
  classical
  dsimp
  let cross : Finset (ι × ι) := (s1 ×ˢ s0) ∪ (s0 ×ˢ s1)
  have hprod_disj : Disjoint (s1 ×ˢ s0) (s0 ×ˢ s1) :=
    Finset.disjoint_product.mpr (Or.inl hdisj)
  have hcross_subset : cross ⊆ s ×ˢ s := by
    intro ij hij
    change ij ∈ (s1 ×ˢ s0) ∪ (s0 ×ˢ s1) at hij
    rw [Finset.mem_union] at hij
    rcases hij with hij | hij
    · exact Finset.product_subset_product hs1 hs0 hij
    · exact Finset.product_subset_product hs0 hs1 hij
  have hsum_prod : ∀ a b : Finset ι,
      (∑ ij ∈ a ×ˢ b, zeta ^ 2 * (w ij.1 * w ij.2)) =
        zeta ^ 2 * (∑ i ∈ a, w i) * (∑ j ∈ b, w j) := by
    intro a b
    rw [Finset.sum_product]
    calc
      (∑ i ∈ a, ∑ j ∈ b, zeta ^ 2 * (w i * w j)) =
          ∑ i ∈ a, (zeta ^ 2 * w i) * (∑ j ∈ b, w j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = zeta ^ 2 * (∑ i ∈ a, w i) * (∑ j ∈ b, w j) := by
        rw [← Finset.sum_mul]
        have hfactor : (∑ i ∈ a, zeta ^ 2 * w i) =
            zeta ^ 2 * ∑ i ∈ a, w i := by
          rw [Finset.mul_sum]
        rw [hfactor]
  have hcross_base :
      (∑ ij ∈ cross, zeta ^ 2 * (w ij.1 * w ij.2)) =
        2 * (zeta ^ 2 * (∑ i ∈ s1, w i) * (∑ j ∈ s0, w j)) := by
    dsimp [cross]
    rw [Finset.sum_union hprod_disj, hsum_prod, hsum_prod]
    ring
  have hcross_bound :
      (∑ ij ∈ cross, zeta ^ 2 * (w ij.1 * w ij.2)) ≤
        ∑ ij ∈ cross, w ij.1 * w ij.2 * (p ij.1 - p ij.2) ^ 2 := by
    apply Finset.sum_le_sum
    intro ij hij
    have hij_s := hcross_subset hij
    rw [Finset.mem_product] at hij_s
    have hweight : 0 ≤ w ij.1 * w ij.2 :=
      mul_nonneg (hw _ hij_s.1) (hw _ hij_s.2)
    have hsq : zeta ^ 2 ≤ (p ij.1 - p ij.2) ^ 2 := by
      change ij ∈ (s1 ×ˢ s0) ∪ (s0 ×ˢ s1) at hij
      rw [Finset.mem_union] at hij
      rcases hij with hij | hij
      · rw [Finset.mem_product] at hij
        have hgap : zeta ≤ p ij.1 - p ij.2 := by
          nlinarith [hp1 ij.1 hij.1, hp0 ij.2 hij.2]
        nlinarith
      · rw [Finset.mem_product] at hij
        have hgap : zeta ≤ p ij.2 - p ij.1 := by
          nlinarith [hp1 ij.2 hij.2, hp0 ij.1 hij.1]
        nlinarith
    calc
      zeta ^ 2 * (w ij.1 * w ij.2) =
          (w ij.1 * w ij.2) * zeta ^ 2 := by ring
      _ ≤ (w ij.1 * w ij.2) * (p ij.1 - p ij.2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hweight
  have hcross_full :
      (∑ ij ∈ cross, w ij.1 * w ij.2 * (p ij.1 - p ij.2) ^ 2) ≤
        ∑ ij ∈ s ×ˢ s, w ij.1 * w ij.2 * (p ij.1 - p ij.2) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hcross_subset
    intro ij hij hnot
    rw [Finset.mem_product] at hij
    exact mul_nonneg (mul_nonneg (hw _ hij.1) (hw _ hij.2)) (sq_nonneg _)
  have hpair :
      2 * (zeta ^ 2 * (∑ i ∈ s1, w i) * (∑ j ∈ s0, w j)) ≤
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * (p i - p j) ^ 2 := by
    have hprod_eq :
        (∑ ij ∈ s ×ˢ s, w ij.1 * w ij.2 * (p ij.1 - p ij.2) ^ 2) =
          ∑ i ∈ s, ∑ j ∈ s, w i * w j * (p i - p j) ^ 2 := by
      rw [Finset.sum_product]
    rw [← hcross_base, ← hprod_eq]
    exact hcross_bound.trans hcross_full
  rw [weighted_variance_eq_pairwise s w p hwsum]
  linarith

lemma normalized_two_cluster_direction_bound
    {ι : Type*} (s s1 s0 : Finset ι) (w p : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hwsum : ∑ i ∈ s, w i = 1)
    {zeta pMinus pPlus beta pi : ℝ}
    (hzeta : 0 < zeta)
    (hsep : zeta ≤ pPlus - pMinus)
    (hs1 : s1 ⊆ s) (hs0 : s0 ⊆ s) (hdisj : Disjoint s1 s0)
    (hp1 : ∀ i ∈ s1, pPlus ≤ p i)
    (hp0 : ∀ i ∈ s0, p i ≤ pMinus)
    (hbeta : 0 ≤ beta)
    (hmass : (∑ i ∈ s1, w i) + (∑ i ∈ s0, w i) + beta = 1)
    (hone : pi ≤ (∑ i ∈ s1, w i) + beta)
    (hzero : 1 - pi ≤ (∑ i ∈ s0, w i) + beta) :
    min pi (1 - pi) ≤
      (2 / zeta^2) *
        (∑ i ∈ s, w i *
          (p i - ∑ j ∈ s, w j * p j)^2) +
      2 * beta := by
  -- Two-cluster variance lower bound: `ζ²·m₁·m₀ ≤ Var`.
  have hvar : zeta ^ 2 * (∑ i ∈ s1, w i) * (∑ i ∈ s0, w i) ≤
      ∑ i ∈ s, w i * (p i - ∑ j ∈ s, w j * p j) ^ 2 :=
    two_cluster_variance s w p hw hwsum zeta pMinus pPlus hzeta hsep s1 s0
      hs1 hs0 hdisj hp1 hp0
  have hm1_nonneg : 0 ≤ ∑ i ∈ s1, w i :=
    Finset.sum_nonneg (fun i hi => hw i (hs1 hi))
  have hm0_nonneg : 0 ≤ ∑ i ∈ s0, w i :=
    Finset.sum_nonneg (fun i hi => hw i (hs0 hi))
  set m1 := ∑ i ∈ s1, w i with hm1
  set m0 := ∑ i ∈ s0, w i with hm0
  -- Direction-minority arithmetic: `min πₜ (1-πₜ) ≤ 2·m₁·m₀ + 2·β`.
  have hmin : min pi (1 - pi) ≤ 2 * m1 * m0 + 2 * beta := by
    by_cases hm0half : 1 / 2 ≤ m0
    · have h := min_le_left pi (1 - pi)
      have hm : m1 ≤ 2 * m1 * m0 := by nlinarith
      linarith
    · by_cases hm1half : 1 / 2 ≤ m1
      · have h := min_le_right pi (1 - pi)
        have hm : m0 ≤ 2 * m1 * m0 := by nlinarith
        linarith
      · have hm0le : m0 ≤ 1 / 2 := le_of_not_ge hm0half
        have hm1le : m1 ≤ 1 / 2 := le_of_not_ge hm1half
        have hmin' : min pi (1 - pi) ≤ 1 / 2 := by
          rcases le_total pi (1 / 2) with hpi | hpi
          · exact (min_le_left _ _).trans hpi
          · exact (min_le_right _ _).trans (by linarith)
        have hprod : 0 ≤ (1 / 2 - m1) * (1 / 2 - m0) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [hprod]
  -- Convert the variance bound into a bound on `2·m₁·m₀`.
  have hzsq : 0 < zeta ^ 2 := by positivity
  have hkey : 2 * m1 * m0 ≤
      (2 / zeta ^ 2) * (∑ i ∈ s, w i * (p i - ∑ j ∈ s, w j * p j) ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hzsq]
    nlinarith [hvar]
  linarith [hmin, hkey]

/-
Jensen gap for binary entropy dominates twice the variance (2-strong
concavity of `Hb` on `[0,1]`, since `Hb'' = -1/(p(1-p)) ≤ -4`).
-/
theorem Hb_jensen_gap_ge_two_variance
    {ι : Type*} (s : Finset ι) (w b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hwsum : ∑ i ∈ s, w i = 1)
    (hb : ∀ i ∈ s, b i ∈ Set.Icc (0 : ℝ) 1) :
    let bbar := ∑ i ∈ s, w i * b i
    2 * ∑ i ∈ s, w i * (b i - bbar)^2 ≤
      Hb bbar - ∑ i ∈ s, w i * Hb (b i) := by
  -- Prove that the function $g(p) = Hb(p) + 2p^2$ is concave on $[0,1]$.
  have h_concave : ConcaveOn ℝ (Set.Icc 0 1) (fun p => Hb p + 2 * p^2) := by
    apply_rules [ concaveOn_of_deriv2_nonpos ] <;> norm_num [ Hb ];
    · exact convex_Icc _ _;
    · exact ContinuousOn.add ( Real.binEntropy_continuous.continuousOn ) ( continuousOn_const.mul ( continuousOn_pow 2 ) );
    · refine' DifferentiableOn.add _ _;
      · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact Real.differentiableAt_binEntropy ( by linarith [ hx.1, hx.2 ] ) ( by linarith [ hx.1, hx.2 ] ) );
      · exact Differentiable.differentiableOn ( by norm_num );
    · -- The derivative of $Hb(p) + 2p^2$ is $\log(1-p) - \log(p) + 4p$.
      have h_deriv : ∀ p ∈ Set.Ioo (0 : ℝ) 1, deriv (fun p => Real.binEntropy p + 2 * p^2) p = Real.log (1 - p) - Real.log p + 4 * p := by
        intro p hp; convert HasDerivAt.deriv ( HasDerivAt.add ( Real.hasDerivAt_binEntropy hp.1.ne' hp.2.ne ) ( HasDerivAt.const_mul 2 ( hasDerivAt_pow 2 p ) ) ) using 1 ; ring;
      exact DifferentiableOn.congr ( fun p hp => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( DifferentiableAt.sub ( DifferentiableAt.log ( differentiableAt_id.const_sub _ ) ( by linarith [ hp.1, hp.2 ] ) ) ( DifferentiableAt.log ( differentiableAt_id ) ( by linarith [ hp.1, hp.2 ] ) ) ) ( differentiableAt_id.const_mul _ ) ) ) h_deriv;
    · -- Let's calculate the first derivative of $g(p) = H(p) + 2p^2$.
      have h_deriv : ∀ p ∈ Set.Ioo (0 : ℝ) 1, deriv (fun p => Real.binEntropy p + 2 * p^2) p = Real.log (1 - p) - Real.log p + 4 * p := by
        intro p hp; convert HasDerivAt.deriv ( HasDerivAt.add ( Real.hasDerivAt_binEntropy hp.1.ne' hp.2.ne ) ( HasDerivAt.const_mul 2 ( hasDerivAt_pow 2 p ) ) ) using 1 ; ring;
      -- Let's calculate the second derivative of $g(p) = H(p) + 2p^2$.
      have h_deriv2 : ∀ p ∈ Set.Ioo (0 : ℝ) 1, deriv (deriv (fun p => Real.binEntropy p + 2 * p^2)) p = -1 / (1 - p) - 1 / p + 4 := by
        intro p hp; refine' HasDerivAt.deriv _ ; convert HasDerivAt.congr_of_eventuallyEq _ ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hp.1 hp.2 ) fun x hx => h_deriv x hx ) using 1 ; ring;
        convert HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_id p ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.sub ( HasDerivAt.log ( hasDerivAt_id p |> HasDerivAt.const_sub 1 ) ( by linarith [ hp.1, hp.2 ] : ( 1 - p ) ≠ 0 ) ) ( HasDerivAt.log ( hasDerivAt_id p ) ( by linarith [ hp.1, hp.2 ] : p ≠ 0 ) ) ) using 1 ; ring!;
      intro p hp hp'; rw [ h_deriv2 p ⟨ hp, hp' ⟩ ] ; ring_nf; nlinarith [ inv_pos.2 hp, inv_pos.2 ( sub_pos.2 hp' ), mul_inv_cancel₀ ( ne_of_gt hp ), mul_inv_cancel₀ ( ne_of_gt ( sub_pos.2 hp' ) ), sq_nonneg ( p - 1 / 2 ) ] ;
  -- Apply Jensen's inequality to the concave function $g(p) = Hb(p) + 2p^2$.
  have h_jensen : ∑ i ∈ s, w i * (Hb (b i) + 2 * (b i)^2) ≤ Hb (∑ i ∈ s, w i * b i) + 2 * (∑ i ∈ s, w i * b i)^2 := by
    convert h_concave.le_map_sum _ _ _ <;> aesop;
  simp_all +decide [ mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_sq, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
  simp_all +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.sum_comm ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, sq ];
  simp_all +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] ; linarith

end AverageHarperStability
