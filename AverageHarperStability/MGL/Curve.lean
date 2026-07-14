import AverageHarperStability.Probability.Finite

open Real Set

namespace AverageHarperStability

/-! Analytic Wyner-Ziv/Mrs-Gerber input, proved in-project rather than assumed. -/

lemma hbInv_spec {u : ℝ} (hu : u ∈ Icc 0 (log 2)) :
    hbInv u ∈ Icc (0 : ℝ) (1 / 2) ∧ Hb (hbInv u) = u := by
  have hu' : u ∈ Icc (Hb 0) (Hb (1 / 2)) := by
    simpa [Hb] using hu
  obtain ⟨p, hp, hpu⟩ :=
    (intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      Real.binEntropy_continuous.continuousOn hu')
  have hp' : p ∈ Icc (0 : ℝ) (1 / 2) := by simpa using hp
  have hHb : Hb p = u := by simpa [Hb] using hpu
  have hleast : IsLeast {q : ℝ | q ∈ Icc (0 : ℝ) (1 / 2) ∧ u ≤ Hb q} p := by
    constructor
    · exact ⟨hp', hHb.ge⟩
    · intro q hq
      by_contra hn
      have hqp : q < p := lt_of_not_ge hn
      have hlt : Hb q < Hb p := by
        apply Real.binEntropy_strictMonoOn
        · simpa [one_div] using hq.1
        · simpa [one_div] using hp'
        · exact hqp
      rw [hHb] at hlt
      exact (not_lt_of_ge hq.2) hlt
  have hinv : hbInv u = p := by
    unfold hbInv
    exact hleast.csInf_eq
  rw [hinv]
  exact ⟨hp', hHb⟩

lemma hbInv_strictMonoOn : StrictMonoOn hbInv (Icc 0 (log 2)) := by
  intro u hu v hv huv
  have hu_spec := hbInv_spec hu
  have hv_spec := hbInv_spec hv
  by_contra hn
  have hle : hbInv v ≤ hbInv u := le_of_not_gt hn
  have hHb_le : Hb (hbInv v) ≤ Hb (hbInv u) := by
    apply Real.binEntropy_strictMonoOn.monotoneOn
    · simpa [one_div] using hv_spec.1
    · simpa [one_div] using hu_spec.1
    · exact hle
  rw [hu_spec.2, hv_spec.2] at hHb_le
  exact (not_le_of_gt huv) hHb_le

lemma hbInv_mapsTo : MapsTo hbInv (Icc 0 (log 2)) (Icc 0 (1/2)) := by
  intro u hu
  exact (hbInv_spec hu).1

lemma hbInv_continuousOn : ContinuousOn hbInv (Icc 0 (log 2)) := by
  let f : Icc (0 : ℝ) (1 / 2) → Icc (0 : ℝ) (log 2) := fun p =>
    ⟨Hb p, ⟨Real.binEntropy_nonneg p.2.1 (p.2.2.trans (by norm_num)),
      Real.binEntropy_le_log_two⟩⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Real.binEntropy_strictMonoOn.injOn
    · simpa [one_div] using p.2
    · simpa [one_div] using q.2
    · exact congrArg Subtype.val hpq
  have hf_surj : Function.Surjective f := by
    intro u
    refine ⟨⟨hbInv u, hbInv_mapsTo u.2⟩, ?_⟩
    apply Subtype.ext
    exact (hbInv_spec u.2).2
  let e : Icc (0 : ℝ) (1 / 2) ≃ Icc (0 : ℝ) (log 2) :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hf_cont : Continuous f := by
    apply Continuous.subtype_mk
    exact Real.binEntropy_continuous.comp continuous_subtype_val
  have he_cont : Continuous e := by simpa [e] using hf_cont
  let h : Icc (0 : ℝ) (1 / 2) ≃ₜ Icc (0 : ℝ) (log 2) :=
    e.toHomeomorphOfContinuousClosed he_cont he_cont.isClosedMap
  rw [continuousOn_iff_continuous_restrict]
  have hval : Continuous
      (fun u : Icc (0 : ℝ) (log 2) => ((h.symm u : Icc (0 : ℝ) (1 / 2)) : ℝ)) :=
    continuous_subtype_val.comp h.symm.continuous
  apply hval.congr
  intro u
  have heq := e.apply_symm_apply u
  have hHb : Hb (e.symm u : ℝ) = u := congrArg Subtype.val heq
  have hinv := hbInv_spec u.2
  change (e.symm u : ℝ) = hbInv u
  apply Real.binEntropy_strictMonoOn.injOn
  · simpa [one_div] using (e.symm u).2
  · simpa [one_div] using hinv.1
  · exact hHb.trans hinv.2.symm

lemma mgl_core_inequality {p q : ℝ} (hp0 : 0 < p) (hq_lt : p < q) (hq12 : q < 1 / 2) :
    let k := fun x => (x * (1 - x)) / (1 - 2 * x) * log ((1 - x) / x)
    k p < k q := by
  dsimp only
  let k : ℝ → ℝ := fun x => (x * (1 - x)) / (1 - 2 * x) * log ((1 - x) / x)
  have hkderiv : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), 0 < deriv k x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hx1 : 1 - x ≠ 0 := by
      apply ne_of_gt
      exact sub_pos.mpr (hx.2.trans (by norm_num))
    have hxdenpos : 0 < 1 - 2 * x := by
      have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hx.2
      linarith
    have hxden : 1 - 2 * x ≠ 0 := ne_of_gt hxdenpos
    have hone : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> norm_num
    have hquot : HasDerivAt (fun y : ℝ => (1 - y) / y) (-1 / x ^ 2) x := by
      have hquot0 : HasDerivAt (fun y : ℝ => (1 - y) / y)
          ((-1 * x - (1 - x) * 1) / x ^ 2) x := by
        simpa only [id_eq] using hone.div (hasDerivAt_id x) hx0
      convert hquot0 using 1 <;> field_simp <;> ring
    have hlog : HasDerivAt (fun y : ℝ => log ((1 - y) / y))
        (-1 / (x * (1 - x))) x := by
      convert hquot.log (div_ne_zero hx1 hx0) using 1 <;> field_simp <;> ring
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
    have hk : HasDerivAt k
        (((1 - 2 * x + 2 * x ^ 2) / (1 - 2 * x) ^ 2) * log ((1 - x) / x) -
          1 / (1 - 2 * x)) x := by
      dsimp [k]
      convert hrat.mul hlog using 1 <;> field_simp <;> ring
    rw [hk.deriv]
    have hz : 0 < (1 - x) / x - 1 := by
      rw [sub_pos, one_lt_div₀ hx.1]
      have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hx.2
      linarith
    have hloglower := Real.lt_log_one_add_of_pos hz
    rw [show 1 + ((1 - x) / x - 1) = (1 - x) / x by ring] at hloglower
    have hmain : (1 - 2 * x) / (1 - 2 * x + 2 * x ^ 2) < log ((1 - x) / x) := by
      have hlower :
          2 * ((1 - x) / x - 1) / (((1 - x) / x - 1) + 2) = 2 * (1 - 2 * x) := by
        field_simp
        ring
      have hnum : 0 < 1 - 2 * x + 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
      calc
        (1 - 2 * x) / (1 - 2 * x + 2 * x ^ 2)
            < 2 * ((1 - x) / x - 1) / (((1 - x) / x - 1) + 2) := by
              rw [hlower, div_lt_iff₀ hnum]
              nlinarith [mul_pos hxdenpos hxdenpos]
        _ < log ((1 - x) / x) := hloglower
    have hnum : 0 < 1 - 2 * x + 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have hmul := mul_lt_mul_of_pos_left hmain
      (div_pos hnum (sq_pos_of_pos hxdenpos))
    rw [sub_pos]
    convert hmul using 1 <;> field_simp <;> ring
  have hkcont : ContinuousOn k (Ioo (0 : ℝ) (1 / 2)) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hx1 : 1 - x ≠ 0 := by
      apply ne_of_gt
      exact sub_pos.mpr (hx.2.trans (by norm_num))
    have hxdenpos : 0 < 1 - 2 * x := by
      have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hx.2
      linarith
    have hxden : 1 - 2 * x ≠ 0 := ne_of_gt hxdenpos
    dsimp [k]
    apply ContinuousAt.mul
    · exact ((continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).div
        (continuousAt_const.sub ((continuousAt_const.mul continuousAt_id))) hxden)
    · have hone : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> norm_num
      exact (hone.div (hasDerivAt_id x) hx0).log (div_ne_zero hx1 hx0) |>.continuousAt
  have hmono : StrictMonoOn k (Ioo (0 : ℝ) (1 / 2)) :=
    strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) (1 / 2)) hkcont (by simpa using hkderiv)
  exact hmono ⟨hp0, hq_lt.trans hq12⟩ ⟨hp0.trans hq_lt, hq12⟩ hq_lt

lemma hbInv_hasDerivAt {u : ℝ} (hu : u ∈ Ioo 0 (log 2)) :
    HasDerivAt hbInv (log (1 - hbInv u) - log (hbInv u))⁻¹ u := by
  have hucc : u ∈ Icc (0 : ℝ) (log 2) := ⟨hu.1.le, hu.2.le⟩
  have hpcc := (hbInv_spec hucc).1
  have hp0 : 0 < hbInv u := by
    apply lt_of_le_of_ne hpcc.1
    intro hp
    have hzero : Hb (hbInv u) = 0 := by rw [← hp]; simp [Hb]
    rw [(hbInv_spec hucc).2] at hzero
    exact (ne_of_gt hu.1) hzero
  have hp12 : hbInv u < 1 / 2 := by
    apply lt_of_le_of_ne hpcc.2
    intro hp
    have htop : Hb (hbInv u) = log 2 := by rw [hp]; simp [Hb]
    rw [(hbInv_spec hucc).2] at htop
    exact (ne_of_lt hu.2) htop
  have hcont : ContinuousAt hbInv u :=
    (hbInv_continuousOn u hucc).continuousAt (Icc_mem_nhds hu.1 hu.2)
  have hder : HasDerivAt Hb (log (1 - hbInv u) - log (hbInv u)) (hbInv u) := by
    simpa [Hb] using Real.hasDerivAt_binEntropy (ne_of_gt hp0) (by linarith : hbInv u ≠ 1)
  have hderpos : 0 < log (1 - hbInv u) - log (hbInv u) := by
    rw [sub_pos]
    exact Real.log_lt_log hp0 (by linarith)
  apply hder.of_local_left_inverse hcont (ne_of_gt hderpos)
  filter_upwards [Icc_mem_nhds hu.1 hu.2] with y hy
  exact (hbInv_spec hy).2

lemma mglSlope_strictMonoOn {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2) :
    StrictMonoOn
      (fun p : ℝ => (1 - 2 * tau) *
        (log (1 - (tau + (1 - 2 * tau) * p)) - log (tau + (1 - 2 * tau) * p)) /
        (log (1 - p) - log p))
      (Ioo 0 (1 / 2)) := by
  let a := 1 - 2 * tau
  let Q : ℝ → ℝ := fun p => tau + a * p
  let L : ℝ → ℝ := fun p => log (1 - p) - log p
  let d : ℝ → ℝ := fun p => a * L (Q p) / L p
  have ha : 0 < a := by dsimp [a]; linarith
  have hQ {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) (1 / 2)) : Q p ∈ Ioo p (1 / 2) := by
    have hpden : 0 < 1 - 2 * p := by
      have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hp.2
      linarith
    have hgap : 0 < tau * (1 - 2 * p) := mul_pos ht0 hpden
    have hhalf : 0 < a * (1 / 2 - p) := mul_pos ha (sub_pos.mpr hp.2)
    dsimp [Q]
    constructor
    · dsimp [a] at hgap ⊢
      nlinarith
    · dsimp [a] at hhalf ⊢
      nlinarith
  have hLder (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
      HasDerivAt L (-1 / (p * (1 - p))) p := by
    dsimp [L]
    have h1 := (Real.hasDerivAt_log (by linarith : 1 - p ≠ 0)).comp p
      ((hasDerivAt_const p 1).sub (hasDerivAt_id p))
    have h2 := Real.hasDerivAt_log (ne_of_gt hp0)
    convert h1.sub h2 using 1 <;>
      field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp1)] <;> ring
  have hLpos (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) (1 / 2)) : 0 < L p := by
    dsimp [L]
    rw [sub_pos]
    have hpden : 0 < 1 - 2 * p := by
      have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hp.2
      linarith
    exact Real.log_lt_log hp.1 (by linarith)
  have hdderiv : ∀ p ∈ Ioo (0 : ℝ) (1 / 2), 0 < deriv d p := by
    intro p hp
    have hqp := hQ hp
    have hp1 : p < 1 := hp.2.trans (by norm_num)
    have hq1 : Q p < 1 := hqp.2.trans (by norm_num)
    have hQder : HasDerivAt Q a p := by
      dsimp [Q]
      convert (hasDerivAt_const p tau).add ((hasDerivAt_const p a).mul (hasDerivAt_id p))
        using 1 <;> simp only [id_eq] <;> ring
    have hLQ : HasDerivAt (fun x => L (Q x))
        (-a / (Q p * (1 - Q p))) p := by
      convert (hLder (Q p) (hp.1.trans hqp.1) hq1).comp p hQder using 1 <;>
        field_simp <;> ring
    have hd : HasDerivAt d
        (a * ((-a / (Q p * (1 - Q p))) * L p - L (Q p) * (-1 / (p * (1 - p)))) /
          (L p) ^ 2) p := by
      dsimp [d]
      have hn : HasDerivAt (fun x => a * L (Q x))
          (a * (-a / (Q p * (1 - Q p)))) p := by
        convert (hasDerivAt_const p a).mul hLQ using 1 <;> ring
      convert hn.div (hLder p hp.1 hp1) (ne_of_gt (hLpos p hp)) using 1 <;> ring
    rw [hd.deriv]
    have hk := mgl_core_inequality hp.1 hqp.1 hqp.2
    dsimp only at hk
    have hp0ne : p ≠ 0 := ne_of_gt hp.1
    have hp1ne : 1 - p ≠ 0 := by linarith
    have hq0ne : Q p ≠ 0 := ne_of_gt (hp.1.trans hqp.1)
    have hq1ne : 1 - Q p ≠ 0 := by linarith
    rw [Real.log_div hp1ne hp0ne, Real.log_div hq1ne hq0ne] at hk
    have hrel : a * (p * (1 - p)) * L p < (Q p * (1 - Q p)) * L (Q p) := by
      have hdenp : 0 < 1 - 2 * p := by
        have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hp.2
        linarith
      have hdenq : 0 < 1 - 2 * Q p := by
        have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hqp.2
        linarith
      have hden_eq : 1 - 2 * Q p = a * (1 - 2 * p) := by
        dsimp [Q, a]
        ring
      rw [hden_eq, div_mul_eq_mul_div, div_mul_eq_mul_div] at hk
      have hk' := (div_lt_div_iff₀ hdenp (mul_pos ha hdenp)).mp hk
      have hk'' : (a * (p * (1 - p)) * L p) * (1 - 2 * p) <
          ((Q p * (1 - Q p)) * L (Q p)) * (1 - 2 * p) := by
        convert hk' using 1 <;> ring
      nlinarith
    have hpprod : 0 < p * (1 - p) := mul_pos hp.1 (by linarith)
    have hqprod : 0 < Q p * (1 - Q p) := mul_pos (hp.1.trans hqp.1) (by linarith)
    have hdiff : a * L p / (Q p * (1 - Q p)) < L (Q p) / (p * (1 - p)) := by
      rw [div_lt_div_iff₀ hqprod hpprod]
      nlinarith
    have hbracket : 0 <
        (-a / (Q p * (1 - Q p))) * L p - L (Q p) * (-1 / (p * (1 - p))) := by
      rw [show (-a / (Q p * (1 - Q p))) * L p - L (Q p) * (-1 / (p * (1 - p))) =
        L (Q p) / (p * (1 - p)) - a * L p / (Q p * (1 - Q p)) by ring]
      exact sub_pos.mpr hdiff
    exact div_pos (mul_pos ha hbracket) (sq_pos_of_pos (hLpos p hp))
  have hdcont : ContinuousOn d (Ioo (0 : ℝ) (1 / 2)) := by
    intro p hp
    have hqp := hQ hp
    have hp1 : p < 1 := hp.2.trans (by norm_num)
    have hq1 : Q p < 1 := hqp.2.trans (by norm_num)
    have hQdiff : DifferentiableAt ℝ Q p := by
      dsimp [Q]
      fun_prop
    have hLQdiff : DifferentiableAt ℝ (fun x => L (Q x)) p :=
      ((hLder (Q p) (hp.1.trans hqp.1) hq1).differentiableAt.comp p hQdiff)
    exact (((differentiableAt_const a).mul hLQdiff).div (hLder p hp.1 hp1).differentiableAt
      (ne_of_gt (hLpos p hp))).continuousAt.continuousWithinAt
  have := strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) (1 / 2)) hdcont (by simpa using hdderiv)
  simpa [d, L, Q, a] using this

lemma hbInv_mem_Ioo {u : ℝ} (hu : u ∈ Ioo 0 (log 2)) : hbInv u ∈ Ioo (0 : ℝ) (1 / 2) := by
  have hucc : u ∈ Icc (0 : ℝ) (log 2) := ⟨hu.1.le, hu.2.le⟩
  have hpcc := (hbInv_spec hucc).1
  constructor
  · apply lt_of_le_of_ne hpcc.1
    intro hp
    have hzero : Hb (hbInv u) = 0 := by rw [← hp]; simp [Hb]
    rw [(hbInv_spec hucc).2] at hzero
    exact (ne_of_gt hu.1) hzero
  · apply lt_of_le_of_ne hpcc.2
    intro hp
    have htop : Hb (hbInv u) = log 2 := by rw [hp]; simp [Hb]
    rw [(hbInv_spec hucc).2] at htop
    exact (ne_of_lt hu.2) htop

lemma mglCurve_hasDerivAt {tau u : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    (hu : u ∈ Ioo 0 (log 2)) :
    HasDerivAt (mglCurve tau)
      ((1 - 2 * tau) *
        (log (1 - (tau + (1 - 2 * tau) * hbInv u)) -
          log (tau + (1 - 2 * tau) * hbInv u)) /
        (log (1 - hbInv u) - log (hbInv u))) u := by
  let a := 1 - 2 * tau
  let p := hbInv u
  let q := tau + a * p
  have ha : 0 < a := by dsimp [a]; linarith
  have hp := hbInv_mem_Ioo hu
  have hpden : 0 < 1 - 2 * p := by
    have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hp.2
    linarith
  have hgap : 0 < tau * (1 - 2 * p) := mul_pos ht0 hpden
  have hhalf : 0 < a * (1 / 2 - p) := mul_pos ha (sub_pos.mpr hp.2)
  have hq : q ∈ Ioo p (1 / 2) := by
    dsimp [q, a]
    constructor <;> nlinarith
  have hLp : 0 < log (1 - p) - log p := by
    rw [sub_pos]
    exact Real.log_lt_log hp.1 (by linarith)
  have hinv := hbInv_hasDerivAt hu
  have hinner : HasDerivAt (fun y => tau + a * hbInv y) (a * (log (1 - p) - log p)⁻¹) u := by
    change HasDerivAt hbInv (log (1 - p) - log p)⁻¹ u at hinv
    convert (hasDerivAt_const u tau).add ((hasDerivAt_const u a).mul hinv) using 1 <;> ring
  have houter : HasDerivAt Hb (log (1 - q) - log q) q := by
    simpa [Hb] using Real.hasDerivAt_binEntropy (ne_of_gt (hp.1.trans hq.1)) (by linarith : q ≠ 1)
  change HasDerivAt (fun y => Hb (tau + (1 - 2 * tau) * hbInv y)) _ u
  convert houter.comp u hinner using 1 <;>
    dsimp [a, p, q] <;> field_simp [ne_of_gt hLp] <;> ring

theorem mglCurve_strictConvex {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2) :
    StrictConvexOn ℝ (Icc 0 (log 2)) (mglCurve tau) := by
  have hmglcont : ContinuousOn (mglCurve tau) (Icc (0 : ℝ) (log 2)) := by
    unfold mglCurve
    have hi : ContinuousOn (fun u => tau + (1 - 2 * tau) * hbInv u)
        (Icc (0 : ℝ) (log 2)) := by
      exact continuousOn_const.add (continuousOn_const.mul hbInv_continuousOn)
    apply Real.binEntropy_continuous.continuousOn.comp
    · exact hi
    · exact fun _ _ => mem_univ _
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc (0 : ℝ) (log 2)) hmglcont
  intro u hu v hv huv
  rw [interior_Icc] at hu hv
  rw [(mglCurve_hasDerivAt ht0 ht1 hu).deriv, (mglCurve_hasDerivAt ht0 ht1 hv).deriv]
  apply mglSlope_strictMonoOn ht0 ht1
  · exact hbInv_mem_Ioo hu
  · exact hbInv_mem_Ioo hv
  · exact hbInv_strictMonoOn ⟨hu.1.le, hu.2.le⟩ ⟨hv.1.le, hv.2.le⟩ huv

theorem mglCurve_mono {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2) :
    MonotoneOn (mglCurve tau) (Icc 0 (log 2)) := by
  intro u hu v hv huv
  have h_mono1 : MonotoneOn hbInv (Icc 0 (log 2)) := hbInv_strictMonoOn.monotoneOn
  have huv_inv : hbInv u ≤ hbInv v := h_mono1 hu hv huv
  have h1 : 0 ≤ 1 - 2 * tau := by linarith
  have h_inner : tau + (1 - 2 * tau) * hbInv u ≤ tau + (1 - 2 * tau) * hbInv v := by
    have h2 : (1 - 2 * tau) * hbInv u ≤ (1 - 2 * tau) * hbInv v := mul_le_mul_of_nonneg_left huv_inv h1
    linarith
  have hu_in : hbInv u ∈ Icc (0 : ℝ) (1 / 2) := hbInv_mapsTo hu
  have hv_in : hbInv v ∈ Icc (0 : ℝ) (1 / 2) := hbInv_mapsTo hv
  have hu_inner_in : tau + (1 - 2 * tau) * hbInv u ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor
    · have h2 : 0 ≤ (1 - 2 * tau) * hbInv u := mul_nonneg h1 hu_in.1
      linarith
    · have h2 : (1 - 2 * tau) * hbInv u ≤ (1 - 2 * tau) * (1 / 2) := mul_le_mul_of_nonneg_left hu_in.2 h1
      linarith
  have hv_inner_in : tau + (1 - 2 * tau) * hbInv v ∈ Icc (0 : ℝ) (1 / 2) := by
    constructor
    · have h2 : 0 ≤ (1 - 2 * tau) * hbInv v := mul_nonneg h1 hv_in.1
      linarith
    · have h2 : (1 - 2 * tau) * hbInv v ≤ (1 - 2 * tau) * (1 / 2) := mul_le_mul_of_nonneg_left hv_in.2 h1
      linarith
  have h_Hb_mono : MonotoneOn Hb (Icc 0 (1/2)) := by
    have : Icc (0:ℝ) (1/2) = Icc (0:ℝ) 2⁻¹ := by norm_num
    rw [this]
    exact binEntropy_strictMonoOn.monotoneOn
  exact h_Hb_mono hu_inner_in hv_inner_in h_inner

end AverageHarperStability
