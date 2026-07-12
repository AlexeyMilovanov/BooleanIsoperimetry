import HarperStability.Core.Basic

/-!
# S5 leaf: step-entropy transfer

`s5_step_entropy_transfer` converts the ℓ¹ branching distance produced
by the KL tilt (`s5_kl_tilt`, file `S5KL.lean`) into closeness of the
*average step entropies* along a single coordinate — paper Section S5,
the `B_m`/(BR) step, in per-coordinate form.  The conclusion is stated
with `2 * Real.sqrt` (an explicit concave modulus for the binary
entropy) so that the downstream Markov count in `Core/S5.lean` needs no
inverse of `H`.

## Proof route (all finite)

1. `|uE Af f - uE Af g| ≤ uE Af (fun x => |f x - g x|)` — triangle
   inequality for the finite average (`uE` is a sum divided by the
   positive constant `|Af|`; use `Finset.abs_sum_le_sum_abs`).
2. **Pointwise modulus for the binary entropy:** for `a, b ∈ [0,1]`,
   `|H a - H b| ≤ H |a - b|`.
   Proof: WLOG `b ≤ a`, `δ := a - b`.  Both
   `H a - H b = ∫_b^a H'` and `H δ - H 0 = ∫_0^δ H'`, and
   `H' = Real.log ((1-s)/s)` is decreasing on `(0,1)` (`H` concave),
   while `s ↦ b + s ≥ s`; hence `H a - H b ≤ H δ`.  For the lower side
   use the symmetry `H x = H (1-x)`
   (`Real.binEntropy_one_sub`) and the same argument.  In Lean, avoid
   explicit integrals: show that `s ↦ H (s + δ) - H s` is
   antitone on `[0, 1-δ]` via `Real.hasDerivAt_binEntropy` and
   `StrictAntiOn`/`AntitoneOn` from derivative sign
   (`H'(s+δ) - H'(s) ≤ 0`), then evaluate at `s := b` versus `s := 0`.
3. **Finite Jensen for the concave `H`:**
   `uE Af (fun x => H (d x)) ≤ H (uE Af d)` when `d` takes values in
   `[0,1]` and `Af` is nonempty (`uE` is a convex combination with
   weights `1/|Af|`; use `ConcaveOn.le_map_sum` /
   `inner_le_weight_mul_Lp_of_norm_le`-free direct form:
   `ConcaveOn.smul_le_sum` on `Real.strictConcaveOn_binEntropy.concaveOn`
   or the local concavity toolbox in `Entropy/Basic`
   (`concaveOn_binEntropy_add_two_sq` minus the quadratic term)).
4. **Elementary bound `H y ≤ 2 * Real.sqrt y` for `y ∈ [0,1]`:**
   for `y ≤ 1/2`: `y * log (1/y) ≤ (2/e) * sqrt y ≤ sqrt y`
   (maximize `sqrt y * log (1/y)`) and
   `(1-y) * log (1/(1-y)) ≤ y ≤ sqrt y` (from `log (1/(1-y)) ≤ y/(1-y)`);
   for `y ≥ 1/2`: `H y ≤ Real.log 2 ≤ 2 * sqrt y`.
   (Any clean proof works; the constant `2` has slack.)

Combining 1–4 with `d x := |rho Af t ... x - rho A t ... x| ∈ [0,1]`
gives the statement.

Instance gotcha (STATUS.md): `uH`/`pOn` are defined under
`Classical.propDecidable`; use instance-robust `simp only` forms.
-/

namespace HarperStability

lemma s5_uE_abs_diff_le {m : ℕ} {Af : Finset (Cube m)} (f g : Cube m → ℝ) :
  |uE Af f - uE Af g| ≤ uE Af (fun x => |f x - g x|) := by
  unfold uE
  by_cases hAf : Af.card = 0
  · simp [hAf]
  · have hden_nonneg : 0 ≤ (Af.card : ℝ) := Nat.cast_nonneg _
    calc
      |(∑ x ∈ Af, f x) / (Af.card : ℝ) -
          (∑ x ∈ Af, g x) / (Af.card : ℝ)|
          = |(∑ x ∈ Af, (f x - g x)) / (Af.card : ℝ)| := by
            rw [← sub_div, ← Finset.sum_sub_distrib]
      _ = |∑ x ∈ Af, (f x - g x)| / (Af.card : ℝ) := by
            rw [abs_div, abs_of_nonneg hden_nonneg]
      _ ≤ (∑ x ∈ Af, |f x - g x|) / (Af.card : ℝ) :=
            div_le_div_of_nonneg_right
              (Finset.abs_sum_le_sum_abs (fun x => f x - g x) Af) hden_nonneg

lemma s5_binEntropy_subadd (x y : ℝ) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : x + y ≤ 1) :
    H (x + y) ≤ H x + H y := by
  by_cases hx : x = 0
  · simp [hx, H]
  by_cases hy : y = 0
  · simp [hy, H]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  have hxlt1 : x < 1 := by linarith
  let f : ℝ → ℝ := fun z => H x + H z - H (x + z)
  have hmono : MonotoneOn f (Set.Icc 0 (1 - x)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 - x))
    · dsimp [f, H]
      exact ((continuous_const.add Real.binEntropy_continuous).sub
        (Real.binEntropy_continuous.comp (continuous_const.add continuous_id))).continuousOn
    · intro z hz
      rw [interior_Icc] at hz
      apply DifferentiableAt.differentiableWithinAt
      dsimp [f, H]
      apply DifferentiableAt.sub
      · apply DifferentiableAt.add
        · exact differentiableAt_const _
        · exact Real.differentiableAt_binEntropy (by linarith [hz.1])
            (by linarith [hz.1, hz.2])
      · exact (Real.differentiableAt_binEntropy (by linarith [hxpos, hz.1])
          (by linarith [hz.2])).comp z
            (differentiableAt_const _ |>.add differentiableAt_id)
    · intro z hz
      rw [interior_Icc] at hz
      have hzpos : 0 < z := hz.1
      have hzlt : z < 1 - x := hz.2
      have hxzpos : 0 < x + z := by linarith
      have hxzlt1 : x + z < 1 := by linarith
      have hderiv :
          deriv f z =
            (Real.log (1 - z) - Real.log z) -
              (Real.log (1 - (x + z)) - Real.log (x + z)) := by
        dsimp [f, H]
        have hderivAt : HasDerivAt
            (fun z => Real.binEntropy x + Real.binEntropy z - Real.binEntropy (x + z))
            ((Real.log (1 - z) - Real.log z) -
              (Real.log (1 - (x + z)) - Real.log (x + z))) z := by
          convert ((Real.hasDerivAt_binEntropy (p := z) (by linarith [hzpos])
              (by linarith [hzpos, hzlt])).const_add (Real.binEntropy x)).sub
            ((Real.hasDerivAt_binEntropy (p := x + z) (by linarith [hxzpos])
              (by linarith [hxzlt1])).comp z
                ((hasDerivAt_const (x := z) (c := x)).add (hasDerivAt_id z))) using 1
          ring
        exact hderivAt.deriv
      rw [hderiv]
      have hle_ratio : (1 - (x + z)) / (x + z) ≤ (1 - z) / z := by
        rw [div_le_div_iff₀ hxzpos hzpos]
        nlinarith [hxpos, hzpos]
      have hlogle :
          Real.log ((1 - (x + z)) / (x + z)) ≤ Real.log ((1 - z) / z) := by
        apply Real.log_le_log
        · exact div_pos (by linarith) hxzpos
        · exact hle_ratio
      rw [Real.log_div (by linarith [hzpos, hzlt]) (ne_of_gt hzpos)] at hlogle
      rw [Real.log_div (by linarith [hxzlt1]) (ne_of_gt hxzpos)] at hlogle
      linarith
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 (1 - x) := by constructor <;> linarith
  have hymem : y ∈ Set.Icc 0 (1 - x) := by constructor <;> linarith
  have hle := hmono h0mem hymem hy0
  dsimp [f] at hle
  nlinarith [show H x + H 0 - H (x + 0) = 0 by simp [H]]

lemma s5_binEntropy_modulus (a b : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    |H a - H b| ≤ H |a - b| := by
  by_cases hab : b ≤ a
  · have hd0 : 0 ≤ a - b := sub_nonneg.mpr hab
    have hdabs : |a - b| = a - b := abs_of_nonneg hd0
    have h1raw := s5_binEntropy_subadd b (a - b) hb hd0 (by linarith [ha'])
    have h1 : H a - H b ≤ H |a - b| := by
      rw [hdabs]
      have htmp : H a ≤ H b + H (a - b) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1raw
      linarith
    have h2raw := s5_binEntropy_subadd (1 - a) (a - b) (by linarith) hd0
      (by linarith [hb])
    have h2 : H b - H a ≤ H |a - b| := by
      rw [hdabs]
      have htmp : H b ≤ H a + H (a - b) := by
        have h := h2raw
        rw [show 1 - a + (a - b) = 1 - b by ring] at h
        rw [show H (1 - b) = H b by unfold H; rw [Real.binEntropy_one_sub]] at h
        rw [show H (1 - a) = H a by unfold H; rw [Real.binEntropy_one_sub]] at h
        exact h
      linarith
    exact abs_le.mpr ⟨by linarith, h1⟩
  · have hba : a ≤ b := le_of_not_ge hab
    have hd0 : 0 ≤ b - a := sub_nonneg.mpr hba
    have hdabs : |a - b| = b - a := by rw [abs_sub_comm, abs_of_nonneg hd0]
    have h1raw := s5_binEntropy_subadd a (b - a) ha hd0 (by linarith [hb'])
    have h1 : H b - H a ≤ H |a - b| := by
      rw [hdabs]
      have htmp : H b ≤ H a + H (b - a) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1raw
      linarith
    have h2raw := s5_binEntropy_subadd (1 - b) (b - a) (by linarith) hd0
      (by linarith [ha])
    have h2 : H a - H b ≤ H |a - b| := by
      rw [hdabs]
      have htmp : H a ≤ H b + H (b - a) := by
        have h := h2raw
        rw [show 1 - b + (b - a) = 1 - a by ring] at h
        rw [show H (1 - a) = H a by unfold H; rw [Real.binEntropy_one_sub]] at h
        rw [show H (1 - b) = H b by unfold H; rw [Real.binEntropy_one_sub]] at h
        exact h
      linarith
    exact abs_le.mpr ⟨by linarith, h2⟩

lemma s5_uE_binEntropy_le {m : ℕ} {Af : Finset (Cube m)} (hne : Af.Nonempty)
    (d : Cube m → ℝ) (h0 : ∀ x ∈ Af, 0 ≤ d x) (h1 : ∀ x ∈ Af, d x ≤ 1) :
  uE Af (fun x => H (d x)) ≤ H (uE Af d) := by
  have hgap := binary_entropy_jensen_gap Af hne d h0 h1
  have hvar_nonneg : 0 ≤ 2 * varOn Af d := by
    exact mul_nonneg (by norm_num) (varOn_nonneg Af d)
  linarith

lemma s5_log_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt x := by
  by_cases hx4 : x ≤ 4
  · have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hspos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hsle2 : Real.sqrt x ≤ 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · norm_num
      · norm_num
        exact hx4
    have hlogs : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos hspos
    have hlogeq : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt (le_of_lt hxpos)]
      ring
    calc
      Real.log x = 2 * Real.log (Real.sqrt x) := hlogeq
      _ ≤ 2 * (Real.sqrt x - 1) := by nlinarith
      _ ≤ Real.sqrt x := by nlinarith
  · have hx_ge4 : 4 ≤ x := le_of_not_ge hx4
    by_cases hxexp : x ≤ Real.exp 2
    · have hlogle2 : Real.log x ≤ 2 := by
        exact (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one hx)).mpr hxexp
      have hsqrtge2 : 2 ≤ Real.sqrt x := by
        rw [Real.le_sqrt (by norm_num) (le_trans (by norm_num) hx_ge4)]
        norm_num
        exact hx_ge4
      linarith
    · have hx_exp : Real.exp 2 ≤ x := le_of_not_ge hxexp
      have hanti := Real.log_div_sqrt_antitoneOn
        (show Real.exp 2 ∈ {x : ℝ | Real.exp 2 ≤ x} by simp)
        (show x ∈ {x : ℝ | Real.exp 2 ≤ x} by simpa using hx_exp) hx_exp
      have hbase : Real.log (Real.exp 2) / Real.sqrt (Real.exp 2) ≤ 1 := by
        rw [Real.log_exp, ← Real.exp_half]
        norm_num
        have h2le : (2 : ℝ) ≤ Real.exp 1 := by
          simpa using (Real.two_mul_le_exp (x := 1))
        rw [div_le_one (Real.exp_pos 1)]
        exact h2le
      have hratio : Real.log x / Real.sqrt x ≤ 1 := le_trans hanti hbase
      have hspos : 0 < Real.sqrt x :=
        Real.sqrt_pos.mpr (lt_of_lt_of_le (Real.exp_pos 2) hx_exp)
      exact (div_le_one hspos).mp hratio

lemma s5_binEntropy_le_two_mul_sqrt (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
  H y ≤ 2 * Real.sqrt y := by
  by_cases hy0 : y = 0
  · simp [hy0, H]
  by_cases hhalf : y ≤ 1 / 2
  · have hypos : 0 < y := lt_of_le_of_ne h0 (Ne.symm hy0)
    have hone_sub_pos : 0 < 1 - y := by linarith
    have hloginv : Real.log y⁻¹ ≤ Real.sqrt y⁻¹ := by
      apply s5_log_le_sqrt_of_one_le
      rw [one_le_inv₀ hypos]
      exact h1
    have hterm1 : y * Real.log y⁻¹ ≤ Real.sqrt y := by
      calc
        y * Real.log y⁻¹ ≤ y * Real.sqrt y⁻¹ :=
          mul_le_mul_of_nonneg_left hloginv h0
        _ = Real.sqrt y := by
          rw [Real.sqrt_inv, ← div_eq_mul_inv, Real.div_sqrt]
    have hlog2 : Real.log (1 - y)⁻¹ ≤ (1 - y)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hone_sub_pos)
    have hterm2 : (1 - y) * Real.log (1 - y)⁻¹ ≤ y := by
      calc
        (1 - y) * Real.log (1 - y)⁻¹ ≤ (1 - y) * ((1 - y)⁻¹ - 1) :=
          mul_le_mul_of_nonneg_left hlog2 (by linarith)
        _ = y := by
          field_simp [ne_of_gt hone_sub_pos]
          ring
    have hy_le_sqrt : y ≤ Real.sqrt y := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [h0, h1]
    unfold H Real.binEntropy
    nlinarith
  · have hhalf' : 1 / 2 ≤ y := le_of_not_ge hhalf
    have hHle : H y ≤ Real.log 2 := by
      unfold H
      exact Real.binEntropy_le_log_two
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      nlinarith
    have hsqrtgehalf : (1 / 2 : ℝ) ≤ Real.sqrt y := by
      rw [Real.le_sqrt (by norm_num) h0]
      nlinarith
    nlinarith

/-- **Step-entropy transfer.**  Along one coordinate `t`, the average
(under the atom `Af`) step entropy of the ambient tree differs from the
atom's own average step entropy by at most `2 * sqrt` of the average
branching distance. -/
lemma s5_step_entropy_transfer {m : ℕ} (A Af : Finset (Cube m))
    (_hsub : Af ⊆ A) (hne : Af.Nonempty) (t : Fin m) :
    |uE Af (fun x =>
        H (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))) -
      uE Af (fun x =>
        H (rho Af t (proj (below (Finset.univ : Finset (Fin m)) t) x)))| ≤
      2 * Real.sqrt
        (uE Af (fun x =>
          |rho Af t (proj (below (Finset.univ : Finset (Fin m)) t) x) -
            rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)|)) := by
  let pA : Cube m → ℝ := fun x =>
    rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
  let pAf : Cube m → ℝ := fun x =>
    rho Af t (proj (below (Finset.univ : Finset (Fin m)) t) x)
  let d : Cube m → ℝ := fun x => |pAf x - pA x|
  have hd0 : ∀ x ∈ Af, 0 ≤ d x := by
    intro x _
    exact abs_nonneg _
  have hd1 : ∀ x ∈ Af, d x ≤ 1 := by
    intro x _
    dsimp [d, pAf, pA]
    apply abs_le.mpr
    constructor
    · linarith [rho_nonneg Af t (proj (below (Finset.univ : Finset (Fin m)) t) x),
        rho_le_one A t (proj (below (Finset.univ : Finset (Fin m)) t) x)]
    · linarith [rho_le_one Af t (proj (below (Finset.univ : Finset (Fin m)) t) x),
        rho_nonneg A t (proj (below (Finset.univ : Finset (Fin m)) t) x)]
  have huE0 : 0 ≤ uE Af d := by
    unfold uE
    exact div_nonneg (Finset.sum_nonneg fun x hx => hd0 x hx) (Nat.cast_nonneg _)
  have huE1 : uE Af d ≤ 1 := by
    unfold uE
    have hcard_pos : 0 < (Af.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    rw [div_le_one hcard_pos]
    calc
      (∑ x ∈ Af, d x) ≤ ∑ x ∈ Af, (1 : ℝ) := by
        exact Finset.sum_le_sum fun x hx => hd1 x hx
      _ = (Af.card : ℝ) := by
        simp
  have hpoint :
      ∀ x ∈ Af,
        |H (pA x) - H (pAf x)| ≤ H (d x) := by
    intro x hx
    have hmod := s5_binEntropy_modulus (pA x) (pAf x)
      (rho_nonneg A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
      (rho_le_one A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
      (rho_nonneg Af t (proj (below (Finset.univ : Finset (Fin m)) t) x))
      (rho_le_one Af t (proj (below (Finset.univ : Finset (Fin m)) t) x))
    simpa [d, abs_sub_comm] using hmod
  have hmono :
      uE Af (fun x => |H (pA x) - H (pAf x)|) ≤
        uE Af (fun x => H (d x)) := by
    unfold uE
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun x hx => hpoint x hx) (Nat.cast_nonneg _)
  calc
    |uE Af (fun x =>
        H (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))) -
      uE Af (fun x =>
        H (rho Af t (proj (below (Finset.univ : Finset (Fin m)) t) x)))|
        ≤ uE Af (fun x => |H (pA x) - H (pAf x)|) := by
          simpa [pA, pAf] using
            s5_uE_abs_diff_le (Af := Af) (fun x => H (pA x)) (fun x => H (pAf x))
    _ ≤ uE Af (fun x => H (d x)) := hmono
    _ ≤ H (uE Af d) := s5_uE_binEntropy_le hne d hd0 hd1
    _ ≤ 2 * Real.sqrt (uE Af d) :=
        s5_binEntropy_le_two_mul_sqrt (uE Af d) huE0 huE1
    _ = 2 * Real.sqrt
        (uE Af (fun x =>
          |rho Af t (proj (below (Finset.univ : Finset (Fin m)) t) x) -
            rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)|)) := by
          rfl

end HarperStability
