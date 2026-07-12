import HarperStability.Core.Basic

/-!
# S5 leaf: same-bin one-sided separation

`s5_same_bin_separation` is the key *one-sided* step of the S5
(pointwise flatness) proof — paper Section S5, step *Same-bin
separation*.  Inside an atom of the binned fold field, the fold at step
`t` is trapped in one bin of width `eps/4`.  If the bin sits more than
`3*eps/4` away from `q`, then EVERY trajectory of the atom strays at
least `eps/2` from `q` at step `t`, on ONE side of `q` — so the step
entropies cannot cancel around `H q`: the atom's average ambient step
entropy at `t` is separated from `H q` by the explicit class constant
`eps * mu0 / 2`.

(An earlier version of this step tried to invert `H` through its global
modulus of continuity; that is quantitatively FALSE — the modulus near
`0` beats the local gap at `q` — and was repaired by this one-sided
argument.  See the paper's intuition block for S5.)

## Proof route (all finite)

Let `ℓ := o + f t * (eps/4)` and
`y x := fold (rho A t (proj (below univ t) x))`.

1. Bin confinement (`s5_fold_pinned_in_bin` below): every `x ∈ Af` has
   `y x ∈ [ℓ, ℓ + eps/4)`.
2. `hbad : 3*eps/4 < |ℓ - q|` plus the triangle inequality give
   `eps/2 < |y x - q|` for every `x ∈ Af`.
3. One-sidedness: the interval `[ℓ, ℓ + eps/4)` has width `eps/4` and
   every point is `> eps/2` from `q`, so it cannot straddle `q`; case
   on the sign of `ℓ - q`: either (LOW) `∀ x ∈ Af, y x ≤ q - eps/2`,
   or (HIGH) `∀ x ∈ Af, q + eps/2 ≤ y x`.
4. Fold symmetry: `H (rho ...) = H (y x)` since `H p = H (min p (1-p))`
   (`Real.binEntropy_one_sub` and a case split on `p ≤ 1/2`).
5. **Calculus fact** (self-contained; do NOT import Reductions):
   for `0 ≤ a ≤ b ≤ 1/2`,
   `(b - a) * (1 - a - b) ≤ H b - H a`.
   Proof: `s ↦ H s - (s - s^2)` has derivative
   `Real.log ((1-s)/s) - (1 - 2*s) ≥ 0` on `(0, 1/2]` — the function
   `ψ s := log ((1-s)/s) - (1-2s)` is decreasing
   (`ψ' = 2 - 1/(s*(1-s)) ≤ -2`) with `ψ (1/2) = 0` — so
   `H b - H a ≥ (b - b^2) - (a - a^2) = (b-a)*(1-a-b)`.
   Use `Real.hasDerivAt_binEntropy` + monotonicity-from-derivative;
   handle the endpoint `a = 0` by continuity or the explicit
   `b*(1-b) ≤ H b`.
6. LOW case: `y x ≤ q - eps/2` (and `y x ≥ 0`, so `q - eps/2 ≥ 0`);
   monotonicity of `H` on `[0, 1/2]` gives
   `uE Af (H ∘ y) ≤ H (q - eps/2)`; step 5 with
   `a := q - eps/2, b := q`:
   `H q - H (q - eps/2) ≥ (eps/2) * (1 - 2*q + eps/2)
     ≥ (eps/2) * 2*(Q.s0 + Q.mu0) ≥ eps * Q.mu0 / 2`,
   using `q ≤ Q.qMax ≤ 1/2 - Q.mu0 - Q.s0` from `validQData`.
7. HIGH case: some realized `y x₀ ≤ 1/2` forces `q + eps/2 ≤ 1/2`;
   `uE Af (H ∘ y) ≥ H (q + eps/2)`; step 5 with
   `a := q, b := q + eps/2`:
   `H (q + eps/2) - H q ≥ (eps/2) * (1 - 2*q - eps/2)
     ≥ (eps/2) * (1/2 - q) ≥ (eps/2) * (Q.s0 + Q.mu0) ≥ eps * Q.mu0 / 2`
   (the middle inequality uses `eps/2 ≤ 1/2 - q` from realizability).
8. `uE` preserves pointwise bounds over the nonempty `Af` (convex
   combination), so in both cases
   `eps * Q.mu0 / 2 ≤ |uE Af (H ∘ rho A t ...) - H q|`.

Instance gotcha (STATUS.md): `uH`/`pOn` are defined under
`Classical.propDecidable`; use instance-robust `simp only` forms.
-/

namespace HarperStability

/-- Bin confinement: if `x` is pinned to bin field `f` (i.e.
`binnedFoldField A (eps/4) o x = f`), then for each coordinate `t` the
folded prefix bias `fold (rho A t ...)` lies in the half-open bin
`[o + f t * (eps/4), o + (f t + 1) * (eps/4))`.
(Moved verbatim from `Core/S5.lean`.) -/
lemma s5_fold_pinned_in_bin {m : ℕ} (A : Finset (Cube m)) (eps o : ℝ) (heps : 0 < eps)
    (f : Fin m → ℤ) (x : Cube m)
    (hx : binnedFoldField A (eps / 4) o x = f) (t : Fin m) :
    o + (f t : ℝ) * (eps / 4) ≤
        fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) ∧
      fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) <
        o + ((f t : ℝ) + 1) * (eps / 4) := by
  have heps4 : 0 < eps / 4 := by linarith
  have hxt : binnedFoldField A (eps / 4) o x t = f t := congrFun hx t
  unfold binnedFoldField at hxt
  set y := fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) with hy
  obtain ⟨hlo, hhi⟩ := Int.floor_eq_iff.mp hxt
  have h1 : (f t : ℝ) * (eps / 4) ≤ y - o := (le_div_iff₀ heps4).mp hlo
  have h2 : y - o < ((f t : ℝ) + 1) * (eps / 4) := (div_lt_iff₀ heps4).mp hhi
  exact ⟨by linarith, by linarith⟩

lemma s5_log_ratio_ge_one_sub_two_mul (x : ℝ) (hx0 : 0 < x) (hxhalf : x ≤ 1 / 2) :
    1 - 2 * x ≤ Real.log ((1 - x) / x) := by
  have h1x_pos : 0 < 1 - x := by linarith
  have hz_pos : 0 < x / (1 - x) := div_pos hx0 h1x_pos
  have hlogz := Real.log_le_sub_one_of_pos (x := x / (1 - x)) hz_pos
  have hlog_eq : Real.log (x / (1 - x)) = -Real.log ((1 - x) / x) := by
    rw [← Real.log_inv ((1 - x) / x)]
    congr 1
    field_simp [hx0.ne', h1x_pos.ne']
  have hlog_lower : 1 - x / (1 - x) ≤ Real.log ((1 - x) / x) := by
    rw [hlog_eq] at hlogz
    linarith
  have halg : 1 - 2 * x ≤ 1 - x / (1 - x) := by
    rw [sub_le_sub_iff_left]
    rw [div_le_iff₀ h1x_pos]
    nlinarith [sq_nonneg x, hxhalf]
  exact halg.trans hlog_lower

/-- **Same-bin separation.**  If the bin of the atom `Af` at coordinate
`t` sits more than `3*eps/4` from `q`, then the atom's average ambient
step entropy at `t` is at least `eps * Q.mu0 / 2` away from `H q`. -/
lemma s5_same_bin_calculus_fact (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    (b - a) * (1 - a - b) ≤ H b - H a := by
  let F : ℝ → ℝ := fun x => H x - (x - x ^ 2)
  have hmono : MonotoneOn F (Set.Icc (0 : ℝ) (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?hcont ?hdiff ?hderiv
    · dsimp [F, H]
      exact (Real.binEntropy_continuous.sub
        (continuous_id.sub (continuous_id.pow 2))).continuousOn
    · intro x hx
      apply DifferentiableAt.differentiableWithinAt
      dsimp [F, H]
      apply DifferentiableAt.sub
      · have hxI : x ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
          simpa [interior_Icc] using hx
        exact (Real.hasDerivAt_binEntropy (by linarith [hxI.1])
          (by linarith [hxI.2])).differentiableAt
      · fun_prop
    · intro x hx
      have hxI : x ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
        simpa [interior_Icc] using hx
      have hx0 : 0 < x := hxI.1
      have hxhalf : x < 1 / 2 := hxI.2
      have hpoly : HasDerivAt (fun y : ℝ => y - y ^ 2) (1 - 2 * x) x := by
        convert (hasDerivAt_id x).sub (hasDerivAt_pow 2 x) using 1
        ring
      have hderiv : deriv F x = (Real.log (1 - x) - Real.log x) - (1 - 2 * x) := by
        apply HasDerivAt.deriv
        dsimp [F, H]
        exact (Real.hasDerivAt_binEntropy (by linarith [hx0])
          (by linarith [hxhalf])).sub hpoly
      rw [hderiv]
      have hlog := s5_log_ratio_ge_one_sub_two_mul x hx0 (le_of_lt hxhalf)
      rw [Real.log_div (by linarith [hxhalf]) (by linarith [hx0])] at hlog
      exact sub_nonneg.mpr hlog
  have ha_half : a ≤ 1 / 2 := hab.trans hb
  have hF := hmono ⟨ha, ha_half⟩ ⟨by linarith, hb⟩ hab
  dsimp [F] at hF
  nlinarith [hF]

lemma s5_same_bin_one_sided (ℓ q eps : ℝ) (heps : 0 < eps)
    (hbad : 3 * eps / 4 < |ℓ - q|) :
    (ℓ + eps / 4 ≤ q - eps / 2) ∨ (q + eps / 2 ≤ ℓ) := by
  rcases lt_trichotomy ℓ q with h | h | h
  · left
    have : ℓ - q < 0 := by linarith
    have : q - ℓ > 3 * eps / 4 := by
      rw [abs_of_neg this] at hbad
      linarith
    linarith
  · right
    have : ℓ - q = 0 := by linarith
    rw [this, abs_zero] at hbad
    linarith
  · right
    have : ℓ - q > 0 := by linarith
    have : ℓ - q > 3 * eps / 4 := by
      rw [abs_of_pos this] at hbad
      linarith
    linarith

lemma s5_fold_nonneg_of_prob (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ fold p := by
  unfold fold
  exact le_min hp0 (sub_nonneg.mpr hp1)

lemma s5_H_eq_H_fold_of_prob (p : ℝ) (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    H p = H (fold p) := by
  unfold H fold
  by_cases h : p ≤ 1 - p
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
    exact (Real.binEntropy_one_sub p).symm

lemma s5_H_mono_half {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    H x ≤ H y := by
  unfold H
  exact Real.binEntropy_strictMonoOn.monotoneOn
    ⟨hx, by norm_num; linarith⟩
    ⟨by linarith, by norm_num; linarith⟩ hxy

lemma s5_uE_le_of_forall {m : ℕ} (Af : Finset (Cube m)) (hne : Af.Nonempty)
    (g : Cube m → ℝ) (C : ℝ) (hC : ∀ x ∈ Af, g x ≤ C) :
    uE Af g ≤ C := by
  have hcard_pos : 0 < (Af.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  unfold uE
  rw [div_le_iff₀ hcard_pos]
  calc
    (∑ x ∈ Af, g x) ≤ ∑ x ∈ Af, C := by
      exact Finset.sum_le_sum hC
    _ = C * (Af.card : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma s5_le_uE_of_forall {m : ℕ} (Af : Finset (Cube m)) (hne : Af.Nonempty)
    (g : Cube m → ℝ) (C : ℝ) (hC : ∀ x ∈ Af, C ≤ g x) :
    C ≤ uE Af g := by
  have hcard_pos : 0 < (Af.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  unfold uE
  rw [le_div_iff₀ hcard_pos]
  calc
    C * (Af.card : ℝ) = ∑ x ∈ Af, C := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ Af, g x := by
      exact Finset.sum_le_sum hC

lemma s5_same_bin_separation {m : ℕ} (A Af : Finset (Cube m)) (Q : QData)
    (hQ : validQData Q) (q eps o : ℝ)
    (heps : 0 < eps) (hq1 : Q.qMin ≤ q) (hq2 : q ≤ Q.qMax)
    (ho1 : 0 ≤ o) (ho2 : o < eps / 4)
    (f : Fin m → ℤ) (t : Fin m)
    (hsub : Af ⊆ A) (hne : Af.Nonempty)
    (hbinned : ∀ x ∈ Af, binnedFoldField A (eps / 4) o x = f)
    (hbad : 3 * eps / 4 < |o + (f t : ℝ) * (eps / 4) - q|) :
    eps * Q.mu0 / 2 ≤
      |uE Af (fun x =>
          H (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))) -
        H q| := by
  have _ : 0 ≤ o := ho1
  have _ : o < eps / 4 := ho2
  have _ : Af ⊆ A := hsub
  have hneAf := hne
  rcases hQ with
    ⟨hQ_qMin_pos, _hQ_qMin_le, hQ_qMax_half, _hQ_s0_pos, hQ_mu0_pos,
      hQ_reg, _hQ_sub, _hQ_log⟩
  have hq_nonneg : 0 ≤ q := by linarith
  have hq_half : q ≤ 1 / 2 := by linarith
  have hTpos : 0 < eps * Q.mu0 / 2 := by positivity
  set ℓ : ℝ := o + (f t : ℝ) * (eps / 4) with hℓ
  have hside := s5_same_bin_one_sided ℓ q eps heps (by simpa [ℓ] using hbad)
  let G : Cube m → ℝ := fun x =>
    H (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
  rcases hside with hlow | hhigh
  · obtain ⟨x0, hx0⟩ := hne
    have hqminus_nonneg : 0 ≤ q - eps / 2 := by
      obtain ⟨_hlo0, hhi0⟩ :=
        s5_fold_pinned_in_bin A eps o heps f x0 (hbinned x0 hx0) t
      have hp0 := rho_nonneg A t (proj (below (Finset.univ : Finset (Fin m)) t) x0)
      have hp1 := rho_le_one A t (proj (below (Finset.univ : Finset (Fin m)) t) x0)
      have hy0 :
          0 ≤ fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x0)) := by
        exact s5_fold_nonneg_of_prob _ hp0 hp1
      nlinarith [hℓ]
    have hqminus_half : q - eps / 2 ≤ 1 / 2 := by linarith
    have hpoint : ∀ x ∈ Af, G x ≤ H (q - eps / 2) := by
      intro x hx
      obtain ⟨_hlo, hhi⟩ :=
        s5_fold_pinned_in_bin A eps o heps f x (hbinned x hx) t
      have hp0 := rho_nonneg A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
      have hp1 := rho_le_one A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
      have hy_nonneg :
          0 ≤ fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) := by
        exact s5_fold_nonneg_of_prob _ hp0 hp1
      have hy_le :
          fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) ≤
            q - eps / 2 := by
        nlinarith [hℓ]
      have hH := s5_H_mono_half hy_nonneg hy_le hqminus_half
      dsimp [G]
      rw [s5_H_eq_H_fold_of_prob _ hp0 hp1]
      exact hH
    have hu_le : uE Af G ≤ H (q - eps / 2) :=
      s5_uE_le_of_forall Af hneAf G _ hpoint
    have hcalc :=
      s5_same_bin_calculus_fact (q - eps / 2) q hqminus_nonneg (by linarith) hq_half
    have hgap : eps * Q.mu0 / 2 ≤ H q - H (q - eps / 2) := by
      have hfactor :
          eps * Q.mu0 / 2 ≤ (q - (q - eps / 2)) * (1 - (q - eps / 2) - q) := by
        have hleft : q - (q - eps / 2) = eps / 2 := by ring
        rw [hleft]
        nlinarith
      exact hfactor.trans hcalc
    have hdiff_nonpos : uE Af G - H q ≤ 0 := by linarith
    rw [abs_of_nonpos hdiff_nonpos]
    linarith
  · obtain ⟨x0, hx0⟩ := hne
    have hqplus_half : q + eps / 2 ≤ 1 / 2 := by
      obtain ⟨hlo0, _hhi0⟩ :=
        s5_fold_pinned_in_bin A eps o heps f x0 (hbinned x0 hx0) t
      have hy_half := fold_le_half
        (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x0))
      nlinarith [hℓ]
    have hqplus_nonneg : 0 ≤ q + eps / 2 := by linarith
    have hpoint : ∀ x ∈ Af, H (q + eps / 2) ≤ G x := by
      intro x hx
      obtain ⟨hlo, _hhi⟩ :=
        s5_fold_pinned_in_bin A eps o heps f x (hbinned x hx) t
      have hp0 := rho_nonneg A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
      have hp1 := rho_le_one A t (proj (below (Finset.univ : Finset (Fin m)) t) x)
      have hy_half := fold_le_half
        (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
      have hy_ge :
          q + eps / 2 ≤
            fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) := by
        nlinarith [hℓ]
      have hH := s5_H_mono_half hqplus_nonneg hy_ge hy_half
      dsimp [G]
      rw [s5_H_eq_H_fold_of_prob _ hp0 hp1]
      exact hH
    have hu_ge : H (q + eps / 2) ≤ uE Af G :=
      s5_le_uE_of_forall Af hneAf G _ hpoint
    have hcalc :=
      s5_same_bin_calculus_fact q (q + eps / 2) hq_nonneg (by linarith) hqplus_half
    have hgap : eps * Q.mu0 / 2 ≤ H (q + eps / 2) - H q := by
      have hfactor :
          eps * Q.mu0 / 2 ≤ ((q + eps / 2) - q) * (1 - q - (q + eps / 2)) := by
        have hleft : (q + eps / 2) - q = eps / 2 := by ring
        rw [hleft]
        nlinarith
      exact hfactor.trans hcalc
    have hdiff_nonneg : 0 ≤ uE Af G - H q := by linarith
    rw [abs_of_nonneg hdiff_nonneg]
    linarith

end HarperStability
