import HarperStability.Interface.Definitions
import HarperStability.Interface.Statements

/-!
# Effective contracts (v0.3 program)

The frozen v0.2 statements assert the existence of SOME sublinear output
slack.  This layer states the same theorems with EXPLICIT slack
envelopes, so that the o(n) formulation (`MainFiniteStatement`) becomes
a corollary of a precise bound.

## The envelope grading

All quantitative losses in the proof are compositions of one operation,
the *graded majorant*

  `effGeo s n = max (s n) (sqrt ((s n + 1) * (n + 1)))`,

which sends a slack of shape `σ^a·n^(1-a)` to `σ^(a/2)·n^(1-a/2)` (the
`max` keeps the envelopes pointwise monotone, which makes the algebra
composable at small `n`).  `effEnv k` is its `k`-fold iterate, so

  `effEnv k σ (n)  ≈  σ(n)^(2^{-k}) · n^(1 - 2^{-k})`.

The certified grades (deliberately padded — correctness first; each can
be tightened later by re-running the corresponding effective section):

  volume toolbox : log-slack        R3 : grade 2      S4 : grade 4
  S5 : grade 7                      S6 : grade 9      S7 : grade 9
  HBL (R2) : grade 13               Main : grade 13   (γ = 2^{-14})

v0.3.1 repair: S4/S5/S7 are UNIFORM in their precision parameter `eps`
(one `∃ K` before `∀ eps`, explicit `K/eps^4` resp. `K/eps^8` factors)
— the original per-`eps` existentials were too weak for the `eps → 0`
schedule inside R2 (found by the E7 pipeline pass and confirmed by
hand); the schedule then costs grades 10 → 13.

Final statement: `MainFiniteEffectiveStatement` — the cover exists with
`exp(K·(effEnv 14 σ n + 1))` balls of radius `rmin + ⌈K·(effEnv 14 σ n + 1)⌉`,
`K` a constant of the class and `epsCover`.  The o(n) version follows
(see `Assembly/Effective.lean`, `mainFinite_of_effective`).

This file is hash-frozen together with the v0.2 interface; effective
workers must not modify it.
-/

namespace HarperStability

/-- One grading step: the pointwise max of the slack and its geometric
mean with the dimension. -/
noncomputable def effGeo (s : ℕ → ℝ) : ℕ → ℝ :=
  fun n => max (s n) (Real.sqrt ((s n + 1) * ((n : ℝ) + 1)))

/-- `k`-fold grading: `effEnv k σ ≈ σ^(2^{-k}) · n^(1-2^{-k})`. -/
noncomputable def effEnv : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, s => s
  | (k + 1), s => effGeo (effEnv k s)

@[simp] lemma effEnv_zero (s : ℕ → ℝ) : effEnv 0 s = s := rfl

@[simp] lemma effEnv_succ (k : ℕ) (s : ℕ → ℝ) :
    effEnv (k + 1) s = effGeo (effEnv k s) := rfl

/-- Logarithmic slack (volume toolbox scale). -/
noncomputable def effLog (K : ℝ) : ℕ → ℝ :=
  fun n => K * (Real.log ((n : ℝ) + 2) + 1)

/-- The effective degradation of a data tuple: only the slack function
changes, to `K * (effEnv k σ + 1)`. -/
noncomputable def effDegrade (D : StabilityData) (K : ℝ) (k : ℕ) :
    StabilityData :=
  { D with sigma := fun n => K * (effEnv k D.sigma n + 1) }

/-! ## Toolkit: pointwise envelope algebra (fully proved; no `Sublinear`
facts here — those live in `Assembly/Effective.lean`). -/

lemma le_effGeo (s : ℕ → ℝ) (n : ℕ) : s n ≤ effGeo s n :=
  le_max_left _ _

lemma effGeo_nonneg (s : ℕ → ℝ) (n : ℕ) : 0 ≤ effGeo s n :=
  le_trans (Real.sqrt_nonneg _) (le_max_right _ _)

lemma effGeo_mono {s t : ℕ → ℝ} (h : ∀ n, s n ≤ t n) (n : ℕ) :
    effGeo s n ≤ effGeo t n := by
  unfold effGeo
  refine max_le_max (h n) (Real.sqrt_le_sqrt ?_)
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  exact mul_le_mul_of_nonneg_right (by linarith [h n]) hn

lemma le_effEnv (k : ℕ) (s : ℕ → ℝ) (n : ℕ) : s n ≤ effEnv k s n := by
  induction k with
  | zero => exact le_refl _
  | succ k ih => exact ih.trans (le_effGeo (effEnv k s) n)

lemma effEnv_nonneg (k : ℕ) (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (n : ℕ) :
    0 ≤ effEnv k s n := by
  cases k with
  | zero => exact hs n
  | succ k => exact effGeo_nonneg _ n

lemma effEnv_mono {s t : ℕ → ℝ} (h : ∀ n, s n ≤ t n) (k : ℕ) (n : ℕ) :
    effEnv k s n ≤ effEnv k t n := by
  induction k generalizing n with
  | zero => exact h n
  | succ k ih => exact effGeo_mono (fun m => ih m) n

/-- Constants pass through one grading step at the cost of a factor 2. -/
lemma effGeo_scale {C : ℝ} (hC : 1 ≤ C) {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (n : ℕ) :
    effGeo (fun m => C * (s m + 1)) n ≤ 2 * C * (effGeo s n + 1) := by
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hsn : 0 ≤ s n := hs n
  have hgeo_ge : s n ≤ effGeo s n := le_effGeo s n
  have hgeo0 : 0 ≤ effGeo s n := effGeo_nonneg s n
  unfold effGeo
  apply max_le
  · nlinarith [le_max_left (s n) (Real.sqrt ((s n + 1) * ((n : ℝ) + 1)))]
  · have h1 : C * (s n + 1) + 1 ≤ 2 * C * (s n + 1) := by nlinarith
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have h2 : Real.sqrt ((C * (s n + 1) + 1) * ((n : ℝ) + 1)) ≤
        Real.sqrt ((2 * C) * ((s n + 1) * ((n : ℝ) + 1))) := by
      apply Real.sqrt_le_sqrt
      calc (C * (s n + 1) + 1) * ((n : ℝ) + 1)
          ≤ (2 * C * (s n + 1)) * ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right h1 hn1
        _ = (2 * C) * ((s n + 1) * ((n : ℝ) + 1)) := by ring
    have h3 : Real.sqrt ((2 * C) * ((s n + 1) * ((n : ℝ) + 1))) =
        Real.sqrt (2 * C) * Real.sqrt ((s n + 1) * ((n : ℝ) + 1)) :=
      Real.sqrt_mul (by linarith) _
    have h4 : Real.sqrt (2 * C) ≤ 2 * C := by
      calc Real.sqrt (2 * C) ≤ Real.sqrt ((2 * C) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * C := Real.sqrt_sq (by linarith)
    have h5 : Real.sqrt ((s n + 1) * ((n : ℝ) + 1)) ≤
        max (s n) (Real.sqrt ((s n + 1) * ((n : ℝ) + 1))) :=
      le_max_right _ _
    have h6 : 0 ≤ Real.sqrt ((s n + 1) * ((n : ℝ) + 1)) :=
      Real.sqrt_nonneg _
    calc Real.sqrt ((C * (s n + 1) + 1) * ((n : ℝ) + 1))
        ≤ Real.sqrt (2 * C) * Real.sqrt ((s n + 1) * ((n : ℝ) + 1)) := by
          rw [← h3]; exact h2
      _ ≤ (2 * C) * Real.sqrt ((s n + 1) * ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right h4 h6
      _ ≤ 2 * C * (max (s n) (Real.sqrt ((s n + 1) * ((n : ℝ) + 1))) + 1) := by
          nlinarith [h5, h6]

/-- Composition of gradings: a slack dominated by `C * (effEnv i σ + 1)`
has its `j`-fold grading dominated at grade `i + j`, with constant
`2^j * C`. -/
lemma effEnv_comp (j : ℕ) {i : ℕ} {C : ℝ} (hC : 1 ≤ C) {s : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (n : ℕ) :
    effEnv j (fun m => C * (effEnv i s m + 1)) n ≤
      (2 ^ j * C) * (effEnv (i + j) s n + 1) := by
  induction j generalizing n with
  | zero =>
    simpa using le_of_eq (by ring)
  | succ j ih =>
    have hD : (1 : ℝ) ≤ 2 ^ j * C := by
      have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have hEnn : ∀ m, 0 ≤ effEnv (i + j) s m := fun m =>
      effEnv_nonneg _ s hs m
    have hstep : ∀ m, effEnv j (fun m' => C * (effEnv i s m' + 1)) m ≤
        (2 ^ j * C) * (effEnv (i + j) s m + 1) := fun m => ih m
    calc effEnv (j + 1) (fun m => C * (effEnv i s m + 1)) n
        = effGeo (effEnv j (fun m => C * (effEnv i s m + 1))) n := rfl
      _ ≤ effGeo (fun m => (2 ^ j * C) * (effEnv (i + j) s m + 1)) n :=
          effGeo_mono hstep n
      _ ≤ 2 * (2 ^ j * C) * (effGeo (effEnv (i + j) s) n + 1) :=
          effGeo_scale hD hEnn n
      _ = (2 ^ (j + 1) * C) * (effEnv (i + (j + 1)) s n + 1) := by
          rw [show i + (j + 1) = (i + j) + 1 by omega]
          rw [effEnv_succ]
          ring

/-! ## Effective contracts -/

/-- Two-sided ball-volume bounds with logarithmic slack. -/
def BallVolumeTwoSidedEff : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧
    ∀ n t : ℕ, t ≤ n / 2 →
      Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - effLog K n) ≤
        ((ball (∅ : Cube n) t).card : ℝ) ∧
      ((ball (∅ : Cube n) t).card : ℝ) ≤
        Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + effLog K n)

/-- Interior volume calculus with logarithmic slack. -/
def InteriorVolumeCalculusEff : Prop :=
  ∀ alphaMin c0 : ℝ, 0 < alphaMin → 0 < c0 →
    ∃ C_V : ℝ, 1 ≤ C_V ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ n k r : ℕ, ∀ alpha beta sizeSlack : ℝ,
        alphaMin ≤ alpha → alpha ≤ 1 / 2 →
        0 ≤ sizeSlack →
        beta = (r : ℝ) / (n : ℝ) →
        alpha + beta ≤ 1 / 2 - c0 →
        1 ≤ k → k ≤ 2 ^ n →
        |Real.log ((k : ℝ)) - H alpha * (n : ℝ)| ≤ sizeSlack →
        |Real.log ((V n k r : ℝ)) - H (alpha + beta) * (n : ℝ)| ≤
            C_V * sizeSlack + effLog K n ∧
        |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + effLog K n

/-- R3, effective and SLACK-UNIFORM (v0.3.2 form, pulled forward): one
constant per compact class `(qMin, qMax, s0, mu0, pLow)` serves ALL
admissible slack functions `sigma`.  This uniformity is REQUIRED by the
R3-on-heavy-atoms consumers (S5): their atom classes carry
`eps`-dependent slacks `sigma' = sigma + G1(eps)`, and a per-`QData`
constant could not be absorbed into the `K/eps^4`-uniform S5 budget
(found by the E4 pipeline pass, 2026-07-10).  Composition with modified
slacks goes through `effEnv_comp`.

Also UNIFORM in the window density `pLow` with the explicit polynomial
factor `pLow⁻¹` (v0.3.3 introduced `pLow⁻²`; v0.3.5 tightened it to the
honest fixed-radius-growth cost `pLow⁻¹`, which the S6 variance-leaf
shape `K_V/pLow` requires): the `p → 0` schedules inside S4 and S6
evaluate R3 at `pLow = p(m)/2` with `p(m) → 0`, so a per-`pLow`
existential is as useless to them as the per-`eps` one was to R2
(found by the E3 pipeline pass, 2026-07-10). -/
def R3Eff : Prop :=
  ∀ (qMin qMax s0 mu0 : ℝ),
    0 < qMin → qMin ≤ qMax → qMax < 1 / 2 →
    0 < s0 → 0 < mu0 → qMax + s0 ≤ 1 / 2 - mu0 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (pLow : ℝ), 0 < pLow → pLow ≤ 1 / 2 →
      ∀ (sigma : ℕ → ℝ), Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
        ∀ m (A : Finset (Cube m)) (q : ℝ),
          A.Nonempty →
          fat ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
          pinned ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
          blockRegular m A q pLow ((K / pLow) * (effEnv 2 sigma m + 1))

/-- S4, effective and geometric (fat+pinned in, envelope of grade 5
out); the pure-entropy modularity of v0.2 is intentionally fused away —
the `p → 0` and offset choices are internal to the proof.

UNIFORM in the bin precision (v0.3.1 repair): one constant serves all
`eps`, with the explicit polynomial factor `eps⁻⁴` — the per-`eps`
existential was too weak for the downstream `eps → 0` schedules.

v0.3.6 (E3 Aristotle refutation, confirmed by hand): grade 4 was FALSE
for minimal slack — the S3 Fano term `m·H(e/m) ≈ e·log(m/e)` at its
input `e ~ effEnv 4` carries an unavoidable log factor; grade 5 absorbs
it via `m·H(e/m) ≤ 2√(e·m)` (same repair pattern as v0.3.4/S6). -/
def S4Eff : Prop :=
  ∀ (Q : QData), validQData Q →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (eps : ℝ), 0 < eps →
        ∀ m (A : Finset (Cube m)) (q : ℝ),
          A.Nonempty → fat Q m A q → pinned Q m A q →
          ∃ o : ℝ, 0 ≤ o ∧ o < eps / 4 ∧
            uH A (binnedFoldField A (eps / 4) o) ≤
              (K / eps ^ 4) * (effEnv 5 Q.sigma m + 1)

/-- S5, effective: pointwise flatness with slack of grade 8, UNIFORM in
`eps` with the explicit `eps⁻⁴` factor (v0.3.1 repair; the honest
dependence of the proved v0.2 chain is `eps⁻³` — `epsCoeff · sepCoeff` —
padded by one power).

v0.3.6: 7 → 8 — the repaired S4 (grade 5) raises the base of the
atom-class ladder by one; the R3-on-atoms slack `effEnv 2` of the
grade-6 atom sigma lands at 8. -/
def S5Eff : Prop :=
  ∀ (Q : QData), validQData Q →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (eps : ℝ), 0 < eps → eps < Q.qMin →
        ∀ m (A : Finset (Cube m)) (q : ℝ),
          A.Nonempty → fat Q m A q → pinned Q m A q →
          averageBadStepsLE A q eps
            ((K / eps ^ 4) * (effEnv 8 Q.sigma m + 1))

/-- S6, effective and geometric: the predictable center has entropy of
grade 10 for every fat+pinned set (the two-cluster parameters are chosen
internally from `validQData`).

v0.3.4 (found by the E5 Aristotle pass, confirmed by hand): grade 8 is
FALSE for minimal slack `sigma = log` — the Fano term
`m·H(e/m) ≈ e·log(m/e)` carries an unavoidable logarithmic loss over
its input `e ~ effEnv 8`, so the honest total is `effEnv 8 · polylog`,
which fits in grade 9 with room (`E9/E8` is a positive power of `m`).

v0.3.6: 9 → 10 — cascade from S4/S5: `bSlack` is now grade 8, the
p-schedule rebalances to `p ~ √((E₈+1)/(m+1))`, the error reaches
`e ~ E₉`, and the Fano bound `m·H(e/m) ≤ 2√(e·m)` lands at grade 10. -/
def S6Eff : Prop :=
  ∀ (Q : QData), validQData Q →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty → fat Q m A q → pinned Q m A q →
        uH A (predictableCenter A) ≤ K * (effEnv 10 Q.sigma m + 1)

/-- S7, effective: the heavy ball with mass slack of grade 10, UNIFORM
in `eps` with the explicit `eps⁻⁸` factor for both the constant and the
dimension threshold (v0.3.1 repair — this is exactly the uniformity the
`eps(n) → 0` schedule of `R2Eff` consumes; the true dependence of the
S5+S6+Fano chain is ≈ `eps⁻⁶`, padded).

v0.3.6: 9 → 10, absorbing the S6 cascade. -/
def S7Eff : Prop :=
  ∀ (Q : QData), validQData Q →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (eps : ℝ), 0 < eps → eps < Q.qMin → eps < 1 / 2 - Q.qMax →
        ∀ m : ℕ, K / eps ^ 8 ≤ (m : ℝ) →
          ∀ (A : Finset (Cube m)) (q : ℝ),
            A.Nonempty → fat Q m A q → pinned Q m A q →
            ∃ a : Cube m,
              Real.exp (-((K / eps ^ 8) * (effEnv 10 Q.sigma m + 1))) *
                  (A.card : ℝ) ≤
                ((A.filter fun x =>
                  hDist x a ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ))).card : ℝ)

/-- R2, effective: every valid tuple admits the heavy-ball lemma with
the grade-14 effective degradation.  The `eps → 0` schedule is internal
and sqrt-representable: `eps(n) := ((effEnv 10 D.sigma n + 1)/((n:ℝ)+1))^(1/16)`
(four nested square roots), clamped into the admissible window; then
the S7 radius excess `4·eps(n)·n ≈ 4·(n+1)^(15/16)·(effEnv 10 σ n + 1)^(1/16)`
is exactly grade 14, and the mass slack
`(K/eps(n)^8)·(effEnv 10 σ n + 1) = K·effGeo(effEnv 10 σ) n`-shaped is
grade 11 ≤ 14. -/
def R2Eff : Prop :=
  ∀ D : StabilityData, validData D →
    ∃ K : ℝ, 1 ≤ K ∧ HBLFor D (effDegrade D K 14)

/-- R1a, effective: peeling converts the grade-14 heavy-ball lemma into
the grade-14 cover (peeling costs only a constant factor). -/
def R1aEff : Prop :=
  (∀ D : StabilityData, validData D →
    ∃ K : ℝ, 1 ≤ K ∧ HBLFor D (effDegrade D K 14)) →
  ∀ (Din : StabilityData) (epsCover : ℝ), validData Din → 0 < epsCover →
    ∃ K : ℝ, 1 ≤ K ∧ CoverFor Din (effDegrade Din K 14) epsCover

/-- The effective main statement at grade `k`. -/
def MainFiniteEffectiveAt (k : ℕ) : Prop :=
  ∀ (Din : StabilityData) (epsCover : ℝ),
    validData Din → 0 < epsCover →
    ∃ K : ℝ, 1 ≤ K ∧
      degradedData Din (effDegrade Din K k) ∧
      CoverFor Din (effDegrade Din K k) epsCover

/-- The certified grade of the main theorem: `γ = 2^{-14}`, i.e. the
cover uses `exp(K·(σ^(1/16384)·n^(16383/16384)+1))`-many balls of radius
`rmin + ⌈the same⌉`.  (v0.3.1: grade 10 → 13 — the `eps → 0` schedule
of R2 with the `eps⁻⁸`-uniform S7 costs three more grading steps.  v0.3.6: 13 → 14 — the S4 Fano
repair cascades S5 7→8, S6/S7 9→10, and the R2 radius schedule
`4·eps(n)·n` with `eps(n) = ((effEnv 10 σ n+1)/(n+1))^{1/16}` is
exactly grade 14.) -/
def effMainGrade : ℕ := 14

/-- **The effective main theorem statement.** -/
def MainFiniteEffectiveStatement : Prop :=
  MainFiniteEffectiveAt effMainGrade

end HarperStability
