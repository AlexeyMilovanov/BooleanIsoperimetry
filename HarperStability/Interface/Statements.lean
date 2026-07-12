import HarperStability.Interface.Definitions

namespace HarperStability

attribute [local instance] Classical.propDecidable

/-!
# Contract-level statements for the decomposed proof

The statements record exactly the hypotheses consumed by each stage.  They
are meant to be faithful and stable, not pretty.

Design decisions (2026-07-08 repair pass, following the Gemini semantic
review and a fable audit):

* geometry is the imported `BooleanIsoperimetry` geometry;
* `S2`, `S4`, `S6` are PURE entropy statements (no `QData`/`fat`/`pinned`):
  they consume `blockRegular`/variance/flatness hypotheses, so the Process
  worker never touches cube geometry;
* `S7` is the standalone heavy-ball theorem (HBL-FAT), and the derivation
  of `QuestionQ` from it is a separate assembly-level statement;
* quantifier orders put every density/precision parameter BEFORE the slack
  that depends on it.
-/

/-- Two-sided ball-volume bounds (nats). -/
def BallVolumeTwoSidedStatement : Prop :=
  ∃ volumeSlack : ℕ → ℝ, Sublinear volumeSlack ∧
    ∀ n t : ℕ, t ≤ n / 2 →
      Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) - volumeSlack n) ≤
        ((ball (∅ : Cube n) t).card : ℝ) ∧
      ((ball (∅ : Cube n) t).card : ℝ) ≤
        Real.exp (H ((t : ℝ) / (n : ℝ)) * (n : ℝ) + volumeSlack n)

/-- Lemma V+: `V(k,r)` dominates the ball grown from the largest ball below
cardinality `k`. -/
def VPlusStatement : Prop :=
  ∀ n k r : ℕ, 1 ≤ k → k ≤ 2 ^ n →
    ∃ t : ℕ,
      t ≤ n ∧
      (ball (∅ : Cube n) t).card ≤ k ∧
      (∀ t' : ℕ, t' ≤ n → (ball (∅ : Cube n) t').card ≤ k → t' ≤ t) ∧
      ((ball (∅ : Cube n) (t + r)).card : ℝ) ≤ (V n k r : ℝ)

/-- Harper lower direction for a centered ball: the Lovasz-Harper profile at
the ball's cardinality is at least the grown ball size.  Equality/attainment
is proved later from the definition of `V` plus Harper extremality. -/
def InteriorVStatement : Prop :=
  ∀ n t r : ℕ, t + r ≤ n →
    ((ball (∅ : Cube n) (t + r)).card : ℝ) ≤
      (V n (ball (∅ : Cube n) t).card r : ℝ)

/-- Interior volume calculus used by R1/R2: once the size is known to be
`H(alpha)n + o(n)` and the grown radius remains bounded away from the
equator, both the Lovasz-Harper profile and the inverse radius are controlled
with one sublinear envelope.  This statement is intentionally quantitative
enough for the reduction layer; the eventual proof lives in the volume worker. -/
def InteriorVolumeCalculusStatement : Prop :=
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
            C_V * sizeSlack + volumeSlack n ∧
        |(rmin n k : ℝ) - alpha * (n : ℝ)| ≤ C_V * sizeSlack + volumeSlack n

/-- Heavy-ball conclusion for every member of a valid stability class. -/
def HBLFor (Din Dout : StabilityData) : Prop :=
  ∀ {n r : ℕ} {S : Finset (Cube n)} {alpha beta : ℝ},
    classMember Din n r S alpha beta →
    heavyBallConclusion n S (Dout.sigma n) (Nat.ceil (Dout.sigma n))

/-- Stability cover for instances of `Din`, with the output slack supplied
by `Dout`. -/
def CoverFor (Din Dout : StabilityData) (epsCover : ℝ) : Prop :=
  ∀ {n r : ℕ} {S : Finset (Cube n)} {alpha beta : ℝ},
    classMember Din n r S alpha beta →
    stabilityCoverConclusion n S epsCover (Dout.sigma n)
      (Nat.ceil (Dout.sigma n))

/-- R1a: heavy-ball lemma (for a degraded tuple) implies the cover. -/
def R1aStatement : Prop :=
  ∀ (Din : StabilityData) (epsCover : ℝ),
    validData Din → 0 < epsCover →
    (∀ D : StabilityData, validData D →
      ∃ Dhbl : StabilityData, degradedData D Dhbl ∧ HBLFor D Dhbl) →
    ∃ Dcover : StabilityData, degradedData Din Dcover ∧
      CoverFor Din Dcover epsCover

/-- R1b: a `1/2`-cover yields one heavy ball. -/
def R1bStatement : Prop :=
  ∀ (D : StabilityData),
    validData D →
    (∀ {n r : ℕ} {S : Finset (Cube n)} {alpha beta : ℝ},
      classMember D n r S alpha beta →
      stabilityCoverConclusion n S (1 / 2) (D.sigma n) (Nat.ceil (D.sigma n))) →
    ∀ {n r : ℕ} {S : Finset (Cube n)} {alpha beta : ℝ},
      classMember D n r S alpha beta →
      heavyBallConclusion n S (D.sigma n + Real.log 2) (Nat.ceil (D.sigma n))

/-- R2: the contradiction scheme Q implies the heavy-ball lemma. -/
def R2Statement : Prop :=
  (∀ Q : QData, validQData Q → QuestionQ Q) →
    ∀ D : StabilityData, validData D →
      ∃ Dhbl : StabilityData, degradedData D Dhbl ∧
        HBLFor D Dhbl

/-- R3: fat+pinned sets are marginal-block-regular on every fixed density
range, with a class-uniform slack.  Conditional regularity consequences are
derived later from this marginal statement plus entropy chain rules/FAT. -/
def R3Statement : Prop :=
  ∀ (Q : QData) (pLow : ℝ),
    validQData Q → 0 < pLow → pLow ≤ 1 / 2 →
    ∃ sigmaStar : ℕ → ℝ,
      Sublinear sigmaStar ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty → fat Q m A q → pinned Q m A q →
        blockRegular m A q pLow (sigmaStar m)

/-- S1: average flatness of the revelation profile (pure entropy).

The middle-window band uses the integer floor convention
`m / 5 ≤ |I| ≤ m - m / 5`.  Applications derive these hypotheses from any
fixed block-regularity range below `1/5`; finitely many small dimensions are
handled by the surrounding finite-threshold bookkeeping. -/
def S1Statement : Prop :=
  ∀ m (A : Finset (Cube m)) (kappa s eps : ℝ),
    A.Nonempty → 0 ≤ s → 0 < eps →
    (∀ I : Finset (Fin m),
      ((m / 5 : ℕ) : ℝ) ≤ (I.card : ℝ) →
      (I.card : ℝ) ≤ (m : ℝ) - ((m / 5 : ℕ) : ℝ) →
      uH A (proj I) ≤ kappa * (I.card : ℝ) + s) →
    kappa * (m : ℝ) - s ≤ uH A (proj (Finset.univ : Finset (Fin m))) →
    (((Finset.univ : Finset (Fin m)).filter
      (fun t => eps ≤ |hstep A t - kappa|)).card : ℝ) ≤
        12 * s / eps + 4

/-- S2: window variance budget (pure entropy; the density parameter is
quantified BEFORE the slack, and the bound is explicit). -/
def S2Statement : Prop :=
  ∀ m (A : Finset (Cube m)) (q pLow s eps e : ℝ),
    A.Nonempty → 0 < pLow → pLow ≤ 1 / 2 → 0 ≤ s → 0 < eps → 0 ≤ e →
    blockRegular m A q pLow s →
    (((Finset.univ : Finset (Fin m)).filter
      (fun t => eps ≤ |hstep A t - H q|)).card : ℝ) ≤ e →
    varianceBudgetLE A pLow ((s + eps * (m : ℝ) + e * Real.log 2) / 2)

/-- S3: quantitative common-field entropy bound for window-computable
randomized estimators (pure entropy; no smallness of `e` assumed).

`BSize` is a per-coordinate image-size envelope for the field values.  In
asymptotic applications it must be fixed or controlled independently of `m`;
the statement itself is a finite deterministic inequality. -/
def S3Statement : Prop :=
  ∀ m (A : Finset (Cube m)) (kappa s : ℝ)
    (B : Type) (F : Cube m → Fin m → B)
    (p e BSize : ℝ),
    A.Nonempty → 0 ≤ kappa → 0 ≤ s → 0 < p → p ≤ 1 / 2 → 0 ≤ e →
    1 ≤ BSize →
    (∀ I : Finset (Fin m),
      p * (m : ℝ) / 2 ≤ (I.card : ℝ) →
      (I.card : ℝ) ≤ 2 * p * (m : ℝ) →
      uH A (proj I) ≤ kappa * (I.card : ℝ) + s) →
    (∀ t : Fin m, ((A.image fun x => F x t).card : ℝ) ≤ BSize) →
    (∃ G : Finset (Fin m) → Cube m → Fin m → B,
      (∀ J : Finset (Fin m), dependsOnWindow J (G J)) ∧
      expectedEstimatorError A F G p ≤ e) →
    uH A F ≤
      2 * kappa * p * (m : ℝ) + s +
      (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) +
      e * Real.log BSize + 2 * (m : ℝ) * Real.exp (-p * (m : ℝ) / 8)

/-- S4: the binned fold field admits one offset with small entropy (pure
entropy: consumes a block-regularity family and a per-density variance
family; the envelope may depend on both).

This statement is intentionally free of a global `q`-range assumption.  When
S3 needs a field entropy cap without a separately valid range, callers may use
the trivial binary entropy cap (`log 2`) as the common-field baseline. -/
def S4Statement : Prop :=
  ∀ (w : ℝ), 0 < w →
  ∀ (sFam : ℝ → ℕ → ℝ) (vFam : ℝ → ℕ → ℝ),
    (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (sFam pLow)) →
    (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow)) →
    ∃ env : ℕ → ℝ, Sublinear env ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty →
        blockRegularFamily m A q sFam →
        (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
          varianceBudgetLE A pLow (vFam pLow m)) →
        ∃ o : ℝ, 0 ≤ o ∧ o < w ∧
          uH A (binnedFoldField A w o) ≤ env m

/-- S5: pointwise flatness in expectation (geometric: uses fat+pinned via
R3-on-atoms internally; stated at the geometry level on purpose). -/
def S5Statement : Prop :=
  ∀ Q : QData, validQData Q →
    ∃ massSlack : ℝ → ℕ → ℝ,
      (∀ eps : ℝ, 0 < eps → Sublinear (massSlack eps)) ∧
      ∀ m (A : Finset (Cube m)) (q eps : ℝ),
        A.Nonempty → 0 < eps → eps < Q.qMin →
        fat Q m A q → pinned Q m A q →
        averageBadStepsLE A q eps (massSlack eps m)

/-- S6: the predictable center has small entropy (pure entropy: consumes
block-regularity, the variance budget, and the PF mass bound; the
two-cluster gap hypothesis is explicit). -/
def S6Statement : Prop :=
  ∀ (qMin qMax eps gap : ℝ),
    0 ≤ qMin → qMin ≤ qMax → qMax < 1 / 2 →
    0 < eps → 0 < gap → qMax + eps ≤ 1 / 2 - gap →
  ∀ (sFam vFam : ℝ → ℕ → ℝ) (bSlack : ℕ → ℝ),
    (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (sFam pLow)) →
    (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → Sublinear (vFam pLow)) →
    Sublinear bSlack →
    ∃ cEnv : ℕ → ℝ, Sublinear cEnv ∧
      ∀ m (A : Finset (Cube m)) (q : ℝ),
        qMin ≤ q → q ≤ qMax →
        A.Nonempty →
        blockRegularFamily m A q sFam →
        (∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 →
          varianceBudgetLE A pLow (vFam pLow m)) →
        averageBadStepsLE A q eps (bSlack m) →
        uH A (predictableCenter A) ≤ cEnv m

/-- S7: the standalone heavy-ball theorem (HBL-FAT): fat+pinned alone give
a `(q+4·eps)m` ball with a `e^{-o(m)}` mass fraction. -/
def S7Statement : Prop :=
  ∀ Q : QData, validQData Q →
  ∀ eps : ℝ, 0 < eps → eps < Q.qMin → eps < 1 / 2 - Q.qMax →
    ∃ env : ℕ → ℝ, Sublinear env ∧
      ∃ m1 : ℕ, ∀ m ≥ m1, ∀ (A : Finset (Cube m)) (q : ℝ),
        A.Nonempty → fat Q m A q → pinned Q m A q →
        ∃ a : Cube m,
          Real.exp (-(env m)) * (A.card : ℝ) ≤
            ((A.filter fun x =>
              hDist x a ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ))).card : ℝ)

/-- Assembly step: the heavy-ball theorem defeats every BAD hypothesis,
yielding the contradiction scheme Q.

This is the formal role played by the prose `R2b`/not-BAD bridge: from the
positive heavy-ball output `S7Statement`, every FAT+PINNED+BAD witness is
contradicted. -/
def QFromS7Statement : Prop :=
  S7Statement → ∀ Q : QData, validQData Q → QuestionQ Q

/-- A0: the component package consumed by the final assembly.

The final forward extraction directly consumes `R1aStatement`,
`R2Statement`, `S7Statement`, and `QFromS7Statement`.  The remaining entries
are the proof-stage inputs used to establish those components. -/
def A0Statement : Prop :=
  BallVolumeTwoSidedStatement ∧ VPlusStatement ∧ InteriorVStatement ∧
  InteriorVolumeCalculusStatement ∧
  R1aStatement ∧ R1bStatement ∧ R2Statement ∧ R3Statement ∧
  S1Statement ∧ S2Statement ∧ S3Statement ∧ S4Statement ∧
  S5Statement ∧ S6Statement ∧ S7Statement ∧ QFromS7Statement

/-- The finite main theorem statement.

The asymptotic corollary in the paper is intentionally outside this finite
interface layer.  The assumption `0 < epsCover` totalizes the statement:
for `epsCover ≥ 1`, the cover conclusion is harmless/trivial. -/
def MainFiniteStatement : Prop :=
  ∀ (Din : StabilityData) (epsCover : ℝ),
    validData Din → 0 < epsCover →
    ∃ Dout : StabilityData, degradedData Din Dout ∧
      CoverFor Din Dout epsCover

end HarperStability
