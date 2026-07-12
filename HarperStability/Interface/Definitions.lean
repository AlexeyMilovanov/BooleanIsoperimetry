import Mathlib
import BooleanIsoperimetry

open Finset

/-!
# Interface definitions for the robust Harper stability formalization

This file intentionally contains only finite, counting-measure objects.  It
is the contract layer shared by all proof workers.

Geometry (`Cube`, `hDist`, `neighborhood`) is imported VERBATIM from
`BooleanIsoperimetry` (top-level names) and deliberately NOT redefined, so
that `harper_vertex_iso` applies to our objects with no bridge lemmas.
Note the imported argument order: `neighborhood r A`.

Entropies are in nats (`Real.negMulLog`, `Real.binEntropy`); consequently
all exponential slacks appear as `Real.exp`, and the `2^{...}` quantities of
the prose are written `Real.exp (... * Real.log 2)`.
-/

namespace HarperStability

attribute [local instance] Classical.propDecidable

/-- Hamming ball of integer radius, via the imported `hDist`. -/
noncomputable def ball {n : ℕ} (a : Cube n) (r : ℕ) : Finset (Cube n) :=
  Finset.univ.filter fun y => hDist y a ≤ r

/-- The Harper minimum `V(k,r)` in dimension `n`, by finite minimization. -/
noncomputable def V (n k r : ℕ) : ℕ :=
  let fams := (Finset.univ : Finset (Cube n)).powerset.filter
    fun A : Finset (Cube n) => A.card = k
  let vals := fams.image fun A => (neighborhood r A).card
  if h : vals.Nonempty then vals.min' h else 0

/-- Radius of the smallest centered Hamming ball with cardinality `≥ k`. -/
noncomputable def rmin (n k : ℕ) : ℕ :=
  let vals := (Finset.range (n + 1)).filter fun r => k ≤ (ball (∅ : Cube n) r).card
  if h : vals.Nonempty then vals.min' h else n

/-- Points of `S` covered by balls of common radius around `centers`. -/
noncomputable def coveredByBalls {n : ℕ} (S centers : Finset (Cube n))
    (radius : ℕ) : Finset (Cube n) :=
  S.filter fun x => ∃ c ∈ centers, hDist x c ≤ radius

/-- Fiber probability of `f = b` under the uniform counting law on `A`. -/
noncomputable def pOn {m : ℕ} {B : Type*} (A : Finset (Cube m))
    (f : Cube m → B) (b : B) : ℝ :=
  ((A.filter fun x => f x = b).card : ℝ) / (A.card : ℝ)

/-- Uniform expectation of a real statistic on `A`. -/
noncomputable def uE {m : ℕ} (A : Finset (Cube m)) (f : Cube m → ℝ) : ℝ :=
  (∑ x ∈ A, f x) / (A.card : ℝ)

/-- Finite variance under the uniform counting law on `A`. -/
noncomputable def varOn {m : ℕ} (A : Finset (Cube m)) (f : Cube m → ℝ) : ℝ :=
  uE A fun x => (f x - uE A f) ^ 2

/-- Shannon entropy (nats) of `f` under the uniform counting law on `A`. -/
noncomputable def uH {m : ℕ} {B : Type*} (A : Finset (Cube m))
    (f : Cube m → B) : ℝ :=
  ∑ b ∈ A.image f, Real.negMulLog (pOn A f b)

/-- Conditional entropy `H(f | g)`, by the finite chain-rule identity. -/
noncomputable def uCondH {m : ℕ} {B C : Type*} (A : Finset (Cube m))
    (f : Cube m → B) (g : Cube m → C) : ℝ :=
  uH A (fun x => (f x, g x)) - uH A g

/-- Conditional variance of `f` given a finite statistic `g`
(fiber-averaged under the counting law on `A`). -/
noncomputable def uCondVar {m : ℕ} {B : Type*} (A : Finset (Cube m))
    (f : Cube m → ℝ) (g : Cube m → B) : ℝ :=
  ∑ b ∈ A.image g, pOn A g b * varOn (A.filter fun x => g x = b) f

/-- Window projection. -/
def proj {m : ℕ} (I : Finset (Fin m)) : Cube m → Cube m :=
  fun x => x ∩ I

/-- Boolean coordinate value. -/
def coord {m : ℕ} (t : Fin m) : Cube m → Bool :=
  fun x => decide (t ∈ x)

/-- Coordinates of a window strictly below `t` (identity revelation order). -/
def below {m : ℕ} (I : Finset (Fin m)) (t : Fin m) : Finset (Fin m) :=
  I.filter fun s => s < t

/-- Prefix branching probability `Pr[X_t = 1 | X_{<t} = w]`.

Callers normally pass `w = proj (below univ t) x`.  For arbitrary
non-projected `w`, this is still the exact finite conditional probability of
the equality fiber, possibly the empty fiber under the totalized `pOn`. -/
noncomputable def rho {m : ℕ} (A : Finset (Cube m)) (t : Fin m) (w : Cube m) :
    ℝ :=
  pOn (A.filter fun x => proj (below (Finset.univ : Finset (Fin m)) t) x = w)
    (coord t) true

/-- Step entropy `H(X_t | X_{<t})` in the identity revelation order. -/
noncomputable def hstep {m : ℕ} (A : Finset (Cube m)) (t : Fin m) : ℝ :=
  uCondH A (coord t) (proj (below (Finset.univ : Finset (Fin m)) t))

/-- Folded bias magnitude. -/
noncomputable def fold (x : ℝ) : ℝ :=
  min x (1 - x)

/-- Binary entropy in nats (local alias). -/
noncomputable def H (x : ℝ) : ℝ :=
  Real.binEntropy x

/-- Explicit finite-asymptotic `o(n)` envelope. -/
def Sublinear (s : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ s n) ∧
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, s n ≤ ε * (n : ℝ)

/-- Binned fold field used in S4/S5 (bin width `w`, offset `o`). -/
noncomputable def binnedFoldField {m : ℕ} (A : Finset (Cube m)) (w o : ℝ) :
    Cube m → Fin m → ℤ :=
  fun x t =>
    Int.floor
      ((fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) - o) / w)

/-- Predictable center obtained from the prefix branching profile. -/
noncomputable def predictableCenter {m : ℕ} (A : Finset (Cube m)) (x : Cube m) :
    Cube m :=
  (Finset.univ : Finset (Fin m)).filter fun t =>
    (1 / 2 : ℝ) < rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)

/-- A field is computable from a coordinate window if it is constant on
window fibers. -/
def dependsOnWindow {m : ℕ} {B : Type*} (I : Finset (Fin m))
    (F : Cube m → B) : Prop :=
  ∀ x y : Cube m, proj I x = proj I y → F x = F y

/-- Probability of a specific random window under independent
`p`-inclusion. -/
noncomputable def windowProb {m : ℕ} (J : Finset (Fin m)) (p : ℝ) : ℝ :=
  p ^ J.card * (1 - p) ^ (m - J.card)

/-- Expected coordinate Hamming error of a randomized window estimator. -/
noncomputable def expectedEstimatorError {m : ℕ} {B : Type*}
    (A : Finset (Cube m)) (F : Cube m → Fin m → B)
    (G : Finset (Fin m) → Cube m → Fin m → B) (p : ℝ) : ℝ :=
  ∑ J : Finset (Fin m),
    windowProb J p * uE A (fun x =>
      (((Finset.univ : Finset (Fin m)).filter fun t => F x t ≠ G J x t).card : ℝ))

/-- The average number of `eps`-bad prefix-bias coordinates is at most
`massSlack` (PF conclusion shape). -/
noncomputable def averageBadStepsLE {m : ℕ} (A : Finset (Cube m))
    (q eps massSlack : ℝ) : Prop :=
  ((∑ x ∈ A,
      (((Finset.univ : Finset (Fin m)).filter fun t =>
        eps ≤ |fold (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)) - q|
      ).card : ℝ))) ≤ massSlack * (A.card : ℝ)

/-- Variance budget for the prefix-bias process over every admissible
window (S2 conclusion shape). -/
noncomputable def varianceBudgetLE {m : ℕ} (A : Finset (Cube m))
    (pLow varianceSlack : ℝ) : Prop :=
  ∀ W : Finset (Fin m),
    pLow * (m : ℝ) ≤ (W.card : ℝ) →
    (W.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
    (∑ t ∈ W,
      uCondVar A
        (fun x => rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
        (proj (below W t))) ≤ varianceSlack

/-- Marginal block regularity on all windows in a fixed density range.

This is intentionally the marginal entropy component consumed by S1--S6, not
the full prose R3 package with every conditional regularity consequence. -/
def blockRegular (m : ℕ) (A : Finset (Cube m)) (q pLow slack : ℝ) : Prop :=
  0 < pLow ∧ pLow ≤ 1 / 2 ∧
  ∀ I : Finset (Fin m),
    pLow * (m : ℝ) ≤ (I.card : ℝ) →
    (I.card : ℝ) ≤ (1 - pLow) * (m : ℝ) →
      |uH A (proj I) - H q * (I.card : ℝ)| ≤ slack

/-- A per-density family of block-regularity slacks (entropy-level input for
the purified S4/S6 contracts). -/
def blockRegularFamily (m : ℕ) (A : Finset (Cube m)) (q : ℝ)
    (sFam : ℝ → ℕ → ℝ) : Prop :=
  ∀ pLow : ℝ, 0 < pLow → pLow ≤ 1 / 2 → blockRegular m A q pLow (sFam pLow m)

/-- Fixed data for the finite main theorem. -/
structure StabilityData where
  rho : ℝ
  deltaCap : ℝ
  cSize : ℝ
  alphaMin : ℝ
  alphaMax : ℝ
  sigma : ℕ → ℝ

/-- Basic validity assumptions for finite stability data. -/
def validData (D : StabilityData) : Prop :=
  0 < D.rho ∧ 0 < D.deltaCap ∧ D.deltaCap < 1 ∧
  1 ≤ D.cSize ∧
  0 < D.alphaMin ∧ D.alphaMin ≤ D.alphaMax ∧ D.alphaMax < 1 / 2 ∧
  Sublinear D.sigma ∧
  ∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ D.sigma n

/-- `Dout` is a degraded-slack version of `Din`.  The exact degradation is
intentionally opaque at interface level and is discharged in assembly. -/
def degradedData (Din Dout : StabilityData) : Prop :=
  validData Dout ∧
  Din.rho = Dout.rho ∧
  Din.deltaCap = Dout.deltaCap ∧
  Din.cSize ≤ Dout.cSize ∧
  Din.alphaMin = Dout.alphaMin ∧
  Din.alphaMax = Dout.alphaMax ∧
  ∀ n, Din.sigma n ≤ Dout.sigma n

/-- Size hypothesis, in nats. -/
def sizeHyp (D : StabilityData) (n : ℕ) (S : Finset (Cube n)) (alpha : ℝ) :
    Prop :=
  |Real.log (S.card : ℝ) - H alpha * (n : ℝ)| ≤ D.cSize * D.sigma n

/-- Near-optimal neighborhood hypothesis (nat units). -/
def nearOptimalHyp (D : StabilityData) (n r : ℕ) (S : Finset (Cube n)) :
    Prop :=
  ((neighborhood r S).card : ℝ) ≤ Real.exp (D.sigma n) * (V n S.card r : ℝ)

/-- Sub-equatorial cap hypothesis. -/
def capHyp (D : StabilityData) (n r : ℕ) (S : Finset (Cube n)) : Prop :=
  ((neighborhood r S).card : ℝ) ≤
    Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2)

/-- Membership in the finite stability class used by R1. -/
def classMember (D : StabilityData) (n r : ℕ) (S : Finset (Cube n))
    (alpha beta : ℝ) : Prop :=
  validData D ∧
  beta = (r : ℝ) / (n : ℝ) ∧
  D.alphaMin ≤ alpha ∧ alpha ≤ D.alphaMax ∧
  D.rho * (n : ℝ) ≤ (r : ℝ) ∧
  sizeHyp D n S alpha ∧ nearOptimalHyp D n r S ∧ capHyp D n r S

/-- Quantitative stability-cover conclusion at a fixed finite dimension. -/
def stabilityCoverConclusion (n : ℕ) (S : Finset (Cube n)) (epsCover : ℝ)
    (coverSlack : ℝ) (radiusSlack : ℕ) : Prop :=
  ∃ centers : Finset (Cube n),
    ((centers.card : ℝ) ≤ Real.exp coverSlack) ∧
    (((S.card - (coveredByBalls S centers (rmin n S.card + radiusSlack)).card : ℕ)) : ℝ)
      ≤ epsCover * (S.card : ℝ)

/-- Quantitative heavy-ball conclusion at a fixed finite dimension. -/
def heavyBallConclusion (n : ℕ) (S : Finset (Cube n)) (massSlack : ℝ)
    (radiusSlack : ℕ) : Prop :=
  ∃ a : Cube n,
    Real.exp (-massSlack) * (S.card : ℝ) ≤
      ((S.filter fun x => hDist x a ≤ rmin n S.card + radiusSlack).card : ℝ)

/-- Fat+pinned+BAD data for the contradiction scheme Q. -/
structure QData where
  qMin : ℝ
  qMax : ℝ
  s0 : ℝ
  mu0 : ℝ
  sigma : ℕ → ℝ

/-- Basic compactness assumptions for Q-data (standing regularity (REG)). -/
def validQData (Q : QData) : Prop :=
  0 < Q.qMin ∧ Q.qMin ≤ Q.qMax ∧ Q.qMax < 1 / 2 ∧
  0 < Q.s0 ∧ 0 < Q.mu0 ∧ Q.qMax + Q.s0 ≤ 1 / 2 - Q.mu0 ∧
  Sublinear Q.sigma ∧
  ∀ m : ℕ, 1 ≤ m → Real.log (m : ℝ) ≤ Q.sigma m

/-- Finite FAT condition. -/
def fat (Q : QData) (m : ℕ) (A : Finset (Cube m)) (q : ℝ) : Prop :=
  A.Nonempty ∧
  validQData Q ∧
  Q.qMin ≤ q ∧ q ≤ Q.qMax ∧
  |Real.log (A.card : ℝ) - H q * (m : ℝ)| ≤ Q.sigma m

/-- Finite PINNED condition.  (The top radius is evaluated at
`q + ⌈s0 m⌉/m`, an `O(1/m)` relaxation of the prose `q + s0`; reviewed and
accepted, absorbed by the slack.) -/
def pinned (Q : QData) (m : ℕ) (A : Finset (Cube m)) (q : ℝ) : Prop :=
  ∀ r : ℕ, r ≤ Nat.ceil (Q.s0 * (m : ℝ)) →
    ((neighborhood r A).card : ℝ) ≤
      Real.exp (H (q + (r : ℝ) / (m : ℝ)) * (m : ℝ) + Q.sigma m)

/-- Finite BAD condition (nats: `e^{-η m}`; the prose `2^{-η m}` is the same
statement up to rescaling `η`). -/
def bad (m : ℕ) (A : Finset (Cube m)) (q delta eta : ℝ) : Prop :=
  ∀ a : Cube m,
    (((A.filter fun x => hDist x a ≤ Nat.ceil ((q + delta) * (m : ℝ))).card : ℕ) : ℝ)
      ≤ Real.exp (-eta * (m : ℝ)) * (A.card : ℝ)

/-- The contradiction scheme Q (uniform-`m0` form).

It is totalized over every `delta > 0`, slightly stronger than the paper's
small-`delta` use; large deltas are harmless for the downstream assembly. -/
def QuestionQ (Q : QData) : Prop :=
  ∀ delta eta : ℝ, 0 < delta → 0 < eta →
    ∃ m0 : ℕ, ∀ m ≥ m0, ∀ (A : Finset (Cube m)) (q : ℝ),
      ¬ (fat Q m A q ∧ pinned Q m A q ∧ bad m A q delta eta)

end HarperStability
