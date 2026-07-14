import Mathlib
import BooleanIsoperimetry

open scoped BigOperators Topology
open Filter Finset Set

/-!
# Frozen definitions for combinatorial average-Harper stability

All entropies use natural logarithms. Thus `exp (eps * n)` below is the
same subexponential-cover shape as `2^(eps₂ * n)`, after rescaling eps.
The finite probability laws are represented by their mass functions; the
predicate `IsLaw` records nonnegativity and total mass one.
-/

namespace AverageHarperStability

attribute [local instance] Classical.propDecidable

/-- A nonnegative mass function of total mass one on the Boolean cube. -/
def IsLaw {n : ℕ} (mu : Cube n → ℝ) : Prop :=
  (∀ x, 0 ≤ mu x) ∧ ∑ x, mu x = 1

/-- Entropy in nats of a finite mass function. -/
noncomputable def entropy {n : ℕ} (mu : Cube n → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (mu x)

/-- Mass of an event under a finite mass function. -/
noncomputable def eventMass {n : ℕ} (mu : Cube n → ℝ)
    (E : Cube n → Prop) : ℝ :=
  ∑ x, if E x then mu x else 0

/-- Pushforward mass of a deterministic cube-valued label. -/
noncomputable def mapMass {n : ℕ} (mu : Cube n → ℝ)
    (D : Cube n → Cube n) (d : Cube n) : ℝ :=
  ∑ x, if D x = d then mu x else 0

/-- The uniform mass on a finite family, totalized at the empty family. -/
noncomputable def uniformMass {n : ℕ} (A : Finset (Cube n)) (x : Cube n) : ℝ :=
  if x ∈ A then 1 / (A.card : ℝ) else 0

/-- Probability of moving from `x` to `y` through a BSC(tau). -/
noncomputable def noiseKernel {n : ℕ} (tau : ℝ) (x y : Cube n) : ℝ :=
  tau ^ hDist x y * (1 - tau) ^ (n - hDist x y)

/-- Output mass after independent coordinate noise with crossover `tau`. -/
noncomputable def noiseMass {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (y : Cube n) : ℝ :=
  ∑ x, mu x * noiseKernel tau x y

/-- Binary entropy in nats. -/
noncomputable def Hb (p : ℝ) : ℝ := Real.binEntropy p

/-- Lower-branch inverse of binary entropy, defined by monotone inversion. -/
noncomputable def hbInv (u : ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Icc (0 : ℝ) (1 / 2) ∧ u ≤ Hb p}

/-- Mrs-Gerber curve in nats. -/
noncomputable def mglCurve (tau u : ℝ) : ℝ :=
  Hb (tau + (1 - 2 * tau) * hbInv u)

/-- Entropy rate of a law in dimension `n`. -/
noncomputable def entropyRate (n : ℕ) (mu : Cube n → ℝ) : ℝ :=
  entropy mu / (n : ℝ)

/-- Entropy rate of the uniform law on a nonempty family. -/
noncomputable def setEntropyRate (n : ℕ) (A : Finset (Cube n)) : ℝ :=
  Real.log (A.card : ℝ) / (n : ℝ)

/-- Points of `A` covered by real-radius Hamming balls around `centers`. -/
noncomputable def coveredByBalls {n : ℕ} (A centers : Finset (Cube n))
    (radius : ℝ) : Finset (Cube n) :=
  A.filter fun x => ∃ c ∈ centers, (hDist x c : ℝ) ≤ radius

/-- Quantitative finite cover conclusion used by the headline theorem. -/
def coverConclusion {n : ℕ} (A : Finset (Cube n)) (eps radius : ℝ) : Prop :=
  ∃ centers : Finset (Cube n),
    (centers.card : ℝ) ≤ Real.exp (eps * (n : ℝ)) ∧
    ((A \ coveredByBalls A centers radius).card : ℝ) ≤ eps * (A.card : ℝ)

/-- The finite corrected Corollary-10 conclusion. The `sqrt(log n/n)` and
`1/n` terms are deliberately explicit; deleting them makes the statement
false even for an exact Bernoulli cloud at finite `n`. -/
def distributionStabilityConclusion {n : ℕ} (err : ℝ) (mu : Cube n → ℝ) : Prop :=
  let u := entropyRate n mu
  let p := hbInv u
  ∃ D : Cube n → Cube n,
    entropy (mapMass mu D) ≤ err * (n : ℝ) ∧
    eventMass mu (fun x =>
      (p + err + Real.sqrt (2 * Real.log (n : ℝ) / (n : ℝ))) * (n : ℝ) <
        (hDist x (D x) : ℝ)) ≤ err + 1 / (n : ℝ)

end AverageHarperStability
