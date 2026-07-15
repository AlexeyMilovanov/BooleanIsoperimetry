import Mathlib

open Finset

/-!
# Trusted Comparator challenge: robust Harper stability

This file is the complete human-trusted Lean statement for the coarse
`o(n)` version of robust Harper stability.  It deliberately imports only
Mathlib.  The definitions below are copied verbatim from the project interface
and from the pinned Boolean-isoperimetry dependency.

The proof is intentionally a `sorry`: Comparator checks that `Solution.lean`
proves this exact statement, with these exact definitions, using only the
permitted axioms in `config.json`.
-/

-- Boolean-cube geometry, copied from BooleanIsoperimetry/Cube.lean.
abbrev Cube (n : ℕ) := Finset (Fin n)

noncomputable def hDist {n : ℕ} (x y : Cube n) : ℕ :=
  (symmDiff x y).card

noncomputable def neighborhood {n : ℕ} (r : ℕ)
    (A : Finset (Cube n)) : Finset (Cube n) :=
  Finset.univ.filter (fun v => ∃ u ∈ A, hDist u v ≤ r)

namespace HarperStability

attribute [local instance] Classical.propDecidable

/-!
The full project interface first elaborates the real numeral `2` inside
`predictableCenter`.  Lean gives the resulting (trivial) `AtLeastTwo`
certificate the generated name below and reuses it in later declarations.
The standalone challenge names the same certificate explicitly so that the
trusted definitions have exactly the same elaborated terms, independently of
the omitted proof-internal definitions.
-/
theorem predictableCenter._proof_1 : Nat.AtLeastTwo (1 + 1) :=
  Nat.instAtLeastTwoHAddOfNat 1

attribute [local instance] predictableCenter._proof_1

noncomputable def ball {n : ℕ} (a : Cube n) (r : ℕ) : Finset (Cube n) :=
  Finset.univ.filter fun y => hDist y a ≤ r

noncomputable def V (n k r : ℕ) : ℕ :=
  let fams := (Finset.univ : Finset (Cube n)).powerset.filter
    fun A : Finset (Cube n) => A.card = k
  let vals := fams.image fun A => (neighborhood r A).card
  if h : vals.Nonempty then vals.min' h else 0

noncomputable def rmin (n k : ℕ) : ℕ :=
  let vals := (Finset.range (n + 1)).filter fun r =>
    k ≤ (ball (∅ : Cube n) r).card
  if h : vals.Nonempty then vals.min' h else n

noncomputable def coveredByBalls {n : ℕ} (S centers : Finset (Cube n))
    (radius : ℕ) : Finset (Cube n) :=
  S.filter fun x => ∃ c ∈ centers, hDist x c ≤ radius

noncomputable def H (x : ℝ) : ℝ :=
  Real.binEntropy x

def Sublinear (s : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ s n) ∧
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, s n ≤ ε * (n : ℝ)

structure StabilityData where
  rho : ℝ
  deltaCap : ℝ
  cSize : ℝ
  alphaMin : ℝ
  alphaMax : ℝ
  sigma : ℕ → ℝ

def validData (D : StabilityData) : Prop :=
  0 < D.rho ∧ 0 < D.deltaCap ∧ D.deltaCap < 1 ∧
  1 ≤ D.cSize ∧
  0 < D.alphaMin ∧ D.alphaMin ≤ D.alphaMax ∧ D.alphaMax < 1 / 2 ∧
  Sublinear D.sigma ∧
  ∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ D.sigma n

def degradedData (Din Dout : StabilityData) : Prop :=
  validData Dout ∧
  Din.rho = Dout.rho ∧
  Din.deltaCap = Dout.deltaCap ∧
  Din.cSize ≤ Dout.cSize ∧
  Din.alphaMin = Dout.alphaMin ∧
  Din.alphaMax = Dout.alphaMax ∧
  ∀ n, Din.sigma n ≤ Dout.sigma n

def sizeHyp (D : StabilityData) (n : ℕ) (S : Finset (Cube n))
    (alpha : ℝ) : Prop :=
  |Real.log (S.card : ℝ) - H alpha * (n : ℝ)| ≤ D.cSize * D.sigma n

def nearOptimalHyp (D : StabilityData) (n r : ℕ)
    (S : Finset (Cube n)) : Prop :=
  ((neighborhood r S).card : ℝ) ≤
    Real.exp (D.sigma n) * (V n S.card r : ℝ)

def capHyp (D : StabilityData) (n r : ℕ) (S : Finset (Cube n)) : Prop :=
  ((neighborhood r S).card : ℝ) ≤
    Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2)

def classMember (D : StabilityData) (n r : ℕ) (S : Finset (Cube n))
    (alpha beta : ℝ) : Prop :=
  validData D ∧
  beta = (r : ℝ) / (n : ℝ) ∧
  D.alphaMin ≤ alpha ∧ alpha ≤ D.alphaMax ∧
  D.rho * (n : ℝ) ≤ (r : ℝ) ∧
  sizeHyp D n S alpha ∧ nearOptimalHyp D n r S ∧ capHyp D n r S

def stabilityCoverConclusion (n : ℕ) (S : Finset (Cube n))
    (epsCover : ℝ) (coverSlack : ℝ) (radiusSlack : ℕ) : Prop :=
  ∃ centers : Finset (Cube n),
    ((centers.card : ℝ) ≤ Real.exp coverSlack) ∧
    (((S.card -
      (coveredByBalls S centers (rmin n S.card + radiusSlack)).card : ℕ)) : ℝ)
      ≤ epsCover * (S.card : ℝ)

def CoverFor (Din Dout : StabilityData) (epsCover : ℝ) : Prop :=
  ∀ {n r : ℕ} {S : Finset (Cube n)} {alpha beta : ℝ},
    classMember Din n r S alpha beta →
    stabilityCoverConclusion n S epsCover (Dout.sigma n)
      (Nat.ceil (Dout.sigma n))

def MainFiniteStatement : Prop :=
  ∀ (Din : StabilityData) (epsCover : ℝ),
    validData Din → 0 < epsCover →
    ∃ Dout : StabilityData, degradedData Din Dout ∧
      CoverFor Din Dout epsCover

end HarperStability

/-- The trusted robust Harper-stability challenge. -/
theorem robust_harper_stability : HarperStability.MainFiniteStatement := by
  sorry
