# The trusted statement (for a reviewer)

This document isolates the **statement** of the main theorem and every
definition it transitively depends on, so that a reviewer can decide whether
the Lean formalization says what it should.

## Why this is enough

The proof is checked by the Lean 4 kernel. The only things a human must trust
are:

1. the Lean kernel and the three standard axioms
   `propext, Classical.choice, Quot.sound` (used throughout Mathlib), and
2. that the **statement below**, together with the short definitions it
   unfolds to, faithfully expresses the intended theorem.

There are no other axioms and no `sorry`:

```
$ lake env lean -c '#print axioms HarperStability.main_finite_skeleton'
'HarperStability.main_finite_skeleton' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Everything else — roughly 8000 Lean declarations — is machine-verified and
carries no trust.

## Plain-English statement

> Fix a "stability class": a density band `[αmin, αmax] ⊂ (0, 1/2)`, a minimal
> boundary thickness `ρ`, a sub-equatorial margin `δcap`, a size-slack
> coefficient `cSize`, and a sublinear slack function `σ` (`σ(n) = o(n)`,
> `σ ≥ log`). For every such class and every `ε > 0` there is a **sublinear**
> output slack `σ_out ≥ σ` such that:
>
> every set `S ⊆ {0,1}ⁿ` whose
> - size is `|S| ≈ exp(H(α)·n)` (within `cSize·σ(n)` in log),
> - `r`-neighbourhood is within a factor `exp(σ(n))` of the **vertex-
>   isoperimetric minimum** `V(n, |S|, r)` (Harper's optimum), with `r ≥ ρ·n`,
> - neighbourhood stays a factor `exp(δcap·n·log2)` below the whole cube,
>
> can be covered — except for an `ε`-fraction of its points — by
> `exp(σ_out(n))` Hamming balls of radius `rmin(n, |S|) + ⌈σ_out(n)⌉`.

"o(n)" here is genuine: `σ_out` is a certified sublinear function, so the ball
count `exp(σ_out(n))` is subexponential and the radius excess `⌈σ_out(n)⌉` is
`o(n)`. This coarse version states **no explicit rate**; the sharper theorems
`main_finite_effective` / `main_finite_effective_uniform` replace `σ_out` by
the explicit envelope `K·(effEnv 14 σ n + 1) ≈ K·σ^(1/16384)·n^(16383/16384)`
(and, for the uniform one, make `K` depend only on the class reals, not on `σ`).

## Where the checked theorem lives

The checked declaration and its proof term,
[`HarperStability.main_finite_skeleton`](../HarperStability/Assembly/Basic.lean),
are in `HarperStability/Assembly/Basic.lean`.  Its proposition
[`MainFiniteStatement`](../HarperStability/Interface/Statements.lean) is
defined in `HarperStability/Interface/Statements.lean`.

The public guard in
[`HarperStability/Statement.lean`](../HarperStability/Statement.lean)
restates the theorem's full outer type without hiding it behind the
`MainFiniteStatement` abbreviation.  The root module `HarperStability.lean`
imports this guard, so `lake build HarperStability` checks it.

## The theorem, verbatim

```lean
theorem main_finite_skeleton : MainFiniteStatement

def MainFiniteStatement : Prop :=
  ∀ (Din : StabilityData) (epsCover : ℝ),
    validData Din → 0 < epsCover →
    ∃ Dout : StabilityData, degradedData Din Dout ∧ CoverFor Din Dout epsCover
```

The rest of this file unfolds every name above.

---

## Layer 0 — the ambient space (from `BooleanIsoperimetry`)

A point of the Hamming cube `{0,1}ⁿ` is encoded as the set of coordinates
equal to `1`.

```lean
abbrev Cube (n : ℕ) := Finset (Fin n)

-- Hamming distance = size of the symmetric difference
noncomputable def hDist {n : ℕ} (x y : Cube n) : ℕ := (symmDiff x y).card

-- the r-neighbourhood of a set A
noncomputable def neighborhood {n : ℕ} (r : ℕ) (A : Finset (Cube n)) : Finset (Cube n) :=
  Finset.univ.filter (fun v => ∃ u ∈ A, hDist u v ≤ r)

-- the Hamming ball of radius r around a point a
noncomputable def ball {n : ℕ} (a : Cube n) (r : ℕ) : Finset (Cube n) :=
  Finset.univ.filter fun y => hDist y a ≤ r
```

## Layer 1 — the two combinatorial optima (Harper's content)

Both are honest finite minimisations — this is where "near-optimal boundary"
gets its meaning.

```lean
-- V(n,k,r): the MINIMUM possible size of the r-neighbourhood
-- over ALL k-point subsets of the cube (the vertex-isoperimetric optimum).
noncomputable def V (n k r : ℕ) : ℕ :=
  let fams := (Finset.univ : Finset (Cube n)).powerset.filter
    fun A : Finset (Cube n) => A.card = k
  let vals := fams.image fun A => (neighborhood r A).card
  if h : vals.Nonempty then vals.min' h else 0

-- rmin(n,k): the minimal radius r such that a single ball already
-- contains at least k points (the "radius of a Hamming ball of volume k").
noncomputable def rmin (n k : ℕ) : ℕ :=
  let vals := (Finset.range (n + 1)).filter fun r => k ≤ (ball (∅ : Cube n) r).card
  if h : vals.Nonempty then vals.min' h else n
```

## Layer 2 — the data of a class

```lean
structure StabilityData where
  rho      : ℝ   -- minimal boundary thickness (r ≥ rho·n)
  deltaCap : ℝ   -- sub-equatorial margin
  cSize    : ℝ   -- size-slack coefficient
  alphaMin : ℝ   -- density band lower end
  alphaMax : ℝ   -- density band upper end (< 1/2)
  sigma    : ℕ → ℝ  -- the sublinear slack function

def validData (D : StabilityData) : Prop :=
  0 < D.rho ∧ 0 < D.deltaCap ∧ D.deltaCap < 1 ∧
  1 ≤ D.cSize ∧
  0 < D.alphaMin ∧ D.alphaMin ≤ D.alphaMax ∧ D.alphaMax < 1 / 2 ∧
  Sublinear D.sigma ∧
  ∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ D.sigma n

-- s is nonnegative and s(n) = o(n)
def Sublinear (s : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ s n) ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, s n ≤ ε * (n : ℝ)

-- binary entropy, in nats
noncomputable def H (x : ℝ) : ℝ := Real.binEntropy x
```

## Layer 3 — what it means to belong to the class

```lean
-- |log|S| − H(α)·n| ≤ cSize·σ(n)   :  S has size ≈ exp(H(α)·n)
def sizeHyp (D : StabilityData) (n : ℕ) (S : Finset (Cube n)) (alpha : ℝ) : Prop :=
  |Real.log (S.card : ℝ) - H alpha * (n : ℝ)| ≤ D.cSize * D.sigma n

-- |∂_r S| ≤ exp(σ(n)) · V(n,|S|,r)  :  boundary within exp(σ) of the optimum
def nearOptimalHyp (D : StabilityData) (n r : ℕ) (S : Finset (Cube n)) : Prop :=
  ((neighborhood r S).card : ℝ) ≤ Real.exp (D.sigma n) * (V n S.card r : ℝ)

-- |∂_r S| ≤ exp((1−δcap)·n·log2)   :  boundary stays below the full cube
def capHyp (D : StabilityData) (n r : ℕ) (S : Finset (Cube n)) : Prop :=
  ((neighborhood r S).card : ℝ) ≤ Real.exp ((1 - D.deltaCap) * (n : ℝ) * Real.log 2)

def classMember (D : StabilityData) (n r : ℕ) (S : Finset (Cube n))
    (alpha beta : ℝ) : Prop :=
  validData D ∧
  beta = (r : ℝ) / (n : ℝ) ∧
  D.alphaMin ≤ alpha ∧ alpha ≤ D.alphaMax ∧
  D.rho * (n : ℝ) ≤ (r : ℝ) ∧
  sizeHyp D n S alpha ∧ nearOptimalHyp D n r S ∧ capHyp D n r S
```

## Layer 4 — the conclusion

```lean
-- points of S that lie in SOME ball of the given radius around a center
noncomputable def coveredByBalls {n : ℕ} (S centers : Finset (Cube n))
    (radius : ℕ) : Finset (Cube n) :=
  S.filter fun x => ∃ c ∈ centers, hDist x c ≤ radius

def stabilityCoverConclusion (n : ℕ) (S : Finset (Cube n)) (epsCover : ℝ)
    (coverSlack : ℝ) (radiusSlack : ℕ) : Prop :=
  ∃ centers : Finset (Cube n),
    ((centers.card : ℝ) ≤ Real.exp coverSlack) ∧
    (((S.card - (coveredByBalls S centers (rmin n S.card + radiusSlack)).card : ℕ)) : ℝ)
      ≤ epsCover * (S.card : ℝ)

-- the cover holds for EVERY member of the class, with output slack from Dout
def CoverFor (Din Dout : StabilityData) (epsCover : ℝ) : Prop :=
  ∀ {n r : ℕ} {S : Finset (Cube n)} {alpha beta : ℝ},
    classMember Din n r S alpha beta →
    stabilityCoverConclusion n S epsCover (Dout.sigma n) (Nat.ceil (Dout.sigma n))
```

So `coverSlack = σ_out(n)` (log of the number of balls) and
`radiusSlack = ⌈σ_out(n)⌉` (excess radius over the optimal `rmin`).

## Layer 5 — the "degraded output" (this is the `o(n)`)

```lean
def degradedData (Din Dout : StabilityData) : Prop :=
  validData Dout ∧
  Din.rho = Dout.rho ∧
  Din.deltaCap = Dout.deltaCap ∧
  Din.cSize ≤ Dout.cSize ∧
  Din.alphaMin = Dout.alphaMin ∧
  Din.alphaMax = Dout.alphaMax ∧
  ∀ n, Din.sigma n ≤ Dout.sigma n
```

`Dout` keeps the same class geometry (`rho, deltaCap, alphaMin, alphaMax`),
may only enlarge `cSize`, and supplies an output slack `Dout.sigma ≥ Din.sigma`
that is **still `Sublinear`** (forced by `validData Dout`). That sublinear
`Dout.sigma` is exactly the `σ_out = o(n)` of the plain statement.

---

## Semantic points that are easy to miss

- The existential `Dout` is chosen before the variables quantified in
  `CoverFor`. Thus one sublinear output slack works simultaneously for every
  `n, r, S, alpha, beta` in the class.
- When `k = S.card`, the fallback branches in `V` and `rmin` are never used:
  `S` is admissible in the definition of `V`, and a radius-`n` ball is the
  whole cube.
- `coveredByBalls` is a filter of `S`, so its cardinality is at most `S.card`;
  the natural-number subtraction in the uncovered count is therefore exact.
- Lean uses natural logarithms. A base-2 formulation is obtained by rescaling
  the slack by `log 2`; this preserves sublinearity, and the harmless ceiling
  can be absorbed into the class-only constant in the uniform theorem.

---

## What a reviewer should scrutinise

1. **The trusted base is small and elementary.** `Cube, hDist, ball,
   neighborhood, V, rmin` are a few lines of finite combinatorics; each class
   hypothesis (`sizeHyp, nearOptimalHyp, capHyp`) is a single inequality.
2. **`V` and `rmin` are true optima** (`Finset.min'` over all `k`-subsets /
   over radii), so "near-optimal boundary" is measured against the genuine
   vertex-isoperimetric minimum, not a proxy.
3. **The `o(n)` is honest**: `Sublinear` carries the `∀ε ∃N` quantifier, so
   `exp(σ_out)` balls of radius `rmin + o(n)` is genuinely subexponential with
   near-optimal radius. This version asserts existence of such a `σ_out` but
   **no rate** — that is what the effective/uniform versions add.
4. **Quantifier order**: `∃ Dout` sits *after* `∀ Din, ε`, so the output may
   depend on the whole input. For the coarse statement this is expected; the
   uniform theorem tightens it (`∃ K` before `∀ σ`, `K` class-reals-only).

## Reproduce the axiom check

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake env lean <<'EOF'
import HarperStability.Assembly
#print axioms HarperStability.main_finite_skeleton
#print axioms HarperStability.main_finite_effective_uniform
EOF
```

Both report `[propext, Classical.choice, Quot.sound]` and nothing else.

## The two sharper statements (same layers, only Layers 4–5 change)

- `main_finite_effective : MainFiniteEffectiveStatement` — replaces the opaque
  `Dout` by `effDegrade Din K 14`, i.e. `σ_out(n) = K·(effEnv 14 σ n + 1)`,
  an explicit envelope `≈ K·σ^(1/16384)·n^(16383/16384)`. Here `∃ K` sits
  after `Din`, so `K` may depend on `σ`.
- `main_finite_effective_uniform : MainFiniteEffectiveUniformStatement` — the
  same explicit envelope, but `∃ K` is hoisted *before* `∀ σ`, so a single `K`
  depends only on the class reals `(rho, deltaCap, cSize, alphaMin, alphaMax)`
  and `epsCover` — never on the slack function `σ`.

The bridges `main_finite_via_effective` and `main_finite_effective_of_uniform`
are machine-checked proofs that the sharper statements imply the coarser ones,
so all three are mutually consistent.
