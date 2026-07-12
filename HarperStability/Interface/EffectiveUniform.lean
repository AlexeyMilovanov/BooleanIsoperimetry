import HarperStability.Interface.Effective

/-!
# Uniform effective contracts (v0.4 program: the ideal formulation)

v0.3 proves `MainFiniteEffectiveStatement`: for every valid tuple there is a
`K` with an `exp(K·(effEnv 14 σ n + 1))`-ball cover.  There `K` may still
depend on the slack FUNCTION `σ`.  This layer states the ideal form: `K`
depends ONLY on the finitely many class reals (and `epsCover`), never on
`σ` — the `∃ K` sits BEFORE the `∀ σ` quantifier, exactly as `R3Eff`
already does (v0.3.2).

Headline (`MainFiniteEffectiveUniformAt effMainGrade`):

  ∀ (class reals, epsCover), ∃ K, ∀ σ ≥ log sublinear, ∀ n, ∀ S in class:
    #balls ≤ exp(K·(effEnv 14 σ n + 1)),
    radius = rmin + ⌈K·(effEnv 14 σ n + 1)⌉.

Expected size of `K` (from the v0.3 explicit constructions):
`K ≤ C·(1 + log(1/epsCover))·(alphaMin·rho·√deltaCap)^(-C₀)` with `C, C₀`
absolute.  All v0.3 section constants are ALREADY class-only in their
proved constructions (e.g. the S4 chain uses `K_V = 30 + K₃ + 13·√(6K₃+1)`,
`K_err = 4·√(83·K_V)`, `K = 1024·K_err + 16384` with `K₃` the `R3Eff`
constant); the porting work is a binder reshuffle of the closed proofs.
The ONE genuinely new proof is the `R2U` dichotomy: the `eps(n)`-schedule
needs `eps(n) ≤ eps₀ := min(qMin-of-the-induced-class, mu0)/2`-type
admissibility; split on the grade-10 ratio
`(effEnv 10 σ n + 1)/((n:ℝ)+1) ≤ eps₀¹⁶` — in the good regime the v0.3
proof runs with class-only constants, in the bad regime four `effGeo`
steps give `effEnv 14 σ n ≥ eps₀·(n+1)`, so the TRIVIAL singleton cover
fits as soon as `K ≥ log 2 / eps₀`.

This file is HASH-FROZEN once registered: sections must adapt proofs,
never these statements.
-/

namespace HarperStability

/-- S4, uniform: the grade-5 fold-field entropy bound with `K` depending
only on the class reals. -/
def S4EffU : Prop :=
  ∀ (qMin qMax s0 mu0 : ℝ),
    0 < qMin → qMin ≤ qMax → qMax < 1 / 2 →
    0 < s0 → 0 < mu0 → qMax + s0 ≤ 1 / 2 - mu0 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (sigma : ℕ → ℝ), Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
        ∀ (eps : ℝ), 0 < eps →
          ∀ m (A : Finset (Cube m)) (q : ℝ),
            A.Nonempty →
            fat ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
            pinned ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
            ∃ o : ℝ, 0 ≤ o ∧ o < eps / 4 ∧
              uH A (binnedFoldField A (eps / 4) o) ≤
                (K / eps ^ 4) * (effEnv 5 sigma m + 1)

/-- S5, uniform: grade-8 pointwise flatness, `K` class-only. -/
def S5EffU : Prop :=
  ∀ (qMin qMax s0 mu0 : ℝ),
    0 < qMin → qMin ≤ qMax → qMax < 1 / 2 →
    0 < s0 → 0 < mu0 → qMax + s0 ≤ 1 / 2 - mu0 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (sigma : ℕ → ℝ), Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
        ∀ (eps : ℝ), 0 < eps → eps < qMin →
          ∀ m (A : Finset (Cube m)) (q : ℝ),
            A.Nonempty →
            fat ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
            pinned ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
            averageBadStepsLE A q eps
              ((K / eps ^ 4) * (effEnv 8 sigma m + 1))

/-- S6, uniform: grade-10 predictable-center entropy, `K` class-only. -/
def S6EffU : Prop :=
  ∀ (qMin qMax s0 mu0 : ℝ),
    0 < qMin → qMin ≤ qMax → qMax < 1 / 2 →
    0 < s0 → 0 < mu0 → qMax + s0 ≤ 1 / 2 - mu0 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (sigma : ℕ → ℝ), Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
        ∀ m (A : Finset (Cube m)) (q : ℝ),
          A.Nonempty →
          fat ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
          pinned ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
          uH A (predictableCenter A) ≤ K * (effEnv 10 sigma m + 1)

/-- S7, uniform: the grade-10 heavy ball, `K` class-only (with the
`K/eps^8` threshold and mass exactly as in `S7Eff`). -/
def S7EffU : Prop :=
  ∀ (qMin qMax s0 mu0 : ℝ),
    0 < qMin → qMin ≤ qMax → qMax < 1 / 2 →
    0 < s0 → 0 < mu0 → qMax + s0 ≤ 1 / 2 - mu0 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (sigma : ℕ → ℝ), Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
        ∀ (eps : ℝ), 0 < eps → eps < qMin → eps < 1 / 2 - qMax →
          ∀ m : ℕ, K / eps ^ 8 ≤ (m : ℝ) →
            ∀ (A : Finset (Cube m)) (q : ℝ),
              A.Nonempty →
              fat ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
              pinned ⟨qMin, qMax, s0, mu0, sigma⟩ m A q →
              ∃ a : Cube m,
                Real.exp (-((K / eps ^ 8) * (effEnv 10 sigma m + 1))) *
                    (A.card : ℝ) ≤
                  ((A.filter fun x =>
                    hDist x a ≤ Nat.ceil ((q + 4 * eps) * (m : ℝ))).card : ℝ)

/-- R2, uniform: the grade-14 heavy-ball lemma with `K` depending only on
the class reals of `D` (never on `D.sigma`). -/
def R2EffU : Prop :=
  ∀ (rho deltaCap cSize alphaMin alphaMax : ℝ),
    0 < rho → 0 < deltaCap → deltaCap < 1 →
    1 ≤ cSize →
    0 < alphaMin → alphaMin ≤ alphaMax → alphaMax < 1 / 2 →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (sigma : ℕ → ℝ), Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
        HBLFor ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩
          (effDegrade ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ K 14)

/-- R1a, uniform: peeling with a class-only constant. -/
def R1aEffU : Prop :=
  R2EffU →
  ∀ (rho deltaCap cSize alphaMin alphaMax epsCover : ℝ),
    0 < rho → 0 < deltaCap → deltaCap < 1 →
    1 ≤ cSize →
    0 < alphaMin → alphaMin ≤ alphaMax → alphaMax < 1 / 2 →
    0 < epsCover →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (sigma : ℕ → ℝ), Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
        CoverFor ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩
          (effDegrade ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ K 14)
          epsCover

/-- The uniform effective main statement at grade `k`. -/
def MainFiniteEffectiveUniformAt (k : ℕ) : Prop :=
  ∀ (rho deltaCap cSize alphaMin alphaMax epsCover : ℝ),
    0 < rho → 0 < deltaCap → deltaCap < 1 →
    1 ≤ cSize →
    0 < alphaMin → alphaMin ≤ alphaMax → alphaMax < 1 / 2 →
    0 < epsCover →
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (sigma : ℕ → ℝ), Sublinear sigma →
        (∀ n : ℕ, 1 ≤ n → Real.log (n : ℝ) ≤ sigma n) →
        degradedData ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩
          (effDegrade ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ K k) ∧
        CoverFor ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩
          (effDegrade ⟨rho, deltaCap, cSize, alphaMin, alphaMax, sigma⟩ K k)
          epsCover

/-- **The ideal formulation**: the uniform effective main statement at the
certified grade (`γ = 2⁻¹⁴`). -/
def MainFiniteEffectiveUniformStatement : Prop :=
  MainFiniteEffectiveUniformAt effMainGrade

end HarperStability
