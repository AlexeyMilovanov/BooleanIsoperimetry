import HarperStability.Core.Basic

/-!
# S5 leaf: the KL tilt inequality

`s5_kl_tilt` is the quantitative "conditioning bends branchings only
slightly" step of the S5 (pointwise flatness) proof — paper Section S5,
step *KL tilt*.  It is a fully general **finite** inequality about a
nonempty subset `Af ⊆ A` of the cube: the total (over coordinates)
average distance between the prefix branching probabilities of `Af` and
of `A` is controlled by the log mass ratio `log(|A|/|Af|)`.

## Proof route (all finite, no asymptotics)

1. **Trajectory factorization.**  For a nonempty `S : Finset (Cube m)`
   and `x ∈ S`, the uniform probability `1/|S|` factorizes EXACTLY
   through the prefix tree: writing `w t := proj (below univ t) x`,
   `1/|S| = ∏ t, P_S(coord t = coord t x | prefix = w t)`, where the
   factor is `rho S t (w t)` if `t ∈ x` and `1 - rho S t (w t)`
   otherwise.  This is a telescoping product of prefix-fiber
   cardinality ratios `|fiber_{t+1}(x)| / |fiber_t(x)|` (fibers of `x`
   in `S` under `proj (below univ ·)`), provable by induction on the
   coordinate with `Finset.card` bookkeeping; `proj univ` separates
   points, so the final fiber is `{x}`.
2. **Exact chain rule for KL.**  Consequently
   `Real.log ((A.card : ℝ) / (Af.card : ℝ))
      = ∑ t, uE Af (fun x => klBern (rho Af t (w t)) (rho A t (w t)))`
   where `klBern a b := a * log (a/b) + (1-a) * log ((1-a)/(1-b))`
   (with `0 * log _ = 0` conventions).  Absolute continuity is
   structural: `Af ⊆ A`, so on realized prefixes `rho A ... = 0`
   (resp. `= 1`) forces `rho Af ... = 0` (resp. `= 1`) and no infinite
   terms appear.
3. **Bernoulli Pinsker:** `2 * (a - b)^2 ≤ klBern a b` for
   `a, b ∈ [0,1]` (one-variable calculus: for fixed `a`, the function
   `b ↦ klBern a b - 2*(a-b)^2` has derivative
   `(b-a) * (1/(b*(1-b)) - 4)`, which is `≥ 0` for `b ≥ a` and `≤ 0`
   for `b ≤ a` since `b*(1-b) ≤ 1/4`; the minimum value `0` is at
   `b = a`).  Hence `|a - b| ≤ Real.sqrt (klBern a b / 2)`.
4. **Jensen for `Real.sqrt`** (concavity) on the finite average `uE Af`
   per coordinate, then **Cauchy–Schwarz over the `m` coordinates**:
   `∑ t, Real.sqrt (k t) ≤ Real.sqrt ((m : ℝ) * ∑ t, k t)`
   (square both sides and use `Finset.sq_sum_le_card_mul_sum_sq`, or
   `Finset.inner_mul_le_norm_mul_norm` with the all-ones vector).

Combining: `∑ t, uE Af |Δ t| ≤ ∑ t, Real.sqrt (uE Af (klBern ·) / 2)
  ≤ Real.sqrt ((m : ℝ) * (∑ t, uE Af (klBern ·)) / 2)
  = Real.sqrt ((m : ℝ) * Real.log ((A.card : ℝ)/(Af.card : ℝ)) / 2)`.

## Conventions

`pOn` (hence `rho`) is totalized to `0` on empty fibers; for `x ∈ Af`
every prefix fiber of `x` in `Af` (hence in `A ⊇ Af`) is nonempty, so
all quantities are honest conditional probabilities.

Instance gotcha (STATUS.md): `uH`/`pOn` are defined under
`Classical.propDecidable`; proofs must use instance-robust steps
(`simp only [Finset.mem_filter, ...]`, element-wise subset arguments),
not `rw`/`exact` with ambient `DecidableEq` instances.
-/

namespace HarperStability

/-- **KL tilt.**  Conditioning the uniform law on `A` to a nonempty
subset `Af ⊆ A` moves the prefix branching probabilities, in total
average `ℓ¹` over the `m` coordinates, by at most
`sqrt (m * log(|A|/|Af|) / 2)`. -/
lemma s5_kl_tilt {m : ℕ} (A Af : Finset (Cube m)) (hsub : Af ⊆ A)
    (hne : Af.Nonempty) :
    (∑ t : Fin m,
        uE Af (fun x =>
          |rho Af t (proj (below (Finset.univ : Finset (Fin m)) t) x) -
            rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)|)) ≤
      Real.sqrt ((m : ℝ) * Real.log ((A.card : ℝ) / (Af.card : ℝ)) / 2) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (kl_tilt_l1_bound A Af hsub hne)

end HarperStability
