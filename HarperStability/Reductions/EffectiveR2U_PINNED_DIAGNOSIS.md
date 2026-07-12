# Diagnosis: the remaining `sorry` in `HarperStability/Reductions/EffectiveR2U.lean`

There is exactly one `sorry`, the `have hpinned : pinned (r2EffUQData D C) n S alpha`
inside the **good-ratio branch** of `r2_effU` (branch `n ≥ n0`, `hgood : ratio ≤ eps0^16`).
This is the section's central hard obligation, not a leaf. This note records what the
proof needs so a future pass does not have to re-derive it.

## Why the obvious routes fail

* `r2_effU_pinned_core` / `r2_effU_downward_pinning_bound` / `r2_effU_classMember_fat_pinned`
  are **existential wrappers** over the closed non-uniform proof: the `Cdp`/`Cpin` they
  return is extracted *after* `D` (hence after `sigma`) and, through `r1_range_control`
  (its `NNonempty` comes from sublinearity of `sigma`), is genuinely **σ-dependent**.
  Lifting them to the class-only `C` via `r2_effU_pinned_mono_C` requires `Cpin' ≤ C`
  with `Cpin'` an opaque σ-dependent witness — unprovable. (A subagent run confirmed
  this: it reduced to an impossible `C ≥ Cdp`.)

## The intended (uniform) mechanism

The good-ratio hypothesis controls `sigma n`:
`hgood` + `le_effEnv` give `D.sigma n + 1 ≤ eps0^16 * ((n:ℝ)+1)`, and `eps0` is
calibrated (`eps0 ≤ (rate/(8*CG))^(1/16)`) so that `CG * eps0^16 ≤ rate/8`. Hence
`CG*(D.sigma n + 1) ≤ rate/8*((n:ℝ)+1)` and `D.sigma n ≤ rate/8*((n:ℝ)+1)`.
This makes the otherwise σ-dependent sublinear thresholds hold with **class-only**
constants, so one can re-run, at this fixed `n`, the closed peeling argument
(`r2_effU_V_upper` for the V-upper step, `V_peel_le`, then
`logsize_le_of_V_upper_large` for the log-size inversion, then the downward-pinning /
cube-bound split on `N0 ≤ n`) with class-only constants instead of `r1_range_control`.

## Constant framework is INSUFFICIENT as frozen (must be augmented)

Matching the closed `r2_eff_logsize` output slack `(L/κ+1)*(Gf + volumeSlack) + (L+2)`
against `Cw*(σ+1)` requires (with `CGv` = the `r2_effU_CG` V-upper constant):

1. `Cw`'s inner coefficient must be **`CGv + 1 + L + Ceff_BV`**, because in `r2_eff_dp_core`
   the `Gf` fed to logsize is `Gf_dp n = CGv*(σ+1) + σ + L`, so `Gf_dp/(σ+1) ≤ CGv+1+L`.
   The frozen `r2_effU_Cw = 1 + Cpre + (L/κ+1)*(CG + Ceff) + (L+2)` uses bare `CG` (= `CGv`),
   missing `+1+L`.
2. The log-size `volumeSlack` is **`effLog K_BV`** where `K_BV` comes from `hBV`
   (`BallVolumeTwoSidedEff`), a *second* interface constant. So the `Ceff` slot must be
   `Ceff_BV = r2_effU_Ceff K_BV`, **not** `r2_effU_Ceff K_IVC`. The frozen `r2_effU_Cw`
   references only `K_IVC`'s `Ceff` and has no `K_BV`-derived parameter at all.
3. `N0` (which defines `Cpre`) needs a threshold-margin term so the logsize thresholds
   `Gf_dp + volumeSlack < rate*n` hold for all `n ≥ N0` (need roughly `n > 1/2 + 2L/rate`,
   plus a similar margin for `effLog K_BV`). The frozen `N0` has no such term.

Therefore a correct fix must: extract `K_BV`/`hbv` from `hBV` before `intro sigma`;
extend `r2_effU_Cw` with a `K_BV`-derived `Ceff_BV` parameter and the `+1+L` correction;
enlarge `N0` with the threshold margins (for both `effLog K_IVC` and `effLog K_BV`);
then write the ~150–200 line class-only peeling proof. These internal `let`/`def`s are
proof-internal (the frozen statement is `R2EffU`), so they may be changed; enlarging `C`
is safe for the already-proved small-`n`, radius-absorb, S7-application, and bad-branch
parts (they use `C` only through monotone upper bounds and `1 ≤ C`, `cSize ≤ C`).

## Suggested decomposition

Extract a focused lemma placed *above* `r2_effU` (so the subagent's target is small and
its own `sorry` is isolated), e.g.

```
lemma r2_effU_pinned_good
  (D) (hvalid) (hBV) (hVPlus)
  (C_V) (hC_V) (K_IVC) (hK_IVC) (c0) (hc0 : c0 = (1/2 - D.alphaMax)/2)
  (hcalc : <IVC calc at (D.alphaMin, c0)>)
  (K_BV) (hK_BV) (hbv : <two-sided ball bound with effLog K_BV>)
  (Ceff Ceff_BV CG kappa L rate Cpre : ℝ) (N0 N0' N0'' : ℕ) (Hlb : ℝ)
  (hCeff : Ceff = r2_effU_Ceff K_IVC) (hCeffBV : Ceff_BV = r2_effU_Ceff K_BV)
  (hCG : CG = r2_effU_CG C_V D.cSize Ceff)
  (hkappa : kappa = Real.log ((1/2 + c0/2)/(1/2 - c0/2)))
  (hL : L = Real.log ((1 - D.alphaMin)/D.alphaMin))
  (hrate : rate = min (H (1/2 - c0/2) - H (1/2 - c0)) (kappa * (c0/2)))
  (hCpre : Cpre = r2_effU_Cpre (N0:ℝ) Hlb) (hN0 : N0 = <max including margins>)
  (hN0' : ∀ m, N0' ≤ m → effLog K_IVC m < rate/8 * m)
  (hN0'' : ∀ m, N0'' ≤ m → effLog K_BV m < rate/8 * m)
  (hHlb_le) (hHlb) (n r) (S) (alpha beta) (hclass) (hSne)
  (hσ1 : CG * (D.sigma n + 1) ≤ rate/8 * ((n:ℝ)+1))
  (hσ2 : D.sigma n ≤ rate/8 * ((n:ℝ)+1)) :
  pinned (r2EffUQData D <the class-only Cpin expression, using the CORRECTED Cw>) n S alpha
```

Then in `r2_effU`: extract `K_BV`, adjust the `Cw`/`N0` definitions to the corrected
forms, derive `hσ1`/`hσ2` from `hgood` + the `eps0` calibration (uses
`Real.rpow`/`Real.rpow_natCast`), and close `hpinned` with the lemma (matching
constants by `rfl`, then `r2_effU_pinned_mono_C` if the exposed constant is only a
lower bound for the final `C`).

## Note

`lake build` requires the `BooleanIsoperimetry` dependency (git `v4.28.0`), which was
absent from `.lake/packages`; fetching it restores a clean build (single `sorry`).
