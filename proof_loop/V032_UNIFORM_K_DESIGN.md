# v0.3.2 design note: sigma-uniform K (draft, apply AFTER the v0.3.1 wave closes)

Goal: in every effective contract move `exists K` BEFORE the slack
function sigma, so that K depends ONLY on the finitely many class
reals (+ epsCover), never on sigma as a function.  Final headline:

  forall (class reals, eps) exists K forall sigma >= log
    forall n, forall S in class(sigma, n):
      #balls <= exp(K*(effEnv 13 sigma n + 1)),
      radius = rmin + ceil(K*(effEnv 13 sigma n + 1)).

Estimated K (from the v0.3.1 explicit constants):
  K <= C * (1 + log(1/epsCover)) * (alphaMin * rho * sqrt(deltaCap))^(-C0),
  C, C0 absolute (C0 <= ~10 with current padding).

## Contract surgery

QData bundles sigma inside the structure, so the uniform statements
quantify the compact part separately, e.g. R3Eff becomes:

  forall qMin qMax s0 mu0, [REG] -> forall pLow, ... ->
    exists K >= 1, forall sigma, (Sublinear sigma) -> (log <= sigma) ->
      forall m A q, fat {qMin,qMax,s0,mu0,sigma} m A q -> pinned ... ->
        blockRegular m A q pLow (K * (effEnv 2 sigma m + 1))

Same reshaping for S4Eff (K/eps^4), S5Eff (K/eps^4), S6Eff, S7Eff
(K/eps^8 + threshold), R2Eff, R1aEff, MainFiniteEffectiveAt.

## The one real proof change: R2 dichotomy AT GRADE 9

Schedule eps(n) = ((effEnv 9 sigma n + 1)/((n:R)+1))^(1/16) needs
eps(n) <= eps0 := min(qMin, mu0)/2.  Do NOT convert this to a
sigma/n-threshold (that costs K >= (1/eps0)^8192).  Instead split on
the GRADE-9 ratio:

  * if (effEnv 9 sigma n + 1)/((n:R)+1) <= eps0^16: schedule admissible,
    pipeline runs, all constants class-only;
  * else: four effGeo steps give effEnv 13 sigma n >= eps0 * (n+1)
    (each sqrt halves the deficit: eps0^16 -> eps0^8 -> eps0^4 ->
    eps0^2 -> eps0), so the TRIVIAL singleton cover fits:
    |S| <= 2^n <= exp(K * eps0 * n) <= exp(K*(effEnv 13 sigma n + 1))
    for K >= log 2 / eps0.  Radius slack is free (any radius >= 0).

All other sections: the v0.3.1 proofs are the port templates; their K
are already class-only in the natural construction.  Porting = binder
reshuffle + (for small-n absorption) using the "+1" of the envelope
with K >= N0(class reals) * log 2 - never a sigma-dependent N0.

## Order of work (after v0.3.1 closes)

1. Rewrite Interface/Effective.lean (v0.3.2), re-freeze hash.
2. Port sections in dependency order E1,E2 (almost no change),
   E3-E6 (binder reshuffle over the v0.3.1 files as drafts),
   E7 (grade-9 dichotomy - the one substantive edit), E8, E9.
3. Delete ALL section worktrees before relaunching (prepare_worktree
   never refreshes).
