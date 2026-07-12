# v0.3 EFFECTIVE PROGRAM OPEN (2026-07-10)

## 2026-07-10 v0.3.1 contract repair (eps-uniformity; grade 10 -> 13)

E7 (R2Eff) was UNPROVABLE as frozen: S7Eff said forall eps exists K -
no control of K(eps) as eps -> 0 - while R2 needs a decaying schedule
eps(n) (fixed eps gives a LINEAR radius excess 4 eps n).  Found by the
E7 codex stage (STATUS: INTERFACE_PROBLEM) and confirmed by hand; a
second, arithmetic defect: even with uniformity, grade 10 was too
tight for the schedule.

Repair (operator, under stopped loops E3-E9; Aristotle tasks canceled
manually by the operator):
1. Interface/Effective.lean (re-frozen, new hash): S4Eff/S5Eff/S7Eff
   now UNIFORM in eps - one exists-K before forall-eps with explicit
   K/eps^4 (S4, S5; true chain dependence ~1/eps^3) resp. K/eps^8
   (S7; true ~1/eps^6); S7 threshold K/eps^8 <= m.  R2Eff/R1aEff and
   effMainGrade: grade 10 -> 13.  Final bound now
   sigma_out = K*(effEnv 13 sigma + 1) ~ K*sigma^(1/8192)*n^(8191/8192).
   The R2 schedule is sqrt-representable:
   eps(n) = ((effEnv 9 sigma n + 1)/(n+1))^(1/16) (four nested sqrt);
   radius excess lands exactly on grade 13, mass slack on grade 10.
2. The proved bridge (mainFinite_of_effective, forall k) and the
   toolkit are unchanged.
3. E4 bonus: iteration 1 had ALREADY CLOSED s5_eff against the old
   contract (codex, 0 sorries); the file is saved at
   E4_s5_eff/EffectiveS5_draft_iter001_closed_old_contract.lean and the
   section notes point to it - porting to the uniform contract is
   mostly quantifier re-ordering.
4. Stale worktrees of E3-E9 deleted (prepare_worktree never refreshes);
   loops relaunched at --start-iteration 2.  E1/E2 untouched (their
   contracts did not change).

Build green (8076 jobs), audit rc=0, hashes OK (Effective.lean line
updated).



Goal: make the o(n) main theorem a corollary of an EXPLICIT bound.
New hash-frozen contract layer Interface/Effective.lean: the graded
majorant effGeo s n = max (s n) (sqrt((s n + 1)(n+1))), its iterates
effEnv k (so effEnv k sigma ~ sigma^(2^-k) n^(1-2^-k)), and effective
statements BallVolumeTwoSidedEff/InteriorVolumeCalculusEff (log slack),
R3Eff (grade 2), S4Eff (4), S5Eff (7), S6Eff (8), S7Eff (9, threshold
folded into K), R2Eff (10), R1aEff (10), MainFiniteEffectiveAt k;
MainFiniteEffectiveStatement = grade 10, i.e.
sigma_out = K*(effEnv 10 sigma + 1) ~ K*sigma^(1/1024)*n^(1023/1024).
Grades are deliberately padded (provability first); tightening gamma
later = one-line contract edits + re-running affected sections.

PROVED already (Assembly/Effective.lean): the toolkit
(effGeo_scale/effEnv_comp/effEnv_sublinear), effDegrade_degraded, and
THE BRIDGE mainFinite_of_effective : forall k, MainFiniteEffectiveAt k
-> MainFiniteStatement.  So once main_finite_effective is closed, the
frozen o(n) theorem is formally a corollary of the precise bound
(main_finite_via_effective).

The v0.2 zero-sorry proof (main_finite_skeleton) is UNTOUCHED and
still axiom-clean.  New sorries (10) live only in the new Effective
files; audit passes in non-strict mode (STRICT is expected to fail
until the v0.3 sections close).

Sections launched 2026-07-10: E1_volume_eff (2 targets), E2_r3_eff,
E3_s4_eff, E4_s5_eff, E5_s6_eff, E6_s7_eff, E7_r2_eff (riskiest:
explicit delta/eta/eps schedules replacing the diagonal), E8_r1a_eff,
E9_assembly_eff.  .interface.sha256 now also freezes
Interface/Effective.lean.

# ZERO SORRIES - FORMALIZATION COMPLETE (2026-07-10)

As of 2026-07-10 ~09:00 UTC the project has ZERO sorry across all of
HarperStability.  STRICT audit (STRICT_NO_SORRY=1 STRICT_AXIOMS=1
scripts/audit.sh) passes: build green, import boundaries clean,
interface hashes intact (Definitions/Statements frozen at v0.2),
and every audited theorem - including

  theorem main_finite_skeleton : MainFiniteStatement

- depends only on [propext, Classical.choice, Quot.sound].
The finite Harper vertex-isoperimetric stability theorem is fully
machine-verified.

Final closing sequence (all merge-gate ACCEPTED):
P5c1 KL tilt 6->5, P5c2 entropy transfer 5->4, P5a2 bad-window
Chebyshev 4->3, P5c3 same-bin separation 3->2, P3b r3_fiber_growth_V
2->1, P5c4 S5 glue 1->0.  All until-zero-sorries loops exited on their
own.  Zero-sorry tree snapshot:
~/harper-stability-lean-backups/harper-stability-lean-ZERO-SORRY-20260710T090035Z.tar.gz

# Formalization Status

Date: 2026-07-08 (updated after the fable interface-repair pass).

## Stage

`PROOF`: interface frozen at v0.2; worker proofs in progress.
Current sorry map (2026-07-08, after the manual Aristotle-P2 merge below):
Volume 0, Entropy 0, Assembly 0; Process 2 (`window_entropy_expectation`,
`S4_skeleton`); Reductions 3 (R1a/R2/R3); Core 3 (S5/S6/S7). Total 8.

Build (verified on the VM, 2026-07-08):

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build HarperStability   # exit 0; 8 expected `sorry` warnings
bash scripts/audit.sh        # hashes OK, boundaries OK, axioms clean
```

## 2026-07-09 Manual merge of Aristotle P5a iter-2 (S6 estimator closed)

The P5a iteration-2 Aristotle result closed BOTH S6Estimator leaves
(center_majority_error_le_twoCluster and s6_expectedEstimatorError_le,
0 sorries in its file), but the merge gate REJECTED it (audit_failed):
Aristotle changed the signature of s6_expectedEstimatorError_le -
three new defensive hypotheses (A.Nonempty, 0 <= varianceSlack,
0 <= massSlack; the old statement was false for empty A with negative
slacks) - AND replaced the closed-form Hoeffding tail
m*exp(-2(p-pLow)^2 m) in the conclusion by the exact deferred sum
(4/gap^2)*((m/p)*sum of windowProb over windows outside
[pLow*m,(1-pLow)*m]).  The gate only merges S6Estimator.lean, so the
call site and s6_errorBound in S6.lean (P5b file) mismatched.

Manual reconciliation (operator; backups in
~/harper-stability-lean-backups/20260709T-fable-p5a-iter2-manual-merge/,
done under the merge-gate flock):

1. S6Estimator.lean replaced by the Aristotle iter-2 version verbatim.
2. S6.lean rewired to the new contract: s6_errorBound third term is now
   the exact bad-window sum; call site passes the three new hypotheses;
   s6_errorBound_sublinear bounds the tail via the NEW leaf
   s6_badWindow_mass_le by the m-independent constant 16/(gap^2 p^2)
   (core_Sublinear_of_le + const).  KEY DESIGN POINT: the p->0
   diagonalization (s6_sublinear_diagonalize) only needs per-fixed-p
   sublinearity, so a CHEBYSHEV bound O(1/m) on the bad-window mass
   suffices - no Hoeffding/Chernoff is needed anywhere in S6.
3. New file Core/S6Window.lean with the single new sorry
   s6_badWindow_mass_le (binomial Chebyshev: marginal identities via
   insert-bijection/prod_add, second moment = m p (1-p), Markov;
   full route in the docstring).  Net sorries: -2 +1.
4. New section P5a2_core_s6_window owns Core/S6Window.lean.
   P5a_core_s6_estimator is DONE (its file has 0 sorries); its paused
   iteration 3 is now redundant - if resumed and its gate fires, the
   audit will reject any stale-signature candidate, so it is safe, but
   the cleanest action is to stop/retire the P5a loop.

Full audit.sh PASSED (8066 jobs; boundaries, hashes, axioms clean).
Sorry map: Reductions 1 (r3_fiber_growth_V_bound); Core 6
(S5KL, S5Transfer, S5Separation, S5 glue, S6Window); S6Estimator 0.

## 2026-07-09 Fable S5 decomposition (replacing the false heavy-atom leaf)

The single remaining S5 sorry (s5_heavy_atom_bad_bins_bound, bounding
deviant bins of a heavy atom by the old s5_atomSlack built only from
sigma+env) was UNPROVABLE as stated: a planted fair coordinate
({0,1} x B product) gives a heavy atom with a deviant bin at zero
entropy/mass cost, and with a separating bin field every singleton
counts as heavy (numerically refuted; see the operator session).  The
paper proof (Section S5) is sound; the Lean statement had dropped the
R3-on-atoms slack and freed env.

Surgery (operator, backups in
~/harper-stability-lean-backups/20260709T-fable-s5-decomposition/, done
under the merge-gate flock; P5c paused beforehand):

1. New leaf files, one sorry each, all with proof-route docstrings:
   - Core/S5KL.lean: s5_kl_tilt - exact KL chain rule along the prefix
     filtration + Bernoulli Pinsker + Jensen + Cauchy-Schwarz;
     sum_t E_Af |rho_Af - rho_A| <= sqrt(m log(|A|/|Af|) / 2).
   - Core/S5Transfer.lean: s5_step_entropy_transfer - per-coordinate
     |E H(rho_A) - E H(rho_Af)| <= 2 sqrt(E|Delta|) (modulus
     |H a - H b| <= H|a-b| + Jensen + H y <= 2 sqrt y).
   - Core/S5Separation.lean: s5_same_bin_separation - one-sided
     same-bin separation with the explicit class constant
     eps*mu0/2 (plus s5_fold_pinned_in_bin moved here verbatim).
2. Core/S5.lean rewired: new s5_atomQ (heavy-atom QData with slack
   sigma + G1), s5_atomSigmaStar (R3 slack for that class at
   pLow = 1/6, via the existing s5_sFam extractor), s5_sepCoeff, and
   s5_atomSlack now = sepCoeff*(G2 + atomSigmaStar + base + G1 + 1) + 40.
   The lemma statement of s5_heavy_atom_bad_bins_bound is unchanged
   textually but now TRUE (its docstring carries the full assembly
   recipe; hS1 is consumed there via S1-on-the-atom).  All previously
   proved plumbing (combiner, massSlack, S5_skeleton) compiles
   unchanged; only two nonneg-sites were repointed to
   s5_atomSlack_nonneg.
3. Sorry map after the surgery: Reductions 1 (r3_fiber_growth_V_bound),
   S6Estimator 2, S5 4 (s5_kl_tilt, s5_step_entropy_transfer,
   s5_same_bin_separation, s5_heavy_atom_bad_bins_bound; the glue lemma
   is the only one allowed to cite the other three).  Full audit.sh
   PASSED (8065 jobs; boundaries, hashes, axioms clean).
4. P5c_core_s5_atom is retired (paused); four new sections own one
   sorry each: P5c1_core_s5_kl, P5c2_core_s5_transfer,
   P5c3_core_s5_separation, P5c4_core_s5_glue.

## 2026-07-09 Manual merge of Aristotle P3b iter-4 (R3 entropy-gap Lipschitz)

The P3b iteration-4 Aristotle result closed r3_entropy_gap_lipschitz in
Reductions/R3Fiber.lean, but the merge gate REJECTED it (audit_failed) for a
visibility mismatch, not math: the proof calls binEntropy_chord_upper from
Reductions/Basic.lean, where Aristotle had removed private in its own
checkout; the gate copies only section files, so the main tree kept the lemma
private -> Unknown identifier at R3Fiber.lean:392.

Manual reconciliation (operator-requested, backups in
~/harper-stability-lean-backups/20260709T-fable-p3b-iter4-manual-merge/),
done under the merge-gate flock while the P5a/P5c loops were live:
1. Reductions/Basic.lean: removed private on binEntropy_chord_upper
   (one-line change; interface hash untouched - only Interface/ is frozen).
2. Reductions/R3Fiber.lean: replaced by the Aristotle iter-4 version.
Full scripts/audit.sh PASSED (8062 jobs; boundaries, hashes, axioms clean).

Sorry map after the merge: Reductions 1 (r3_fiber_growth_V_bound),
Core 3 (S5 x1, S6Estimator x2). Total 4, plus 1 in the dead scratch file
Reductions/scratch_upper.lean (imported nowhere). P3b remaining leaf is
r3_fiber_growth_V_bound; the paused iter-5 strategy pass has a 3-iteration
plan for it (r3_theta_floor_bounds, r3_vplus_volume_ratio_lower, assembly).

## 2026-07-09 Fable P3 decomposition merge (Reductions)

P3 was paused after its Codex pass; the iter-3 worktree (never gated) was
extended by a manual decomposition pass and merged under the gate lock
(backup: `~/harper-stability-lean-backups/20260709T-fable-p3-decomposition/`).
Reductions sorries went from 5 opaque ones to 7 SMALLER leaves, with these
now PROVED: `r1a_subset_nearOptimalHyp` (full assembly: range control + two
volume-calculus applications + finite-prefix bump), `r2_downward_pinning`
(equator branch; core isolated), `r3_cond_entropy_bound` (two-sided, via the
new exact identity `uCondH_eq_expected_log_fiber` = expected log fiber size,
`uH_of_injOn_eq_log_card`, subadditivity, and `r3_fiber_log_lower` applied to
both `I` and `Iᶜ` — NO dense-fiber cap needed), plus helpers
(`sublinear_const/const_mul/indicator_prefix`, `card_le_V`,
`cube_card_le_two_pow`, `binEntropy_le_log_two_sub_two_sq` from the strong
concavity fact).  The old `r3_sparse_fibers_light` (uniform `c·ζ` form, not
provable for small `ζ` by the growth argument) was REPLACED by
`r3_fiber_log_lower` (expected-log form; the internal Markov argument gives
`ζ²`-type exponents, absorbed by the diagonal).

Remaining Reductions leaves (all with proof-route docstrings):
1. `binEntropy_chord_lower` / `binEntropy_chord_upper` — textbook chord
   bounds via `Real.hasDerivAt_binEntropy`; ideal Aristotle bites.
2. `r1_range_control` — cap + `V+` + ball volume + the quadratic gap force
   `alpha + beta ≤ 1/2 - c0` for large `n`.
3. `r2_dp_core` — sub-equatorial downward pinning (chained neighborhoods +
   `V+` growth from the enlarged base + chords).
4. `sublinear_diag_envelope` — self-contained diagonalization helper.
5. `r2_hbl_from_q_and_dp` — QData construction + diagonal + `hVC` at `r := 0`
   for the `rmin` conversion (signature now includes the volume statements).
6. `r3_fiber_log_lower` — per-fiber Harper growth through the fiber
   embedding + `r3_fiber_transfer` + pinned + Markov + diagonal.

Instance gotcha for future workers: `uH`/`pOn` are defined under
`Classical.propDecidable`, so proofs that `unfold` them must use
instance-robust steps (`simp only [mem_filter/mem_image/...]`,
element-wise subset proofs) — `rw`/`exact` with ambient
`Finset.decidableEq` terms fails with instance-mismatch errors.

## 2026-07-08 Manual merge of the Aristotle P2 (Entropy) result

The Aristotle run 059d3961 (submitted from
`proof_loop_runs/20260708T142037Z-proof-until-zero-gemini-fixed/P2_entropy_probability/iter_001_proof`)
closed ALL Entropy sorries but returned after the loop had stopped, and the
merge gate REJECTED it (`result.json: audit_failed`) because of a merge
race, not because of the proofs: while Aristotle was running, P4 had merged
its own `uH_comp_le` into `Process/Basic.lean`; replaying Aristotle's
Entropy on top produced a duplicate declaration (and a downstream
`DecidableEq B` failure at the `uH_le_of_dependsOnWindow` call site).

Manual reconciliation (operator-approved, backups in
`~/harper-stability-lean-backups/20260708T-manual-aristotle-p2-merge/`):

1. `Entropy/Basic.lean` replaced by Aristotle's version — all 22 previous
   declarations preserved VERBATIM (checked mechanically), 9 sorries closed
   (`hstep_nonneg`, `hstep_le_log_two`, `hstep_eq_uE_binEntropy_rho`,
   `uH_proj_chain`, `uCondH_anti`, `sum_hstep_le_uH_proj`,
   `binary_entropy_jensen_gap`, `observer_surplus_lemma`,
   `deterministic_field_fano`), plus 10 new reusable helpers
   (`uH_comp_le`, `uH_prod_sub_eq_sum`, `uH_prod_le`, `uH_pi_le_sum`,
   `uH_bool_eq_binEntropy`, `uCondH_bool_eq_uE_binEntropy`,
   `concaveOn_binEntropy_add_two_sq`, `uCondH_gap_ge_two_uCondVar`,
   `uH_diff_col_le`, `sum_binEntropy_le`). Two proofs carry raised (nonzero)
   `maxHeartbeats` — allowed by the audit policy.
2. `Process/Basic.lean`: the duplicate local `uH_comp_le` deleted; the
   canonical version now lives in Entropy (it takes `[DecidableEq]`
   instances — call sites without them should open with `classical`, as
   `uH_le_of_dependsOnWindow` now does). `pOn_comp_eq_sum` kept.

Verified after the merge: `lake build` green; `scripts/audit.sh` passes
(interface hashes unchanged, import boundaries clean); axiom audit:
`main_from_components` depends only on `propext, Classical.choice,
Quot.sound`.

NOTE for future loop iterations: the Entropy toolkit is COMPLETE and
sorry-free — prefer reusing its lemmas over re-deriving fiber identities.
Known still-missing shared tools (needed by Core S5-S7, to be added as new
lemmas WITHOUT touching frozen statements): finite Pinsker, a KL
event-conditioning adapter, and a finite Azuma inequality.

## 2026-07-08 Fable interface-repair pass (v0.2)

The previous tree DID NOT COMPILE (the "third repair pass" had introduced
pseudo-Lean: `exists x in A`, `forall n >= N`, bare `sum` for the protected
`Finset.sum`, `x.inter I`, `empty`; the earlier "build success" in this
file referred to a stale `.olean` from an older revision — .lean mtimes
were newer than .olean mtimes). Fixes applied:

1. Full syntax repair of `Interface/Definitions.lean` and
   `Interface/Statements.lean`; `lake build` is green again.
2. Applied the outstanding HIGH items of the Gemini semantic review
   `reviews/20260708T013231Z-.../semantic_review.md`:
   - local `hDist`/`neighborhood`/`Cube` DELETED; the BooleanIsoperimetry
     geometry is used verbatim (note arg order `neighborhood r A`), so
     `harper_vertex_iso` applies with no bridge lemmas;
   - `S2`, `S4`, `S6` are now PURE entropy statements (no
     `QData`/`fat`/`pinned`), consuming `blockRegular`(+`Family`),
     variance and PF-mass hypotheses;
   - `S7` restated as the standalone heavy-ball theorem (HBL-FAT), with
     the new `QFromS7Statement` covering the Q derivation in assembly.
3. Fable audit fixes beyond the review:
   - S2 quantifier order corrected (density BEFORE slack; the old
     `exists slack, forall pLow` form was unprovable) and the bound made
     explicit: `(s + eps*m + e*log 2)/2`;
   - `A.Nonempty` added where junk-value semantics could bite
     (R3, S1-S7);
   - `VPlusStatement` gained the missing `k <= 2^n` guard; S3 gained
     `1 <= BSize`; S6 gained the explicit two-cluster gap hypothesis
     `0 < 1 - 2q - 2eps`; S7 eps-range matches the prose
     (`eps < min(qMin, 1/2 - qMax)`);
   - dead `hasWindowEstimator` removed (S3 uses
     `expectedEstimatorError` + `dependsOnWindow`);
   - classical-decidability handled via
     `attribute [local instance] Classical.propDecidable`.
4. Gemini's two "human questions" resolved per the prose review record:
   the `q + ceil(s0 m)/m` top-radius relaxation is accepted (O(1/m),
   absorbed in slack; comment added at `pinned`); nats vs bits in `bad`
   is a documented rescaling of `eta`.

## Statement-level status

## 2026-07-08 six-part review repair pass (v0.3)

Applied the agreed interface repairs from
`interface_part_reviews/20260708T052219Z-six-part-review`:

1. `VPlusStatement` now chooses a radius `t <= n` and its maximality is
   only among radii `t' <= n`, fixing the false endpoint case `k = 2^n`.
2. Added `InteriorVolumeCalculusStatement`, the explicit interior
   entropy-volume/radius calculus consumed by the reductions.
3. `S3Statement` now carries the missing sign guards
   `0 <= kappa`, `0 <= s`, and `0 <= e`.
4. `S6Statement` is uniform over a whole range
   `q in [qMin, qMax]` with one gap hypothesis, matching the way S7/A0
   consume the predictable-center lemma.
5. `A0Statement` now includes `QFromS7Statement`; assembly has a
   corresponding `sorry` skeleton and the package tuple includes it.

Build and semantic review were re-run immediately after this section was
added; see the newest directory under `interface_part_reviews/`.

## 2026-07-08 second six-part review repair pass (v0.4)

Applied the next repair layer from
`interface_part_reviews/20260708T075311Z-six-part-review`:

1. Strengthened `validData`: `1 <= cSize`, `Sublinear sigma`, and a
   nats log lower bound `log n <= sigma n` for `n >= 1`.
2. Strengthened `validQData`: `Sublinear sigma` and the analogous log lower
   bound.
3. Made `degradedData` include `validData Dout`, so degraded outputs remain
   admissible.
4. Made `fat` include `A.Nonempty`, eliminating the empty-set junk case.
5. Repaired `InteriorVolumeCalculusStatement` with compact parameters
   `alphaMin`, `c0` and a constant `C_V`, used on both entropy-volume and
   inverse-radius errors.
6. Added `HBLFor` and `CoverFor`; restated `R1aStatement` and `R2Statement`
   around the universal HBL oracle / valid degraded-output shape requested by
   review.
7. Restricted `S4`/`S6` slack-family sublinearity hypotheses to
   `0 < pLow <= 1/2`.
8. Cleaned worker signatures: process skeletons are pure, core skeletons
   expose the real upstream dependencies, and assembly imports `Entropy`.
9. `scripts/audit.sh` now treats `native_decide` as an escape hatch.

Verified on the VM:

```bash
lake build HarperStability   # exit 0; expected skeleton-stage sorry warnings
```

## 2026-07-08 P6 assembly/CI repair pass (v0.5)

Applied the P6-only repair requested after
`interface_part_reviews/20260708T084950Z-six-part-review`:

1. Added named `q_from_s7_skeleton : QFromS7Statement`.
2. Proved `main_from_components` directly by destructuring `A0Statement` and
   composing `R1a`, `R2`, `S7`, and `QFromS7`; it no longer contains `sorry`.
3. Clarified docstrings for `InteriorVStatement`, marginal `blockRegular`,
   marginal `R3Statement`, all-`delta` `QuestionQ`, and finite/asymptotic
   boundary of `MainFiniteStatement`.
4. Added `scripts/audit_axioms.lean` for theorem-level `#print axioms`.
5. Strengthened `scripts/audit.sh` with optional strict no-`sorry` mode,
   import-boundary grep, interface hash reporting/checking, and axiom-audit
   execution.
6. Added `.github/workflows/lean.yml` running build + audit.

The monorepo is now treated as the official layout; import boundaries are
enforced by audit rather than by separate repositories.

## 2026-07-08 full-freeze polish pass (v0.6)

Applied the minor-edits and policy repairs requested by the P1--P6 review
cycle:

1. Added P2 entropy-toolkit statement skeletons:
   `rho_nonneg`, `rho_le_one`, `hstep_eq_uE_binEntropy_rho`,
   `windowProb_nonneg`, `sum_windowProb_eq_one`, `windowProb_split_below`,
   `binary_entropy_jensen_gap`, `observer_surplus_lemma`, and
   `deterministic_field_fano`.
2. Clarified `rho`, `blockRegular`, `R3Statement`, `QuestionQ`,
   `InteriorVStatement`, and `MainFiniteStatement` docstrings.
3. Replaced the coarse audit import-boundary grep with a per-layer allowlist:
   `Interface` may import `Interface`; `Volume`/`Entropy` may import
   `Interface`; `Reductions` may import `Interface|Volume|Entropy`;
   `Process` may import `Interface|Entropy`; `Core` may import
   `Interface|Entropy`; `Assembly` may import all.
4. Added `.interface.sha256` for the current frozen interface and verified it
   under `scripts/audit.sh`.
5. Updated GitHub Actions with separate skeleton audit and proof-stage strict
   gate on `proof-*` tags.

Verified on the VM:

```bash
lake build HarperStability
bash scripts/audit.sh
```

Both exit 0. In the axiom audit, `main_from_components` is free of `sorryAx`;
the package skeletons still depend on `sorryAx`, as expected during skeleton
stage.

## 2026-07-08 final review-polish repair pass (v0.7)

Applied the remaining minor/interface-policy repairs from
`interface_part_reviews/20260708T101420Z-six-part-review`:

1. Added the missing explicit `S3Statement` dependency to
   `S6_skeleton`, and passed `hS3` in assembly.
2. Added the entropy helper statement
   `windowProb_mem_past_independent`.
3. Updated P3/P4 docstrings: reductions worker policy, S1 floor bands, S3
   `BSize`, and S4 q-range-free use.
4. Hardened `scripts/audit.sh` further:
   top-level wrapper modules are checked, same-layer imports are allowed by
   explicit per-layer allowlists, dead boundary helpers were removed, and
   strict axiom audit now rejects every axiom outside
   `{propext, Classical.choice, Quot.sound}`.
5. Refreshed `.interface.sha256` for the current frozen interface.

This pass is intended to leave only skeleton-stage `sorry` obligations, not
semantic interface or CI-policy blockers.

## 2026-07-08 final audit hardening pass (v0.8)

Applied the last `ACCEPT_WITH_MINOR_EDITS` items:

1. Documented that `QFromS7Statement` is the formal replacement for the prose
   `R2b`/not-BAD bridge.
2. Documented near `A0Statement` that final extraction directly uses
   `R1a`, `R2`, `S7`, and `QFromS7`; the other components are proof-stage
   inputs.
3. Hardened `scripts/audit.sh`:
   all import lines are scanned, external imports are allowed only through
   `Interface`, `.interface.sha256` is mandatory, and
   `main_from_components` is always checked against the axiom whitelist
   `{propext, Classical.choice, Quot.sound}`.

| statement | state |
|---|---|
| Definitions | frozen v0.2, compiles |
| BallVolumeTwoSided / VPlus / InteriorV | stated; needs semantics re-review (changed guards) |
| R1a / R1b / R2 / R3 | stated; needs semantics re-review |
| S1 | stated; mirrors proven-in-lab skeleton (3 lemmas already proved in lab pilot) |
| S2--S7, QFromS7 | stated v0.2 (purified); needs semantics re-review |
| workers | `sorry` skeletons compile against v0.2 |
| assembly | `sorry` skeleton compiles |

## Next actions

1. Re-run the Gemini semantic review against interface v0.2 (expected
   verdict: the three HIGH items are addressed; check the purified S2/S4/S6
   for faithfulness).
2. Port the lab S1 pilot proofs (`harper-stability-lab/writeup-lean/
   S1Skeleton.lean`) into `Process/`.
3. First Aristotle submissions: entropy chain rule + submodularity
   (Entropy worker), two-sided volume bounds (Volume worker).
4. Add CI: `lake build` + axiom audit (`#print axioms` on assembly tops)
   + escape-hatch grep + interface hash check.

## 2026-07-10 ops: VM de-thrash (operator)

VM was swap-thrashing (load 70 on 8 cores, swap 6.2/8G): up to 6
concurrent worktree builds with 6-7G lean peaks.  Fixes applied:
1. Local concurrency capped at 3 sections via scripts/wave_scheduler.sh
   (nohup; log in the run dir).  Kept E7+E1+E2; E3-E6, E8, E9 queued
   (priority: E4 first - its old-contract draft makes it fast).
   The scheduler counts only lean/agy/codex processes as local work,
   resumes queued sections as slots free, skips sections whose target
   file has no sorry, and exits when the queue empties.
2. prepare_worktree now SEEDS .lake/build from ROOT (213M copy) - new
   worktrees build incrementally instead of recompiling all heavy
   modules from scratch (backup of the script pre-patch in
   ~/harper-stability-lean-backups/20260710T-fable-v03-effective/).
3. Cleanup: retired/paused sections _worktrees, aristotle_unpacked,
   HSLean_* staging deleted (staging archived first to WSL:
   /mnt/c/Users/ddovg/harper-vm-archive/hslean_staging_archive_20260710.tar.gz).
   proof_loop_runs 4.4G -> 0.6G; disk free 6.2G -> 9.9G.
   NOTE: the big disk consumers are OTHER projects (settler-spec-agent
   40G, aristotle_runs 26G, kolmogorov-* ~33G) - untouched.
   Also untouched: foreign CPU hogs run_eval6.py / test_all_s.py.
Result: load 70 -> ~5, swap pressure gone, 16G+ RAM free.

## 2026-07-10 evening: E1 merged manually; R3Eff flipped to sigma-uniform (v0.3.2 pulled forward)

1. E1 (volume-eff): both targets were PROVED in its worktree but the
   gate rejected twice - the helper lemmas lived in Volume/Basic.lean,
   outside the section prefix.  Manually merged Basic.lean +
   Effective.lean under the gate flock; audit PASSED.  E1 is DONE
   (ball_volume_two_sided_eff, interior_volume_calculus_eff proved).
   allowed_prefixes for E1 widened to the whole Volume/ dir.
2. E4 was honestly blocked (its codex verdict INTERFACE_PROBLEM,
   confirmed by hand): S5 needs R3 on eps-dependent atom classes, and
   the per-QData R3Eff constant cannot be absorbed into the uniform
   K/eps^4 budget.  Fix: R3Eff re-frozen in the SIGMA-UNIFORM v0.3.2
   form (compact class reals quantified before exists-K, sigma after;
   QData rebuilt as a literal).  EffectiveR3.lean ported by the
   operator: the proved cond-entropy chain and wrapper survive with
   binder reshuffles (r3_eff : R3Eff proved, sigma-uniform), only the
   two sigma-uniform leaves remain sorried.  Interface hash updated.
3. The flipped contract was hot-synced into the live worktrees of
   E3/E5/E6/E7 (their proofs may consume R3Eff; Interface.Effective is
   a cheap rebuild - heavy Basic modules do not import it).  E2 and E4
   worktrees cleared (recreated seeded on next iteration); E2
   relaunched at iteration 3; scheduler restarted (E4 queued).
4. Progress meanwhile: E7 closed two of its three leaves (only
   r2_eff_hbl_from_q_and_dp remains); E3 merged S4 helpers.
   Remaining eff sorries: 9.

## 2026-07-10 late: v0.3.3 - R3Eff pLow-uniform (third uniformity axis)

E3 hit the pLow axis of the same disease (INTERFACE_PROBLEM, confirmed):
S4 needs R3 at pLow = p(m)/2 with a schedule, per-pLow exists-K useless.
Same would hit S6 (vFam at p/2).  Fix: R3Eff re-frozen with exists-K
before BOTH pLow and sigma; slack (K/pLow^2)*(effEnv 2 sigma m + 1);
the V-growth leaf now carries the EXPLICIT exponent (pLow/8)*zeta^2*m.
Grade check: S4 grade 4 survives exactly; S6 grade 8 roomy.
EffectiveR3.lean ported again (build green first try); no compiled
consumers break (hR3 only in sorried signatures elsewhere).  Contract
re-hashed; hot-synced into E3/E5/E7 worktrees; E2 relaunched at
iteration 4 with fresh worktree; its stale iter-3 Aristotle task
canceled.  Uniformity axes now explicit: n, sigma (v0.3.2), eps
(v0.3.1), pLow (v0.3.3).

Ops note: around 20:21 the wave scheduler and freshly resumed E4/E8
loops died SILENTLY (empty logs, no clean-exit lines) - most likely
OOM during the operator root build + two fresh worktree builds.
Scheduler restarted; E4/E8 will be re-resumed automatically.

## 2026-07-10 night: v0.3.4 - S6Eff grade 8 -> 9 (Aristotle refutation confirmed)

The E5 Aristotle pass (iter 4, COMPLETE) closed two S6 leaves and
REFUTED s6_eff_entropy_term_grade8: the Fano term m*H(e/m) ~ e*log(m/e)
carries an unavoidable log loss over e ~ effEnv 8, so for sigma = log
the grade-8 bound fails; verified by hand, and it scales to the S6Eff
CONTRACT itself (honest total is effEnv8 * polylog).  Fix: S6Eff and
the Fano leaf re-frozen at grade 9 (E9/E8 is a positive power of m,
beats any polylog; with H y <= 2 sqrt y the grade-9 leaf is nearly
trivial - route in the docstring).  The proved s6_eff assembly and the
CLOSED s7_eff (E6) were re-ported by the operator (grade-9 absorptions;
build green first try; s7_eff remains fully proved).  Contract
re-hashed, hot-synced into E3/E5/E7 worktrees (E5 also got its ported
section file); E6 stale worktree removed.  Remaining eff sorries: 9.

## 2026-07-11 v0.3.5: s6_eff CLOSED; R3Eff density exponent honest (pLow^-1)

E5: the iter-6 Aristotle result (racing our v0.3.3/v0.3.4 fixes -
both its complaints were already repaired) PROVED the full grade-9
route (s6_eff_grade9_from_current_route) plus the grade-9 Fano leaf;
the operator closed s6_eff : S6Eff as a one-line wrapper.  E5 has ONE
sorry left (s6_eff_variance_grade5).

Fifth and hopefully last quantitative mismatch: that variance leaf
(shape K_V/pLow, chosen by the pipeline) is NOT derivable from the
v0.3.3 R3Eff with its padded K/pLow^2 - the honest R3 density cost is
pLow^-1, so R3Eff was tightened to (K/pLow)*(effEnv 2 sigma m + 1)
(v0.3.5), EffectiveR3.lean re-ported (leaves restated, proved chain
adjusted; build green), contract re-hashed, live worktrees synced,
E2/E5 relaunched with fresh worktrees, E2 stale Aristotle canceled.
S4 grade-4 arithmetic only gets roomier from this change.

Remaining eff sorries: 8 (R3 x2, S4, S5, S6-variance, R2 x?, R1a,
assembly).

## 2026-07-10 late: v0.3.3 - R3Eff pLow-uniform (third uniformity axis)

E3 (S4Eff) hit the same wall one axis over (its codex verdict
INTERFACE_PROBLEM, confirmed): the S4 proof needs R3 at pLow = p(m)/2
with a p(m)-schedule, and the per-pLow exists-K of R3Eff cannot feed a
single outer constant.  The same would have hit S6 (vFam at p/2).

Fix: R3Eff re-frozen with exists-K before BOTH pLow and sigma;
conclusion slack (K/pLow^2)*(effEnv 2 sigma m + 1) (honest density
cost is pLow^-1); the V-growth leaf now has the EXPLICIT exponent
(pLow/8)*zeta^2*m instead of exists-c.  Grade check: S4 at grade 4
survives (p-balance with /p^2 budget lands exactly on grade 4), S6
grade 8 roomy.  EffectiveR3.lean ported again by the operator (the
proved cond-entropy chain and wrapper carry K/pLow^2 bookkeeping;
build green first try); only R3Eff consumers with APPLICATIONS of hR3
would break, and there are none compiled (all consumers have hR3 only
in sorried signatures).  Contract hash updated; new contract
hot-synced into E3/E5/E7 worktrees (their WIP skeletons adapt next
iteration); E2 worktree recreated, loop relaunched at iteration 5...
(start-iteration 4); its stale iter-3 Aristotle task canceled
(project 494ca10c).

Uniformity axes now explicit in contracts: n (always), sigma (v0.3.2
flip), eps (v0.3.1), pLow (v0.3.3).  Remaining eff sorries: 11.

## 2026-07-11 E8 manually merged: r1a_eff CLOSED

E8 iterations 3-4 had CLOSED r1a_eff but were gate-rejected on the
P3b pattern: 16 private lemmas in Reductions/Basic.lean
(r1_range_control, r1a_subset_*, sublinear_*, neighborhood_mono_set,
cube_card_le_two_pow, card_le_V, degradedData_trans) needed by the
proof; the worktree diff was PURE de-privatization (verified: zero
content changes).  Operator merged Basic.lean + EffectiveR1.lean under
the gate flock; audit PASSED.  R1aEff is proved.  Also: E4 iter-8
candidate was rejected on v0.3.4->v0.3.5 vintage skew (built before the
R3Eff density-exponent tightening); its worktree is synced, next
iteration adapts.

Sections fully closed so far: E1 (volume), E6 (S7), E5-main (s6_eff),
E8 (R1a).
## 2026-07-11 (Fable, manual) — v0.3.6 GRADE CASCADE + three closures

Overnight (gates self-fired after my merge-lock expired on its 50-min timer):
- E9 iter-3 ACCEPTED: `main_finite_effective` PROVED (assembly sorry closed);
  also delegated `s6_eff` to the route theorem (racing my identical fix).
- E5 ACCEPTED: `s6_eff_variance_grade5` closed — `Core/EffectiveS6.lean` fully
  proved. E5 loop self-exited.
- E3 iter-8 REJECTED (audit): candidate carried the proved variance-budget
  leaf but a v0.3.1-vintage `hR3 Q pLow` call; harvested manually (below).
- DISCOVERY: the "deployed" E4 s5_eff candidate from the previous session had
  silently never landed (olean timestamp 23:22 predates the deploy; E9's gate
  counted before=7 WITH the stub). Candidate redeployed from E4's worktree.

v0.3.6 (contract flip + ports, all mine, backups in
`~/harper-stability-lean-backups/20260711T-fable-v036-cascade/`):
- E3's Aristotle REFUTATION of `s4_fano_term_le` at grade 4 CONFIRMED by hand:
  the S3 Fano term `m·H(e/m) ≈ e·log(m/e)` at `e ~ effEnv 4` exceeds any
  `C·(effEnv 4+1)` by `log m` (same defect class as v0.3.4/S6 — both
  S3-consumers carry the H-term; the v0.3.4 "count logs" audit stopped at S6).
- Honest cascade, Interface re-frozen (hash updated): S4Eff 4→5, S5Eff 7→8
  (atom-ladder base +1 ⟹ R3-on-atoms `effEnv 2` of grade-6 atom-σ = 8),
  S6Eff 9→10 (bSlack 8 ⟹ p* ~ √((E₈+1)/(m+1)), e ~ E₉, Fano ≤ 2√(E₉m) = E₁₀),
  S7Eff 9→10, R2Eff/R1aEff/effMainGrade 13→14. γ = 2⁻¹⁴ = 1/16384:
  σ_out ≈ K·σ^(1/16384)·n^(16383/16384).
- Ports: value-map effEnv literals per chain (S6 {7,8,9}+1, statics {2,3,5}
  fixed; R2 whole tail {9..13}+1; R1/Assembly 13→14; S5 ladder {4..7}+1;
  S7 {7,9}+1), then bare-numeral repairs: `effEnv_nonneg k`,
  `s6_env_mono_grade`, `s6_env_geo_sq`, `effEnv_comp k (i:=j)`,
  `effEnv (5+2)`-style paren args, scale constants 2^13/8192 → 2^14/16384,
  `effMainGrade` restored symbolic in Assembly. S6 cross-bounds
  (`s6_env_need1/3`) took one extra geo-square hop each (le_trans+nlinarith).
- E4's s5_eff candidate: deployed with ladder shift + the v0.3.5 vintage
  port (`s5_K3` divisor `(1/6)²` → `(1/6)`) + `(i := 5)→(i := 6)`.
  **`s5_eff : S5Eff` now PROVED in tree** — E4 section CLOSED, no loop needed.
- E3's candidate deployed with `s4_r3_fixedDensity_blockRegular_eff` re-proved
  against the σ/pLow-uniform R3Eff (K := K3/pLow) and the Fano leaf RESTATED
  at grade 5 (route in the leaf docstring: `m·H ≤ 2√(e·m)`).

State after build: 6 sorries — E2 ×2 (r3_fiber leaves), E3 ×3
(`s4_fano_term_le` grade 5, `s4_rate_gap_certificate`, `s4_eff`), E7 ×1
(`r2_eff_hbl_from_q_and_dp`). Closed sections: E1, E4, E5, E6, E8, E9.
Loops: E2 kept running through the flip (its leaf statements unchanged);
E3/E7/E9 loops + scheduler killed pre-flip; stale worktrees (E3/E4/E5/E7/E9)
deleted; scheduler relaunched (it skips zero-sorry sections automatically).
sections.json notes for E3/E7 extended with v0.3.6 routes.

## 2026-07-11 (Fable, manual) — E7 CLOSED via manual merge (7/9 sections done)

E7 iters 12–14 all produced a COMPLETE r2_eff_hbl_from_q_and_dp proof but
were gate-rejected (audit_failed): the candidate de-privatized 9 helpers in
Reductions/Basic.lean (subset_neighborhood_self, neighborhood_mono_radius,
V_peel_le, V_upper_of_classMember, sublinear_lt_of_pos, log_ratio_upper,
H_diff_le, logsize_le_of_V_upper_large, +1) — outside E7 prefix, so the
replay saw Unknown identifiers. Diff verified: pure private→public, zero
content changes; the added `import Volume.Basic` is matrix-legal (precedent:
EffectiveR1). Manually merged Basic.lean + EffectiveR2.lean under the gate
lock; build green, audit rc=0. Backup:
~/harper-stability-lean-backups/20260711T-fable-e7-merge/.

Overnight before that: E3 iter-11 (6→5) and iter-12 (5→4) ACCEPTED — the
grade-5 Fano leaf and the rate-gap certificate are closed.

**r2_eff : R2Eff is PROVED. Tree: 3 sorries** — s4_eff assembly (E3, its
loop running) + the two R3 fiber leaves (E2, its loop running). Scheduler
relaunched. Closed: E1 E4 E5 E6 E7 E8 E9.

## 2026-07-11 (Fable, manual) — E2 CLOSED via manual merge (8/9): ONE sorry left

E2 iter-4 Aristotle closed BOTH R3 fiber leaves (r3_fiber_growth_V_bound_eff
+ r3_fiber_log_lower_eff, explicit ζ-threshold, pLow/σ-uniform K, clean
axioms) but the gate rejected 3→1 (audit_failed): the candidate de-privatized
13 helpers in Reductions/R3Fiber.lean (outside prefix) AND generalized
r3_fiber_growth_witness_safe from hBV-choose to an abstract sublinear vSlack
(internal callers consistently rewired; the lemma was private, so no external
users). R3Fiber is not hash-frozen; tree copy untouched since the worktree
was seeded ⟹ wholesale-merged the worktree R3Fiber.lean + candidate
EffectiveR3.lean under the gate lock. Build green, audit rc=0. Backup:
~/harper-stability-lean-backups/20260711T-fable-e2-merge/.

**r3_eff : R3Eff is PROVED. Tree: 1 sorry — s4_eff (E3 loop running).**
Closed: E1 E2 E4 E5 E6 E7 E8 E9.

## 2026-07-11 (Fable, manual) — v0.3.6b: S4 decomposition rewritten after 3rd refutation

E3 iter-13 Aristotle REFUTED s4_eff_variance_grade2 (grade-2/pLow uniform
variance family): the S1/S2 entropy→variance conversion carries a pLow-FREE
Pinsker/threshold term 13·√((s1+1)(m+1)) ≤ 13·(E₃+1) — genuinely grade 3.
CONFIRMED by hand (at the schedule pLow = p/2 the grade-2/pLow budget is
m^(13/16) vs the m^(14/16) threshold term). The GRADE-5 CONTRACT IS SAFE:
hand-verified pointwise route — two-term family
(K_V/pLow)(E₂+1) + K_V(E₃+1); error splits by √-subadditivity into the
PROVED grade-4 part + a new part ≤ (4√K_V/eps)·⁴√((E₃+1)(m+1)³) ≤ that is
E₅-with-m^(1/32)-room; Fano absorbs the log via log x ≤ (16/e)x^(1/16) +
the m+1 ≤ E₃+1 dichotomy (trivial cap branch). No schedule change; no
contract change. Their iter-13 proofs (error_grade4, cert_combine,
fano_term_le_explicit, eg4_core + earlier leaves) all kept in the file.
Installed 5 new sorried leaves with full route docstrings
(variance_twoterm, error_twoterm, quarterroot_le_env5, fano_twoterm,
certificate_v2); s4_eff is already delegated to certificate_v2. Build
green (DONE_RC=0, exactly 5 sorry-declarations), audit rc=0. E3 loop
relaunched with fresh worktree; notes updated (v0.3.6b block). Backup of
the pre-v2 file: ~/harper-stability-lean-backups/20260711T-fable-e2-merge/EffectiveS4_pre_v2.lean.

## 2026-07-11 (Fable, manual) — v0.3 EFFECTIVE PROGRAM COMPLETE: ZERO SORRIES, CLEAN AXIOMS

s4_eff closed BY HAND (the pipeline was stuck on a false leaf; iter-13
Aristotle refuted the grade-2/pLow variance family — confirmed, and my own
first repair (v0.3.6b ⁴√-statements at the old √-schedule) was ALSO wrong:
the honest error there is exactly grade 5 with no room, so its Fano term
overflows by a log. Final route (v0.3.6c, hand-verified pointwise then
hand-proved in Lean, ~700 new lines):
* quarter-root schedule s4_eff_p2 = min(⁴√((E₃+1)/(m+1)), 1/3) — the old
  schedule and all its lemmas kept untouched;
* two-term variance family (K_V/pLow)(E₂+1) + K_V(E₃+1)
  (s4_eff_variance_twoterm — mirrors the in-file iter-8 derivation with the
  R3 constant hoisted out of the pLow-quantifier);
* scheduled error ≤ (K_err/eps)((E₄+1) + ⁸√((E₃+1)³(m+1)⁵))
  (s4_eff_error_twoterm + s4_error_core), strictly inside grade 5 with
  ratio^(1/8) room;
* Fano absorbs its log pointwise: log x = 8·log(⁸√x) ≤ 8·⁸√x and
  R·⁸√ratio = ⁴√((E₃+1)(m+1)³) ≤ E₅+1 (s4_fano_twoterm + the
  explicit-constant variant s4_fano_twoterm_explicit — 12(C+1)+3);
* certificate v2 at sS := 0 (cap-flatness; fatness enters only through the
  variance family), K = 1024·K_err + 16384, eps ≥ 4 branch via
  s4_uH_binnedFold_trivial.
Ops lessons: per-declaration heartbeat budgets (set_option maxHeartbeats)
— wandering timeouts are BUDGET exhaustion, not the reported line;
clear_value on set-variables to stop envelope-tower unfolding; field_simp
often closes goals (dangling `ring` ⟹ "no goals"); rw of an m-equation
rewrites inside exp-args — use field_simp identities instead.

**FINAL STATE: 0 sorries project-wide; audit rc=0;
#print axioms main_finite_effective = [propext, Classical.choice, Quot.sound];
main_finite_via_effective (the o(n) theorem as a corollary of
K·σ^(1/16384)·n^(16383/16384)) equally clean. All nine sections E1–E9
CLOSED. The v0.2 skeleton remains intact and canonical.**

## 2026-07-11 (Fable) — v0.4 UNIFORM-K PHASE LAUNCHED (the ideal formulation)

New frozen interface HarperStability/Interface/EffectiveUniform.lean
(hash-registered alongside Effective.lean): S4EffU/S5EffU/S6EffU/S7EffU/
R2EffU/R1aEffU/MainFiniteEffectiveUniformAt — every ∃K hoisted BEFORE
∀sigma (K = class reals + epsCover only), grades unchanged
(5/8/10/10/14). Seven worker files with 7 sorries and full route
docstrings; the one genuinely new proof is the R2U grade-10 ratio
dichotomy (V032_UNIFORM_K_DESIGN.md, grades adapted 9→10/13→14); all
other targets are binder reshuffles of the CLOSED v0.3 proofs whose
constants are already class-only. Sections U1–U4 registered (disjoint
files, prefixes added); v0.3 files untouched and still zero-sorry.

Pipeline upgraded per user directive: proof/strategy iterations now run
SIX local stages — Gemini → Codex → Opus → Codex → Gemini → Codex —
then Aristotle, via a new claude-backend edit stage (scoped permissions:
acceptEdits + whitelisted lake-build; flip to the agy-style
skip-permissions later if desired). wave_scheduler queue = U1..U4
(MAXLOCAL=3), octal bug fixed earlier, OWNED map extended.

## 2026-07-11 (Fable, manual) — r1a_effU CLOSED via manual merge (5/7 uniform targets)

Aristotle U4 job 3934885b proved r1a_degraded_for_subset_effU → r1a_effU
sorry-free on clean axioms. The genuinely new mathematics: the
range-control constants made class-only via r1_range_control_uniform
(range-or-large-slack dichotomy: every class member is either strictly
sub-equatorial or n·log2 ≤ C·(σn+1), constants before sigma) +
r1_range_control_lower_param — placed in Reductions/Basic.lean (outside
U4 prefix, gate would reject; diff verified pure 128-line append) and
merged manually with EffectiveR1U.lean. NOTE: the loops followup polled
the duplicate submission 0086fe7c while the finished result was
3934885b - fetched explicitly via aristotle download. Build green,
audit rc=0. Remaining: 2 sorries - hpinned (U3, R2U good-branch) +
main_finite_effective_uniform (U4 assembly). Backup:
~/harper-stability-lean-backups/20260711T-fable-u4-merge/.

## 2026-07-11 (Fable) - U4 assembly proof merged; ONE sorry left project-wide
main_finite_effective_uniform written by the Opus stage (full r3->s4U->..->r1aU composition, constants before sigma) + bonus main_finite_effective_of_uniform (uniform => plain, via structure eta). Built green against the tree, merged. U4 target CLOSED; loop retired. THE ONLY remaining sorry in the whole project is r2_effU_pinned_good (U3, the class-only peeling at fixed n in the good-ratio branch). When U3 closes it, main_finite_effective_uniform becomes verified on clean axioms with no further work.

## 2026-07-12 (Fable) - v0.4 UNIFORM-K COMPLETE: the ideal formulation is DONE
Aristotle (U3 job 89e03a50) closed the last sorry r2_effU_pinned_good (the class-only peeling at fixed n, good-ratio branch). Vintage-skew: its snapshot predated my r1a/assembly merges, so I merged surgically - only EffectiveR2U.lean (the proof) + a UNION Basic.lean = tree r1a lemmas + Aristotles 3 R2U helpers (r1_range_control_at, r1_sublinear_log_succ, r1_range_control_class_constants); the two big range-control lemmas needed maxHeartbeats 2000000. Build green, audit rc=0, TREE SORRY COUNT = 0.
#print axioms main_finite_effective_uniform = [propext, Classical.choice, Quot.sound] (clean). Same for main_finite_effective_of_uniform, r2_effU, r1a_effU. All 7 uniform targets closed; all interfaces frozen; v0.2 and v0.3 intact.
THE FULL RESULT: for every class (rho, deltaCap, cSize, alphaMin, alphaMax, epsCover) there is a SINGLE K (class-reals + epsCover only, NOT sigma) such that for every sublinear sigma >= log and every n, every class member is covered by exp(K*(effEnv 14 sigma n + 1)) balls of radius rmin + ceil(same); K <= C*(1+log(1/epsCover))*(alphaMin*rho*sqrt(deltaCap))^(-C0), C/C0 absolute. gamma = 2^-14 = 1/16384.
