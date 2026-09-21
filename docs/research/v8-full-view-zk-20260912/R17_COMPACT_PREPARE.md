# Compact binding and ordinary preparation: R36

Source base 2c03cc7b5dad76d731ae0628eef233b98eb034b1 plus the R34–R36
changeset. This is an isolated, explicitly new research transcript profile:
AV8/R17/structuredG271-two-channel/compact-binding-research-v2.
It is NOT byte-compatible with research-v1 and does not inherit a full
privacy or Fiat--Shamir soundness theorem. No production paths were changed.

## Structural change and retained baseline work

The old optimized verifier's central technique was verifier-derived compact
functional binding, not merely faster multiplication. R36 restores that
architecture for the ordinary channel through the repair's actual dual map.
It retains R35's compact terminal, baseline fused/block kernels, weighted
sparse permutation correction, inactive/pivot corrections and image term.

The primary prepare computes only dual entries 0 and (use_x ? 2 : 1) for the
interpolant subtraction. Each comes from the exact three source points,
kappa/kappa²/kappa³ scales and inactive inventory, followed by the same
permutation and inactive-pivot subtraction. No full ordinary original,
dual or chord vector is constructed. A zeroed 1024-entry buffer is scratch
storage only; the primary first-fold branch consumes it and the terminal
overwrites every location it reads. It is never used as the ordinary
functional. The G channel is still expanded: this is an explicit remaining
cost, not a claimed fully compact verifier.

The prover and second dense reference use prepare (dense ordinary path).
Only the primary verifier uses prepare_compact. Both call prepare_mode and
bind the identical verifier-derived descriptor and claim. Both complete
verifiers still execute and their outcomes are compared; no negative test
or invalid-proof image correction was removed.

## Transcript boundary

The new profile is bound from transcript initialization in both the producer
and verifier, not just tagged after the old challenges. Immediately before
tau, the compact-functional/v2 descriptor contains, in fixed order:

- The exact 1024 permutation entries (u16 little-endian) and 1024 inactive
  flags, not a prover-provided map hash or a claimed fingerprint.
- Fixed shape bytes [20,22,10,4,4,2,use_x].
- z[10], kappa, abc[3], iv[2], iv_g[2], and p0.x,p0.y,p1.x,p1.y,gamma,
  using the retained canonical field-byte encoder.
- The claim is then separately absorbed; the explicitly new image-residual
  domain is absorbed before sampling tau.

Those inputs determine both source weight functions and their chord/dual
transforms under the fixed source definitions. The source loop that absorbs
expanded weight bytes is removed in v2, on both dense and compact paths.
This is intentionally a new transcript, NOT a theorem that hashing a
description equals hashing its expansion. No oracle answer is assumed equal
across versions. Shared-oracle security and the source encoding/refinement
argument remain obligations. No new hiding assumption is introduced.

## Focused proof and actual-source checks

CompactPrepare.lean reuses SourceOriginalWeights.sourceMultilinearWeight_eq
and the existing transportDual definition. It proves entry_eq_source for
the indicator-first product-loop formula, then selected_eq_source_dual for
any selected coordinate. Both hold for arbitrary inputs; no honest-proof,
nonzero challenge or balanced-witness premise is added.

Exact target: lean/AspisV8R17/CompactPrepare.lean. Compiled locally with the
existing cached /Users/dominic/ZK/AspisFormal workspace and the worktree's
target/r17-lean and target/r16-lean import caches; lake env lean -j1 -M2500.
Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
Exit 0, wall 7.39 s, peak RSS 1457274880 bytes, swaps 0.
entry_eq_source axioms: propext, Quot.sound. selected_eq_source_dual axioms:
propext, Classical.choice, Quot.sound. No sorry or new axiom. No unchanged
manifest replay. This is a source-shaped algebra theorem, not complete
Rust/field/point-construction or descriptor-encoding refinement.

Focused Rust gate: 128 selected-entry comparisons against actual source
original_weights then transport().dual, both x/y coordinate choices, with
allocation denied after fixed-map initialization. Includes zero, one,
maximal limbs and degenerate kappa. Exit 0, 27.16 s including compilation,
RSS 533440 KiB, swaps 0; optimized release, 4G/6G/zero-swap scope, Tasks128.

Fresh deterministic world-0 test proof (not a privacy-distribution sample):
exit 0, 17.53 s including compilation, RSS 448768 KiB, swaps 0;
5G/7G/zero-swap scope. Both complete host verifiers accept. Subsequent
actual-proof/negative gate: honest exit 0, 0.03 s, RSS 26736 KiB;
G-final mutation rejection exit 0, reported 0.00 s, RSS 3520 KiB; swaps 0,
4G/6G/zero-swap scope. The old v1 fixture separately rejects under v2:
exit 0, reported 0.00 s, RSS 3168 KiB, swaps 0, 3G/4G/zero-swap scope.
All scopes TasksMax=128 except old-v1 rejection TasksMax=64.

## Actual SBF result

Source/table/frame gates pass: exit 0, wall 40.45 s, RSS 619696 KiB,
swaps 0; 5G/7G/zero-swap scope, TasksMax=128. ELF SHA256:
e99e9961d88b24453b91580b98fe08f3df28d490dad377de4e3ce48fb6d1ddfe.
Fresh proof SHA256:
d18b5455261d41ba2bbe8d44dd525faa057e50b5110f7cc4225ed32e298204f0.

Primary acceptance is **20591164 CU**, 4536522 below R35's 25127686
(about 18.05%). This compares fresh fixtures across transcript versions;
it is not a same-proof/same-challenge microbenchmark. The primary trace has
only ONE original-weight expansion, belonging to G. That G original stage
costs 12894084 CU, its dual 94939 CU and chord 2258151 CU. These three
stages alone still cost 15247174 CU. The ordinary compact terminal interval
is 1568856 CU. This identifies the remaining structural target directly.

The full program still heap-fails in the retained second dense pass:
honest 23851288 CU; corrupt 21023257 CU, not a completed checked rejection.
All four 1.2M/1.4M cases exhaust CU. Same 100M diagnostic budget, 256 KiB
heap, read-only accounts and no settlement. Driver exit 0, 0.13 s, RSS
31404 KiB, swaps 0; 3G/4G/zero-swap scope, TasksMax=64. All accounts
unchanged. Driver exit 0 reports observations, not transaction acceptance.

Two tooling failures preceded the final checks: the initial stager refused
an ambiguous three-occurrence replacement (exit 1, no compilation); the
match was narrowed to the exact preparation loop and a fresh stage created.
The initial SVM launch used a mistyped binary path (exit 127, 0.00 s,
RSS 880 KiB, swaps 0); no ELF execution occurred. Correcting the path used
the already accepted ELF, without rebuilding or changing a cap.

Evidence: evidence/r17-compact-prepare-*. The fresh fixture and staged
workspace remain on the Tailscale NUC at
/home/dombarker/project-offloads/aspis-r17-sbf-probe-20260921-r36b.
Reconstruct by applying stage_r17_compact_prepare.py to the R35 stage;
check_r17_compact_control.py, generate_r17_compact_fixture.py and
check_r17_host_proof.py are the focused optimized runners. The SBF runner
advances each prior source pin through the new exact before/after hashes.

## First remaining implementation and security propositions

Next implementation: eliminate the remaining G original/dual/chord expansion
by evaluating the SAME transported 271-node Vandermonde functional compactly.
The existing original_weights_transported_pairing theorem already reduces
this to the source G pairing against the inverse-transported chord of the
arbitrary lifted quotient. Its G term is a sum of the 271 coin coefficients
times evaluations at the fixed nodes 1..271. Use that exact transpose
identity and the retained structured arithmetic; do not treat G as an MLE,
move coins to the disproved first-271 placement, or weaken final checks.

The first source-refinement obligation for this step is that the compact
descriptor and selected-entry implementation determine the exact two-channel
source functionals, interpolant subtraction and image residuals for every
canonical input. The local entry model and finite tests are evidence toward
that, not its complete source proof. A global argument must also justify the
new descriptor framing, shared oracle, C2/seed chronology, adaptive losses,
failures/retries/publication and soundness. No full privacy claim follows.
