# Prover commitment continuation 42

**Target not yet established.** Concrete public-normalized private-read
bounds, a pointwise honest-run continuation theorem, and the generated
64-byte entropy owner/model/reservation bridge are proved locally. The full
arbitrary-byte native-to-owner gate remains unproved after a changed-proof
600-second timeout. This is a verification obstruction, not a privacy
counterexample. Native publication, the source experiment conversion and both
WholeRunJoins remain open. No endpoint premise is removed.

The task base is f57f0546d8af9a4355a3df1f8eaf91dc7a4e33c4 (the fresh
worktree supplied to this continuation). No shipped sources changed.

## Raw private domains

`ProverCommitRawFresh42` closes the unverified part-41 domain-separation
draft: all three raw seed families differ from both public bindings, and
outside `PrivateMemo40.guessed` they avoid the retained old history plus
both binding reads. The statement digest address remains a separate
obligation; no private-derived read bound is replaced by this result.

J9442 is a rejected draft (simplifier did not reduce `if True`);
J9444 compiles the corrected module: exit 0, wall 2.15 s, peak RSS
4,163,112 KiB, zero swaps. All three printed axioms lists are subsets of
[propext, Classical.choice, Quot.sound]. Exact source bytes, dependency
fingerprints, source revision and commands are in
`../../100bit-spend-path-20261013/evidence/prover-commit42-20261022/lean/`.

J9400 was refused because its receipt already exists for another module;
no compiler ran and its existing evidence is not attributed to this work.
A read-only range inventory identified available numbers within J9400–J9799.

## Selected generated owner

The unchanged generated Types/Funs from part 41 are now installed and
compiled independently (J9443/J9445), exit 0, standard generated definitions.
The semantic bridge is supplied in the following section; compilation alone is no refinement claim.

## Generated 64-byte owner bridge and reservation (local closure)

`ProverCommitOwnerZero42.zero_from` proves the extracted recursive byte test
for every full array by symbolic suffix-length induction. `OwnerBytes42`
connects the U8 arrays to the ROM's UInt8 functions, including exact zero
and nonzero equivalence. `OwnerRun42.run_exact` and `generate_exact` prove
the extracted selected owner against the byte-blind schedule for arbitrary
64-byte tapes, including OS errors and retained cursor/history/ledger.
`OwnerModel42.generate_model` then projects this execution to
`ProverCommitPublicNonce40.generate`. `OwnerLedger42.prepared_model` and
`continuation` compose the exact selected owner with part-36 reservation
and any subsequent continuation, retaining its full state. These are local
control/model theorems; they do not certify the native entropy callback's
entire caller or mask/publication continuation.

The generated Types module's global `instDiscriminantErrorIsize` conflicted
with the prover extraction in J9449. The fix replaces only that attribute
with `errorDiscriminant42`, preserving Os=0 and RepeatedZero=1. The Types
source and object were snapshotted under the task host workspace before
overwrite; Funs and zero-test dependencies were rebuilt. Thus this is a
shared object replacement, not reuse of a stale dependent.

Accepted final targets: Types J9450 (1.40 s, 2,562,376 KiB), Funs J9451
(1.33 s, 2,559,720 KiB), zero J9452 (2.15 s, 3,727,520 KiB), bytes J9454
(2.15 s, 4,151,560 KiB), run J9458 (2.05 s, 4,164,496 KiB), model J9459
(1.91 s, 4,163,452 KiB), ledger J9468 (1.87 s, 4,163,964 KiB).
All exit 0, zero swaps. All printed theorem axioms are subsets of
[propext, Classical.choice, Quot.sound]. Draft failures and all section-6
fields are retained in the attempt JSON and raw receipts. No native bounded
check was rerun, and no new OS RNG, nonce or ledger assumption was added.

## Concrete conditional private-read carrier and run transport

`ProverCommitGlobal42` defines the two public positions in the actual
`gAddr`/`attVec` order. `normalized_attVec` and `normalized_rest` prove the
exact projection to the local binding substitution. `conditional_law`
instantiates part 41 on `aA` (the finite-ROM encoding of `gAddr`) with an
arbitrary frozen context that covers the statement digest. It retains an
unnormalized context indicator, including empty fibers.

`ProverCommitPrivateBounds42` uses a carrier containing **two** independent
nonzero private seeds and the answer vector; the public nonce and both
binding answers are fixed parameters. `src_private` shows that a private
commitment position never uses the public nonce or a binding answer as its
designated freshness field. `seed_field`/`answer_field` establish the actual
grammar fields on this carrier. `private_pair` preserves the old designated
field argument; `fixed_mass` gives ≤2^-255 against any fixed frozen address,
and `frozen_mass` gives q/2^255 for q retained addresses, with repetitions.
This covers mask expansion, D-seed, source expansion, salts, leaves and
Merkle nodes. No private-derived read is replaced by raw-seed counting.

`ProverCommitPrivatePairs42.pair_all`/`pair_mass` preserve the private/private
pair bound, using the existing structural dependency/separation theorem.
`ContextBounds42.context_frozen_mass` integrates the bound against the
context indicator, retaining its probability factor. Its `normalized_local`
and `global_private_address` identify the **actual** `gAddr`/`attVec`
coordinates with this bounded carrier.

`ProverCommitGlobalRun42.run_eq` proves the honest `runC` equation (rather
than assuming a run callback), under public memo coherence and the private
frozen-hit/pair complements. `continuation` transports any subsequent
observation of that vector with an arbitrary retained state. This is a
pointwise local continuation theorem; the complete adaptive eight-attempt
source/experiment composition, charged observer queries, and actual native
publication are not inferred from it.

Accepted final targets: Global J9464 (1.98 s, 4,178,832 KiB), PrivateBounds
J9472 (2.18 s, 4,176,908 KiB), PrivatePairs J9480 (2.21 s, 4,172,328 KiB),
ContextBounds J9478 (1.91 s, 4,166,340 KiB), GlobalRun J9482 (2.01 s,
4,161,368 KiB). All exit 0, zero swaps, printed axioms only in
[propext, Classical.choice, Quot.sound]. J9474 hit the ordinary heartbeat
limit during underspecified elaboration; the replacement supplies explicit
grammar arguments and a symbolic update equality, with no limit increase.
No existing inherited module was changed for these new proof modules.

## Charged adaptive reads and selected retry control

`ProverCommitNormalCarrier42` embeds fixed nonce/binding values into the
existing coupling carrier, leaving the old public coordinates unused. Its
commutation lemmas show that private seed/rest lenses leave these fixed
public values intact. `ProverCommitCharged42.hit_private` instantiates the
existing charging and adaptive observer argument on this normalized carrier.
It uses the actual `qry_tame`, `charged_tame` and `verLog_rest` proofs; it does
not assume the observer's query remains unchanged. `CarrierJoin42` proves
that this carrier's `uVec` is precisely the `gAddr` normalization above, that
the public nonce is fixed, that both private seeds are retained, and that
charged private observer hits have mass ≤2^-255. Public bindings are excluded
from the freshness theorem.

`ProverCommitOwnerSuccess42.source_success` retains the entire selected
owner's successful output, including the exact public nonce, both private
blocks and state. `RetryOwner42.entropy_model` installs the extracted selected
64-byte owner as the entropy callback of `ProverCommitRetry34.realAttempt`;
`eight_model` transports it through all eight attempts, before the actual
serializer guard, retaining every state update. This is a local selected
callback/control theorem with an unrestricted subsequent continuation; it
does not assert that the entire downstream native prover has been refined.
Reservation remains in the successful continuation, so it is not moved before
the native public-byte guard.

Accepted focused targets: RetryOwner J9483 (1.95 s, 4,160,608 KiB),
OwnerSuccess J9485 (2.26 s, 4,152,768 KiB), NormalCarrier J9488 (8.68 s,
4,117,772 KiB), Charged J9487 (4.75 s, 4,133,152 KiB), CarrierJoin J9492
(1.99 s, 4,164,724 KiB). All exit 0, zero swaps, standard axioms only.
J9487 initially stopped in dependency preflight before a pin or compiler
receipt existed; its source snapshot is retained as `preflight-9487-*`.
After NormalCarrier compiled, J9487 was used for exactly one real compile.
No existing receipt or source/dependency compilation was rerun unchanged.

## Native full-byte gate: demonstrated verification obstruction

The part-41 native/reference control check used only two arbitrary first
bytes per 64-byte candidate. The Lean owner bridge above covers arbitrary
arrays, but the external native-to-reference connection must also preserve
arbitrary arrays before it can support a full native source claim. This
continuation explicitly tried to close that gap rather than promote the
compressed control check to an arbitrary-byte theorem.

`selected-api-full-bytes-v1` makes all 64 bytes of all sixteen candidates
arbitrary, retaining arbitrary public nonce, OS statuses, returned secrets,
call count and successful-draw count. Its native method is verbatim from
`state_only_entropy.rs` (`native-source-check.json`). At 363.347 seconds the
CBMC child was still expanding the recursive zero-test and had reached
6,451,548 KiB RSS. I sent TERM to that exact child, retaining the receipt
(exit 1, zero swaps, scope peak 6,616,354,816 bytes). This was an intentional
resource review stop, not an OOM, a counterexample, or a failed assertion.

The replacement isolates the recursive zero-test. `zero-helper-exact-v1`
checks the original helper against direct array equality at index zero, the
only entry index used by generate/run. All 19 checks pass for arbitrary
32-byte arrays: exit 0, 0.533 seconds, reported peak RSS 134,472 KiB,
zero swaps. The original Rust reference is retained as `owner-original.rs`;
the Kani-only `owner.rs` replaces just this helper and asserts its call
index is zero. The generated Lean source continues to describe the original
structural helper, already proved by symbolic suffix induction.

`selected-api-full-bytes-fast-zero-v1` then checks the changed reference
against the same verbatim native method. Symbolic expansion finishes in
85.754 seconds; 34,746 verification conditions reduce to 1,860. Solving
these does **not** finish within the capped 600-second attempt: exit 124,
wall 600.082 seconds, scope peak 6,602,473,472 bytes, zero swaps. The GNU-time
RSS field is 15,300 KiB for the timeout process tree that was reaped; it is
**not** the peak CBMC RSS. A live observation at 9:27 showed 6,436,716 KiB
for the child. The scope peak is retained as the reliable aggregate resource
measurement. The logs report no counterexample, but do not certify the gate.

Each attempt has its own retained input snapshot, SHA256 manifest, command,
source revision plus exact harness overlays, raw stdout/stderr/time and
cgroup receipt under `native/`, `native-input-snapshots/` and `pins/`.
The original reference matches the part-41 extracted source byte for byte.
The later helper substitution is not misrepresented as an unchanged rerun.
The same pinned Kani target cache is reused; no larger cap is attempted.
Time was in MIR compilation/symbolic control and SAT checking, not field
arithmetic. Kani requires its verification dev MIR build; no unoptimized
arithmetic release gate ran.

**Exact next interface:** prove the one-candidate transition of the verbatim
native `generate_for_mask_nonce` body, for arbitrary 64-byte successful draws
and OS errors, including nonce, copied fields, status, call/draw counts and
retained state; compose that transition through the sixteen-iteration
native for-loop into `AspisR1PublicNonce41.owner.generate`. The zero-test
helper itself is now checked. The existing compressed control gate plus the
new arbitrary-array Lean bridge do not silently discharge this remaining
native loop relation. No unconditional native owner or whole-prover theorem
is claimed. Per the user's stopping rule, work stops on this demonstrated
verification obstruction; no unchanged timeout rerun or cap increase is used.

## Verbatim active endpoint before/after: unchanged

The full original module binders and body are retained in identical
`endpoint/before.lean.txt` and `endpoint/after.lean.txt` snapshots.
The active statement quantifier remains `x : Statement K CommitHandle`;
the arbitrary `rust : FSExperiments K CommitHandle Aux R1Bat F` and
`RustProverRefinement` premise remain. The D146 deployed statement-domain
restriction has not been silently installed without the source join.

Before:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```


## Final audit, scope and remaining work

J9493 compiles `R1Z.ProverCommitAudit42`, exit 0, wall 1.73 seconds, peak RSS
4,147,688 KiB, zero swaps. It prints axioms for all **56** new top theorems
and the existing deployed endpoint: every list is a subset of
[propext, Classical.choice, Quot.sound]. `final-proof-audit.json` verifies the
final source bytes and the final audit's retained dependency objects against
the installed host sources/objects. `theorem-inventory.json` enumerates the
actual statements audited. No rejected draft is treated as accepted because
Lean printed an axiom line containing its generated error placeholder.
The collector retains rejected attempts separately from accepted receipts.
All 52 real Lean compiles use J9442–J9493; J9400 is a refused existing receipt,
not our compile. The assigned range is not exhausted. The range inventory is
a preflight record, not falsely described as a post-build inventory.

The local bounds and run agreement are not a completed successful **source**
continuation with both worlds' joint adaptive reservation/oracle histories.
The charged-hit theorem retains RCommitBytes, ROpen and RComLog, and the
concrete global run retains RAddrIn, RCausal, public memo coherence and the
private bad-event complements. These are existing source/model obligations,
not added trust items. The new theorems establish their normalized local
instances or consequences only as stated. In particular, an unrestricted
subsequent callback is not asserted to implement the native mask builder,
serializer or simulator publication.

Trust list remains **P1, P7, TrustedStd, E1, E2**. E1 is the law of successful
OS draws; E2 is atomic durable reservation. No nonce probability law, ledger
cap, availability assumption or new TrustedStd field is added. Public nonce
choices remain arbitrary. D146's source-representable statement domain and
D143 observables remain the announced deployment scope. The unchanged
endpoint still quantifies over `x : Statement K CommitHandle` and arbitrary
`rust`; this continuation does not silently install D146 or remove
`RustProverRefinement`. Its before/after statements and complete module
snapshots are identical. The part-40 numerical envelope is reused unchanged
and remains conditional; this is not a <2^-100 deployed-source theorem.

Complete native simulator publication, the literal source-to-FSExperiments
conversion, `shippedProverExperiment`, both concrete WholeRunJoins, and the
endpoint without RustProverRefinement remain **open**. They were not replaced
by definitions equating source to model or by structures assuming their own
conclusions. The native full-byte loop relation above is the next deliverable
before extending the local generated-owner theorem into that composition.

All Lean work ran on the pinned build host with -M7000 in scopes capped at
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Native checks used
the same caps and `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`. Recorded aggregate
reservations stayed below 55 GiB. No local Lean build, cold dependency build,
uncapped job, memory-killed rerun, unchanged full regression or full frozen
manifest replay was performed. The full source experiment is not ready for a
formal release replay. No SSH session went silent for twenty minutes.

All **491** tracked files under `crates/` and `programs/` remain byte-identical
to task base f57f0546d8af9a4355a3df1f8eaf91dc7a4e33c4, verified by
`shipped-sources-unchanged.json`. There are no new untracked shipped sources.
Thus the shipped-file rule does not require an ELF rebuild. Historical ELF
evidence is reused only for unchanged shipped artifacts. No binary, .olean,
LLBC, ELF, tarball or local target directory is committed. No wallet/account
key or funds was created, modified or removed. No push or merge occurred.

Stage commits: `e8f03ae14` (raw domains), `895e2347f` (generated owner and
reservation model), `49213759b` (concrete normalized bounds and run),
`9747473e3` (charged adaptive reads and selected retry callback). The final
commit retains the focused audit, native verification obstruction receipts
and this report. **Target not yet established.**
