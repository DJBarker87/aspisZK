# Prover commitment continuation 43

Target not yet established. Worktree base: 5296bb1e509fdd32ec3cbb4fc70f640db071e7c7.
Branch: codex/cx-prover-commit43-20261022. No shipped sources changed.

## Stage 1: sixteen-candidate owner

The per-candidate native transition gate passes all 174 checks for arbitrary
64-byte draws, OS status, public nonce, retained bytes and every reachable
call/draw counter in the 0–15 candidate prefix. The extracted native body is
verbatim except for explicit stop/continue outcome wrapping: success and OS
error become terminal `Some` values; fall-through becomes `None`. The prior
verified zero-helper contract is reused as a verified substitution, not a
new trust item. No whole-loop harness runs. The Kani gate verifies bounded
native execution; its source mapping remains an external P6 boundary, not a
Lean proof about Rust syntax.

`ProverCommitNative43.range_run` proves the native `Range<usize>` denotation
by induction over the remaining candidates, preserving the complete
schedule/tape/state transition. `increment` proves no counter wrap before 16.
`generate_owner` identifies the zero-nonce guard and sixteen-step loop with
`AspisR1PublicNonce41.owner.generate`; `continuation` retains arbitrary
subsequent observations of both result and state. This closes the specific
part-42 native candidate/finite-loop verification gap, with the native
boundary and its independently proved Lean composition kept explicit.

J9494 is a rejected elaboration draft. J9495 accepts all five new theorems:
exit 0, wall 2.19 s, peak RSS 4,173,992 KiB, zero swaps, each axiom list
[propext, Classical.choice, Quot.sound]. Exact targets, source hashes,
dependency fingerprints, commands, source revision and full compiler output
are in `../../100bit-spend-path-20261013/evidence/prover-commit43-20261022/lean/`.
The native receipt and pinned inputs are beside them under `native/`,
`native-input-snapshots/`, `pins/` and `harness/native-source-check.json`.
No inherited Lean source/object is changed by the new module.

## Remaining stages

Native simulator publication, the literal source experiment conversion,
`shippedProverExperiment`, both WholeRunJoins and the endpoint without
RustProverRefinement remain open at this stage checkpoint. Trust list remains
P1, P7, TrustedStd, E1, E2. No nonce law or ledger cap is added. D143
observables and D146's announced source-representable statement domain are
retained. No release claim or endpoint premise removal is made here.

## Publication caller checkpoint

J9498 accepts `ProverCommitPublish43`: exact six-part per-query byte order,
finite query-loop composition, node-slot fold/recursive agreement, padded
slot lengths, both final length guards, and replay/transcript/Merkle/merge
error precedence. J9499 accepts `ProverCommitLeaves43`: every pair consumes
two successive salts from the same retained coin state, folded leaves consume
one, all writes transport through the existing TrustedStd insert-state law,
and ordered iteration transports unchanged. J9503 accepts
`ProverCommitCompact43`: exact zero-high-half acceptance and low-half bytes,
compact-value fold/recursion, semantic-row fold/recursion, and successful
compact length. These are **local caller/algebra theorems**, not yet a
complete source publication certificate. Codecs and multiproof calls remain
explicit results in the publication driver; their concrete source identities
are not silently assumed. No new TrustedStd field or caller law is added.

J9496–9497 and J9501–9502 are rejected elaboration drafts. J9500 was refused
because a receipt from another job already exists; no compiler ran and that
receipt is not attributed here. A read-only inventory selected the next free
assigned numbers. Accepted wall/RSS/swap fields: J9498 1.38 s / 2,542,888 KiB /
0; J9499 1.33 s / 2,535,676 KiB / 0; J9503 1.51 s / 2,532,328 KiB / 0. All
exit 0; every printed axiom list is a subset of the three standard axioms.

The native leaf/query transition passes with arbitrary 4-byte payloads,
ordered coin-call trace and all returned salts, and length plus an arbitrary
selected output byte (48.626 s, 2,761,680 KiB, zero swaps). The initial full
output comparison failed an unwinding assertion because its 108-byte buffer
exceeded the fixed comparison unwind bound; it is rejected, not treated as
a source counterexample. The replacement changes the observed comparison,
not the source body or the unwinding-assertion policy. The compact-cell
transition passes 578 checks on all 32 bytes (including high-half rejection),
with native source equality audited modulo whitespace and visibility only.

The native merge call-boundary transition passes on arbitrary old/new 32-byte
answers, arbitrary address and retained frame, under the already named
TrustedStd insert contract. This checks caller control, not BTreeMap internals.
The full map state/ordered merge transport is the existing universal
`ProverCommitMerge33.native_ordered_loop_decode`. The separate larger sorted
substitute gate remains pending and is not used as accepted evidence.

The initial entropy gate collapsed OS error payloads to a status. The stronger
`candidate-full-bytes-error-payload-v2` additionally checks preservation of an
arbitrary opaque error code (u32 carrier), with exit 0, wall 3.044 s, RSS
277,032 KiB, zero swaps. The extracted owner and Lean induction already
preserve their generic error payload. The stronger native gate is the
accepted final boundary; the status-only gate is retained for provenance.

## Direct source padding closure

The isolated original `append_nodes` source translates directly: Charon v2
exit 0, 0.194 s, 175,784 KiB; Aeneas v2 exit 0, 0.279 s, 61,424 KiB; zero
swaps, `has_errors=false`, no external templates. V1 was a rejected launcher
root-name typo, not a compiler/tool obstruction. The generated Funs is
installed verbatim. The Types discriminant attribute is expanded to a unique
instance preserving Transcript=0 and Parse=1; generated resource options and
imports are unchanged. No inherited shared source/object is overwritten.

J9506/J9507 accept Types/Funs. J9514 accepts the generic source padding proof;
J9519 additionally accepts `ProverCommitPadding43.model`, installing the
concrete source helper in `ProverCommitPublish43.appendSlot`, including error
and exact bytes. The bound covers **out + nodes + cap** before subtraction,
not just final output length. It is an explicit source-capacity obligation,
not an assumption that the native call succeeded. J9519: exit 0, 1.51 s,
2,589,216 KiB, zero swaps, all four printed axioms lists standard. The port
and source hashes are retained under `extraction/AspisR1Padding43/`.
J9504, J9508–9509, J9513 and J9515–9518 are rejected drafts. J9505 stopped
in dependency preflight with no compiler or pin receipt and is retired.

The original larger sorted-map merge gate times out at 600.578 s, exit 124,
zero swaps, scope peak 6,694,014,976 bytes. The original padding gate times
out at 600.157 s, exit 124, zero swaps, scope peak 6,625,206,272 bytes. Neither
is accepted or rerun unchanged. GNU-time's 15,480/15,120 KiB reaped-parent
RSS figures do not measure the peak CBMC descendant; the retained cgroup
peaks are the aggregate evidence. Their replacements are the passing
contract-level native merge check plus the universal part-33 map proof, and
the directly extracted and proved padding source above. No cap was raised.

## Demonstrated next source interface: native parent collection

**Publication is not complete; target not yet established.** The next actual
source operation in `sim.rs:378` is:

```rust
let parents:BTreeSet<usize>=level.keys().map(|i|i/2).collect();
```

The exact statement, source SHA and accepted TrustedStd field inventory are
in `parents/interface-audit.json`. This is the native parent traversal that
assigns subsequent coin values and builds the stored sibling tree; replacing
it with an unordered set equality would lose the source coin schedule.

The focused native-source diagnostic keeps BTreeMap internals opaque, as
D145 requires. Charon and Aeneas both exit 0 (0.286 s / 181,564 KiB and
0.280 s / 64,944 KiB; zero swaps), but the result imports generated external
**axiom templates** for `BTreeMap::keys`, iterator map/next and, decisively,
`BTreeSet::from_iter`. Those templates are retained only as inert `.lean.txt`
and are never installed or imported. A translation with unresolved external
operations is not a source refinement. The diagnostic is a small source/API
probe, not a new owned reference containing forbidden iterator/map loops.

The existing named map laws cover empty, insert, get, ordered entries and
lazy entry insertion; they do not supply BTreeSet collection. D145 explicitly
says “Do not add any other field.” No BTreeSet law, opaque source-caller
success law or new trust item is added. The earlier list/map publication
proofs cannot silently discharge this distinct native operation. This is a
source/library interface obstruction, not a counterexample to privacy or to
the actual standard-library implementation.

**Exact next deliverable:** a source certificate that native collection and
iteration of `level.keys().map(|i|i/2)` yields precisely the increasing,
duplicate-free parent list of the decoded current level, with no missing or
extra parent and the same subsequent coin state. It must connect a small
structural owned parent collector to the native BTreeSet wrapper using a
verified source bridge under the current trust boundary, not an additional
TrustedStd field. Then complete `program_tree` and `multiproof::generate`,
the concrete compact prefix/row byte image and six-slot driver. Native
`indices.sort(); indices.dedup()` also needs its concrete source bridge; it
is not claimed proved by the salt/query loop results.

Per the stopping rule, dependent source-to-FSExperiments conversion,
`shippedProverExperiment`, both concrete WholeRunJoins and endpoint premise
removal stop here. They have not been replaced by model-equal definitions,
unproved callback laws or structures containing their desired conclusions.
The environment and public nonce remain adversary inputs in the local models;
no completed concrete deployed experiment is claimed. No new trust item,
nonce law, ledger cap or availability assumption is introduced.

## Verbatim active endpoint before/after: unchanged

Full surrounding binders and theorem body are byte-identical in `endpoint/before.lean.txt` and `endpoint/after.lean.txt`. The quantifier is still `x : Statement K CommitHandle`, the runtime is still arbitrary `rust : FSExperiments ...`, and `RustProverRefinement` remains a premise. D146 is retained as the announced deployment domain; it has not been silently installed in an endpoint lacking a source join.

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

## Final focused audit and handoff

J9535 accepts `R1Z.ProverCommitAudit43`: exit 0, wall 1.80 s, peak RSS
4,148,660 KiB, zero swaps. It prints all **33** new top theorem axiom lists
and the unchanged deployed endpoint: every list is a subset of
[propext, Classical.choice, Quot.sound]. `final-proof-audit.json` verifies
all final installed source hashes and the audit receipt's dependency-object
hashes. `theorem-inventory.json` enumerates exactly the audited statements.
Failed drafts, refused numbers and preflight-only failures remain separate
from accepted compiler evidence. No rejected `sorryAx` diagnostic is counted.
The Lean attempt JSON and native-attempt JSON retain target, command, exit,
wall, peak RSS, swap, source revision plus exact overlays, fingerprints and
full axiom outputs. All Lean compiles ran on the pinned host using Env J,
-M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0 and TasksMax=64. Native
and extraction gates used those same scope caps and the required RUSTFLAGS.
Reservations were checked below 55 GiB. No SSH session went silent for twenty
minutes. No local Lean, cold dependency build, uncapped gate, dense arithmetic
in a debug binary, unchanged full regression or full frozen manifest ran.
The dependency closure is not ready for a formal release replay.

All 491 tracked files under crates/ and programs/ remain byte-identical to
task base 5296bb1e509fdd32ec3cbb4fc70f640db071e7c7, with no new untracked
shipped file (`shipped-sources-unchanged.json`). The shipped-file rule does
not trigger an ELF rebuild; existing ELF evidence is reused only for unchanged
artifacts. No binary, object, LLBC, ELF, tarball or local target directory is
committed. No wallet/account key or funds were created, changed or removed.
No push or merge occurred. Trust list remains P1, P7, TrustedStd, E1, E2;
P6 native/source boundaries remain explicit evidence boundaries. D143's
observables and exclusion of timing/other side channels remain the announced
scope. **Target not yet established.**
