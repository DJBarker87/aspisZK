# PoolW handoff: phase 1 incomplete, Kani budget exhausted

Branch `codex/cx-pool-write-20261026`; original source/revision anchor
`f5179758aadda385a098982570bc17be2c48f263`. All stage commits local; no push.
**S2 OPEN. No global ledger row or whole-P1 premise removed. Target not yet
established. No concrete accepted attacker-chosen checkpoint write found.**

## Checked local source obligations

- **Actual native complete copy tail F2183–2188**, KANI012: arbitrary complete
  384/192-byte input/output arrays and arbitrary distinct public keys, real SDK
  cells with initial zero borrow counters, fixed Pool owner/normal writable
  metadata. Successful tail writes exactly the two supplied complete images,
  preserving keys, owners and lamports. Separate allocations are explicit; this
  does not construct the native accepted P1 prefix or canonical-history action.
- **Actual pure ASC8 codec**, KANI014–017: all checkpoint fields / all192 input
  bytes arbitrary, encoder header/master/domain/sequence/bump/reserved bytes,
  full encoder-decoder roundtrip, accepted decoder-encoder byte identity, and
  every selected lane-sequence encoding. No stubs.
- **Native freshness/metadata cuts**, KANI009–011/020–023/025–026: exact-size
  mismatch, all-zero/rent equivalence at default Rent, nonzero first-byte
  rejection, wrong owner/executable/readonly rejection, System-empty creation
  mode and Pool-owned zero/occupied modes. Full images/funds frames in their
  stated classes. KANI030/031 additionally check *tiny* empty/one-byte held
  borrow errors, not a general192/384-byte error/cleanup frame.
- **Actual pure planner on a narrower coherent class**, KANI033–035: fixed
  nonzero identities/policy and zero unused lane roots/frontiers; arbitrary
  bounded lane sequences, canonical supplied global root and bumps. First
  checkpoint outputs, repeat decrease/duplicate/overflow/next-sequence cases,
  and selected wrong lane master/order rejection pass. This is NOT arbitrary
  accepted-state coverage or proof of the strict lane decoder/global combiner.
- **Actual System-CPI helper construction/order**, KANI037/038/040: top-up,
  funded allocation/assignment, and zero-lamport creation, exact instructions,
  three account infos and all four signer seeds checked against a recording
  implementation of the original native runtime trait. Calls retain the
  recorder's prefix under its declared effect map. It does not execute or prove
  the actual System program, arbitrary runtime effect maps, Rent::get, or a
  whole accepted P1 path. Existing runtime trust is unchanged.

## Checked Lean scope

`PoolW_ZeroSource` is the Aeneas-extracted P6 Boolean-state index scan;
`PoolW_ZeroStep/ZeroArithmetic/ZeroExact/ZeroFacts` prove its symbolic total
exactness for arbitrary bounded slices and acceptance iff every byte is zero.
`PoolW_ZeroGuard` gives the P6 guard reference's precise metadata/read-error and
success inversion using canonical Hiq metadata. **Native whole-guard coupling
remains open.** `PoolW_Store` proves same-physical-public-key two-copy outputs,
other-account and full-metadata frames on a functional store, not an actual
runtime/history instance. `PoolW_Audit` audits all18 new theorems plus the
extracted definition: only propext, Classical.choice, Quot.sound.

## Exact obstruction and next source deliverable

Direct caller extraction AENEAS003 rejects AccountInfo slice indexing F2140
(type parameters containing mutable borrows, InterpStatements.ml:730). Native
root-crate encoder extraction AENEAS006 fails at pure419–422 (Unreachable,
InterpAbs.ml:1955); isolated planner AENEAS007 raises Not_found in
InterpReduceCollapse.ml:1991. The old full-Pool zero-guard extraction was never
rerun unchanged. AENEAS005 exits0 but omits all three selected external roots;
coverage audit rejects it as evidence for those bodies. AENEAS009 extracts the
P6 reference successfully. Raw templates with unfilled axioms are diagnostic
artifacts and are never imported into the proved family.

Missing phase-1 obligations:
1. P6/source coupling for the complete actual AS8C prefix and planner-wrapper
   F704–791/F2130–2188, preserving every earlier effect/error, including decode,
   Vec/Box allocation, fresh preparation, optional System CPI and post-CPI guard.
2. Native metadata/strict master and lane decoder, address/PDA seed/hash leaves,
   and their success/error joins on the same actual account snapshots. No new
   runtime item has been proposed or adopted to hide these source gaps.
3. Full arbitrary accepted planner coverage and the native guard/borrow-error
   continuation frame. KANI039's final CPI error-prefix check timed out;
   no corresponding error-prefix theorem is claimed.
4. Derive the final source certificate from accepted native P1, keyed by its
   actual public key and canonical committed action. The isolated native tail
   result cannot be substituted for this missing construction.

P1 writes planner/encoder ASC8 after optional **System** CPI; it contains no
verifier CPI or verifier-returned CP. CP unique-writer/native-child/copy facts
remain the separately reused Hist_/Hiq_/Hir_/SInt2 predecessor obligations.
No fourth history-only wrapper, CheckpointVersionBinding assumption, or new
whole-lifecycle trust item was introduced.

Phase2 needs the complete phase1 certificate above plus encoded marker65,
exact192 size and occupied-target freshness rejection, then exhaustive live
handler/close/CPI frames. Runtime-history work needs the same physical public
key and canonical action, admitted genesis/assignment, post-CPI store/load
association and rollback/retention, with the real native CP writer/copy events.
Upstream master/lane correctness and proof/public same-world binding remain
separate; these local results do not instantiate the final Hir_ lifetime law.

## Runs, resources, freeze and stopping condition

**Kani40/40 exhausted; Lean15/100 (8 pass,7 development failures).** Native
Kani22 pass,11 timeouts,1 unwinding failure,6 compile failures; all failed
snapshots/logs retained and excluded. KANI032's 35-iteration builtin memcmp
unwind failure was diagnosed (64-byte array), then split/replaced by80-bound
coherent checks033–035. No timed-out or memory-killed job was rerun unchanged;
no memory cap increase or tool/launcher repair. Tiny read-only validation is
not a prover rerun. Nine Charon and nine Aeneas extraction attempts are separately
receipted, not counted as Lean compiles. No package/manifest/SBF replay.

Every run has exact target/command, revision, source hash and snapshots,
dependency fingerprint, exit, wall time, peak RSS, swap and axiom output (N/A
for Kani/extraction). `PoolW_ATTEMPTS.json` indexes the complete receipts.
All scopes6G high/8G max/swap0/64 tasks; Lean-M7000; Rust optimized. Three
simultaneous own scopes were observed (24GiB aggregate reservation); final
scope inventory shows no live PoolW job. Other workers' scopes were untouched.
L015 final audit: exit0,2.0162405840237625s,4330460KiB,swap0, all standard axioms.

`PoolW_VALIDATION.json` passes source freeze, exact native slice matching,
all current Lean source→successful-receipt hashes, source/snapshot and cap/
optimizer/axiom checks, assigned diff and frozen SDK leaf versions/checksums.
The actual host Hist_src dependency tree and local repository both match the
**157-file union** of inherited132/132/133 compiler inputs
(`PoolW_INPUTS.json`, `PoolW_HOST_INPUT_MATCH.json`). These are input equality
checks, not newly built ELFs or source-to-SBF refinement.

No shipped source or cfg(kani) module in a shipped crate changed: proof-only
isolated crates live under this evidence prefix. No ELF rebuild trigger.
Inherited artifact pins, not newly reproduced:
- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No keys, funds or live accounts touched. No S1/S3/S4/S5/S6/S9 candidate,
session A worktree, NP6_/F3K_/prover-rw source or existing proved module changed.
Stop because the required Kani gate budget is exhausted. The remaining Lean
allowance cannot certify the missing native P6 gates; no partial result is
promoted into the requested complete source certificate.
