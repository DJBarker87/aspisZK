# pv-alib resume3 — audit and candidate replay checkpoint

Same worktree and branch, starting at `828c0ce4af`. Historical report follows
and is superseded by this checkpoint wherever status or ID allocation differs.

52775 output and axioms were recovered read-only from `runs/52775`; no replay
of its unchanged source occurred. Receipt `52775.json`: exit 0, 1.07 s,
2,637,212 KiB peak RSS, zero swaps, source revision
`80c2e3cfda4c696a740df920ff5e06f01c797a7c`, standard axioms only.

Before the first resume compile, all 5,673 external objects were verified
against research's coherent replay manifest, including actual LEAN_PATH
selection. `resume3-external-verification.json` has zero mismatches. Project
cone sources were checked against the EJR record and committed SHA source
records; `resume3-project-preflight.json` has no missing module or mismatch.
Own MoveWorld/MoveSelected drafts were absent remotely and await private staging.

V233 and V265: no longer provisional for the scoped library/source candidate
claim. Combined audit `PV_AL_Rows233265Audit`, 37698: exit 0, 1.08 s,
2,630,884 KiB, zero swaps, revision `828c0ce4af`, 159 axiom reports, all subsets
of {propext, Classical.choice, Quot.sound}. It covers every closing theorem
and own support declarations of both cones. Rejected 37697 had duplicate
namespace qualification in generated queries; no theorem failure or credit.

One cached candidate cone replay `PV_AL_Rows233265Replay`, 37600: exit 0,
0.97 s, 2,634,172 KiB, zero swaps, same revision. All 41 project modules
import together; seven closing signatures check. Its axioms result is the
combined audit 37698; this replay itself emits signature checks only.
`resume3-candidate-cone.json` and 37600's dependency-object hashes freeze the
exact cone. This is focused cached candidate evidence, not a full manifest
or deployed endpoint replay. V232 and SHA-NI semantics remain untouched.

V184 remains OPEN while the native/world and selected bridges are checked.
No endpoint premise or trust field has changed. Target not yet established.

ID correction: all historical 52700-52775 uses were invalid cross-job reuse;
their evidence is retained without reruns. Resume3 uses 37600-37699 ONLY,
with 37697-37699 reserved for audits. 3 of the remaining 25 Lean attempts
are now spent; 22 Lean attempts and 4 Kani runs remain.

---

# pv-alib resume from 86aae376c0 — host-stop handoff

Worktree `/Users/dominic/ZK/.worktrees/pv-alib`, branch
`codex/pv-alib-20261027`. **Target not yet established.**

The initial report is retained verbatim in `REPORT-initial-stop.md`. Lead
ruling D304 supersedes its stop decision: the checked `[17,29]` allocation
mismatch refutes the proposed copy reference, not ledger row V184. Both pinned
and initial native receipts remain in this directory and the counterexample
remains part of this report. No ledger statement was weakened.

## V184 progress

Before: `ProverRwFull.ExternalFuns.op33`, exact complete Result/value law with
allocation/world carrier, arbitrary generic inputs.

The new safe `pop_move_reference<T>` has no Copy/Clone bound and uses
`remove(len-1)` only on a nonempty vector. The optimized pinned nightly native
differential `pop-move-world-03` passes 99 cases: lengths 0–32, capacities
length+0/+1/+17, payload `Result<Vec<u32>,Vec<u8>>`. Native and reference retain
their respective buffer identities and capacities, return identical complete
values and remaining contents, and each make zero alloc/realloc/dealloc calls.
This is a measurement, not an unbounded machine theorem.

No-stub Kani `kani-pop-noncopy-01` passes 697 checks (12 unreachable), arbitrary
bytes and both Result variants, lengths 0–4, unwind 6. No arithmetic stubs or
function replacement was used. Buffer/capacity preservation is checked; the
allocator counts come from the separate native differential, not from Kani.

Lean attempts 52706–52707 prove `PV_AL_PopWorld.complete`, `.retains_buffer`,
`.remaining`, `.zero_allocations`, `.nonvacuous`, and
`PV_AL_PopSelected.{callback,consumed,world_projection}`. These use an explicit
world and retained buffer/capacity carrier; arbitrary pre-existing allocation
history is preserved. Every vector has an admissible carrier, and the complete
Result is `ok` without a conclusion-shaped premise. These are model and
candidate installation theorems, not a completed native remove source law.

The borrowed reference extracts with the unchanged pinned extractor, but
`Vec::remove` remains external. Expanding native `remove`/`try_remove` is
rejected by the fail-closed structured-Drop preflight; the owned wrapper is
also rejected for structured Drop. The emitted external axiom template is
retained as rejected extraction evidence, never installed or kernel-accepted.
After: native remove fidelity remains; V184 stays **OPEN**, no closing theorem.
The other two rows received real source-law attempts and candidate results below.

## V233 selected split-block law

Before: `ProverRwFull.ExternalFuns.op209`, selected split_blocks source/value
law for arbitrary sized input slices and link to the consumed callback. CBL's
fixed soft digest did not supply it.

After: the selected **library-law candidate** is supplied by
`PV_AL_SplitSelected.native_callback` and `.consumed`, with
`PV_AL_SplitBridge.source_reference` and `.consumed_reassembles`. Status:
**OPEN -> CLOSED-ON-CANDIDATE** at this scoped library-law boundary. The complete
source reference law is `PV_AL_SplitObservation.complete`; it covers arbitrary
representable slices and arbitrary block sizes, including division-by-zero
failure. The consumed native 64-byte specialization has no length premise.

The safe Drop-free reference extracts with unchanged pinned tools and has no
external-function holes. `PV_AL_RangeLoop.source` proves its range-copy loop by
induction; no concrete long input is kernel-normalized. `PV_AL_BlockCodec` and
`PV_AL_SplitCarrier` prove exact bytes through the native generic-array storage.
`PV_AL_SplitNativeShape.consumed_storage` identifies the pre-existing consumed
block carrier. The native USIZE field is derived from literal typenum size
expressions, not assumed. Four auxiliary numeric constants/expressions are
installed (156/178/192/202); no additional ledger-row credit is claimed.

`kani-split64-02` is a no-stub native/reference gate: arbitrary bytes and output
coordinates, lengths 0–129, unwind 132; 389 checks pass. `native-split-02` checks
1,026 prefixes through length 1025. `SPLIT-FIDELITY-SCAN.json` records restoration
and output preservation. The rejected owned temporary-vector extraction and
initial no_std import error are retained. One overbroad trait-record
simplification (52735) was stopped after 76.29 s at 2,636,476 KiB, then replaced
by a projected size recurrence and small scalar proof (52747/52748); no limits
were raised. Attempts 52753/52755 print standard axioms only.

There are no conclusion-shaped or source-equality hypotheses. Every input
slice has a concrete successful 64-byte callback result; the native trait and
its size are constructed and checked. Other callback instantiations retain
their original operation. This is not an unbounded native-machine refinement
or a deployed endpoint instance: the bounded P6 gate's scope remains explicit,
and whole native composition/replay remains separate. No SHA-NI semantics
claim is made, and V232 is untouched.

## V265 source callback and structural gate

Before: `ProverRwFull.ExternalFuns.op259`; the prepared selector lacked the
native/reference source gate. After: **OPEN -> CLOSED-ON-CANDIDATE**, at the
selected source/library-law boundary. Closing theorems:
`PV_AL_CircleNative.source_reference` and
`PV_AL_CircleSelected.{native_source,consumed}`. They cover every block and both
rows with complete Result behavior. Both carrier roundtrips and both row
images are proved. No totality, field equality, source-equivalence or
conclusion-shaped hypothesis is assumed.

Ruling (k)'s structural route is used. The owned safe reference preserves every
frozen arithmetic call and its order, singularity priority, both map errors,
fallback constants and row selection. Explicit matches replace ok_or/? and
unwrap_or_else outside shipped crates. `STRUCTURAL-CIRCLE-GATE.json` checks the
complete pinned native control bodies and identical fallback parameters.
`PV_AL_CircleControl.native_owned` proves the generic control transport with
failure/divergence intact; the native map/fallback/wrapper equations specialize
it to the same extracted arithmetic. The relative sampler source path in the
extraction metadata is resolved against its proof crate, not the SSH login
folder; `circle-native-input-pins.json` checks every relevant source file
against this worktree.

The unchanged pinned tools extract the reference with no external-function
holes or opaque arithmetic leaves. Three positive shift-count literal ABI
mismatches were normalized to the current scalar API; the generic U64 shift
identities are proved in `PV_AL_ShiftLiterals`. Exact edits are recorded in
`primitive-shift-normalization.json` and reproduced by `promote.py --check`.
The extractor and release Rust are unchanged. Source, structural-link and
selected-law checks print only standard axioms (52756/52758/52759/52760/
52763/52764/52767).

`native-circle-owned-03` passes 8,712 wrapper comparisons (8,582 accepted;
130 rejected/fallback), direct map comparisons, directed ±i singular cases,
and both row fallbacks. Earlier reference tests and failed closure/core/Drop
extractions are retained separately. `CIRCLE-FIDELITY-SCAN.json` records all
three live Array.update results and quotient reuse. The fresh Lean emission
(52765) and native Rust agree on zero and FF digit fixtures, including
`[255,2048,7168,14336]`, where quotient writes change the output. The legacy
mut-iterator low_base_p_digits body is absent from this op259 graph. No
chained-field-arithmetic Kani was attempted.

This is a structural source/library result plus fresh extraction and native
checks, not an unbounded whole-machine proof or a deployed endpoint instance.
The final owner dependency replay and whole native composition remain separate.
Final audit and closure replay remain pending at the host stop described below.

No endpoint premise or T field changed. No `crates/` or `programs/` file changed,
so no ELF rebuild is claimed; the three release pins remain inherited, not
freshly checked. The initial `[17,29]` copy-reference counterexample is retained
and is not relabeled as a row counterexample or a successful gate.

## V184 further source work and exact remaining gap

Attempts 52768/52769/52770/52772/52773 pass. In particular,
`PV_AL_MoveLast.source` proves the complete generic Result law for the safe
move reference using the explicit `Vec::remove` library model, for every
representable vector and every payload Type, with no Copy/Clone bound.
`PV_AL_MoveFacts` proves the last index bounds and that the suffix copy count
is zero. `PV_AL_MoveMemory.last_copy` proves the data-buffer memory is unchanged
for every element width, including zero-sized types. The explicit world model
retains allocation history/counters, address, capacity, data bytes and an
arbitrary external frame. No source-equality hypothesis is introduced.

These facts do not yet close the native/world association. Attempt 52774's
native-value bridge failed on a guard simplification; its failed log, including
Lean's error-generated `sorryAx`, is retained and receives no proof credit.
The adjusted 52775 source was admitted, and its fetched time log reports exit
0, 1.07 s, peak 2,637,212 KiB and zero swaps. However, output/axioms collection
failed, so it is **not accepted for closure**. `52775-INCOMPLETE.json` distinguishes
the observed timed exit from the missing proof audit. `PV_AL_MoveWorld` and
`PV_AL_MoveSelected` are written, uncompiled drafts; their statements are not
claimed as theorems. `pop-zst-world.rs` is an unexecuted additional native test.

V184 therefore remains **OPEN -> OPEN**. Before: exact selected op33 complete
source/value law with explicit allocation world. After: generic move-reference
value and zero-copy facts proved; native/world/selected bridge and frozen stdlib
structural association still pending. There is no closing theorem credited.
The 99-case allocation observation and 697-check Kani gate remain valid at
their stated bounds. The old `[17,29]` copy-reference counterexample remains
retained as a failed approach, never a counterexample to V184.

## Host stop, accounting and handoff

Host SSH receipt collection failed with a missing `52775-output.log`; a
read-only follow-up exited 255 with `Connection closed by 100.108.41.90 port 22`.
Per `local-lean.txt` rule 5 ("If the launcher or host misbehaves, stop and report
the exact error ... the lead fixes infrastructure"), no further host scope was
launched and no infrastructure was repaired. This is an infrastructure stop,
not budget exhaustion, a row counterexample, or an ELF mismatch. `HOST-STOP.txt`
records the exact failure. Own host cache cleanup is deferred because the
host connection failed; preserve source, receipts and keys when cleaning caches.
No wallet/account keys were created or removed.

Total: **75/100 charged Lean attempts**, of which 40 have accepted complete
receipts, 34 are rejected and 1 has incomplete receipt collection. The resume
used 69 of its 94 remaining attempts. **2/6 Kani runs** passed; 25 Lean attempts
and 4 Kani runs remain. IDs 52700–52775 are used, with 52727 uncharged; prior
excluded IDs remain excluded. Audit IDs 52997–52999 are unused. The latest
user instruction explicitly reauthorizes the full 52500–52999 block despite
the earlier common-file range correction; no claim of global ID exclusivity
is made. `TALLY.json` and per-attempt source snapshots retain exact accounting.

`RECEIPTS.json` records exact targets, exits, wall/RSS/swap, revisions and
printed axioms for all complete receipts. Accepted receipts print only standard
axioms; failed logs are never treated as accepted proofs. The only incomplete
receipt is identified separately. Capped scopes used 6G high / 8G max / zero
swap / 64 tasks and Lean -M7000; no caps were raised. Generator promotion
`--check` and the circle structural gate pass locally at handoff. No final
combined axioms audit or frozen dependency-manifest replay was performed:
focused V184 prerequisites are not yet fully audited. Candidate row results
are not a coherent release replay.

Endpoint assumptions removed: **zero**. Retained: all deployed endpoint,
whole-native composition and owner-integration obligations. Added/changed:
no endpoint premise, simulator/observer weakening or T field; only scoped
candidate source laws and proof-only references. V233 and V265 are candidate
library/source closures, subject to owner integration and final replay. No
release Rust source changed. Inherited ELF pins (not freshly checked):

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Next: recover the existing 52775 output/axioms without rerunning its source;
then compile the smallest changed native/world/selected bridges, check the
frozen stdlib structural link, perform one combined axioms audit and one final
candidate closure-manifest replay. Clean only own compiled caches after those
checks. **Target not yet established.**

Source/proof commit log from `aa27e73f99` is retained in `COMMITS.txt`;
`f1db3be67a` contains the final V184 attempt and host-stop evidence.
Working tree was clean after that path-limited commit. No push was performed.
