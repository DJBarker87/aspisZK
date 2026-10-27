# pv-alib resume at 86aae376c0

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
Work continues on alternative source routes and the other two rows.

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
V184 work continues within the remaining budget.

No endpoint premise or T field changed. No `crates/` or `programs/` file changed,
so no ELF rebuild is claimed; the three release pins remain inherited, not
freshly checked. The initial `[17,29]` copy-reference counterexample is retained
and is not relabeled as a row counterexample or a successful gate.
