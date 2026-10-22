# S126 fixed-input caller export, 22 October 2026

S2 remains OPEN. This addresses the reference-layer existential-input gap
identified in the last section of `HANDOFF-SESSION-A-20261021.md` at
f4669da3e298974347f8aa7faacddce36ebabe72. The root research worktree and the
lead interface were read only; their source, objects and evidence were not
modified. This is not an inhabitant of all fourteen `S2CallerFacts` fields.

## Exact new result

The recommended consumer is
`AspisS2OwnedStage1.SdkReference.ProofGate.FixedLinked.borrowed_stage1_fixed_input_witness`
in `lean-candidates/s126-caller-boundary-20261021/S126SdkFixedInputExportV1.lean`.
It starts with one complete successful installed borrowed-reference stage1
execution, including the original reverse release finalizer, and concludes:

- `inputBytes initial 0 = ok proofAccount` and
  `inputBytes initial 1 = ok publicBytes`, where `inputBytes` is the actual
  emitted account-index/data-slot/cell-read/deref computation on the fixed
  **initial SDK state**;
- that same full proof account has58295 bytes, and the first-call proof is
  exactly `(proofAccount.val.drop688).take57607`, of length57607;
- the actual source decoder succeeds on those same public bytes;
- the current source `firstCurrent` succeeds on that public/proof suffix,
  retaining the same digest/error interpretations and release observer None.

The intermediate `FixedLinked.SourceLinkedFirst initial ops verifierOps`
also retains the same decoded statement/common/candidate encoder, actual
Vec.index[688,58295) operation and reference gate. Both
`owned_stage1_source_linked_first` and `borrowed_stage1_source_linked_first`
derive it. This supplies the identity-bearing witness requested in the lead
handoff, at the complete extracted reference's initial heap.

## Before/after and retained premises

Previously `Linked.SourceLinkedFirst ops verifierOps` existentially selected
its proof/public buffers with no initial account-read equations. The new
predicate adds **two conclusions** connecting those same witnesses to
initial account0/account1. Program, SDK states, instruction, Ops and current
verifier Ops retain their quantifiers. The sole enclosing execution premise
is still successful complete installed stage1. There is no new input match,
frame, clone, candidate/tag, parsed-public or independently successful child
premise. `forget_initial_inputs` formally derives the exact previous
predicate from the strengthened one, on the same carriers and call results.

The proof follows the complete emitted parent, retains each reached account
and cell read, and composes the existing checked acquire counter-update byte
frames. It normalizes only the already proved value-preserving byte clone.
It does not assume a free frame predicate. `gate_proof_length` consumes the
existing TOTAL wrong-length rejection theorem; `compact_suffix_total`
supplies exact successful range contents and length. No parser/multiproof
cone was reproved or changed.

These initial SDK equations are **not yet identities with an externally fixed
native runtime snapshot**. Native-to-reference initial-heap embedding and
successful native continuation binding still have to instantiate them.
They also do not establish writer→account→TX2-reader transport, ASF8 public
reconstruction, node/y1 views, complete call order, account metadata effects,
or the total local digest interpretation. The320-byte ASQ8 instruction,
1880-byte ASF8 serialization, verifier checkpoint and Pool checkpoint remain
distinct. Existing lead interface lemmas can consume the suffix equality
once the native input interpretation is proved. No whole S2/S6/S1, TOTAL
caller or100-bit soundness conclusion is claimed.

## Focused verification

| Target | Accepted receipt | Exit | Wall s | RSS bytes | Swap | Axioms |
|---|---|---:|---:|---:|---:|---|
| S2SdkFixedInputCallerV1 | s2-sdk-fixed-input-caller-v10 |0|14.591208833|3492069376|0|standard3|
| S126SdkFixedInputCurrentV1 | s126-sdk-fixed-input-current-v1 |0|6.006692583|3296559104|0|standard2|
| S126SdkFixedInputExportV1 | s126-sdk-fixed-input-export-v2 |0|17.924650792|3240902656|0|standard4|

All audited axioms are subsets of[propext,Classical.choice,Quot.sound].
Smallest changed target, then dependent current-caller bridge, then suffix
export were compiled with Lean4.32.0, `lake env lean -j1 -M4400`, the atomic
local lock and pinned warm imports. No cold build or unchanged full replay
ran. Exact source/tool/direct-import pins, object hashes (no exported objects),
source context e281e7de3 and failed sources are retained under
`evidence/s126-current-caller-20261021/`. The focused transitive import manifest
is `focused-import-pins.json`; `accepted-targets.json` adds only these three
accepted receipt rows.

Attempts1..9 are excluded. Attempt1 lacked a warm import in its selected path;
the recorded existing union fixed that environment without rebuilding.
Subsequent diagnostics fixed a nonexistent Expr projection accessor, metadata
on the target expression, typed tag-read selection, focused-goal handling and
the heap projection/frame-chain matcher. Error-recovery sorryAx reports from
failed compilations are not accepted proofs. Accepted sources contain no
sorry, custom axiom, native_decide or resource override. Export-v1 was green
but is superseded by v2, which additionally exports the complete borrowed case.

## Reference admission split

`evidence/s126-current-caller-20261021/sdk-reference-admission/` is a separate
source-only Kani packet. `proofs::reference_admission` passes all1722
noncover checks and both covers, exit0,15.182s,575428KiB RSS,swap0, in a fresh
6G/8G/MemorySwapMax0 scope. It constructs the complete borrowed reference
from the native-derived decoder-entry scalar facts, on the original owned
buffers, with the same scan=false boundary. It reaches the original public
allocation exactly once, returns exactly InvalidAccountData and restores the
recorded counters/Rc/lamport state. Proof slot remains arbitrary0..2; proof
counter may be saturated; proof/checkpoint alias remains allowed at this prefix.

This removes the need to solve two entire prefix executions in one solver
query. It does not itself prove shared native/reference execution, actual
scan transport, successful continuation substitution or unrestricted runtime
embedding. The borrowed source equals the previously checked source byte for
byte. Local-path dependency snapshots were recorded after the check; they
are not a new release freeze. `check-reference-admission-packet.py` validates
the source-only manifest, exact harness/stubs, ordinary result/covers, source
and tool pins and unchanged borrowed parent without a solver replay.

## Next enclosing obligation

Connect a successful original-SDK native execution to this fixed-initial-heap
reference witness, with installed actual child calls and their ordered effects.
The all-window native certificate remains a decoder-error-prefix frame and
cannot supply that success-domain binding. The actual std-any scan, cut
continuations, native heap/ABI interpretation and child/oracle transport stay
explicit. After that connection, compose the fixed source-first witness with
S1's original Prepared/prepared_claim trace; the existing trace/parsing proofs
remain reusable. Aggregate freeze adoption/re-pin and final coherent release
dependency replay are still required. No shipped source or artifact changed.

## Dependency-pin correction for the reference admission receipt

The v1 receipt above lacked pre-execution local-path dependency inventories.
This missing evidence justified one focused repeat after changing the runner
to record those inventories before codegen/solver and verify them unchanged
afterward. `sdk-reference-admission-check-v2` passes all1722 checks and both
covers: exit0,13.369s,575196KiB RSS,swap0, fresh6G/8G/0 scope. Source/lock and
four local dependency trees are pinned before the run; exported source copies
match those pins, and every postcheck is true. The accepted packet is now
`sdk-reference-admission-v2/`; the focused checker selects v2. Original v1
source/receipts are retained with their historical qualification. This repairs
the source-pin omission; it does not enlarge the conditional decoder-error
prefix scope. Byte-identical dependency source/log snapshots retain their
original whitespace. No unchanged Lean or release replay was run.

## SDK leaf coupling and first-entry continuation (2026-10-22)

The lead's final section of `HANDOFF-SESSION-A-20261021.md` remains the
consumer specification. The fixed-initial-heap Lean exports above identify
initial account0/account1, account0 length58295 and exact suffix57607; they
have not yet been instantiated with the externally fixed accepted SDK run.
They do not populate all fourteen fields of `S2LeadInterface.S2CallerFacts`.
In particular checkpoint retention/TX2 public reconstruction, reached node/y1
views, writer/account/reader transport and ordered oracle laws require their
actual independent witnesses. Byte frames imply none of those oracle laws.

New accepted source-only packets are `sdk-live-pairs/` and
`sdk-drop-frames/`. Their focused checkers reproduce source generators and
check original source, locks, exact target metadata, all-properties summaries,
source manifests, resource limits and matching prior unary model/frame pins.
No unchanged Lean or full release replay ran.

| Target | Exit | Wall seconds | Peak RSS KiB | Swap | Exact bounded claim |
| --- | --- | --- | --- | --- | --- |
| sdk-live-pair-length-check-v1 | 0 | 2.926 | 345496 | 0 | actual SDK/model length result + counter/restoration |
| sdk-live-pair-shared-check-v1 | 0 | 3.301 | 349268 | 0 | actual SDK/model real shared guard/error + counter/Drop restoration |
| sdk-live-pair-exclusive-check-v1 | 0 | 3.155 | 349816 | 0 | actual SDK/model real exclusive guard/error + counter/Drop restoration |
| sdk-drop-shared-frame-v1 | 0 | 10.728 | 1388348 | 0 | actual Ref Drop writes only live counter and decrements it |
| sdk-drop-exclusive-frame-v1 | 0 | 10.905 | 1002148 | 0 | actual RefMut Drop writes only live counter and resets it |

Kani0.67.0, original solana-account-info2.3.0 source
`6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a`;
full source/tool/lock/import dependencies appear in the packets. Each solver
received fresh admission, MemoryHigh6G/MemoryMax8G/MemorySwapMax0, optimized
backend and one compilation job. `#print axioms`: N/A for these bounded Rust
checks; no new Lean theorem or axiom. These are helper correspondences, not
TOTAL source execution or a discharged enclosing source/caller premise.
The real typed heap domain covers10MiB/all views, signed borrow counters and
all nonzero usize Rc headers. General valid runtime heap embedding and
contextual/source/ABI composition remain explicit. Prior matching unary
actual/model counter-only frames are reused, not rechecked. The new ordinary
pairs replace the unsuccessful paired DFCC attempt, not those unary frames.

`sdk-coupling-attempts/` retains unsuccessful whole-prefix pairs, point-frame
and reference constructor attempts. They receive no proof credit. Source
changes, not cap increases or unchanged replay, are required next. In the
first reference constructor, successful checkpoint Vec replacement also
invalidates its attempted checkpoint pointer-preservation assertion. That
assertion is corrected in the next candidate; proof/public pointer identity
and checkpoint byte identity are different claims.

The native first-entry-only experiment progresses beyond the historical
decoder-error cut, but is not yet a complete source certificate. In v1,
windows4/11 failed the observer assertion and neither reached cover fired.
Generated-goto inspection found `observer()` reading the mutable bare
`Option::None` callback-retention global, although its Rust source returns
literal `None`. The callback assignment then changes this generated constant.
This is an instrumentation/codegen correspondence defect, not evidence that
the shipped release selects Some. The corrected candidate puts that retained
callback in a uniquely tagged GhostStorage object; source observer remains
literal None. Its affected window is checked first before extending coverage.
Previously passing v1 windows are partial historical evidence; no full entry
frame, successful native/reference join or whole S2 closure follows. Source
scan/comparison/typed-child installation, first-result/writeback effects,
valid runtime heap interpretation and ordered oracle transport remain.

## Complete corrected first-entry coverage and successful reference constructor

`sdk-first-entry-v2/` contains all17 corrected original-SDK entry cases:
15 proof windows plus public and checkpoint roots, no pending cases. Each
complete enabled inventory is reconciled against the raw all-properties log;
all noncovers succeed and both entry covers are reached. Per-target source,
lock, tool/import dependency pins, fresh admission, exit10 (the two reached
covers), exact wall/RSS/swap are in its receipts and `qualification.json`.
`local-check.json` records the local source-only audit. The checker reproduces
all17 source generators, requires identical source domains except coordinate
selection, and reuses the unchanged generic `S2SdkNativeFrameCoverageV1`
index/list proof (source20a9919c…). No unchanged Lean or solver replay ran.
These are actual original SDK first-entry byte/scalar/typed-call checks,
unlike the earlier decoder-error prefix. They still stop at first entry and
require actual child/gate/scan/runtime instantiation; no post-return frame or
whole S2 theorem is inferred from coverage.

`sdk-observer-codegen-mismatch/` retains the two failed v1 cases, complete
reports and exact generated-goto inspection. The corrected v2 source uses
uniquely tagged callback retention. The affected window4 passes after this
source correction; the entire17-case corrected family was then checked.
The actual release observer source is unchanged literal None.

`sdk-reference-first/` checks complete borrowed-reference successful stage1
from native-derived scalar facts, canonical slots, original buffers,
admitted comparison status/tag image, scanner=false and shared successful
typed children. All4195 enabled noncovers succeed; both covers reached:
raw exit10,65.312s,4708660KiB RSS,swap0, fresh6G/8G/0. Same decoded-public
projection, original first wrapper/None, initial proof/public pointers,
checkpoint output byte and restored counters/metadata are checked together.
Its source-only checker independently reconciles the complete raw inventory,
reproduces source and verifies every pre/post dependency pin. Checkpoint Vec
allocation replacement is distinguished from copied byte equality. This is
conditional reference construction, not a source-child installation theorem.

## Same-call checkpoint writer premise removed at the reference layer

New `CheckpointWriter.owned_stage1_fixed_saved_current` and
`borrowed_stage1_fixed_saved_current` in `S126SdkFixedSavedCurrentV1.lean`
consume one complete installed stage1 success and derive, together:

- initial account0 proof and account1 public byte views;
- full proof length58295 and its exact [688,58295) suffix of length57607;
- actual source decode of those public bytes;
- actual current-first success on those same bytes/suffix/split, with the
  existing decoded-reuse/None/source tx1 connection;
- final heap bytes at the ORIGINAL account2 data slot equal the SAME returned
  checkpoint, after the complete guard-release finalizer.

Before, `borrowed_stage1_fixed_input_witness` returned a current-first
checkpoint without asserting its saved final bytes. The new result retains
that same fixed-input/current-first conclusion and adds same-checkpoint
retention at the original slot. It does not add a writer, child-success,
range, clone, buffer-frame or independent saved-checkpoint premise.
The single accepted installed reference execution remains its only premise.
Account metadata stability, physical native storage embedding and TX2
writer/account/reader transport are distinct, still open claims.

Focused Lean4.32 checks, one local mkdir lock, -j1 -M4400:

| Target / accepted receipt | Exit | Wall s | Peak RSS bytes | Swap | Axioms |
| --- | --- | --- | --- | --- | --- |
| S2SdkCheckpointWriterV1 / s2-sdk-checkpoint-writer-v3 | 0 | 16.529665833 | 3232088064 | 0 | 2 standard-only reports |
| S2SdkSavedFirstV1 / s2-sdk-saved-first-v5 | 0 | 24.676025625 | 3232694272 | 0 | 3 standard-only reports |
| S2SdkFixedSavedFirstV1 / s2-sdk-fixed-saved-first-v2 | 0 | 22.872966667 | 3246161920 | 0 | 3 standard-only reports |
| S126SdkFixedSavedCurrentV1 / s126-sdk-fixed-saved-current-v1 | 0 | 11.026304500 | 3228614656 | 0 | 2 standard-only reports |

Standard-only means subsets of propext/Classical.choice/Quot.sound. Failed
historical drafts and superseded green intermediates are retained, excluded
from accepted targets; no sorry source, custom axioms, native_decide or resource
option override is used. Focused import hashes cover seven old/new accepted
targets and5616 selected objects; objects are not distributed. This is a
focused cached proof, not a coherent final release rebuild. Four caller files
are unchanged at the adopted S4 freeze, explicitly pinned in
`caller-source-adoption-overlay-20261022.json`; changed transitive S4/powers
semantics remain their owners' re-pin obligations. No shipped source or ELF
was changed. Whole S1/S2/S6 and the100-bit target remain unestablished.
