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
