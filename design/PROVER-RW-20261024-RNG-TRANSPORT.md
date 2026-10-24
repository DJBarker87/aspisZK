# Secure callback error transport preflight

Branch codex/cx-prover-rw-20261023, continuation after reviewed067e1ddd1e and
proofc88daf1e50bec23f1d1425b33a4820ce963ddc7d. No shipped source, backend,
protocol, trust, feature, wire, security contract or artifact was changed.

## Exact result and obstruction

ProverRwRngTransportValidity.pattern_iff_nonzero proves, for Aeneas.Std.I32 x,
`((-2147483648 ≤ x.val ∧ x.val ≤ -1) ∨
  (1 ≤ x.val ∧ x.val ≤ 2147483647)) ↔ x.val ≠ 0`.
The two subtype conversions preserve the I32 value and are inverse in both
orders. This is a checked candidate representation lemma about the precise
archived LLBC pattern, not a Rust NonZeroI32 association. It has no native
carrier, provider, output-equivalence, layout or probability premise.

Before: native Error transport absent, existing callback theorems quantify
over uninstalled NativeTypes. After: unchanged native boundary, plus a proved
bijection between two mathematical subtypes of the already installed I32.
No premise of the existing callback/source theorem has been removed. No
native-operation theorem or secure factory binding is claimed by this packet.

A decisive current-route obstruction is retained aeneas-003: transparent
NonZeroI32Inner has an I32 TPattern of exactly those disjoint ranges; type
analysis rejects it before function translation (TypesAnalysis.ml:485).
Making the core declarations opaque instead yields two external type holes.
The existing NativeTypes adaptation installs neither. There is no supplied
native association to compose with the new bijection. Filling a template with
the subtype would propose that missing association, not prove it.

## Selected source and operation assessment

The archived failed LLBC selects x86_64-unknown-linux-gnu, little endian,
8-byte pointers; its includes expose getrandom::error::Error and both core
NonZero layers. getrandom0.3.4 error.rs selects i32/NonZeroI32 on non-UEFI,
with Error(NonZeroRawOsError) deriving Copy, Clone, Eq, PartialEq. Core's
NonZero<T> is transparent over T::NonZeroInner; the niche macro derives
Copy/Clone over pattern_type!(i32 is ..0 | 1..). Its unsafe constructor warns
that an invalid value is immediate UB. Zero must stay excluded.

Copy excludes a user Drop implementation (core marker.rs), supporting a
trivial destructor for the selected error. This is source evidence for the
proposed operation proof, not a proof that arbitrary ADTs can be copied or
all physical cleanup is trivial. EntropyError is an enum with Os(Error) and
RepeatedZeroBlock and a source From that wraps the exact Error. Its lifetime
must still be modeled through move/deinitialization. In the reused prototype
LLBC closure call_once16, the tuple field is moved to local3, Error::Entropy
is constructed, then StorageDead3/2/1 occur; there is no error-field read.
The closure's drop_glue25 only returns unit and ends argument storage. Those
are prototype declarations, not extraction of the actual secure closure.

Charon documents Move/Copy and LLBC StorageDead/Drop separately. Aeneas Move
sets the source place to Bottom; Copy checks absence of Bottom and delegates
to copy_value (with explicit ADT restrictions). drop_value preserves the old
value in a dummy binding, then writes Bottom, allowing outstanding borrow
bookkeeping. StorageDead additionally simplifies the dummy binding. Merely
replacing any of these operations by unit would skip those obligations.
The inspected extended backend's Drop branch also has a drop_as_no_op option;
this packet neither enables nor relies on it. No physical erasure follows.

The current prototype LLBC's Result.map_err9 is opaque; its accepted Lean
installation follows core result.rs:962–971's two match branches. That is
reused source-shaped value control, not fresh extraction of map_err/drop.
Likewise, native_from/callback_step/error_state proofs are reused conditional
control facts; no unchanged niche failure, runtime fixture or ELF gate reran.

## Concrete proposal for lead escalation, not implemented

Recommend an isolated extractor candidate for the exact I32 pattern, leaving
shipped Rust and Charon cb50 output unchanged. Do not erase TPattern, attach
an arbitrary opaque type, or generalize to arbitrary NonZero APIs. Scope the
feature to transporting valid error values through aggregate wrapping,
Result matching, From, move, selected Copy if emitted, and terminal disposal.
Fail closed on construction from an unchecked scalar, projection/cast,
transmute, comparison, mutation, or a different pattern unless separately
supported and proved. This is sufficient for this selected error boundary;
it is not a complete NonZero library implementation.

Proposed implementation sites in the pinned extended Aeneas source:

- `src/llbc/TypesAnalysis.ml`: recognize only TPattern(TLiteral I32,
  OrPattern[Range(MIN,-1);Range(1,MAX)]) as a non-borrowing refined scalar;
  retain its predicate and distinct type identity. Apply the same restriction
  in each analysis traversal; a catch-all unwrapping branch is unacceptable.
- `src/pure/Pure.ml`, `src/pure/PureTypeCheck.ml`: carry a specific refined
  scalar type, with no implicit coercion from I32. All generated visitors and
  equality/type checks must retain it. This avoids an unproved external sort.
- `src/symbolic/SymbolicToPureTypes.ml`, `src/extract/ExtractTypes.ml` and
  Lean support: map that explicit node to `{x : I32 // x.val ≠ 0}` using the
  checked pattern equivalence. Preserve the transparent outer Error/NonZero
  records. Code generation must not silently manufacture validity proofs.
- `src/interp/InterpExpressions.ml`, `src/interp/InterpStatements.ml` and
  associated value/type invariant checks: review/support only the consumed
  operations above. Borrow-free disposal must retain the existing Bottom and
  dummy-binding semantics; unsupported operations remain hard errors.
- Add job-owned extractor regression cases and the secure-factory extraction
  driver/source map. Candidate files listed above are a concrete design
  boundary, not an assertion that this unimplemented patch compiles without
  changes to generated visitors or downstream exhaustive matches.

Pins: Charon cb50ff16b9f1066b8a97dc06da704de2da2fa41c (0.1.223), Aeneas
b59d5188c082f704a418c7cb4e52ad69328002d1 plus the already selected
lean432-extended-static binary and its existing extension set; exact current
binary SHA/size and source excerpts are in source-inspection.json. Keep
nightly-2026-06-01 rustc14210df0e27ccd7d9e6a05b8085cbd438e4bbc65,
getrandom0.3.4, zeroize1.8.1 and Lean4.32.0. The generic Rust1.94.1 version
in old receipts is the host default, not the Charon compiler; do not substitute
it for the pinned nightly. New candidate source/patch/binary/dependency pins
and build receipts are mandatory. This proposal does not authorize adoption.

Required semantics and validation:

1. Define a relation from *valid LLBC pattern values*, including the two outer
   records, to the Lean subtype by equality of scalar value. Prove totality,
   uniqueness and both round trips; the new theorem supplies only the range
   simplification, not LLBC/native soundness or record transport.
2. Prove wrap/From, Result branch/tag transport, move, any actually emitted
   Copy, and selected disposal simulate the source operations. Include source
   and destination initialization state, Bottom, no live loans, no user Drop,
   and preservation of all other locals. Inspect the *actual* emitted
   StateOnlyAttemptEntropyError disposal, not merely the prototype closure.
3. Extract actual prover::prove_masked_retrying and its anonymous factory,
   StateOnlyAttemptSecrets::generate, From, and the selected map_err closure.
   This actual factory calls generate() with a fresh **96-byte** buffer; it
   must not be replaced by the 64-byte preselected-public-nonce prototype.
   A later generate_for_mask_nonce caller requires a separate 64-byte binding.
4. At the existing OS primitive boundary retain each fill's input zero buffer,
   returned partial/full buffer, advanced provider state and ordered event,
   with separate source Ok/Err and extraction failure/divergence. On fill
   error, preserve that reply before wrap/map_err discards only the error
   interior. Earlier zero-block replies remain in sequence. No reset, event
   omission, freshness, independence or retry uniformity premise is allowed.
5. Test MIN,-1,1,MAX and reject0; wrap both entropy variants; positive/custom
   and negative OS errors; Ok; partial-write Err on first and later fill;
   repeated zero, late nonzero and cap paths; provider state changes on error;
   StorageDead after move; invalid/uninitialized values; unsupported patterns,
   and an ADT with a real Drop/borrow must fail closed. Use small checked
   simulation cases first, optimized Rust extraction/arithmetic gates, then
   actual dependent bridge and one full axioms/interface audit. Resource
   failures must change the candidate, never its cap.

Trust impact: this is an operational extractor extension inside the existing
source-to-Lean trust boundary, not inherently new cryptographic trust. Its
validity and simulation correctness must nevertheless be established before
calling it accepted. If instead native correspondence is postulated as a
primitive contract, that is a new unproved trust item requiring explicit lead
approval. Neither route is adopted here; no new axiom or premise is inserted.

Invalidation: a candidate binary invalidates extraction/generated-Lean and
all dependent proof/source-binding evidence in its affected closure, including
secure factory transport and downstream native identity claims. Retain prior
receipts as historical evidence; rebuild the changed extraction, smallest
lemma, affected bridge and audit. Final coherent manifest needs lead approval.
Unchanged unrelated artifacts can be reused only after dependency assessment.
A backend-only candidate does not change shipped ELF/performance by itself;
this packet establishes no new identity, reproducibility or timing result.
If escalation chooses a crates/ or programs/ normalization change instead,
all three ELF rebuilds and dependent proof/runtime/event/performance gates
become necessary, including current default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548;
H5 interleaved slowdown≤10% and quiet-host<15s remain later gates. Such source
changes are outside this job's authorization.

## Validation, retained failures and handoff

New focused host Lean launches:11551 Validity, exit0/wall1.13s/
peak2,633,220KiB/swap0;11552 Audit, exit0/wall1.05s/
peak2,622,568KiB/swap0. Both used MemoryHigh5G/MemoryMax7G,
MemorySwapMax0/TasksMax64, populated24+7=31GiB, outside the parallel window
under the launcher's shared global lock. Exact commands, revision76e1dd3340
plus immutable audit WIP snapshot, source/dependency hashes and all four
full standard-axiom reports are retained in rng-transport/. No bridge launch
was spent on the unsupported native type; that dependency is the blocker.
No full manifest, Rust/extraction, runtime, timing or ELF job was launched.

The read-only inventory initially encountered a null LLBC declaration slot;
it was corrected to skip null slots, without dropping any actual declaration.
The receipt collector initially referenced a tool-side assessment as an
evidence-side file; the erroneous reference was removed, with the original
assessment still in tools/rng-caller. These are collection-script errors,
not Lean or extraction attempts. Original niche failure, opaque-type holes
and prior failed proof ledgers remain intact; none was rerun or relabelled.

New allocation use2/9, cumulative213/220,7remaining. Kani44/60,16remaining.
Prior ledgers are preserved and hash-linked. The original material handoff's
stale Work-in-progress sentence is corrected; its conditional scope is intact.

Established: exact candidate validity equivalence and reversible value map.
Retained: native representation association, selected-operation simulation,
actual secure factory binding, partial-write/provider/event transport,
41LocalLeaves/16TypeLeaves and layout/sampling component cuts. No native
assumption discharged, new trust inserted or source premise weakened.
Next deliverable: lead-reviewed, separately authorized extractor candidate
with the validations above, then actual secure callback extraction/bridge.
Do not commission further native success-body wrappers across this gap.
E1 remains literal ProverCommitPublicNonce40.E1. General cap8 draw inventory,
successful bytes/context→Raw, full event/status/body closure, physical cleanup,
filesystem implementation and L1/L2 remain open. Both deployed targets not
yet established. No keys were altered; no merge or push.
