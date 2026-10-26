# S6 accepted execution and allocator step — 26 October 2026

Whole S1/S2/S6 and the100-bit per-attempt target remain OPEN. This packet
changes no frozen production source and removes zero concrete enclosing
source/trust premises. It establishes a weaker sufficient enclosing source
interface, an actual SDK allocation step certificate, and arithmetic induction.

## Enclosing theorem: native total allocation is not required

`S6SdkAcceptedExtractionV1.original_sdk_reached_first_accepted_extraction`
has EXACTLY the conclusions of
`S6SdkFirstOnlyV1.original_sdk_reached_first`. Complete Entry/account/library
carriers, actual original SDK wrapper acceptance, checkpoint write and public
account frame, decoded statement, original native decoder, byte roundtrip,
same first_decoded call, proof slice, observer selection and firstCurrent
conclusions are unchanged. Other premises are unchanged.

Before, the source-refinement premise required, for every program/accounts/data:

    native1 program accounts data = stage1_owned installedOps program accounts data

After, it requires only, for every program/accounts/data/saved:

    native1 program accounts data = ok (Ok saved) ->
    stage1_owned installedOps program accounts data = ok (Ok saved)

`of_full` derives this directional law from the old equality. The new proof
uses the SAME native accepted call obtained from original SDK acceptance,
then preserves the entire previous proof. `check.py` compares the complete
theorem text against the old theorem after exactly the name, premise type,
and its single use are replaced. No hidden carrier/quantifier/conclusion
change, SourceCuts hypothesis or second-stage success is added.

This is ACCEPTED-ONLY refinement. It does not promise equal rejection,
abort, divergence, oracle history, probability law or native resource state
for every input. It does not replace actual account/SDK execution with an
opaque carrier. It leaves the exact same SDK wrapper body and every state
conclusion intact, while allowing a native allocation abort where the
allocation-erased source interpretation returns normally.

The concrete accepted stage1 source instance remains OWED to the S2 owner;
the theorem does not manufacture it. Therefore this is a genuine weakening
of an enclosing requirement, not discharge of actual source correspondence.
It also does not establish adaptive-experiment transport or final soundness.
Accepted SDK execution supplies a reachable native acceptance, so the proof
does not rely on vacuous absence of accepted runs.

**Correction to the previous next-step priority:** a proof that EVERY native
decoder allocation succeeds is NOT a prerequisite for this accepted S6 reuse
theorem. Total heap headroom remains a separate totality obligation. The
S2 owner may supply this narrower directional instance rather than complete
native/source result equality. There is no approval or source decision
needed for the mathematical weakening; adoption still requires the concrete
instance and coherent release pins. Do not duplicate the lead's S2/SDK work.

## Actual SDK allocation step

`tools/s6-bump-step-20261026` copies the COMPLETE BumpAllocator struct,
constructor and GlobalAlloc implementation from the release-pinned
solana-program-entrypoint2.3.0 package. The package archive checksum is
`32ce041b1a0ed275290a5008ee1a4a6c48f5054c8a3d78d313c08958a06aedbd`, checked
against Cargo.lock at frozen revision
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. The only surrounding change is
imports. Source bytes and copied declarations are checked; no body edits.

The native harness calls that exact alloc and dealloc implementation on a
valid262144-byte arena. Initial cursor is arbitrary0 or8..262144, requested
size arbitrary1..262144, alignment arbitrary1/2/4/8. Zero cursor exercises
initialization. The independent owned reference uses checked subtraction
and floor division, rather than the SDK's saturation and bitmask.

The final native certificate checks exact returned pointer/header, unchanged
header on allocation rejection, aligned success, lower header bound8,
monotone cursor, requested-byte coverage, at most7 bytes rounding loss and
actual no-op deallocation. All116 assertions and4 covers pass, including
both fresh and existing cursor success and allocation rejection. The negative
control changes only expected successful pointer by8 and fails exactly that
assertion. This directly invokes the allocator method; it does not rely on
Kani dispatching a custom global allocator for Box, which earlier NP6 controls
showed was unsupported.

The arena provider uses Kani's ordinary successful malloc model. This is a
one-step certificate on a valid arena, not actual entrypoint admission,
global allocator selection, Box initialization/cleanup, source-to-Lean
extraction, SBF layout or whole native caller correspondence. Target is
aarch64/darwin, not a fresh Linux or SBF certificate. Exact tool/std pins are
in the receipts. No cross-target promotion is made.

## Arithmetic induction

`S6AlignedAllocationRangeV1.step_fits` proves one offset-reference step
reserves the8-byte cursor header and loses at most7 bytes to rounding.
`reserve_fits` composes arbitrary finite request lists by induction, preserving
all intermediate bounds. Required input is8 plus the sum of(bytes+7), with
each alignment positive and at most8. It uses cumulative requested bytes;
no deallocation refund is assumed. `snapshot_charge` consumes the existing
complete Entry/admittedSizes interface and proves its conservative aligned
charge is at most61964, including every rejected width/alias configuration.

These are TOTAL mathematical/reference range results for requests satisfying
their displayed capacity conditions. The Rust word/reference and Lean Nat
definitions have NOT yet been joined by extraction. The Kani certificate
independently verifies the matching one-step inequalities on native words.
Neither result silently instantiates a native runtime heap in the enclosing
SDK theorem or eliminates the concrete stage1 source association premise.

## Source allocation inventory

`tools/s6-allocation-backbone-20261026/inspect.py` reads the existing pinned
Charon LLBC, SHA256
`8220a6aa2e782c21c365e0a905d61e5427df6729c44c240c99d40d24f6c03856`.
The LLBC is NOT exported. The source-only report includes226 functions,
including an over-approximation of concrete trait implementation methods,
unwind callees, all opaque operations, both trait dispatch sites and missing
method slots. Every unfamiliar statement/control form fails inspection.

The structural bound is CONDITIONAL on listed opaque/builtin/trait/drop
operations allocating0 and faithful extraction. Under those conditions,
the raw decoder has at most5 Box requests. Both statement constructors are
retained as alternative branches; all7 reachable loop bodies have charge0.
The adapter wrapper adds one Box, already separately checked in the earlier
native wrapper packet. This is SOURCE INSPECTION, not a formal native bound.

165 complete Rust function source texts match the current frozen sources
exactly. Three macro-generated field functions have no source_text in this
IR; they are explicitly unresolved in this inventory. Current full source
files are retained for review, and old whole-file differences are not hidden.
The extraction records x86_64 layouts: snapshot752, afterstate680, late1432,
common1576, statement1792 bytes, each align8. These historical extraction
layouts do NOT establish current SBF or aarch64 layouts/footprint. No
allocation-free Std certificate or source-layout re-pin is inferred.

## Validation and failed predecessors

| Focused target | Exit | Wall seconds | Peak RSS bytes | Swap |
|---|---:|---:|---:|---:|
| S6AlignedAllocationRangeV1 |0|45.531719500|2166456320|0|
| S6SdkAcceptedExtractionV1 |0|53.261916791|2149744640|0|
| Native allocator step, final positive |0|16.466918708|1249001472|0|
| Native shifted-pointer negative, expected failure |1|8.084526166|935624704|0|

Both first changed-file Lean checks passed, using the atomic local lock,
-j1 -M4400, pinned warm imports. Five #print axioms results contain only
propext/Classical.choice/Quot.sound. No full unchanged replay was run.
Native final positive/negative receipts are referenced by
`s6-bump-step-terminal-v1/manifest.json`; they record exact status, timing,
RSS, zero swap, source/tool/std pins and4GiB aggregate watchdog. Native
#print axioms is N/A. The native scopes are sequential with local Lean.

An initial NUC tiny compile failed because the copied declaration needed a
Layout import; the handmade lock also acquired Cargo's standard header.
Both are retained/excluded. The corrected fresh NUC admission was denied
because other live capped reservations occupied its safe budget; no new
compiler was launched and no other session's cap was changed. These tiny
focused jobs then ran locally under the4GiB aggregate watchdog.

The8192-byte predecessor passed in4.365492s/183058432 bytes. Expanding a
MaybeUninit stack array to256KiB timed out at121.548057s/694484992 bytes;
no larger cap or unchanged rerun was used. Replacing only the harness arena
provider with a valid uninitialized malloc arena made the same256KiB step
check pass in8.659734s/1296924672 bytes. The final source adds the explicit
rounding-loss assertion and fresh/existing cursor covers. All predecessors,
including the intended negative controls, remain correctly classified.

Next source/caller deliverable: consume the S2 owner's concrete accepted
stage1 binding in the unchanged S6 SDK/account reuse conclusion. For separate
TOTAL heap work, extract the owned Rust reference, prove allocation-free
leaf/drop closure and current-target layouts, and account for actual entry
prefix/metadata and later calls before claiming a native capacity bound.
S1 still needs its retained arithmetic/dot/scan contracts joined at the same
actual preparation caller; the lead owns SAP canonicality/data binding.
No production, protocol, security-contract or source-adoption decision is
made by this packet.
