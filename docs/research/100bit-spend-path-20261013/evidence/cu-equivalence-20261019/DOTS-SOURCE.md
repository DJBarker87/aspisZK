The complete old/new four_dots functions now have an exact paired source kit.
extract-cu-dots.py --check asserts the sole candidate-10 delta is the original
three-line fixed-prefix addition. Both entire functions and the unchanged
field.rs, field/wide_exact.rs and fast_pairing.rs are copied verbatim. These
files are unchanged from candidate 10 through production revision 39c2971dd.
Only a small crate/module boundary is added; no Rust function body is edited.

cu-dots-charon-a successfully extracts both complete functions and all closure
loops, with identical arithmetic callees deliberately opaque for a parametric
comparison. Exit 0, wall 1.604 s, peak RSS 228836 KiB, zero process/cgroup swap.
cu-dots-aeneas-a successfully emits both complete function/loop declarations
using the isolated tested no-branch-join frontend. Exit 0, wall 2.205 s,
peak RSS 135696 KiB, zero process/cgroup swap. Both actual scopes are capped
at memory high/max 6/8 GiB and swap max 0; commands, revision, features, pins
and host observations are in the respective receipts. These are frontend
runs: #print axioms is inapplicable, and no new Lean success is inferred.

The generated FunsExternal_Template.lean is DIAGNOSTIC ONLY. Its axiom
placeholders are not imported or admitted. Shared arithmetic leaves need
explicit universal parameters or already checked concrete definitions, and
core.array.from_fn needs a concrete state-threading interpretation plus its
standard-library source boundary. Treating an arbitrary polymorphic array
constructor as extensional would be unjustified. The emitted old/new closure
carriers also differ (Slice versus Array 608); their source-loop relation must
consume the checked range identities and actual loop bounds.

The exact emitted declarations now typecheck under an explicit universal
Arithmetic class and a concrete ordered state-threading array builder. No
property or success of any arithmetic operation is assumed. emit-cu-dots.py
--check pins the raw frontend emission and verifies all declaration bodies
remain byte-identical: only one namespace-level [Arithmetic] variable is
inserted. Generated Types are promoted unchanged. The axiom template remains
diagnostic only and is not imported.

CuSavingsArrayBuilder checks mutable-state naturality for arbitrary callbacks,
including failed/divergent executions. CuSavingsDotsSlot checks both complete
emitted callbacks equal one common continuation computation, then proves its
continuation transport through the actual 18 binds. CuSavingsDotsSameBytes
consumes that theorem and the array builder to compare the complete old/new
four_dots functions on arbitrary 608-byte input arrays and arbitrary gamma
arrays under any shared arithmetic instance. This is source-linked execution,
not a new handwritten arithmetic model assumed equal to the source.

For full-width input slices, CuSavingsDotsReads checks the actual offset
arithmetic sequences and all three decoder continuations. CuSavingsDotsBase
compares the complete actual base loop, discharging term bounds from iterator
execution. CuSavingsDotsBatches binds its end bound to the actual scalar min
result and compares the whole batch loop without a success/termination
premise. CuSavingsDotsTail compares the complete two-term loop, including
mutable accumulator handback. All preserve failures/divergence under arbitrary
shared arithmetic. CuSavingsDotsSlotPrefix consumes them: each actual slot
with index below four observes only the first 608 bytes of any longer query.
No valid-fixture or successful-decoder premise is used.

Successful receipts: cu-dots-types-a, cu-array-builder-d, cu-dots-externals-a,
cu-dots-funs-a, cu-loop-relation-a, cu-dots-reads-c, cu-dots-slot-f,
cu-dots-same-bytes-m, cu-dots-base-step-c, cu-dots-base-progress-b,
cu-dots-base-b, cu-dots-tail-b, cu-dots-batches-c, cu-dots-slot-prefix-a.
All exit zero with zero process/cgroup swap. Peak RSS is below 2.6 GiB and
Lean wall time is 1.6-2.9 seconds per successful target. The concrete array
builder, generic loop relation, reads and arithmetic-parameter declarations
use standard Lean axioms only. Source kernel proofs additionally carry the
already recorded backend Formatter TYPE through Debug/unwrap, never a
proposition asserting any optimization or verifier equivalence. Exact axiom
sets and source/receipt hashes are checked by COMPONENT-AUDIT.json.

Two expanding proof-search attempts were stopped and replaced, without cap
increases or unchanged reruns. See PROOF-SEARCH-REVIEW.md. Refused launches
remain explicitly classified as not launched, not failed theorem results.

The constructor/capture obligation is now checked. CuSavingsArrayBuilderBounded
proves its literal counter calls the callback only below the declared length,
while preserving a supplied state invariant through actual successful handback.
CuSavingsDotsSlotPost proves the actual emitted slot callback preserves its
capture whenever it succeeds; it never assumes success. These discharge the
bounded constructor premises from the source callback rather than postulating
them.

CuSavingsDotsPrefixKernel.source_eq now compares the COMPLETE emitted old/new
four_dots functions on every arbitrary slice of length at least 608, arbitrary
gamma arrays, and every shared Arithmetic instance. Its query_composition
consumes the actual emitted View.query success bound, preserving failed or
divergent query executions. This expression composes the two actual emitted
operations; it is not yet an extraction of their entire enclosing verifier
caller. Receipts: cu-array-builder-bounded-a, cu-dots-slot-post-a,
cu-dots-prefix-kernel-a. All exit zero, wall 1.6-1.9 seconds, peak RSS below
2.6 GiB, process/cgroup swap zero. The bounded builder uses standard axioms;
source slot/kernel contracts additionally carry only the existing Formatter
TYPE through Debug/unwrap. No new equivalence proposition is admitted.

REMAINING: Rust standard-library admission of the concrete array builder,
concrete interpretation of the unchanged shared arithmetic helpers, and
embedding this comparison in the actual enclosing verifier/adapter source
contexts. ARRAY-LIBRARY-SOURCE.md records the exact current frontend failures
and bounded diagnostic evidence. No failed library emission or its partial
axiom template is imported into a checked proof. The final whole-verifier
error/checkpoint/hash/effect composition and soundness/privacy transfers remain
OPEN. Production Rust and the measured sub-1.2M build remain unchanged.
