# Native destructor and loan continuation (unadopted)

Parent 80a4a0718149f7e63b1e04d3476c3c142bd31afd. D187/D191 permit isolated
host tool candidates only. No installed tools or shipped crates/programs change.
The native-entropy design/report and every old failure remain authoritative at
their recorded scope. This document is committed before any backend build.

## Exact pinned input and proposed execution

In retained V5 LLBC, real_drop's Precise Drop targets regular function2 with
two region arguments. Function2 is actual generated Guard::drop_glue, taking
&mut Guard and returning unit; it reborrows self and calls actual function3
Drop::drop. No Guard-name match or bespoke counter evaluator is justified.
The interpreter's existing Drop ignores fn_ptr, moves the original value into
a dummy binding and writes Bottom. Its symbolic ordinary call path already
instantiates signatures, checks typed inputs, creates region abstractions and
synthesizes a real function call. Concrete mode executes the actual body.

The smallest candidate will lower an eligible Precise/regular Drop into fresh
mutable-reference and unit temporaries: borrow original place; move reference
into actual fn_ptr call; end temporary lifetimes; then dispose original place
using existing drop_value. The call must precede disposal. The original Drop
cannot remain as an effectful call a second time. The disposal operation must
preserve dummy bindings/loans and Bottom. Ordinary noDrop calls are unchanged.
This is a candidate source transformation requiring validation, not an accepted
source-to-output relation. It cannot bypass check_ty_is_supported.

## Initialization, loans, field order, failure

Charon precise drops belong on initialized control-flow branches. Do not infer
initialization from type or erase a symbolic/partially moved value. Borrowing
an invalid place must fail through normal interpreter checks. Shared/mutable
loan ownership remains in the context; ending the call abstraction must write
back the updated original before final disposal. Loans inside Guard add a
second level: the ABI must transport both updated Guard and the backward
function returning nested referents. Existing pair-valued take/swap library
signatures conflict with emitted triples. No output rewriting or new premise
is allowed to repair this. An ABI source repair needs a complete typed relation
for forward outputs, backward outputs and nested loans, not an extra tuple slot.

Actual compiler glue determines recursive field and enum order. Conditional
and recursive drops must pass through the same lowering, preserving their
branches and call sequence. BuiltinOrAuto UntrackedDestruct and generic capture
glue are not regular structured bodies and remain rejected. Unknown/opaque
glue and escaping outputs remain rejected. No cleanup-equivalence axiom enters.
Unwind is an additional boundary: the interpreter explicitly rejects
UnwindResume and ignores Call's on_unwind. Thus a successful normal execution
probe alone never establishes postfailure cleanup. Unless actual unwind and
loan transport are supported, this candidate cannot support whole native owners.
Retain on_unwind in lowered Call and preserve raw failure; do not claim unwind
support from syntactic retention. No filtering Bottom/dummy variables.

## Validation and stopping criteria

Build only a private copy with native release OCaml compilation, exact source
and binary manifests, full-hierarchy pre/in-scope admission and Docker barrier.
Use existing 6G/8G/noSwap/Tasks64. Count build failures. First probe unchanged
ordinary noDrop, then full minimal Guard translation and full Lean dependency
closure. Native counter0->1 evidence is reused only for its pinned source.
Unsupported escaped/capture and selected64 must reject without an accepted
artifact. Recursive/order and failure/writeback tests are required for any
claimed supported scope. No Zeroizing/provider work before the complete Guard
regression is green. A failed typed nested-loan route is an actual blocker,
not permission to substitute an owned success-only wrapper. No full manifest.

Before/after statements: all existing mathematical and native-refinement
statements remain identical; no premise is removed or added. The compliance
change removes only Types' generated source limits, with fresh receipts11563/4.
Current budgets: backend7/12, extraction24/36, Lean225/260, Kani44/60.

## Prebuild source inspection correction

The inherited filter_marker_traits also deletes Destruct's associated actual
regular drop_glue body. Calling its id alone would leave a missing dependency.
Candidate008 therefore retains directly Drop-referenced regular glue as a
standalone item before marker filtering, preserving its id/body/signature and
generic parameters. This metadata change is additional compiler work, distinct
from refined-error behavior. The disposal uses normal StorageDead only for a
local place; projections, implicit/generic glue and opaque bodies reject.
Lowering occurs after ordinary storage filtering so synthetic lifetimes survive.
This does not solve borrowed take/swap ABI or unwind; these remain acceptance
blockers. Exact patch is retained as an unaccepted experiment.
