The exact fixed-prefix statement in fast_dots.rs at producing revision
39c2971dd is extracted by extract-cu-prefix.py. Its free-function boundary
returns the same reference. The production statement is unchanged; generated
Types/Funs are promoted byte-for-byte and checked by audit-components.py.

CuSavingsPrefix.source_success executes all three emitted operations:
subslice, checked shared-slice-to-array conversion, and unwrap. Given length
at least 608, it returns exactly the first 608 bytes. source_short identifies
the actual panic result below that bound. read_eq and range_eq prove every
bounded read/range sees the original bytes. base_range, middle_range and
tail_range bound the three exact decoder offset families used by four_dots,
including the final range ending at byte 608. These are symbolic index proofs,
not enumerations of concrete fixture bytes.

Successful receipts: cu-prefix-types-a, cu-prefix-funs-b, cu-prefix-proof-c.
All exit zero with no process/cgroup swap, below 2.6 GiB peak RSS and below
2.3 seconds. The first emitted wrapper was named prefix, a reserved Lean
keyword; its failed Funs compile and original input are retained at
cu-prefix-funs-a. Renaming only that test wrapper to fixed_prefix resolves the
emission naming problem. Failed proof drafts are retained separately.

Axioms boundary: read/range/bound theorems use only standard Lean axioms.
The emitted function and its success/failure theorems also refer to
Aeneas.Std.core.fmt.Formatter through unwrap's Debug dictionary. The pinned
backend declares this as an opaque TYPE, not a proposition asserting any
optimization or equivalence. unwrap ignores its Debug argument and returns
the Ok value or panic on Err. The exact extra axiom is recorded per target in
COMPONENT-AUDIT; it is not reported as standard-axioms-only. Backend file:
aspis-r1-j17-port-20261015/backend/Aeneas/Std/Core/Fmt.lean, SHA-256
26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce.

The actual complete View.query accessor, folds method and salted width
constants now have an exact source kit. No reduced View carrier or parser
premise is used. CuSavingsQueryAccess.query_length proves every successful
query has exactly the selected width (3360 for S1, 4864 otherwise), by inverting
the actual checked index arithmetic and source subslice. query_prefix_bound
therefore discharges the 608-byte bound from source execution.
CuSavingsQueryPrefix consumes this result: for arbitrary View/index inputs,
the original and fixed-prefix decoder reads agree for all three production
range families, preserving query failure/divergence. The decoder is arbitrary;
this is not a proof limited to valid fixture values.

New successful receipts: cu-query-types-a, cu-query-funs-a,
cu-query-constants-d, cu-query-access-b, cu-query-prefix-a. All exit zero,
use zero process/cgroup swap, peak below 2.6 GiB and finish below 2.1 seconds.
The query/prefix composition inherits the same Formatter TYPE boundary;
query accessor/constants proofs use only standard Lean axioms.

Frontend boundary: the pinned Aeneas interpreter fails while merging query
branches containing nested shared references (cu-query-aeneas-a,
InterpMatchCtxs.ml:230). The isolated optional no-branch-join frontend selects
the existing unmerged-context/duplicated-continuation path. It does not disable
borrow, type, arithmetic or translation checks. The same unchanged LLBC emits
successfully (cu-query-aeneas-b); the generated Types/Funs are promoted
byte-for-byte and checked by audit-components.py. The original frontend and
production Rust are untouched. AENEAS-NO-BRANCH-JOIN.md records the exact
patch, build and paired regression boundary. This remains trusted frontend
translation, not a theorem proving Aeneas itself correct.

The complete emitted slot/base/batch/tail comparisons now check under
universal shared arithmetic and a concrete state-threading array builder.
The complete old/new kernel comparison also checks for arbitrary same-608-byte
inputs. See DOTS-SOURCE.md for those source-linked results and axioms.

The four-slot counter/capture invariants and complete full-width kernel
comparison now also check. CuSavingsDotsPrefixKernel.source_eq compares the
actual emitted old/new complete functions for every slice of length at least
608. query_composition derives that bound from actual View.query execution,
including failed/divergent queries. See DOTS-SOURCE.md for the exact scope.

Remaining for candidate 10: Rust-library admission of the concrete array
builder, concrete shared-helper interpretation, and source binding of the
entire enclosing verifier caller. The library frontier is recorded in
ARRAY-LIBRARY-SOURCE.md. Final soundness/privacy composition is unfinished;
no source-admission claim is inferred from a failed frontend run.
