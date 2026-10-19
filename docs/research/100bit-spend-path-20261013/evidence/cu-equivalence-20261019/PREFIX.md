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

Remaining source composition: establish the bound from actual View.query
execution and consume the range theorem through the four-dot array/slice
accesses and decoder sequence. The full View carrier/query/folds/widths have
an exact new source kit, with no invented reduced carrier or parser premise.
Charon succeeds; the pinned Aeneas interpreter currently fails while merging
branches containing nested shared references (cu-query-aeneas-a,
InterpMatchCtxs.ml:230). An isolated no-branch-join experiment selects the
existing path-duplication continuation rather than merging those states; all
borrow and translation checks remain enabled. No successful consuming theorem
is claimed from an extraction failure. Other candidate source bridges and the
full soundness/privacy composition remain open.
