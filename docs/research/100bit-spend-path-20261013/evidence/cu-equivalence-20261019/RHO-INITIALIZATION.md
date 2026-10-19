The full unchanged BatchedWeights::new method was selected as a new extraction
root. Charon succeeded (rho-charon-init-a). Aeneas then failed while ending
borrows in that method, at InterpBorrowsCore.ml:1498 (rho-aeneas-init-a).
It did not emit a checked initialization theorem. No larger memory cap,
production Rust edit, or replacement heap behavior was used.

The assignment RHS is now separately extracted by extract-rho-init-row.py.
The expression is byte-identical to the production source at 39c2971dd; the
free-function boundary is explicit. The reused field carriers are checked
against the existing exact production cuts. Charon/Aeneas receipts are
rho-init-row-charon-a and rho-init-row-aeneas-a. Generated Types/Funs are
promoted bytes-unchanged; audit-components checks that correspondence.

CuSavingsRhoInitRow.row_success checks the entire emitted assignment method,
and word_initial_val proves every u32-to-u64 cast preserves its value, without
requiring canonical input. For canonical inputs, initial_bound establishes
the exact RhoBound at counter zero and canonical_initial proves that reduction
returns the original field carrier. initial_finish consumes the checked
source finish method to prove a canonical slice round-trip from the list
initialization model. That list model is NOT an emitted new/zip loop, and the
theorem does not establish that the original Rust new method allocates or
initializes that model. These remain separate source obligations.

Focused successes: rho-init-row-types-a, rho-init-row-funs-a,
rho-init-row-proof-c. They print only standard Lean axioms (Types uses none),
exit zero, use zero process/cgroup swap, take less than two seconds and peak
below 2.6 GiB RSS. The two earlier local proof drafts failed to parse a nested
record layout; their failed receipts are retained and not counted as success.

Still required: full mutable zip/initialization execution, fallible allocation
admission, the outer row/query loops and counter, canonical reference field
update and checkpoint/serialization composition, then the complete soundness
and privacy transfers. No whole-verifier equivalence follows from this file.
