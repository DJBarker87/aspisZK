# P6B stage 1: exact boundary audit

Target not yet established. Starting revision 4c673b6d3856dcf0ea9df07039b73eb030717346.
Only P6B modules and this receipt directory are authorized changes.

The latest counted theorem is AspisR1.Rc3_Top.deployed. L195–L199 and
L166 are deployment-only rows, not explicit binders of that theorem.
Op5T_P6.boundary already derives all four mathematical callback gates for
parent/parent/parent/referenceLeaf, conditional on total digest equality.
It explicitly does not establish arbitrary SDK child/source association.
The requested op5-tx2-20261026 directory is absent; the existing packet is
op5-tx2-20261025 and its final report is used without modifying it.

D188's digestSource plus digest_eq_hashv identifies op43 exactly with hashv,
INCLUDING failure/divergence. RuntimeSyscall is success-only by definition.
S2Z.Oracle.total_of_returning already identifies the separate missing law:
forall parts, exists digest, hashv parts = Result.ok digest.
The source wrapper calls hashv then toBytes; toBytes cannot turn failure or
divergence into success. Thus the extra law concerns runtime return/abort
semantics, not an unproved pure Merkle/compression arithmetic identity.
Next: kernel-check necessity, sufficiency, and a non-vacuous countermodel
before the task's explicit runtime-trust stop condition is applied.

Validation: read-only source inspection and pinned hashes, no Lean/Kani/Rust
execution yet (0/100 Lean; 0/20 Kani). No release result, ELF rebuild, key
change, or other worktree access. Axioms: N/A at this stage. No rows removed.
