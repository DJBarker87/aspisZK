# Worker-owned input and parser repairs

K001 stopped before Kani in cargo metadata because the frozen source archive
omitted c3/build and c3/check path dependencies. Their four unchanged frozen
files were added and pinned in NGU_FROZEN_EXTRA.json; no lock or predicate was
changed. The missing-feature receipt recovery was read-only; no resubmission.
The collector now retains every existing log even for an early preflight failure.

K004 is a completed failing control, not rerun. Kani terse Rust assert_eq emits
a placeholder diagnostic at core::panicking::assert_failed_inner rather than
the original source expression. Inspection finds exactly1 failed check, the
same native source and graph as K003, and only NGU_invert in RUSTFLAGS differs.
That cfg only changes XOR0 to1 in check(actual,expected). No mutable static
or other XOR use exists. The parser accepts this uniquely failed assert_eq
panic with those independent source/config checks; intended assertion semantics
are unchanged. This is source/receipt validation, not a claimed Kani PASS.

The launcher and admission infrastructure are unchanged. The own client now
records source_revision, source_tree_dirty and frozen_revision. Earlier raw
receipts keep their original bytes; NGU_REVISION_ASSOCIATION.json supplies the
stage-boundary revision alongside exact snapshotted dirty-source hashes.
