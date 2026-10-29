# D487 skeleton integrity audit

Base 7d8769c123; branch codex/pv-skw-20261029; exact sparse worktree pv-skw.
Skeletons and links remain read-only. No crates/programs changes. IDs 68700–68799,
reserved audit IDs 68797–68799; 100 Lean / 10 native scopes / zero Kani maximum.

Read pv-common.txt including (u), (v), AGENTS.md security/proof discipline,
r1p-common.txt and local-lean.txt. Existing records inspected: PV_2TNV_CanonicalWitness,
PV_2TNV_TransferCore and transfer-13 input/comparison record paths. These witness the
spend relation, not an observer-emission or allocator-world trace. Explicit model
instances are therefore used, without claiming native producer association.

DIAG has FOUR explicit link hypotheses per theorem (twelve applications total),
not fifteen distinct DIAG links. Also check the three projection-step laws used
internally, making fifteen conditions. L1 audit covers BOTH CountSkeleton and
OriginalCountSkeleton, since the latter is the reported D466 skeleton.

Proof order: independent nonempty DIAG models; L1 actual recursive owner model;
OWNM model retaining concrete_source_dense; statement audit, axioms audit, one
combined final manifest. Reuse verified cohorts, separately where incompatible.
