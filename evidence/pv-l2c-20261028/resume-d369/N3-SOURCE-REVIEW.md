# Final diagnostic disposition

Probe5 passed; see D370-FINDING.md. The proposed private-module recording
backend could not compile and was removed. Row 444 is inactive, not active;
its raw value nevertheless survives native masking. The historical plan below
is retained to explain the failed probes, not as an executed instrumentation
claim.

---

# N3 source review, pending native reachability diagnostic

At 9062bd72f5 the 437-file private view equals the tracked worktree source.
No frozen Rust source is edited. guard-probe-body-check.json compares both
copied diagnostic bodies modulo whitespace with the frozen native functions.
These copies provide diagnostics only, not a universal structural native link.

The actual compiler wrapper is pair_forest_trace.rs:
compile_pool_v1_pair_forest_private_transfer_merged_c1_v1. It validates public,
input lane and common input, snapshot pool/domain, and output-value conservation.
compile_forest_from_copies checks computed recipient/change commitments against
public, and checks super-root sibling canonicality. It does not reject a raw
noncanonical recipient.owner_key. The earlier compiler-only probe records that
M31(P) survives at c1[0][444]. This is stronger than the earlier abstract
CanonicalityBoundary alias diagnostic, but guard reachability is still pending.

The semantic path build_with_material clones 16 semantic columns plus ten mask
columns; build_with_helper_mode calls check_semantic_columns before c1.
check_base_columns starts at lane zero and check_base_column walks rows from
zero, rejecting raw limbs >=P. This precedes helper construction and challenges,
so the existing poleBad event cannot account for this branch.

The changed finite probe checks native mask creation and application, row 444
active/unmasked, exact raw-cell preservation, both inactive balances, and the
actual native semantic entry with a recording first-commitment backend. The
backend deliberately stops after the guard; it is not claimed as a complete
prover/reference law. The bad case also invokes the actual fixture entry,
whose common prove_masked_with_attempt kernel is shared with the secure API.
Fixed successful entropy values test a concrete random tape, not a sampler law.
Both the original public and complete returned public transition must agree.

No checked reached-guard counterexample is credited until this probe passes.
