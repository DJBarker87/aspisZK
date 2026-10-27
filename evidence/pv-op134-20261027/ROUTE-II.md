# V230 / op134 route (ii) addendum

Base: 8483406290, codex/pv-op134-20261027. Target not yet established.
No shipped source is changed by this addendum.

## Direct extraction receipt

op134 was absent from the 15-op historical refusal table on
codex/pv-extract-20261027. This job tested it directly, with the existing
cbmid extraction context (the unchanged shipped hiding function body plus
previously recorded harness-only cfg additions), the unchanged pinned Charon
and Aeneas tools, built MIR, release profile, strict joins, abort-on-error.
See charon-op134-001/receipt.json and aeneas-op134-001/receipt.json for commands,
input snapshots, source revision, wall time, RSS and swaps. Charon exits 0;
Aeneas exits 2 with exactly:

> ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation; structured Drop requires destructor semantics

No extraction equation is claimed. The guard scans the included closure:
op134 calls active_rows, which calls schedule; schedule uses mutable iterator
reference outputs and endpoint_counts borrows slices. active_rows also uses
flat_map, collect, Vec deref_mut, sort_unstable and dedup. The root returns
an owned array, which does not evade this whole-closure guard. No Kani retry.

## Proposed owner-approved prover rewrite (not implemented here)

Introduce a prover-local owned index-loop helper returning the SAME complete
Result<[u16;64], PoolV1PairHidingLayoutErrorV1>. Build an owned schedule using
index loops and value reads, preserving all shape/endpoint-capacity errors,
relocation and link order. Walk owned links by index; read producer and
consumer values into locals; validate row < 1024 before indexing; OR the bit
into masks[row >> 4] using row & 15. Duplicate endpoints and their order do
not affect OR; prove that algebraic fact in Lean. To supply op133 too, scan
rows 0..1024 in increasing order and push exactly the set bits. This gives
ascending order and dedup by construction. No reference-returning iterator,
slice helper or sort/dedup should enter the extraction closure. Do not replace
complete Result equality with success-only or array-only equality.

The row's immediate host caller is
crates/aspis-r1-cost-probe/src/host_semantic.rs::no_pole (line 368), mapping
layout errors to Error::Public; redirect only that prover caller after the
rewrite and complete Lean equality gate. Also inventory the same prover
callback in crates/aspis-r1-cost-probe/src/prover.rs::prove_masked_with_attempt
(the call at line 196; preserve Error::Semantic) and prover-side users in
aspis-prover/src/state_only_entropy.rs and v6_onefold_prover.rs before adoption.

Keep crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs and its public
re-export in pool_v1/mod.rs unchanged for the verifier/shared-statement path.
Its inactive-mask helper continues to call the original active-mask function.
The selected SBF verifier already uses the distinct static helper
`pair_forest_copy_terminal.rs::pool_v1_pair_forest_copy_active_row_masks_compiled_v1`
(line 42), which returns `constants::ACTIVE_ROW_MASKS`; v7_verifier.rs imports
it at line 48. Preserve that compiled verifier path and its static schedule
as well. Do not redirect it to the proposed host index-loop helper.
No global alias, cfg substitution in the statement crate, or verifier redirect.

## Remaining proof gate

Published PV_CBM_CallbackBundle.op134_reference stays unchanged. It equates
the selected callback to PV_CBM_ReferenceRaw.reference.masks, not to shipped
code. Reference inventory uniqueness/completeness and row ordering/dedup are
separate obligations. Even after those are proved, the complete Result
shipped = extracted candidate-copy equation and its release adoption remain
P obligations, never added to the capped three-field trust list T.
