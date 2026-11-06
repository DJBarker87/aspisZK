# QueryScan retained findings

Target not yet established.

QF1: NJO_LEDGER's conservative TX1:069->TX1:202 edge resolves `QueryScan::default` to `IncrementalMerkleTreeV1::default` in crates/aspis-statement/src/pool_v1/incremental_merkle.rs. This is not a real frozen call dependency: queries_from_pairs constructs the private r0_transcript::QueryScan. The user explicitly requires202 retained if OPEN; it is retained, no pruning or outside-slice work is attempted, and069 remains OPEN. Exact required child is that conservative TX1:202 row (itself depending on203), pending lead resolution or closure.

NJT_QK001 did not verify: compiler could not resolve crate::KMX_stubs. The owned scratch setup exposed the prescribed unchanged KMX module under cfg(kani), with cfg allocator_api, in NJT_QL008. NJT_QK003 then passed and NJT_QK002 failed its intended inverted value assertion. No timed-out or memory-killed job was retried; no harness/function renaming changed a verdict.

NJT_QL002's import inspection failed on missing NJE_COMBINED_IMPORT: own input LEAN_PATH omitted NJO_PATHS. The list was appended/deduplicated after NJM consumer paths; QL003 passed. QL005's finish proof needed explicit irreducible constants; QL007 had redundant solved-goal tactics; QL010 needed local reply unfolding; QL014 used Lean's reserved prefix token as a variable; QL013/015 had own alias/transparency elaboration errors. Failed drafts and sorryAx prints are excluded. Successor receipts identify accepted sources; no failure earns credit.

Additional non-credit draft diagnostics: QL020 required reducing the let-pair before splitting the fixed source walk (QL021 passes). QL026 needed multiplication commutativity in the chunk membership bound (QL027 passes). QL028 needed explicit Usize5 numeral normalization in frame.drop (QL029 passes). Each failed source snapshot and any sorryAx lines remain excluded; no failed draft is imported into the final object export.
