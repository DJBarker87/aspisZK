# Own runner repairs

NKE_K001 stopped before submission: the adapted serial client did not retrieve the source-pin manifest produced by NKE_L008. Retrieved it read-only and added it to stage artifact retrieval. The frozen-source validation is unchanged. No Kani process started; K001 is reserved as setup failure and never credited.

NKE_K002: pre-proof cargo failure because the frozen crate includes tools/r1-builder-reference/tree.rs outside the stage copier roots. Added the exact retained NJU tool inputs (unchanged frozen source) to the transport; no theorem/verdict and no credit.

NKE_K003: pre-proof unresolved KMX imports. Matched the predecessor include of the exact KMX_stubs.rs inside the harness module and added its cfg(kani) allocator_api attribute. Gate strips only that exact attribute when comparing to frozen lib.rs. No production body change or credit.

NKE batch runner prints only one-line summaries, retaining complete raw receipts. NKE prepare_audit selects only current source hashes with focused exit0 receipts, merges NKC+NJU expected-import inventories (0 conflicts), and rejects stale/mutated focused sources. NKE final-check source validation strips ONLY the exact two cfg(kani) additions before frozen hashes, identical to the strict per-Kani gate.

Budget guard correction: K001 (missing local pins) and K018 (admission missing JSON) never launched.38 native receipts throughK040 are recorded; K041/K042 are the final2 of40 native scopes, not an allowance increase. Runner caps the ACTUAL native receipt count at40, rejects existing receipt IDs and preserves both no-launch artifacts. Serial local guard prevents concurrent uncounted submission.
