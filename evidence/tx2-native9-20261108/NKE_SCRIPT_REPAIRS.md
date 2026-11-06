# Own runner repairs

NKE_K001 stopped before submission: the adapted serial client did not retrieve the source-pin manifest produced by NKE_L008. Retrieved it read-only and added it to stage artifact retrieval. The frozen-source validation is unchanged. No Kani process started; K001 is reserved as setup failure and never credited.

NKE_K002: pre-proof cargo failure because the frozen crate includes tools/r1-builder-reference/tree.rs outside the stage copier roots. Added the exact retained NJU tool inputs (unchanged frozen source) to the transport; no theorem/verdict and no credit.

NKE_K003: pre-proof unresolved KMX imports. Matched the predecessor include of the exact KMX_stubs.rs inside the harness module and added its cfg(kani) allocator_api attribute. Gate strips only that exact attribute when comparing to frozen lib.rs. No production body change or credit.
