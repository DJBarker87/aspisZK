# Own runner changes

Only own NIL client/validator/queue scripts were changed. Shared reservation, launcher, shim and coherent workspace were never edited. All existing checks remain, with additive source/hash/feature/budget/control gates.

Initial parser repairs accept semantic assert_eq failures reported at core::panicking::assert_failed_inner while requiring FAILED, nonzero exit and no unwind assertion. Existing receipts were classified read-only. Source identity erasure was strengthened to require the entire frozen prefix byte-identical, followed only by enumerated cfg(kani) modules; spacing between adjacent appended modules does not affect the frozen prefix.

Final client adds projection and retention Python-only scoped targets, preserving admission, caps, timeout, selected-object pinning and immutable receipts. It does not alter Kani flags or source assertions. Queue pauses affect only the local scheduler between native submissions; in-flight native jobs complete unchanged. Every resumed completed target is read from its receipt rather than resubmitted.
