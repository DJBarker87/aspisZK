Exact raw checkpoint reads and retained scalar composition

JFq_Raw.source derives a concrete returned array and reader from the bounded
raw source call and a named small-window selection. JFq_Scalar.k/e compose
that exact return with scalar decode. They are generic helpers; no accepted
wrapper or whole checkpoint result is assumed or established.

Accepted final helper receipts: 011 and 012. Standard axioms only.
Rejected 002–006: parser keyword, cursor/platform-size normalization.
Rejected 008: pair-let normalization. Replacement uses explicit uncurry.
The receipt snapshots retain all rejected sources and diagnostics.
No timeout/memory kill; all scopes terminal. No top premise changed.
