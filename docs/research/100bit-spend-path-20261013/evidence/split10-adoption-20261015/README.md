# Split10 adoption

The lead reviewed and adopted exactly the two program files and gate driver
measured in the [frozen split10 bundle](../split10-v152-20261015/README.md).
The gate now selects `[3, 10]`; the program continues to accept `[3, 11]`.
All 22 queries are checked: the checkpoint records the next query, and
settlement resumes there and requires the final count to equal 22.
No parser, field, challenge, query-count, account-provenance or settlement
condition changed. The exact source pins and review scope are in
[adoption.json](adoption.json).

The five retained full-mask cases and split11 compatibility passed. The worst
measured transaction is 1,368,461 CU, with 31,539 CU headroom; this is fixture
evidence, not a universal maximum. See [the cost reconciliation](../../SPLIT10-COSTS-20261015.md).

The frozen experiment README predates adoption and intentionally remains
unchanged. No live program was deployed. Task keys remain on the NUC.
