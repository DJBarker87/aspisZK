# Layout obligation

The source page branches assign cursor 4 (Genesis/SamePage) or 5 (Rollover).
Under deployed r1-split-checkpoint, expected account count is cursor+8 for
transfer and cursor+13 for withdrawal. Marker/payer/system/registry/verifier/
proof/token indices are cursor+[0,1,2,3,5,6,7]; checkpoint is expected-1.
The two registry elements and optional five token accounts must be in bounds
on the SAME accounts slice after require_exact_account_count succeeds.

The layout-tail model has an arbitrary full uniqueness Result, including
all errors. Native branch/domain evidence for zero-page, current-page header,
PDA, full/rollover and uniqueness remains required. It cannot be inferred from
these offsets. Account count K010/K011's <=3 fixture does not cover production;
layout-tail evidence must use the actual 12/13/17/18 account counts.
