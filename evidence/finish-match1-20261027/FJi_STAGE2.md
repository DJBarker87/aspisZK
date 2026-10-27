# Coordinate suffix VALUES

All eight separate `FJi_Coordinate0.value` through `FJi_Coordinate7.value`
are checked against the SAME coefficient/scalar/state parameters of
`FJi_Accumulations.accumulate`. Each gives old coordinate + coefficient * scalar
as a Nat equality. The lane proof inverts the actual checked multiply/add;
no overflow bound, canonicality requirement, or output-value assumption is added.
`FJi_EightValue.value` combines the eight. `FJi_Inputs` ties the scalar read and
coordinate extraction to the installed input arrays and installed `to_limbs` order.

Successful receipts: FJi_003,005–014; exact metadata and printed standard-axiom
audits are retained per attempt. Failures002 (mul notation mismatch) and004
(substitution removed a local name) were corrected in source. Failed axioms
outputs including sorryAx are rejected, not accepted proof evidence.
This stage is term-suffix correctness, not yet seven-group accumulation or L143.
Before/after deployed statements and ledger remain unchanged: delta0T/0P/0G/0C.
