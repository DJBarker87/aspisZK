# S10 pass 5

## Stage 1: complete indirect dispatch accounting

All thirteen remaining owned Pool callback instructions now have corroborated
compiler target-flow evidence for `processor::solana_sha256`. The new narrow
aggregate rule follows offset 288 of the noalias/readonly `context` formal of
`apply_prepared_settlement_plan_v1`. Its sole final caller stores the constant
callback into a private alloca immediately before the call, in the same block;
the target aggregate is not passed as any other call argument. All final
caller multisets and function-address escape checks remain mandatory. Multiple
LLVM calls in a function are never paired to ELF instructions by textual order:
every candidate must resolve to the same target set.

The result is 21 compiler-resolved sites (15 SHA callbacks and six null observer
operands), including pass 4's eight. This is compiler calling-convention/SSA
provenance under the frozen compiler boundary, not a Lean source refinement.
The separate independent replay checks every classification and rejects lost
callers, escaping addresses, unknown operands, and changed field offsets,
constants, store chronology, readonly/noalias attributes and alloca provenance.

The other 131 sites have individual instruction-address/register/caller entries
in `indirect-boundaries.json`: 130 formatting/vtable calls and one boxed
bincode-error drop. Two explicit operational specifications cover exact ABI,
live receiver/vtable provenance, mutable state, callback/write order, ordinary
errors, panic/abort, allocator behavior and confinement from spend-oracle/account
state. These are proposed trusted library boundaries, not proved target sets,
owner adoption or new Lean axioms. The boundary does not cover owned callbacks.

Host receipts record 6G/8G/zero-swap/64-task scopes and current reservations.
Final extraction: exit 0, 4.927 s, peak 671708 KiB, zero swaps. Final resolution:
exit 0, 0.050 s, peak 22220 KiB, zero swaps. Exact command/revision/script and
input SHA pins accompany each receipt. The v2 extraction adds the declaration
signature to the witness for independent attribute checking; v1 is retained.
`#print axioms`: N/A, compiler evidence only. No shipped source/ELF changed.

Source/model identities, full source Calls tree/carriers, final instance/inline
correspondence and the final source-coverage instance are still open. The
current model target is `OraclePortFrozen2.dV_frozen2`; the authoritative headline
is `OraclePortHeadlineFrozen2PerAttempt.final_soundness` (design addendum 13:05).
