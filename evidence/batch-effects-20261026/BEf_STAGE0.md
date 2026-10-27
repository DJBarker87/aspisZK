# BEf stage 0: source/effect audit

Target not yet established. L166 remains open. Work is confined to BEf_ modules
and this receipt directory; no shipped source or other worker candidate changes.

Read Security and proof discipline, r1p-common/local-lean, S2 ownership/plan/
diagnosis/interface, C3-BIN route B, owner-approved frozen3/runtime amendment,
P6C handoff, Op5T two-slot source installation, SdkC/SdkD batch syntax and CPhy.
The requested Op5T receipt directory resolves to op5-tx2-20261025.

Current checked-in top is Rc4_Top.deployed (imports Rc3_Top and Rc2_Top).
No top statement is changed in this audit. L166 is a deployment-audit row,
not a literal top binder; removing a binder is not sufficient to discharge it.

Actual candidate.rs:153-206 batch_merkle/body/tree carry local idx/val arrays;
there is no pending-weight, allocator or account-heap argument. The proof slice
is shared. Local scratch changes and hash effects occur before Merkle/Parse
rejection. SdkC_Source.run retains attempted partial syscalls on failure;
CheckpointBytes5Effect.run (StateT Result) discards its failure carrier.

D188 S2W_DigestExtraction.AeneasExtraction has stage1,stage2,digestSource value
equalities. It has no explicit mutable carrier, allocator event, borrow guard
or rejected-prefix effect field. A stateful lift must not silently promote
those equalities into native effect correspondence. The existing countermodel
in P6C concerns arbitrary child ports; it is not a shipped vulnerability.

Next: check a prefix-preserving carrier interpreter, source-batch Result
projection, and carrier non-identifiability independently. These are local
model facts until native effect association is proved. No row removed yet.

Budget used: 0/100 Lean; 0/30 Kani. No release/build claim. Frozen ELF pins are
inherited, not reproduced; no shipped/cfg(kani) edit triggers an ELF rebuild.
