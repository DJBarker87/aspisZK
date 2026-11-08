# Session17 local model/binding corrections


## SPEC-C13 — original native stack coordinates (session17)

Checked `PV_LIB_SPEC_OriginalStackGap17.original_pair_impossible` (55575),
then `NativeObligations17.no_original_stack` (55584). Adopted ELF SHA256
fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558:
f8eef LEA callerRsp+0x70 -> RSI; f8ef4 CALL fac90 pushes8 bytes. The scope
and spawn prologues retained in BinaryStack16 require a nonwrapping360-byte
stack below scope entry. Thus runPointer=scopeEntryRsp+0x78 and360<=entryRsp.
The retained ORIGINAL Entry14 capture has runHeader.pointer=112. No Nat
entryRsp satisfies that conjunction. SESSION17_NATIVE_CALLER.txt retains the
binary evidence. This refutes the SAME-fixture nonwrapping stack target only;
it is NOT a negation of the existential Cut92Composition.Witness, and no
formal binary execution or OS grant has been proved. Modular wrapping is NOT
silently identified with a valid granted stack.

Coordinate repair: OriginalStackGap17.pairedFrame derives runPointer from
entryRsp+0x78, rather than accepting it independently. repaired_pair and
repaired_excludes_original check both implications. Relocating the original
physical captures and granting their real stack is STILL OPEN: doing so changes
Entry14's physical world and cannot be silently substituted into thread-29's
same-input joins. The exact OriginalStack target and its checked negation are
in NativeObligations17. No original85 frame is claimed adequate.

## SPEC-C14 — trigger replies are not fixed-runtime native semantics (session17)

Checked `FixedNativeGap17.fixed_answer/bound_answer/no_reply_identity` (55579)
at the ACTUAL original84 poll, not a fresh fixture. Frozen runtime forwards
FnOnce to18 and its current environment returns Ok(null). The operational
context-bound adapter computes Ok(false) from source0/local20 and physical65520.
The complete replies disagree on the same Entry14 world. Therefore the
candidate reply-identity transport for these parameters is false. The eighteen
frozen statements were NOT rebound or weakened. The operational adapter is
the retained local semantic repair; it has not been made an inhabitant of the
fixed Runtime's universal contracts. A corrected environment binding plus
reached full-state transport remains required. This is NOT a joint contradiction.

## SPEC-C15 — ZERO_CAP is not the effective capacity of a Unit Vec (session17)

Checked `UnitReserve17.old_rejects_unit` (55581). Values14.reserve rejects an
initialized empty RawVec header on len0/extra1, even for Unit append10. Pinned
Rust1.94.1 raw_vec/mod.rs (SHA256
0c6b3d1bedcc8c1aa6d8f37ad5553e1b14c452c732745612cf23c4663c090965)
lines43..47 and601..603 retain stored ZERO_CAP but return effective usize::MAX
for element size0. SESSION17_RAWVEC_SOURCE.txt retains the exact source excerpts.

Repair `UnitReserve17.reserve/values` implements that distinction ONLY for
this retained F=Task=Unit append10 specialization, still checking the actual
source RawVec header and rejecting capacity overflow. unit_no_growth proves
its exact graph; other_functions retains all other Values14 meanings.
Non-ZST growth remains explicitly partial. This new value instance is NOT
silently substituted into ReachedNative14; original-history transport and
all actual layout/provenance bindings remain required. No row or frozen
contract changed, and this local header example is not original reachability.

These correct local candidate bindings, not the frozen eighteen statements.
No shared SPEC_CORRECTIONS.md, provider, ledger, endpoint or T field was edited.
