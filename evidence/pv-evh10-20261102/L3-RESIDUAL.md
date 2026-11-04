# D588 — physical interpretation residual (l3-2)

Named residual: **ActualEntropyEntryPrefix source-to-machine carrier**.
Classification: **V370/L3**. Status: unconstructed and unproved.

This is precisely the paired-history construction in BLOCKER-D587.md:
`actual_correspondence base heap box ops : Correspondence base heap box ops
(ActualEntropyEntryPrefix base heap box ops)`, with its original four binders
and source dictionary `opsNative (rawBase base) heap box ops` unchanged.
The domain must include every reached entropy initializer prefix, retry,
pending/granted/exhausted stack answer, and prefixes followed by failure,
fault or divergence. It cannot require separation or eventual success.

The missing producer must derive source State, mask, retry and limit from the
same reached machine history; establish `state_eq`, `retry_eq`, `limit_eq`
and `mask_backing`; and bind every existing source live slot to its physical
storage and lifetime. In particular, all initialized bytes of all entries in
`state(q).frame.live` must lie outside the new entropy reservation, as stated
in BLOCKER-D587. Finite table geometry alone does not prove that conclusion.
Heap OWNER does not include this stack/PC/lifetime association.

Attached evidence: [l3-residual-D588.json](l3-residual-D588.json) hash-pins the
D581–D587 binary, OS-model, resource and interface records in this worktree.
The adopted binary is da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0.
Evidence remains **binary-structural (adopted binary), plus V370 compiler-cohort**;
D582 uses the named Linux reference OS model. No machine/compiler correctness
proof is claimed. D583/D585 correct D581's arithmetic: entropy sp=c-288,
caller mask=sp+304, caller Result=sp+352. D581's original arithmetic remains
historical evidence, superseded at these offsets.

Under l3-2 this residual belongs to physical secret residence, stack wiping,
and other L3 claims. Every L3 headline relying on that interpretation must
name **ActualEntropyEntryPrefix source-to-machine carrier (V370/L3)** explicitly.
It is NOT a premise of native events, fileTrace, countTrace, timeTrace or
oraclePrefix. No physical-frame construction is pursued in D588. No residual
was discharged, no T field was added, and no physical conclusion is assumed.
