# Finish transport: checked local bridge; accepted-pair row still open

Branch `codex/cx-finish-transport-20261025`. Base
`4dfb9dccec5ce1289c8cabe88b125e6378fd5aea`. No push or merge.

## Exact checked result and before/after

`AspisR1.FinT_Model.finish_value`, lean/FinT_Model.lean, closes the retained
RowFinish_Model candidate's canonical-comparison transport and full local
source/frozen2 acceptance-value equation. The source parent is the pinned
`Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops)`;
its round uses current wrapping indices. `FinT_Returned.returned_state`
derives completeState from the SAME supplied saved-ten/twelve accumulator.
No separately chosen complete accumulator replaces that state.

Before, `RowFinish_Control.parent_value` concluded the exact conditional
source result in terms of raw comparisons. `Port4D_ReturnedFinish.accepted_twelve`
concluded the frozen2 equality only with a successful whole finish premise.
After, with the complete explicitly quantified statement printed in
FinT_018/stdout.log, FinT_Model.finish_value concludes:

```
decide (source_finish ops v p a none = ok (.Ok ())) =
  OraclePortFrozen2.finish parsed q tr i (CheckpointBytes5Output.accumulator a)
∧ decide (Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) =
  D0TypedChecks.verify (typedRows parsed q tr) i
```

Here `source_finish` is only explanatory notation for the exact parent above.
`OraclePortFrozen2.finish_value` supplies the frozen2 reduction at the derived
completeState. This checks the whole Boolean verdict, including failed source
comparisons, under the named total primitive evaluations. It is NOT a complete
Result/error/effect transport. The carrier, query indices and frozen model are
unchanged. No desired comparison, finish equality or model acceptance is assumed.

Retained: S2, alpha indices, exact round primitive/array/pair/dot returns,
PairingLaws, matches_S4_S7, semantic_S3_S9, dot_S5, canonical roundtrips for
all eight comparison operands, matching read, decoded query and frozen input/
query bindings, and the same saved-ten/twelve equations. Relative to the earlier
accepted-only theorem, totality/canonicality are additional implementation
premises; this is not a premise-weakening claim. None of session A's arithmetic
laws is discharged, modified or promoted to cryptographic trust.

The transport replacement keeps the field abstract in FinT_Pairing and
FinT_Algebra. This avoids reducing large concrete field-operation instances
while comparing canonical meanings. FinT_Comparisons supplies source operand
reflection. No release dictionary is unfolded by these new proofs and no
heartbeat/depth option is raised.

## Why this does not close the requested accepted_pair_claims row

The actual accepted_pair_claims installation uses `AspisR1CurrentCaller.Ops`;
its op19 accepts queries/start/end and returns QueryGeometry. The finish/op19
proved here belongs to the DIFFERENT `VTop_Stages.Ops`, taking view/prepared/
accumulator/observer. FinT_018 checks both exact types.

More fundamentally, ClaimsUnrolledSdk.sdkOps preserves adapterOps.op11, the
entire TX2 child. RowShape_Tx2Boundary already proves this and projects its
success on the same D189 cut. D188 AeneasExtraction.stage2 identifies the
outer native wrapper with stage2_owned under that still-arbitrary adapter
operation dictionary; it has no field equating op11 to VTop TX2 or binding
VTop's interior finish operation. Its complete statement is printed in018.

VTop_Entry.install supplies a separate extracted two-entry installation, but
using it here would additionally replace adapterOps.op11 (and its TX1 op10),
not merely fix the requested finish slot while preserving the accepted-pair
installation. That change was NOT made or hidden as another hypothesis.
The clarification request asks the lead to identify an existing same-pair
TX2/VTop binding. No such binding was found in the assigned handoffs/modules.

Thus the source finish/frozen2 local equality is checked, but the SAME accepted
native execution connection remains unproved. This is not a checked source
counterexample. No shipped-source disagreement was found. Next deliverable:
identify or establish the concrete TX2 child installation on the D189 second
cut, then use its actual resume/query/flush return to instantiate this theorem.
The original requested row, S2 and the 100-bit release target remain OPEN.

## Validation, pins and resource receipts

18/60 Lean attempts (no dependency builds), 0/20 Kani. Accepted proof targets:
001 Comparisons,002 Returned,010 Algebra,012 Pairing,016 Model;018 is the
successful combined statement/axiom audit.008 is diagnostic only, with True
conclusion; no closure credit.017's audit had one wrong qualified type name;
018 corrects it. All errors and failed sources are retained, including the
heartbeat failures, and are excluded from proof credit. No unchanged
source+dependencies was rerun, no cap increased, no memory kill or wall timeout.

016: exit0,2.739863502967637s,4,359,396KiB RSS,swap0, source revision
8f5e73ebe1fac47bdeb997dd5c09a0fb1e24e877 (exact source hash in receipt; working source dirty).
018: exit0,2.040112347982358s,5,142,572KiB RSS,swap0, source revision
8a7a2dcdd4 (full exact revision/hash in receipt; working source dirty).
Every new top theorem's successful audit lists only propext,Classical.choice,
Quot.sound. Failed-module sorryAx output is excluded.

Every attempt reused the pinned SInt2 workspace and ran lake env lean -j1
-M7000 -DElab.async=false inside its own systemd scope with MemoryHigh=6G,
MemoryMax=8G,MemorySwapMax=0,TasksMax=64. Reservation inspections found no
other populated build scopes; only one job from this task ran at a time.
All launched jobs are terminal. No build/launcher/monitoring infrastructure
changed. No package or frozen-manifest replay ran.

Each FinT_NNN/receipt.json records exact command/target, revision/dirty state,
source SHA256, direct dependency object/sidecar fingerprints, exit,wall,RSS,
swap,cgroup limits and full printed axiom lines. validation-summary.json
verifies every receipt source, all caps, no duplicate source+dependency retry,
and final source/accepted-receipt identity. source-boundaries.json pins reused
source/extraction evidence and inherited coherent-closure manifest. Extraction
was reused, not rerun; release/source/artifact association is not newly proved.

No shipped or cfg(kani) file changed; no three-ELF rebuild trigger fired.
Inherited pins, NOT freshly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Only new FinT_ modules and this evidence directory changed. No session A live
worktree/candidate, other worker slot, key, protocol parameter, failure event,
wire format, feature or security metric changed. No objects/binaries committed.
