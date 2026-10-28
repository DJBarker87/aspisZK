# D336 handoff — four selected source/callback packets closed

Exact worktree `/Users/dominic/ZK/.worktrees/pv-l3`, branch
`codex/pv-batch3-20261027`. Entry `678657d1e6334f1a4e4c327382ad4fb516751588`.
No merge or push. Final replay source `b9e465139149eadad7af8d247f94c53d9d104560`;
flat bridge source `151fe2bab1e6211669d8e9dd0e007f657963cf3f`.
Prior handoff is preserved in `RESUME-HANDOFF-before-d336.md`; journal `D336.md`.

## Exact scope and residuals

| Row / op | Before | After on the selected original ProverRwFull instance |
|---|---|---|
| V230 / 134 | P/OPEN, no installed native source law | Complete Result equals `ok (.Ok PV_Op134_Masks.masks)`; successful 64-mask witness; concrete error carrier explicit |
| V239 / 222 | P/OPEN, no installed source law | Arbitrary raw column/point complete Result equals the extracted bounded sparse/fold reference; formal `ok none` witness and separate finite valid-column `Some 7` evidence |
| V217 / 117 | P/OPEN, no installed source law | Arbitrary raw 16/10 coefficients, explicit value and 10-point input obey the exact scatter/prepared-Horner Result reference; formal successful zero witness |
| V220 / 121 | P/OPEN, no installed source law | Arbitrary raw 28 coefficients/challenge obey the exact grouped block Result reference; formal successful zero witness; no naive-Horner replacement |

Closing theorems: `PV_B3_Close134.source`, `PV_B3_Install222.source`,
`PV_B3_Install117.source`, `PV_B3_Install121.source`.
`PV_B3_FlatInstallD336.installed` selects all four on one original carrier;
its four laws and all 258 other callback frames pass. `PV_B3_TypeFrame134`
proves the chosen native error carrier and all 27 other external type frames.
`PV_B3_ClosureD336.closure` prints the complete combined statement.

Each native link is a **script-checked structural source argument under (k)**,
supported by the copy's complete-Result extraction and named Lean control,
representation and helper facts. It is not a universal native machine theorem.
`STRUCTURAL{134,222,117,121}-D336.json` lists pins and deliberate differences.
Same-input native comparisons are **finite validation**, reused after exact
source checks in `d336-native-reuse.json`. For 134, the containing copy file
changed historically; its root, bump helper and whole MASK_LINKS table are
identical to the measured version, and original files are identical. That
whole-file mismatch is recorded, not hidden. Ruling-(n) checks are recorded
per function in `d336-ruling-n.json`; all nine polynomial restorations apply.
No XR module or definition is imported or copied.

Four selected source/callback obligations are discharged; **zero privacy
endpoint premises were removed**. No premise was added or weakened. The
remaining native callbacks, actual native execution/dictionary installation
(V165/V167), D234/V403 and further model interpretation, real RunJoin,
deployment E1/E2, client proof-account route, inversion zero boundary and
L1/L2/L3 remain open. T is exactly entropy_law, entropy_kernel, observation.
**Target not yet established.** `d336-row-status.json` retains exact original
row residuals and separates selected-instance closure from endpoint closure.

## Verification and resources

43/100 charged Lean attempts: 27 accepted, 16 rejected; Kani 0. IDs
40500–40549 and 40597–40599 consumed (53 total). Ten IDs were zero-charge
refusals, including early retry 40501 blocked by the existing cooldown guard.
All later reservation checks respected >=180 s gaps. Do not reuse any consumed
ID. 57 charged attempts remain, but only 40550–40596 are unused within this
allocation; a further allocation is needed beyond them.

| Target / ID | Exit | Wall s | Peak RSS KiB | Swap | Proof revision |
|---|---:|---:|---:|---:|---|
| PV_B3_AuditD336 / 40597 | 0 | 5.284 | 2677532 | 0 | 6f4e2f6cd35ad6c7fdb0a6dba14c47511d7d4595 |
| PV_B3_ClosureD336 nested / 40598 | 124 | 900.270 | 2661324 | 0 | 6f4e2f6cd35ad6c7fdb0a6dba14c47511d7d4595 |
| PV_B3_FlatInstallD336 / 40549 | 0 | 11.994 | 2697544 | 0 | 151fe2bab1e6211669d8e9dd0e007f657963cf3f |
| PV_B3_ClosureD336 flat / 40599 | 0 | 2.623 | 2672304 | 0 | b9e465139149eadad7af8d247f94c53d9d104560 |

One combined audit: 2177 reports. The new flat bridge has its own full axiom
checks; final replay checks 263 reports including its closure and all flat
frames. Every accepted report is a subset of
{propext, Classical.choice, Quot.sound}. Maximum Lean RSS 2697544 KiB;
all swaps zero, caps always 6G/8G/swap0/Tasks64 and Lean -M7000.
The nested record replay timed out and was replaced by the flat installation,
never rerun unchanged or with a larger cap. Both snapshots/receipts remain.
Other failed drafts, including recursion/scalar/simplifier repairs, remain.

`d336-receipt-index.json` includes complete wrapped axiom reports, targets,
exit/wall/RSS/swap/revisions and SHA snapshots for every run.
`d336-accepted-source-bindings.json` binds all 27 accepted sources to exact
committed blobs. `COMMIT-LOG-D336.txt` records the continuation's commits.
Some early read-only transport overlapped a compile's SSH session; scopes
never overlapped. Later transport was serialized. See D336.md for deviations.

All 88 project sources, private objects and transitive dependency fingerprints
match (`d336-cache-verification.json`). No other job's project object was used.
All 5673 external objects and the actual env-J selection match the coherent
h4 manifest before the first compile and before audit. No shared source/object
was written, rebuilt or substituted. No unresolved project module remains.

No crates/ or programs/ source changed: diff against c97270adc2 is empty.
Local and final host checks cover all 523 files. Inherited pins apply:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Inherited worst per-call cost projection +1.906124819123782%, below +2%.
No unchanged ELF, fixture or timing regression was rerun; no new Rust job ran.

No own scope remains. No keys, accounts, balances, nonce ledgers or retained
counterexample binaries were destroyed. The pinned private cache is retained
for pending dependent endpoint/native integration, per resource rule 6/h6;
no local target or binary artifact was created or committed.

Next concrete deliverable: integrate the flat selected dictionary into the
actual native execution/RunJoin carrier and discharge its separate reached
model/canonicality obligations, then connect to the unchanged privacy endpoint
and deployment/client/side-channel conditions. Do not treat the four source
packets or finite native comparisons as deployed privacy closure.
