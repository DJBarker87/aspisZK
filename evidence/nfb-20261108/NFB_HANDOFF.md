# NFB host delivery

Branch codex/cx-nfb-host-20261107; base 953e3af13bb. This job closes no
ledger row. The exact AspisR1.NFB_NMFBHost.Remaining and the final
NNC_NMFPrimeB term are OPEN. No adopted top, RSL, NNH, shipped source,
release artifact or trust declaration was edited.

## Stage 1

NFB_NMFB and NFB_NMFBHost compiled UNCHANGED against the real pinned run-5
objects: NNR_L001 (exit 0, 0.320125 s, 498428 KiB), NNR_L002 (exit 0,
12.945446 s, 6554056 KiB). Swap 0, standard axioms only. No stand-in statement
divergence was found. Sources and complete receipts are in
../nfb-host-20261108/NNR_L001 and NNR_L002.

## Obligation inventory

All names below are under AspisR1 unless explicitly qualified. CLOSED means
the indicated local statement has a compiled term, not that TOP:NMF_B closes.

| Item | Status | Lean term and receipt |
|---|---|---|
| M1a slot roundtrip | CLOSED | NNR_Clock.M1a, exact NFB_NMFBHost.M1a; L003 |
| M1b clock-free missing literal | CLOSED | NNR_ClockFree.M1b, exact NFB_NMFBHost.M1b; L004; SHA/PDA leaf factorization, not whole-dictionary reduction |
| M1c slot-bound EnvRep | CLOSED | NNR_Clock.M1c, NFB_NMFBHost.M1c c (env2 c); L003 |
| M1d local S5 rebuild | OPEN (partial local rebuild) | NNR_Producers.produce, accepted, game, origin (L007); NNR_Retime.env/missing/sdk_same/first/second (L005); NNR_RecorderClockFree.event (L026). Full literal-host signature/Exec/a0 install at corrected env2 and final Remaining are not delivered. |
| M2a same-occurrence C04 domain | CLOSED | NNR_C04Domain.at_record (L008), NNR_RecordTransport.window (L016), NNR_OuterInvert.accepted (L021); no Root0 input |
| M2b aborting windows relevant to target | CLOSED for exact returning target | NNR_CommonReturned.safe (L012), NNR_NoAbort.child/returned (L013): an outer-failing detail cannot occur in a returned common run. General abort-prefix transport remains the reused NNH_NativeOracleBatch.aborting, not a new arbitrary-abort window equality. |
| M2c occurrence list | CLOSED | NNR_InvocationTransport.forward (L018), NNR_CommonTransport.accepted (L019), preserving actual-event list |
| M2d outer native outcome | CLOSED | NNR_Lift.M2 (L025), EXACT NFB_NMFBHost.M2 |
| M2e digest oracle | CLOSED | NNR_Oracle.M2e (L006), EXACT NFB_NMFBHost.M2e |
| M3 Root0 image | CLOSED | NNR_RootImage.M3 (L009), EXACT NFB_NMFBHost.M3; uses SAME source-cut getters/range and canonical V0 Root0 |
| Delivered/Missing/Associated and final NNC_NMFPrimeB | OPEN | Exact NFB_NMFBHost.Remaining still refers to old S.env2 = envOf c. Corrected producer's ref is at env2 c. No equality or final term claimed. |

## Owner-visible slot statement

The proved corrected-environment facts say that the slot c.j.slot output by the
attacker is fed to the model as the runtime clock reply,
NND_Carrier.reply NND_Carrier.slot c.j.slot, and decoding that reply yields
exactly c.j.slot; the reindexed producer consumes its weak entry Ref at that
environment. Thus a top using this representation counts a run with the runtime
clock equal to the selected attacker-output slot. Under the existing
RuntimeClockSlotBinding reading, that output records the reply bound to the
bank slot, so this representation must exclude no deployed run; it must not
become an independently assumed equality or a filter on Realizes. This job
proves the roundtrip, EnvRep, model/recorder clock-independence and local producer
restatement, but does NOT prove or install the complete lossless final-top
representation. The old host permits a different clock reply (M1_refuted), so
that final signature/composition obligation remains explicit for the owner.

## Binder grouping

NFB_BinderGroup compiles unchanged at L027. NNR_BinderHost (L029) proves
host_shape at the actual NNH_LiteralHost.S_host, with before :=
NNH_RecordSig.physical (envSig L0 copy) (data L0 copy std) (record L0 copy)
and Ret := NNH_LiteralHost.retained L0. The following are CLOSED specialized
terms, all under AspisR1.NNR_BinderHost, standard-only: exec_same,
top_splitB_grouped, deployed_charge_grouped, failG_eq,
indicator_eq_of_fixed, indicator_eq_of_trust. These retain their original
interface arguments; no missing top interface has been discharged by an alias.
Their receipt is ../nfb-host-20261108/NNR_L029/receipt.json.

No trust row is added, removed or reclassified by grouping. The averaged event
gains exactly Ret(ctx H). It equals the old event under the old cross-world
premise and under the trust reading Runs -> Ret, at the same oracle/world.
first/second/QueriesF/ERec/ctx, bound T, r, m, each and budget are unchanged.
The first host specialization attempt L028 failed only on uninstantiated Tx
in the host_shape header; L029 explicitly pins Tx. No statement changed.

## Final validation and run-6 overlay

NNR_COMBINED_IMPORT passed L030: exit 0, 4.240144 s, peak RSS 6662972 KiB,
swap 0, all 15 printed delivery roots standard-only. It imports the run-5
NNH_ContinuationCombined and last focused S5 combination NNH_S5FocusedHost,
the unchanged NFB modules and every delivered NNR module. This is a focused
coherent import, not a final G0, raw audit or frozen-release manifest replay.

Used the entire 30-scope allowance: 23 exit 0, seven retained elaboration/
heartbeat failures; 0 Kani, 0 extraction. Every scope had exit-0/allowed-true
admission, a fresh >=40 GB disk preflight, one scope at a time, 6G/8G/swap0/
tasks64, -j1 -M7000 -DElab.async=false and unchanged 180 s process timeout.
Every passing root has standard axioms only. Failures are NOT closure evidence;
failed logs may contain Lean's error-recovery sorryAx, never a passing delivery.

For NNH run 6, prepend:
/home/dombarker/project-offloads/codex-cx-nfb-host-20261108/NNR_objects
before the READ-ONLY run-5 path:
NNH_R4_objects:NNH_objects:NNH_seed:NNH_library_seed
under /home/dombarker/project-offloads/codex-cx-integrate-20261111.
Toolchain: leanprover/lean4:v4.32.0. Do not treat this overlay as a final top.

Hashes/receipts: ../nfb-host-20261108/NNR_SOURCE_PINS.json (new sources),
NNR_HOST_DELIVERY.json (all overlay object/sidecar and tool hashes),
NNR_IMPORTED_PINS.json (resolved inherited/direct objects, including Aeneas),
NNR_COMPILE.tsv and NNR_L*/receipt.json (exact command, source revision/hash,
dependencies, exit, time, RSS, swap and full printed axioms). Inherited objects
were resolved read-only in place; no bulk cache copy or unchanged rebuild was
needed. The pinned NNH cache-import manifest is recorded in each receipt.
Host generated source/attempt-source/tmp scratch copies were removed after
receipts were retained locally. Delivery objects are retained for run 6.
No key, wallet, sibling worktree, cache, shared launcher or reservation script
was modified or deleted. No pushed commits or shipped-file changes.

target not yet established
