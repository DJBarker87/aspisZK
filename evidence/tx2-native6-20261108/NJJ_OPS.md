# Ops and residue classification under (au)

TX2:065 OPEN; target not yet established. Baseline NIU ledger13: 432 CLOSED / 167 OPEN / 599. A standard operation is part of its enclosing native cut, not a new child row. A library-model proof is not a native caller certificate. No trust row is added. The typed root must not take an arbitrary dictionary, including one hidden in another record.

## Every field of VTop_Stages.Ops

The authoritative declaration has 25 fields: op0–op23 and unwrap32. The direct TX2 common body reads only op0,2,5,6,9,10,11,13–19,20–23. The unused fields are irrelevant to this root, not missing child certificates.

| Field | Frozen meaning | Class and disposition |
|---|---|---|
| op0 | Option::ok_or | Aeneas std model (au)(1), NHT_Constants.core.option.Option.ok_or; complete Some/None Result |
| op1 | WideExact::ZERO | Unreached by TX2 common; literal constructor, no root obligation |
| op2 | WideExact::from_le_bytes | CLOSED child TX2:031; NJC_ClosedCalls.inactive_clause / NET_WideModel; SAME proof[7495..7527] |
| op3 | parse_shape | Unreached inside common; authenticated caller owns its invocation |
| op4 | canonical_scan | Unreached inside common; TX1:084 history obligation retained separately, not silently CLOSED |
| op5 | batch_merkle | Genuine OPEN child TX2:053; NJE_ owns Merkle5 / verify_in_place; no assumed result |
| op6 | query_loop | CLOSED child TX2:058; NFS_QueryLoopRoot.tx2 and NFW_QueryResume.tx2; caller must derive SAME input domain; no selected-address-to-payload inference |
| op7 | Prepared::new | Unreached inside common; no replacement by a successful fixture |
| op8 | checkpoint | Unreached inside common; no writer child at this site |
| op9 | BatchedWeights::finish | Genuine OPEN child TX2:099; Port3_FlushInstall.flush is a model law, not a native CLOSED status. iter_mut/writeback itself is (au)(1)/(2) |
| op10 | BatchedWeights::new | Genuine OPEN child TX2:100; NHV_PendingPacket.source proves complete emitted/model width64 Result; reserve/resize/index/push itself is (au)(1)/(2), not an additional child |
| op11 | QueryGeometry::for_range | CLOSED TX2:104; NFN_NFB_GeometryComposed.result_state_effects / NJC_ClosedCalls.geometry_clause |
| op12 | Accumulator::new | Unreached inside common; resume supplies the accumulator |
| op13 | mark | CLOSED TX2:118 on deployed literal None; NJC_OrderedCalls.mark; no Option<fn> native credit |
| op14 | OFF_ROUND1 | Emitted literal/constant model NHT_Constants, not a child |
| op15 | OFF_FOLDED_ROOT | Same; 7751 |
| op16 | SPLIT | Same; 10 |
| op17 | powers29 | CLOSED TX2:138; NFW_PowersCohort.source / NJC_OrderedCalls.powers; canonical SAME resumed gamma is an internal domain |
| op18 | resume | Genuine OPEN TX2:124; NJC_RawCalls.source / NIY_ResumePort.source are full model transports, not native root closure |
| op19 | finish_relation | Genuine OPEN TX2:115; sibling NJF_; retain only SAME-call NIG_FinishInput.Domain, never independent child-output equations |
| op20 | OFF_OPENINGS | Emitted constant; 10055 |
| op21 | OFF_FINAL | Emitted constant; 8007 |
| op22 | OFF_ROUND0 | Emitted constant; 7527 |
| op23 | OFF_INACTIVE | Emitted constant; 7495 |
| unwrap32 | Result::unwrap on array conversion | Pinned Aeneas std model (au)(1); success returns the exact array; failed conversion abort has no suffix. NJC_ConcreteUnwrap proves the raw-reader instance. No Formatter axiom is admitted |

## M01–M13

| Member | Correct classification | Remaining compositional work |
|---|---|---|
| M01 resume | Genuine OPEN TX2:124 enclosing safe std operations | Install concrete library models and child Results into all staged native cuts, with full Result and abort prefixes. The safe std calls do not create producer child rows |
| M02 Merkle | Genuine OPEN TX2:053 | NJE_ dependency, complete Result/effects/frame and caller domain; no work in sibling tree |
| M03 pending | Genuine OPEN TX2:100 | One native initialization iteration with arbitrary pre-state plus Lean induction; existing filled child TX2:045 CLOSED; safe reserve/resize/copies are inside this cut |
| M04 query | CLOSED TX2:058 with caller obligations | Instantiate its full law at the SAME native cut arguments; reference query dictionary residue must be inspected, never assumed as a root parameter |
| M05 flush | Genuine OPEN TX2:099 (and value TX2:102) | Native one iteration plus CLOSED reducer/value laws and frame induction. Vec deref_mut_back is the Aeneas std model; no additional writeback producer child |
| M06 finish | Genuine OPEN TX2:115 | NJF_ dependency; SAME history-derived finish domain. No arbitrary endpoint/output assumption |
| M07 filled/reserve | CLOSED filled TX2:045 + std (au)(1)/(2) + existing Allocator on returning/abort scope | The actual reserve reply must be the one threaded through this invocation. A fresh Bool or a mere rename to Reservation is insufficient. Box allocator follows (aa); no new success/totality law |
| M08 raw/K/E | Raw TX2:107 and readers TX2:105/106 remain ledger OPEN; scalar/array std calls are (au)(1)/(2) | NJC concrete raw Result and CLOSED field parsers TX2:019/031; nominal parser association must apply those actual complete Results, not invent a native std producer. Native cuts execute try_into/unwrap/from_le_bytes |
| M09 semantic/weights | Genuine OPEN helpers TX2:121/122 + safe iterator std | Native arbitrary loop/body frame followed by existing finite induction; native std iterators are not child rows |
| M10 validator | Genuine ledger OPEN TX2:126; NJC candidate complete law | Reuse NJC_ValidateCalls.source and full arbitrary-array domain; credit awaits gate |
| M11 canonical_scan | Genuine OPEN TX1:084 history function; ChunksExact external rule-3 (au)(3) | Supply complete remaining-byte model once, then parser/outer-loop composition; no chunks producer child. No forbidden whole-buffer rerun |
| M12 header/checksum/public | Iterator::any external rule-3 (au)(3); slice equality/from_le_bytes standard (au)(1); digest op43 approved RuntimeSyscall value scope | Exact ordered byte slices and unchanged reply per native cuts; no digest value model or independent oracle seed. No assumption of header success |
| M13 Prepared/Accumulator | Safe Box/Vec std (au)(1)/(2), Box returning/abort scope existing Allocator (aa) | Parent cut must assert full moved values and SAME allocation; not separate producer children. Any unsafe construction encountered requires P6 (au)(4), never covered by this classification |

No unsafe MaybeUninit/raw-write construction is present in the frozen direct resume/common snippets above. This is not a claim that unrelated child implementations contain no unsafe code. Their own bridges retain P6 obligations.
