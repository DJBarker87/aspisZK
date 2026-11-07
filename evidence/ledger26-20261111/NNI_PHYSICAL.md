# NNI physical association report

Target not yet established. Nineteenth all-slices composition gate PASS:583 CLOSED /0 QUALIFIED /16 OPEN of599. Only TX1:136 is promoted. TX2:217 remains OPEN under ruling(t). No Pool row promotion. Counts are composed association obligations, not security bits or runtime measurements.

| Inventory part | CLOSED | OPEN | Total |
|---|---:|---:|---:|
| (ao)(3)(b) | 40 | 13 | 53 |
| (ao)(3)(c) | 543 | 3 | 546 |

Distances minimise (OPEN members, call edges), including the entry. Canonical inventory edges remain, with spurious-by-name annotations visible; no removed edge or hidden clause. The first two endpoints match ledger25 for comparison.

TX1 to TX1:094: TX1:330 [OPEN] → TX1:333 [OPEN] → TX1:344 [OPEN] → TX1:345 [OPEN] → TX1:328 [OPEN] → TX1:094 [OPEN]. 6 OPEN, 5 edges.

TX2 to TX2:115: TX2:213 [OPEN] → TX2:221 [OPEN] → TX2:240 [OPEN] → TX2:241 [OPEN] → TX2:064 [CLOSED] → TX2:065 [CLOSED] → TX2:115 [CLOSED]. 4 OPEN, 6 edges.

TX1 to TX1:136: TX1:330 [OPEN] → TX1:333 [OPEN] → TX1:344 [OPEN] → TX1:345 [OPEN] → TX1:328 [OPEN] → TX1:094 [OPEN] → TX1:087 [OPEN] → TX1:137 [OPEN] → TX1:136 [CLOSED]. 8 OPEN, 8 edges.

TX2 to TX2:217: TX2:213 [OPEN] → TX2:221 [OPEN] → TX2:240 [OPEN] → TX2:241 [OPEN] → TX2:242 [OPEN] → TX2:233 [OPEN] → TX2:217 [OPEN]. 7 OPEN, 6 edges.

## OPEN members by source file

### crates/aspis-r1-cost-probe/src/candidate.rs

| Row | Member | Owner / next deliverable |
|---|---|---|
| TX1:087 | prepare | NNG_: Needs canonical137 child, exact emitted prepare fold/full mutable geometry/Results and SAME successful semantic provenance; original R4 must be caller-proved. No candidate. |
| TX1:094 | tx1 | TX1 principal, child-first: Needs087 then actual canonical_scan R4 discharge and source/effect/domain installation; LIB_VLibR4.discharge is support, not094 root. |

### crates/aspis-r1-cost-probe/src/r1_semantic.rs

| Row | Member | Owner / next deliverable |
|---|---|---|
| TX1:137 | verify_observed | NNG_: NNG_SourcePublic137.source lacks the observation/bind and nested RE.bind continuation equality (L475 excluded). No literal137 RowSpec candidate. Concrete136 caller-domain support alone is not the parent root. |

### programs/r1-cost-probe/src/lib.rs

| Row | Member | Owner / next deliverable |
|---|---|---|
| TX1:328 | first_decoded | TX1 principal, child-first: Needs094 plus complete rev3 Ref fold, clone/abort/error arms and own source/domain transport. No rev3 candidate. |
| TX1:330 | process_r1_cost_probe_instruction | NNF_ fold / shared instantiation: CANDIDATE-FOLD NNF_Folds.entry_tx1; needs completed333/221 and both wrapper packets. |
| TX2:213 | process_r1_cost_probe_instruction | NNF_ fold / shared instantiation: CANDIDATE-FOLD NNF_Folds.entry_tx2; needs both wrappers via333/221; no instantiated entry root. |

### programs/r1-cost-probe/src/r1_pool_adapter.rs

| Row | Member | Owner / next deliverable |
|---|---|---|
| TX1:333 | process | NNF_ fold / shared instantiation: CANDIDATE-FOLD NNF_Folds.process_tx1/NNF_TAS.roots; needs344 and240 wrapper packets at SAME implementation fields; no invented hypotheses. |
| TX2:217 | decode_lane_from_pool_release | NMX_ native fidelity control: NMX_K010/NMX_shape_stub compile failure, not unimplied assertion failure under stub_verified for Result<Box<Lane>,ProgramError>. Ruling(t) per-shape controls incomplete;0 Kani authorized here. Lean reference/all-length/allocation/one-step induction support replays. |
| TX2:221 | process | NNF_ fold / shared instantiation: CANDIDATE-FOLD NNF_Folds.process_tx2/NNF_TAS.roots; needs344 and240 packets, same-function pair333/221 cannot close before wrappers. |

### programs/r1-cost-probe/src/r1_pool_adapter_owned.rs

| Row | Member | Owner / next deliverable |
|---|---|---|
| TX1:344 | stage1 | NMV_ fold / principal instantiation: CANDIDATE-FOLD NMV_CandidateRoots.root344; missing canonical345 root and exact installed library/representation arguments. ReviewedTranscription-TX1:344 retained, unused by CLOSED rows. |
| TX1:345 | stage1_owned | TX1 principal / NMT_ support: Needs328 and actual owned-input/source/event association. No rev3 NMT_345 root. |
| TX2:233 | authenticate_asq8_accounts | NMX_, child-first: Needs217 and234 plus complete canonical Box/native/source/observation association. Conditional folds retain library/representation parameters; not credit. |
| TX2:234 | authenticate_invariant_release_registry | NMX_: No candidate. Current source-erasure/effect-program/canonical registry interpretation remains WIP; full String-clone allocation/error prefixes and same-Args representation still required. |
| TX2:240 | stage2 | NMV_ fold / shared instantiation: CANDIDATE-FOLD NMV_CandidateRoots.root240; needs canonical241. Concrete PoolLaws is available (LIBB_PoolNoWrite.laws), but no instantiated240 root at this gate; pending exact library/implementation arguments remain. |
| TX2:241 | stage2_owned | NMS_ support / TX2 principal: Needs242 and concrete SAME getter/range/encoder/native064 installation. Resume extents remain internally provable but not discharged without closed241; Root0 is separate top occurrence obligation. No rev3 candidate. |
| TX2:242 | validate_asq8 | NMS_ support / TX2 principal: Needs233 and own full source fold/getters/Results/rev3 effects/domain derivation. No rev3 candidate. |

## Physical and trust boundaries

Frozen crates/programs-r1/Cargo.lock4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Poolb936275465. Default ELFf8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc. Inherited pins, no rebuild and no shipped changes. Coherent cached import, not a cold release replay or source-to-ELF certificate.

TX1:136 uses the actual fresh receipted verify_finish emission, bc audit and the concrete LIB_VLib.library graphs; canonical child roots and their domains compose at SAME arguments. finishInputDom remains an own-input clause at OPEN137. TX2:217 reference and full allocation observation replay for every length; the native contract-interface missing control prevents credit. ReviewedTranscription-TX2:217 is ADDED-LEAD-20261107 but UNUSED by CLOSED rows. The two(bn) wrapper transcription rows are also carried unused. All prior trust retained; additions/reclassifications only. No new cryptographic trust.

TX2:233→016/039 and240→043 are RECLASSIFIED_SPURIOUS_BY_NAME, not undischarged caller clauses; every edge is retained. The first pair is u64::to_le_bytes on checkpoint_sequence as PDA seed; the third is Clock::get, bound by existing RuntimeClockSlotBinding. The real NLG resume-extents clauses remain OPEN pending closed241, separate from Root0. Full text and all top items are in NNI_TOP_TASK_SNAPSHOT.md, NNI_TOP_COMPOSITION.json and the ledger. TOP:PoolLaws is closed at the exact concrete field, but TOP:G0 is OPEN; no headline composition is claimed. The historical RZ-STATE approval request is superseded by the owner’s approved a⊤ normalization; implementation/gate remains OPEN, no Realizes filtering.

Latest carried Pool context is ledger25’s read-only PCE15/278 new helpers CLOSED,263 OPEN,119 shared,397 ON. All3 ON guard owners and P1..P4/prefix/read-to-settlement retain their PCE OPEN statuses. Later library/Pool packets are support only; no Pool settlement/execution promotion. RuntimePersistence remains data-only; no CPI success/token/system/rent/rollback/readonly/counter-frame law invented. Digest/error43/44; PDA38 quantified. Frozen3,L154 statement parameter,narrowedD188,100-bit PER-ATTEMPT,privacy and two transactions unchanged. K086/(aj)(a) remains PENDING exactly as ledger25.

extraction provenance is unresolved (NMH_/NML_: 336 blobs, 18 reproduced, 317 not reproduced, 2 semantic diffs outside the canonical domain; conservative impact 561 CLOSED rows by name matching)

Current same-method conservative impact:563/583 CLOSED rows;133 matching unresolved blobs in136’s closure. No row reopened. Fresh136 emission does not supply per-definition equality/provenance for every reused child. (bk) release campaign remains a blocker.
