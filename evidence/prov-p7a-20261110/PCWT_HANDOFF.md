# PCWT_ HANDOFF: phase P7a, discharge of CONDITIONAL_ON_BINDING (48 keys)

Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275. Branch codex/pc-prov-p7a-20261110 (base research 9fb1e206d7d). No ledger row, trust row, RSL, security contract or shipped source changed; no trust row or transcription proposed; nothing pushed or merged. Lean scopes 15 of 35 (one at a time, 6G/8G, swap 0, caps unraised, wall 2 to 7 s, peak RSS 2.5 to 4.9 GiB, 9 exit 0 and 6 failed shapes), extraction scopes 0 of 8. Every compiled file runs at maxHeartbeats 200000 or lower and contains no sorry; every theorem's #print axioms is propext, Classical.choice, Quot.sound (and Quot.sound alone for the ClaimSum equivalence).

## Difference at a matching configuration
None found. No input or call site to report.

## Result for the 48 keys (PCWT_STATUS.json)
Before: 48 CONDITIONAL_ON_BINDING. After: 15 EQUALITY_PROVED, 15 DEPENDS_ON_LIBRARY_TRUST, 18 CONDITIONAL_ON_BINDING. Per key: what is bound, gate instantiation, frozen item at 4bb3b3f with file:line are in PCWT_BINDINGS.json; the exact missing piece of each open key is in PCWT_REMAINING.json.

| module | keys | now | file (receipt) |
|---|---|---|---|
| WeightsFieldExplicitDecoder | 1 | EQUALITY_PROVED | PRVEq_WeightsFieldExplicitDecoder_t1 (L001) |
| CurrentClaimSumModel | 1 | EQUALITY_PROVED | PRVEq_CurrentClaimSumModel_t2 (L002) |
| Port5Q2_ReaderWeights | 2 | DEPENDS_ON_LIBRARY_TRUST (HM-B, HM-C) | PRVEq_Port5Q2_ReaderWeights_t3 (L004) |
| AspisR1WithdrawalCaller.Funs | 5 | DEPENDS_ON_LIBRARY_TRUST (HM-B, HM-D, HM-F, HM-C) | PRVEq_AspisR1WithdrawalCaller_Funs_t4 (L006) |
| Port3_NativeGeometryBody | 4 of 8 | EQUALITY_PROVED (closure_3); closure_4 stay CONDITIONAL | PRVEq_Port3_closures_t5 (L009) |
| CurrentCompactCallerModelV1 | 6 of 8 | EQUALITY_PROVED (constants); prepare, tx1 stay CONDITIONAL | PRVEq_CompactOff_t7 (L012) |
| AdapterRwModel | 9 of 15 | observer, Clone, Copy EQUALITY_PROVED; digest32, ProgramError clone, data_len, data, readonly_meta_ok, require_readonly_account DEPENDS_ON_LIBRARY_TRUST (HM-A) | _t6 (L011), _t8 (L014), _t9 (L015) |
| NMT_first.Funs | 1 | DEPENDS_ON_LIBRARY_TRUST (HM-A) | _t8 (L014) |
| NMT_stage1_owned.Funs | 1 of 2 | OwnedAccount.data DEPENDS_ON_LIBRARY_TRUST (HM-A); stage1_owned stays CONDITIONAL | _t8 (L014) |

## What these statements are, and are not
The discharge follows the lead's release definition (b): the Ops/Ext premise is replaced by an instance built from fresh frozen definitions (or an SDK item left as a named HM-A parameter) and the fresh = gate equality is restated at it. Three kinds of instance occur. (1) Port3 is stated at the concrete adopted dictionary NFN_NEW_GeometryDictionary.adopted of the L187 closure, with adopted.op5 and adopted.op6 proved equal to the fresh frozen M31 eq and ZERO. (2) The compact constants and the AdapterRw items are stated at a constructed Ops (an arbitrary base Ops with the used slots set; or panicOps with the used slots set, all unused slots panic and are not claimed). (3) Items whose only external is an SDK function are stated for every ops with the SDK slot as the parameter. For (2) and (3) the deployed dictionaries (DrvI_Installation.sdk, DrvC_Installation.currentInstalled, whose adapter/currentBase/geometry data the Configuration leaves abstract) were not compared slot by slot; that remains the consumer's binding and is stated in each record's instance_scope. The Aspis callees of the other keys live in other type universes; binding them needs either a same-universe frozen emission or a transport, which is why the open keys are open.

## Failed shapes (none retired)
L003 text defect and missing Option Try/discriminant helpers (fixed in L004); L005 encode_common simp left the shim unfolded (shim_eq added, L006); L007 panicOps by tactic failed on the Port3 Ops (Iterator-typed field), replaced by the concrete adopted Ops (L009); L008 duplicate definition; L010 tx1 arity; L013 namespace of the SDK type names. None was killed by memory or time.

## Open (18 keys, PCWT_REMAINING.json)
AdapterRw first_decoded (tx1, op10; error conversion, op44), require_verifier_checkpoint (frozen checkpoint_size emission in the AdapterRw universe: one extraction scope, not run), stage1_owned, stage2_owned, validate_asq8, authenticate_asq8_accounts (require_distinct_accounts has no emission: Aeneas rejects returns inside nested loops; the registry authentication Ops instance is not built; op21/op24/op47 slots); CurrentCompactCaller prepare and tx1 (16 callee slots); Port3 closure_4 x4 (core::array::from_fn: no accepted trust row, no extraction route); S1NativeCompact x3 (frozen expand_values needs the HM-B chunk iterator models, which have no Lean definition; slice-iterator roots belong to PCWH_); NMT_stage1_owned.stage1_owned (17 callee parameters); VTop_Model x2 (23 Ext fields).

## Next deliverable
A same-universe frozen emission of verifier::checkpoint_size (with Variant::final_len and CHECKPOINT_FIXED) to close require_verifier_checkpoint; then the tx1 closure and error conversion for first_decoded; the remaining Aspis callees need either a transport between the CurrentCaller / AdapterRw / VTop universes or per-universe emissions with the callees included.

Target not yet established.
