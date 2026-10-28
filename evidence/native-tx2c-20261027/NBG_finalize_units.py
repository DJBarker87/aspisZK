from pathlib import Path
import json
E=Path(__file__).resolve().parent
rows=json.loads((E/'NBG_U01_STATUS.json').read_text())
extra={
'CM31::from_le_bytes':('K010; CandidateCM31Parser.from_le_bytes_refines (L065)','exact8 arbitrary bytes; full Option, both canonical rejects'),
'CM31::mul':('LPi_FieldValues.cm_mul / LPi_CMProduct.source,cross_value (L014/L087)','canonical2+2 limbs; M31 products/reducer return canonical; proved wide cross-product bound and each sub domain'),
'CM31::mul_m31':('LPi_MixedValues.cm_m31 (L084/L087)','all raw2+1 limbs; two paired M31 products, each full raw-u32 domain'),
'CM31::write_le_bytes':('K010; LPi_WriterValues.cm_writer (L062/L065)','all raw2 limbs, arbitrary exact8 mutable bytes; complete output'),
'M31::inv':('K028; NBG_SquareTrace.native_result (L095), NBG_InverseBridge.inverse_result (L080), NBG_INV_SOURCE.json','all raw32 values including zero panic; SAME17-call DAG and same loop traces; approved field-mul discharge'),
'M31::mul':('LPf_BaseMultiply.product_bound,word_product,source (L010); K027 reducer; L087/L094','all raw32 operands; widening product fits u64, exact natural product moduloP; approved Lean field method, NEVER multiplication in Kani'),
'M31::reduce_u64':('K027; NBG_Reducer.m31_reduce (L066)','every u64; full natural modP result and canonical output'),
'M31::to_le_bytes':('K009; LPi_ByteWord.source (L063/L065)','every raw32 word; all four little-endian bytes'),
'QM31::from_le_bytes':('K011; CandidateQM31Parser.from_le_bytes_refines (L065)','exact16 arbitrary bytes; four canonical limb rejects and full Option'),
'QM31::mul':('LPi_TowerValues.qm_mul (L015/L087)','canonical4+4 limbs; derives canonical sums/products before each CM31/mul_by_r/add/sub use'),
'QM31::mul_m31':('LPi_MixedValues.qm_m31 (L084/L087)','all raw4+1 limbs; two CM31 scalarings on their all-raw domain'),
'QM31::square':('NBG_FieldSquare.input_value,cm_square,qm_square (L093)','canonical4 limbs; proves optimized CM31 wide product cannot wrap; all intermediate callee domains derived'),
'QM31::write_le_bytes':('K011; LPi_WriterValues.qm_writer (L062/L065)','all raw4 limbs, arbitrary exact16 mutable bytes; both CM31 slices exactly8'),
'WideExact::c0':('K031; NBG_GetterPorts.c0 (L073)','all raw8 limbs; selected cohort field projection on explicit coordinate port'),
'WideExact::c1':('K031; NBG_GetterPorts.c1 (L073)','all raw8 limbs; selected cohort field projection on explicit coordinate port'),
'WideExact::from_le_bytes':('K017; NBG_WideBytes.bytes_result (L071), NBG_WideCarriers.limbs_result/wrong_byte_length (L022)','all valid slices: wrong lengths reject before indexing; exact32 all bytes and full Option; K017 lengths0..33 plus source-parametric length guard, not a claim of unbounded Kani slices'),
'WideExact::from_qm31':('K015; NBG_Embedding.from_qm31_result (L023)','all raw4 limbs; normalization plus four upper zero limbs'),
'WideExact::from_m31':('K029; NBG_Embedding.from_m31_result (L023); inherited S1M31EmbeddingTotalV1','every raw32 scalar; exact trait member, both normalization passes and seven zero limbs'),
'WideExact::mul':('LPi_TowerValues.wide_mul (L015/L087)','canonical8+8 limbs; derives all QM31 and mul_u domains, full natural8-coordinate output'),
'WideExact::mul_m31':('NBG_FieldDischarge.wide_scale (L087)','all raw8+1 limbs; derives normalized scalar, both QM31 scalarings have all-raw domain'),
'WideExact::mul_qm31':('NBG_FieldDischarge.canonical_fio,wide_qm (L087)','canonical self8, arbitrary raw rhs4; derives canonical RHS before both QM31 multiplications'),
'WideExact::sub':('K016; NBG_CheckedSub.wide_result (L091)','canonical8+8 limbs; exact checked CurrentWide cohort result; all M31 arithmetic bounds derived'),
'WideExact::to_le_bytes':('K030/K031; NBG_WriterPorts.writer_result/word_order (L082); reused P6ToBytes.OutputInvariant induction','all raw8 limbs; one native arbitrary-state4-byte write/frame, eight disjoint stride4 chunks, exact reused model output/word order'),
'WideExact::to_limbs':('K014/K031; NBG_WideCarriers.to_limbs_result (L022)','all raw8 limbs; complete ordered eight-word carrier, not only canonical words'),
'reduce_u64':('K027; LPf_CoreReduction.source (L009/L066)','every u64; two nonoverflowing folds, cast/subtract placement and canonical natural remainder'),
'square_n':('K028; NBG_SquareLoop.square_n_result (L061), NBG_SquareTrace.native_result (L095)','all raw32 values and machine counts; arbitrary Range pre-state, exact raw Result from same per-cell trace, including zero iterations'),
'mul_u':('LPi_TowerValues.mul_u (L015/L087); K007 closed mul_by_r','canonical4 limbs; source/model constructor swaps halves and applies closed mul_by_r to c1')}
for r in rows:
 if r['name'] in extra:
  evidence,domain=extra[r['name']];r.update(status='CLOSED local',evidence=evidence,domain=domain)
 else:r['domain']=r['evidence'].split(';')[-1].strip()
assert len(rows)==47 and all(r['status']=='CLOSED local' for r in rows)
(E/'NBG_U01_STATUS.json').write_text(json.dumps(rows,indent=2)+'\n')
text='''# NBG U01 canonical arithmetic and byte carriers — CLOSED on stated local domains

All47 assigned members have a source-to-selected-cohort helper bridge below.
This is the approved hybrid P6 method: native gates for primitive/control/byte
steps, Lean-discharged multiplication, same-call composition and loop induction.
It is NOT47 Kani multiplication proofs, a headline implementation installation,
a source-to-ELF theorem or a claim that enclosing TX2 callers' domains are closed.

Frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; exact69 source/body pins in
NBG_TARGETS.json / NBG_SOURCE_START.json. Release arithmetic scope excludes
r0-op-count and r0-e4-reference; canonical domains and every internal child use
are explicit. SInt2 objects/Aeneas library are pinned. FIo Funs/Types/External
and the RPz7 replayed cohort differ ONLY in import names
(NBG_FIO_SOURCE_SELECTION.json); field declarations are byte-identical after
removing import lines. No different dictionaries are silently identified.
S1 CodeField locator correction is NBG_COHORT_CORRECTIONS.md.

| Member | Bridge evidence | Exact domain / child obligations discharged |
|---|---|---|
'''
for r in rows:text+=f"| `{r['name']}` | {r['evidence']} | {r['domain']} |\n"
text+='''
## Composition and effects

The field-method rows use the owner's explicit translated-field exception,
not an unpaired stub or a guessed native return. LPf proves widening casts,
full32×32 product bounds, successful emitted multiplication, exact modP value
and canonical output; K027 checks the actual reducer. The pure frozen field
bodies compose those closed scalar/complex/quartic calls in source order.
LPi_CMProduct proves the wide cross-product bound; LPi_TowerValues derives
canonical operands at every nested add/sub/mul/mul_by_r/mul_u call. New
NBG_FieldSquare proves the two-product optimized CM31 kernel's wide bound and
its exact natural coordinates before composing QM31::square. No multiplication
is proved/evaluated natively in Kani. Field callbacks have no allocator, SDK,
log or digest effect in this release configuration. Compiler/platform/P6 and
source-to-ELF boundaries are retained, not silently discharged.

K028 establishes one actual Range.next/square-body transition on arbitrary
pre-state. Its only field stub is paired with LPf_BaseMultiply.source on ALL
raw u32 inputs (NBG_STUBS.md). NBG_SquareTrace constructs the exact raw scalar
Result by induction from per-cell natural relations; the trace contains no
whole-output equality. The source validator compares ALL17 ordered inverse
calls and operands with the reused model (NBG_INV_SOURCE.json), including
zero assertion and loop counts. SAQ_Inverse/R72 reference is imported unchanged.

K030 establishes one serializer update/frame on arbitrary32-byte pre-state
and index<8. K031 establishes the same ordered eight words and getters even
on raw noncanonical limbs. The frozen loop has exactly eight disjoint4-byte
chunks zipped with those words. The reused P6ToBytes output induction and
NBG_WriterPorts give the SAME full32-byte model result. There is no whole-buffer
native loop gate. Exact-width CM31/QM31 parser/writer domains are8/16; callers
must supply those checked slice widths. WideExact wrong-length rejection is
source-parametric and model-total, not extrapolated from bounded Kani slices.

Coherent digest/error slots stay op43/op44. All NBC modules are imported;
none of their seven results is re-proved. No XRn_Join kit or stand-in is used.
Each root has an accepted #print axioms audit with only propext,Classical.choice,
Quot.sound or none. Exact commands,revision/source/dependency hashes,exit,wall,
RSS,swap and cgroup caps are in the receipts. Rejected diagnostics and the
stopped atomic-decoder proposal carry no closure credit. Cache recovery and
minimal-import generic utility replays are recorded separately and add no
protocol assumption. All unchanged/new objects stay in the designated
persistent cache; the coherent workspace and Aeneas objects are untouched.

Every prover/build scope is serial, admitted by exit0 AND allowed:true,
high6G/max8G/swap0/tasks64; Lean-M7000, optimized offline Kani and frozen graph/
lock checks. No cap/timeout increase or unchanged killed/timed-out shape rerun.
No headline premise removed: RPx_Deployed.deployed,L154 statement parameter,
narrowed D188,frozen3,RuntimePersistence and game unchanged. S2 and deployed
100-bit target remain unestablished. U00's allocation bridge and U02 codecs
remain open; this unit is not promoted to either enclosing caller or S2.
No shipped/cfg(kani) repository source change, so no ELF rebuild trigger.
Inherited pins, not reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
'''
(E/'NBG_U01_BRIDGE.md').write_text(text)
rows=json.loads((E/'NBG_U02_STATUS.json').read_text())
extra={'validate_common':'K023; NBG_PaymentChecks.common_result (L076), all raw fields, full error priority',
'validate_pool_v1_private_transfer_public_v1':'K024; NBG_PaymentValidators.transfer_result (L079), all raw records, full Result',
'validate_pool_v1_withdrawal_public_v1':'K025; NBG_PaymentValidators.withdrawal_result (L079), all raw records, full Result',
'require_header':'K026; NBG_Header.header_result/tag_result/slice_equal (L088), all216 bytes, arbitrary magic and both/all enum kinds'}
for r in rows:
 if r['name'] in extra:r.update(status='CLOSED local',evidence=extra[r['name']])
assert sum(r['status']=='CLOSED local' for r in rows)==8
(E/'NBG_U02_STATUS.json').write_text(json.dumps(rows,indent=2)+'\n')
old=(E/'NBG_U02_BRIDGE.md').read_text();tail=old[old.index('## Native gates'):]
tail=tail.replace('total common/transfer/withdrawal validator and header model result laws; ','').replace('The optional NBG_PaymentChecks model normalization is awaiting recovery of missing unchanged imported objects; it is not accepted yet.','NBG_PaymentChecks and NBG_PaymentValidators now prove the total common/transfer/withdrawal Result laws (L076/L079); NBG_Header proves every header rejection/success (L088).')
text='''# NBG U02 atomic digest and payment codecs — OPEN

Eight local members CLOSED; exactly eight enclosing codec members OPEN below.
Frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; coherent SInt2 selection, source/body
pins and all retained boundaries as NBG_U01_BRIDGE.md. No headline premise removed.

| Member | Status | Evidence / domain |
|---|---|---|
'''+''.join(f"| `{r['name']}` | {r['status']} | {r['evidence']} |\n" for r in rows)+'\n'+tail+'''
Atomic decoder L074 exhausted DEFAULT200000 elaboration heartbeats in combined
8-word Result/Option normalization. That shape is stopped; no unchanged rerun
or larger limit. NBG_AtomicDecode_PROPOSAL.lean.txt is excluded from importable
modules and closure. Replacement: one-word and rejecting-prefix lemmas, then
composition. K019 remains a full native check, not a model bridge. Digest
encoding K020 is only the arbitrary-state iteration; its model induction and
enumerator association remain open. No codec success/desired output is assumed.
'''
(E/'NBG_U02_BRIDGE.md').write_text(text)
