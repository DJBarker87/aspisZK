"""Render exact member obligations from the inherited48-member inventory."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
rows=json.loads(Path('evidence/native-tx2b-20261027/NBD_MEMBER_STATUS.json').read_text())
new={
'validate_verified_afterstate':('CLOSED locally','NBH_VALIDATORS_BRIDGE.md; native K002/K004, model L004/L007/L016/L018. Exact Result on every typed afterstate/raw limb; no canonicality hypothesis.'),
'validate_pool_v1_pair_live_snapshot_v1':('CLOSED locally','NBH_VALIDATORS_BRIDGE.md; native K003/K005, model L005/L014/L015/L017/L018. Exact ordered Result on every typed snapshot/raw limb.'),
'exact':('CLOSED on reached8/32 specializations','NBH_EXACT_BRIDGE.md; K006/K007 and L021, with all22 actual call ranges proved in NBH_ExactCallerDomains.json. No claim about arbitrary native const N outside the reached domain.')}
open_rows={
'decode_pool_v1_pair_verified_afterstate_v1':'K020 proves the native envelope prefix and K030 arbitrary-usize length cut. exact8/32 is CLOSED. OPEN: NBH_Dep_DigestDecode on the SAME root/20 rows, then full ordered decoder/native-cohort carrier association; noncanonical digests precede index validation.',
'encode_pool_v1_pair_verified_afterstate_v1':'Validator CLOSED. K026 proves exact native dynamic range/pointer/length per frontier iteration. K024 full dynamic store TIMED OUT, excluded. OPEN: NBH_Dep_DigestEncode, native fixed prefix, iterator/copy framing and full Result composition with existing S2K model byte/loop laws; no passing full native store is claimed.',
'encode_pool_v1_pair_live_snapshot_v1':'Validator CLOSED. K027 proves native dynamic row range/pointer/length. K025 full dynamic store TIMED OUT, excluded. OPEN: DigestEncode, fill/header/pool/domain/index/root stores and native/model loop/copy association, complete output/error frame. Output-width rejection must occur before validation or mutation.',
'encode_pool_v1_pair_late_public_statement_v1':'K028 proves source length/index preflight on arbitrary u64s and all represented widths<=1521, including unchanged output. Actual ASF8 slice is1520 bytes. OPEN: native header/zero-fill and both SAME live/afterstate child codecs, their output subranges and mutation-on-error after fill/header. Lower child domains and wrapped errors must be derived, not assumed.',
'decode_pool_identity_v1':'K018 proves complete native Result/fields on the represented width domain; K030 covers every usize first-length guard. OPEN: SAME identity carrier/error interpretation inside the adopted master/op48 bridge. Identity decoding itself does not authenticate owner/PDA or enforce master required bindings.',
'decode_verifier_policy_v1':'K019 plus K030 prove native ordered Result/fields and unrestricted length admission; its SAME parsed policy uses K017. OPEN: interpret that carrier/result in the adopted enclosing master decoder and policy callback.',
'validate_verifier_policy_v1':'K017 proves every native typed policy Result, including exact flags/zero/immutable-authority order. OPEN: instantiate/associate the SAME carrier at coherent policy callback op15, without assuming callback output or stronger immutable/unpaused policy.',
'decode_pool_v1_pair_forest_master_v1':'K022 proves native length/magic/version/lane/digest header; K030 arbitrary lengths. OPEN: reserved-byte scan, format/boolean, SAME identity/policy children, one native sequence-store iteration plus Lean induction, validate_master and complete op48 Result/carrier association. Iterator-written cells have no D188 credit.',
'decode_pool_v1_pair_forest_checkpoint_v1':'K023 proves native header; K030 arbitrary lengths. OPEN: reserved scan, nonzero master/domain, DigestDecode, one sequence-store/bound iteration plus induction and complete op49 Result/carrier association. This is192-byte Pool ASC8, not1768-byte verifier checkpoint.',
'first_canonical_byte':'OPEN at NBH_Dep_DigestEncode/M31Encode for arbitrary raw M31 values, then byte0 of that SAME emitted array. No precondition that raw digest limbs are canonical may be silently imposed on this helper.',
'pool_v1_pair_forest_output_lane_v1':'CLOSED digest scanner child is reusable for all raw limbs. OPEN: first_canonical_byte, native full Result and coherent op17 carrier association; derive any canonical branch domain from this SAME nullifier scan, then byte0&7.',
'validate_master':'OPEN: native ordered required identity/policy checks, one arbitrary lane-sequence iteration and Lean induction (capacity<=2^20), has_checkpoint/next-sequence/all-zero invariants and its enclosing adopted master association. No held unrelated U00 dependency is asserted.',
'required_binding_is_zero':'K012 gives native arbitrary32-byte zero/selected-byte laws; L014 gives generic cohort array equality. OPEN inside each enclosing concrete validator/callback: identify that SAME byte carrier and result, not a separately assumed successful zero test.',
'decode_pool_v1_pair_forest_terminal_request_v1':'K021 proves native ASQ8 header in exact source order and K030 arbitrary lengths. OPEN: SAME variant TransferDecode/WithdrawalDecode, complete public/request carrier and post-payment nonzero profile/release/Pool checks. A zero binding does not skip earlier payment errors.',
'encode_pool_v1_pair_forest_terminal_statement_v1':'K029 proves exact native ASF8 fixed prefix bytes through144 and zero remaining cut buffer on arbitrary projected fields/anchor bytes. OPEN: SAME statement projections/validation, lower DigestEncode, complete late child and same-variant payment Encode, output ranges/errors, and full association with installed RPz7/S6 encoder. Prefix is not encoder success; live deployment lies at public256..288.',
'validate_pool_v1_pair_forest_terminal_statement_v1':'OPEN: native ordered account-zero/lane checks, SAME variant payment Encode, pool/domain/sequence/anchor equalities, nullifier/output-lane child and full late Encode. Associate every reached Result to the adopted validator on SAME input, proving every child domain. Existing helper/model facts are not native enclosing closure.',
'encode_pool_v1_pair_forest_terminal_result_v1':'OPEN and deliberately unattempted here: full ASR8 validation, DigestEncode/afterstate Encode, exact bytes/errors/carrier. No headline soundness need: op53 universally quantified (NBD_EMIT_QUANTIFIER.md). ASF8 was prioritized.',
'validate_result':'OPEN and unattempted: exact native required bindings, canonical nullifier/lane selection and SAME afterstate encoder with full error order/carrier. No soundness credit is needed from universal op53.',
'validate_pool_v1_pair_forest_terminal_result_against_statement_v1':'OPEN and unattempted: statement validation FIRST, result validation SECOND, then exact kind/master/lane account/lane/nullifier/ENTIRE afterstate equality. Requires both enclosing validators and their SAME carriers; no hash identity substitute.'}
reg_gates={
'validate_verifier_registry_v1':'K008','validate_verifier_registry_entry_v1':'K009','validate_verifier_registry_v2':'K010','validate_verifier_registry_entry_v2':'K011',
'decode_verifier_registry_v1':'K013 + K030','decode_verifier_registry_entry_v1':'K014 + K030','decode_verifier_registry_v2':'K015 + K030','decode_verifier_registry_entry_v2':'K016 + K030'}
slots={'VerifierRegistryV1::is_paused':25,'VerifierRegistryV1::is_immutable':26,'VerifierRegistryV2::is_paused':27,'VerifierRegistryV2::is_immutable':28,'VerifierRegistryEntryV2::is_active_at':29,'VerifierRegistryEntryV1::is_active_at':30,'decode_verifier_registry_v1':31,'decode_verifier_registry_entry_v1':32,'decode_verifier_registry_v2':33,'decode_verifier_registry_entry_v2':34}
for row in rows:
 n=row['id'].split('.rs::',1)[1]
 if n in new:row['status'],row['evidence_or_open']=new[n]
 elif row['status'].startswith('CLOSED'):row['evidence_or_open']='INHERITED without edits/reproof: '+row['evidence_or_open']
 elif n in open_rows:row['evidence_or_open']=open_rows[n]
 elif n in reg_gates:row['evidence_or_open']='Native '+reg_gates[n]+' proves the full typed value/error law on its explicit domain (K030 supplies arbitrary-usize initial rejection for decoders). OPEN: SAME concrete carrier/full Result and panic distinction in its enclosing coherent registry/authentication callback'+(' op'+str(slots[n]) if n in slots else '')+'. No model dictionary or independent success observation is an installation.'
 elif n in slots:row['evidence_or_open']='Inherited native NBD_K005 covers arbitrary full records and slot. OPEN: SAME carrier/Boolean Result association at coherent op'+str(slots[n])+'. NBH_SLOT_FINDING.md corrects the reversed flag locators; no caller success or fixture domain is assumed.'
 elif n.startswith('VerifierRegistryEntry') and n.endswith('has_no_retirement_slot'):row['evidence_or_open']='Inherited native NBD_K005 covers all retirement u64s (MAX sentinel). OPEN: identify this SAME decoded carrier and predicate inside its active-at-slot/entry-validator bridge; no separate adopted getter counterpart exists.'
 elif n=='VerifierEntryStatusV1::try_from':row['evidence_or_open']='Inherited NBD_K005 checks every status byte and native new entry decoders retain exact invalid-status rejection. OPEN: map those SAME variants/errors into each adopted entry decoder, not a separately selected status.'
 elif n.startswith('PoolV1PairForestTerminal'):
  row['evidence_or_open']='Inherited NBD_K009 proves native value and typed-reference identity on arbitrary variants; NBD source_parts/common are reusable. OPEN: associate this exact nullifier/kind projection inside the adopted statement/payment validator or encoder on the SAME variant. There is no separate named adopted getter definition.'
 else:raise AssertionError((row['id'],n))
(E/'NBH_MEMBER_STATUS.json').write_text(json.dumps(rows,indent=2)+'\n')
intro={
'U03':'Three new reached-member bridges are CLOSED (NBH_VALIDATORS_BRIDGE.md, NBH_EXACT_BRIDGE.md), plus the inherited digest scanner. Four enclosing codecs remain OPEN. Native dynamic-store timeouts are excluded; range/copy-boundary evidence does not silently replace them.',
'U04':'All local native registry/policy/identity Result gates passed; adopted enclosing callback/carrier associations remain OPEN. Correct flag slots: op25 paused1,op26 immutable1,op27 paused2,op28 immutable2. Coherent digest/error remain op43/op44. Decoder success authenticates no owners or PDAs.',
'U05':'ASF8 statement side was prioritized: K029 checks its native fixed prefix; ASQ8 header K021 and arbitrary length K030 are supporting evidence. Full validation/encoding remains OPEN. ASR8 emission is unattempted and unnecessary for headline soundness because op53 is universally quantified.'}
for unit in ['U03','U04','U05']:
 rs=[r for r in rows if r['unit']==unit];closed=sum(r['status'].startswith('CLOSED') for r in rs)
 text=f'# NBH_{unit} — OPEN\n\n'+intro[unit]+f'\n\n{closed}/{len(rs)} reached local members CLOSED;{len(rs)-closed} exact open members below. Unit closure is not claimed. No headline premise is removed.\n\n'
 text+='| Frozen member | Status | Established evidence / exact remaining obligation |\n|---|---|---|\n'
 for r in rs:text+='| `'+r['id']+'` | '+r['status']+' | '+r['evidence_or_open']+' |\n'
 text+='\nRetained: frozen3, L154 statement parameter, narrowed D188, RuntimePersistence, approved two-transaction game, native P6/TrustedStd/runtime and source-to-ELF boundary; all security metrics/carriers/adversary/event unchanged. NBH_DEPENDENCIES.md lists every needed lower native bridge explicitly. No absent NBG result is assumed.\n'
 (E/('NBH_'+unit+'_BRIDGE.md')).write_text(text)
assert sum(r['status'].startswith('CLOSED') for r in rows)==8
assert sum(r['status']=='OPEN' for r in rows)==40
print('48 exact rows:8 reached closures (5 inherited),40 OPEN')
