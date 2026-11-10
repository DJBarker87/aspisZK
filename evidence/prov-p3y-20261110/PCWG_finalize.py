#!/usr/bin/env python3
"""PCWG finalize: writes PCWG_SET/STATUS/REMAINING/DIFFERENCES/CLASSIFICATIONS/TOOLS/SCOPES from the receipts. Run: python3 -I PCWG_finalize.py"""
import json,subprocess,collections
rec=json.loads(subprocess.check_output(['git','show','research:evidence/prov-p6y-20261110/PCXI_RECEIPTS.json']))
rs=[r for r in rec['records'] if r['verdict']=='TEXT_DIFFERS' and r.get('reason','').startswith('item text differs from every frozen item of that name')]
assert len(rs)==33
S='SETTLED';N='NOT SETTLED'
ev={'NEG':'PRVEq_NEG_PushActual_Funs_p3y.lean (PCWG_L001, exit 0)','NGD_AtG':'PRVEq_NGD_AtG_Funs_p3y.lean (PCWG_L008, exit 0)','NGD_SlotRef':'PRVEq_NGD_SlotRef_Funs_p3y.lean (PCWG_L005, exit 0)','NCX':'PRVEq_NCX_Funs_p3y.lean + PRVEq_NCX_Lemmas_p3y.lean (PCWG_L025 and PCWG_L020, exit 0)'}
st={}
def put(d,v,cls,how,evk,note=''): st[d]=dict(definition=d,status=v,class_=cls,how=how,evidence=ev.get(evk,evk),note=note)
neg_ok={'NEG_PushActual.power_limb_at':('equality','PRVEq.NEG_PushActual.Funs_p3y.verifier.power_limb_at'),
'NEG_PushActual.residue_limb_at':('equality','...verifier.residue_limb_at'),
'NEG_PushActual.update_residue_row_loop0.body':('equality','...update_residue_row_loop0.body'),
'NEG_PushActual.update_residue_row_loop0':('equality','...update_residue_row_loop0'),
'NEG_PushActual.update_residue_row_loop1.body':('loop-return refinement (done payload projected to snd)','...update_residue_row_loop1.body_proj'),
'NEG_PushActual.update_residue_row_loop1':('loop-return refinement (loop_proj via PRVEq_P3W.loop_map)','...update_residue_row_loop1.loop_proj')}
for d,(h,t) in neg_ok.items(): put(d,S,'FRESH_EQ_GATE' if h=='equality' else 'LOOP_RETURN_REFINEMENT',h+'; theorem '+t,'NEG','Fresh text = P1n emission PRVFresh_NEI_PushRaw_Funs_n3 (frozen 4bb3b3f); NEG gate Funs text equals the NEI gate Funs text except the namespace line (diffed).')
for d in ('NEG_PushActual.update_residue_row','NEG_PushActual.BatchedWeights.push'):
    put(d,N,'DEPENDS_ON_LIBRARY_TRUST','fresh text calls MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter with the external (FunsExternal) shape back : IterMut -> Array; the gate carries a hand model (NEG_RowIsolated.FunsExternal) with back : (IterMut -> IterMut) -> Array. Probe PCWG_L002: Application type mismatch at into_iter_back. Trust rows HM-B (slice iterator) and HM-D (array/slice). External name: MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter','NEG','Not a value difference: two models of the same library call. Needs the model association, not a gate rewrite.')
put('NGD_AtG.shape',S,'FRESH_EQ_GATE','frozen item chosen: r1_wire::row_shape (crates/aspis-r1-cost-probe/src/r1_wire.rs 39:0-49:1); theorem PRVEq.NGD_AtG.Funs_p3y.r1_wire.row_shape (function equality). Gate folds CLAIMS+LANES*32 to 3712, LANES*32 to 928, 28*32 to 896.','NGD_AtG','Same-name frozen item (v8_privacy_affine_gate::shape) is unrelated; chosen by signature (u8 -> Option (u8, usize)), table values and CLAIMS=87, LANES=29. The two other row_shape items (semantic_wire.rs row 25 = CLAIMS*32, state_only_prefix.rs) differ at row 25 and are not the gate.')
put('NGD_SlotRef.OFF_NODES',S,'CONSTANT_ENCODING','fresh compact.OFF_NODES = ok 28359#usize = ok gate OFF_NODES (theorem PRVEq.NGD_SlotRef.Funs_p3y.compact.OFF_NODES); the 14-constant chain proved with addlit/mullit/sublit','NGD_SlotRef','Fresh = P1n emission PCQK_E015 (frozen compact.rs). Gate constant is pure Usize, fresh is Result Usize: encoded as ok. CONDITIONAL_ON_BINDING class unchanged for consumers.')
for d,h in [('NCX_Reference.POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK','fresh = ok gate (1<<<0 ||| 1<<<1 = 3)'),('NCX_Reference.required_binding_is_zero','function equality via rbz_gate (zero loop spec) and rbz_fresh (array equality)'),('NCX_Reference.validate_verifier_registry_v2','statement with explicit type maps eMap/regMap: fresh mapped = gate'),('NCX_Reference.validate_verifier_registry_entry_v2','statement with explicit type maps eMap/entMap: fresh mapped = gate')]:
    put(d,S,'FRESH_EQ_GATE' if 'equality' in h else 'REFINEMENT_THROUGH_TYPE_MAP',h,'NCX','Fresh = PCWG_E001 (aspis-statement at 4bb3b3f, Aeneas original 959659a6, overflow checks ON). Types differ only by namespace: fresh Types vs NCX_Reference.Types compared field by field (identical except VerifierEntryStatusV1 discriminant).')
for d in ('NCX_Reference.decode_verifier_registry_entry_v2','NCX_Reference.decode_verifier_registry_v2'):
    put(d,N,'DEPENDS_ON_LIBRARY_TRUST','fresh emission calls the external axiom Slice.Insts.CoreCmpPartialEqArray.ne (PCWG_E001 FunsExternal_Template; HM-D), plus TryFromArrayCopySlice.try_from and from_le_bytes models. The gate replaces them by the loop helpers equal/zero/magic/read32/word. Statement not attempted beyond the emission.','NCX','No value difference found: Rust texts read side by side (same checks in the same order, same field offsets).')
for d in ('NCX_Reference.magic','NCX_Reference.word','NCX_Reference.zero','NCX_Reference.zero_loop','NCX_Reference.zero_loop.body'):
    put(d,N,'GATE_ONLY_HELPER','no frozen item of this role exists: the reference helpers stand in for slice/array comparisons and conversions inside the frozen decoders. Same-name frozen items (word in v6_query_batch.rs, magic in wallet_populated_migration_v2.rs, zero in a test file) are unrelated.','NCX','Semantics of zero/zero_loop are proved (PRVEq_P3Y.zero_loop_spec, zero_spec, used by required_binding_is_zero); that is use, not a fresh = gate equality.')
put('NCX_Reference.VerifierEntryStatusV1',N,'TYPE_ENCODING_DIFFERS','fresh type has @[discriminant u8] (frozen #[repr(u8)]), gate has @[discriminant isize]; constructors Pending/Active/Paused/Retired correspond (isomorphism smap/smapInv proved, PRVEq_NCX_Funs_p3y.lean). Not claimed as equal.','NCX','Encoding difference in the gate source (repr attribute omitted in the reference), not a value difference.')
for d in ('NCV_Reference.EMPTY',):
    put(d,N,'NO_FRESH_EXTRACTION','plausible counterpart: the 21 empty-tree roots in programs/aspis-pool/src/empty_roots.rs (first root 1438900896 = EMPTY[0][0]), M31 wrapper elements vs [[u32;8];21]; pool crate not extracted in this job.','NCV','Needs a fresh extraction of the pool crate at b936275 plus a table refinement.')
for d in ['NCV_Reference.bytes32','NCV_Reference.bytes32_loop','NCV_Reference.bytes32_loop.body','NCV_Reference.digest','NCV_Reference.digest_loop','NCV_Reference.digest_loop.body','NCV_Reference.identity','NCV_Reference.zero','NCV_Reference.zero_loop','NCV_Reference.zero_loop.body']:
    put(d,N,'GATE_ONLY_HELPER','NCV_Reference is a hand-written reference for the frozen TX2 decoders (its own header: no external decoder calls). These functions have no frozen item: same-name frozen items (nullifier.rs bytes32, aspis-core digest, a durable_witness_state test identity, a test zero) are unrelated. The frozen decoders live in other modules (aspis-statement pool_v1 format.rs, e.g. POOL_V1_IDENTITY_MAGIC) and are the correct extraction targets.','NCV','Not settled; no value difference claimed or found.')
assert set(st)=={r['definition'] for r in rs},set(st)^{r['definition'] for r in rs}
json.dump([{'definition':r['definition'],'module':r['module'],'receipt_item_kind':r['receipt_item_kind'],'first_difference':r['first_difference'],'receipt_files':r['receipt_files']} for r in rs],open('PCWG_SET.json','w'),indent=1)
sl=[v for v in st.values()]
cnt=collections.Counter(v['status'] for v in sl);cls=collections.Counter(v['class_'] for v in sl)
by=collections.defaultdict(lambda:collections.Counter())
for r in rs: by[r['module']][st[r['definition']]['status']]+=1
out={'target_established':False,'job':'PCWG_ (P3y)','frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','counts':dict(cnt),'by_class':dict(cls),'by_module':{k:dict(v) for k,v in by.items()},'items':sl,
 'headline_effect':'33 same-name TEXT_DIFFERS items: 12 SETTLED, 21 NOT SETTLED (this job adds 12 to the settled side; the lead decides how it composes with the 8 and 4 of PCWF_)',
 'configuration':'overflow checks ON (checked gate configuration); no wrapping operator involved in these items'}
json.dump(out,open('PCWG_STATUS.json','w'),indent=1)
rem=[{'definition':v['definition'],'class':v['class_'],'next':{'DEPENDS_ON_LIBRARY_TRUST':'association of the gate/fresh library models (HM-B slice iterator, HM-D array/slice) or a conditional statement with the model equation as hypothesis; not a gate rewrite','GATE_ONLY_HELPER':'extract the frozen decoders that these helpers stand in for and prove those, then retire the helper names from the cone','TYPE_ENCODING_DIFFERS':'lead ruling: accept the isomorphism, or re-extract the reference with #[repr(u8)]','NO_FRESH_EXTRACTION':'fresh extraction of aspis-pool empty_roots at b936275 and a table refinement'}[v['class_']]} for v in sl if v['status']==N]
json.dump(rem,open('PCWG_REMAINING.json','w'),indent=1)
diff={'value_differences_at_matching_configuration':[],'note':'none found; no stop-and-report item','encoding_differences':[
 {'item':'NEG_PushActual loop1/loop1.body','kind':'loop-return type','detail':'gate drops the iterator from the done payload; fresh returns (iter, back). Proved as projection refinement.'},
 {'item':'NEG_PushActual update_residue_row, BatchedWeights.push','kind':'library model','detail':'into_iter back function type differs between the gate hand model and the fresh external shape'},
 {'item':'NGD_AtG.shape','kind':'constant folding','detail':'gate literals 3712/928/896 versus fresh (CLAIMS+LANES)*32, LANES*32, 28*32 with CLAIMS=POINTS*LANES=87'},
 {'item':'NGD_SlotRef.OFF_NODES','kind':'Result versus pure constant','detail':'fresh Result Usize chain evaluates to ok 28359; gate pure Usize'},
 {'item':'NCX validate/required_binding_is_zero','kind':'namespace and helper encoding','detail':'fresh uses array equality and ne, gate uses the zero loop helper; error enum and structs are renamed copies (explicit maps)'},
 {'item':'NCX VerifierEntryStatusV1','kind':'discriminant representation','detail':'gate @[discriminant isize], frozen repr(u8)'},
 {'item':'NCX decode_*','kind':'reference reading helpers','detail':'gate read32/word return a default when a slice conversion fails (unreachable after the length check); the frozen code unwraps. Not proved; observation only.'}]}
json.dump(diff,open('PCWG_DIFFERENCES.json','w'),indent=1)
# scopes
sc=[]
for l in open('PCWG_ATTEMPTS.jsonl'):
    d=json.loads(l)
    if d.get('event')=='result': sc.append({k:d.get(k) for k in ('attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_tree_dirty')})
json.dump(sc,open('PCWG_SCOPES.json','w'),indent=1)
print(dict(cnt),len(sc),collections.Counter((s['kind'],s['exit_status']) for s in sc))
