from pathlib import Path
import json,subprocess,lzma,re,hashlib
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
base='evidence/tx2-owned-20261111/'
def get(p):return subprocess.check_output(['git','show',rev+':'+base+p])
raw=get('NMS_extract_stage2/raw/NMS_stage2/Funs.lean').decode()
a=raw.index('def r1_pool_adapter.owned.stage2_owned\n');root=raw[a:];root=root[:root.index('\nend ')]
for name in ['validate_asq8','OwnedAccount.data','encode_pool_v1_pair_forest_terminal_statement_v1','tx2_authenticated','observer','emit_result']:
 assert name in root,name
pins=json.loads(get('NMS_extract_stage2/NMS_PINS.json'));assert pins['charon_exit']==pins['aeneas_exit']==0
llbc=json.loads(lzma.decompress(get('NMS_extract_stage2/stage2.llbc.xz')))
def loops(x):
 if isinstance(x,dict):return sum(k=='Loop' for k in x)+sum(loops(v) for v in x.values())
 if isinstance(x,list):return sum(loops(v) for v in x)
 return 0
selected=[]
for f in llbc.get('translated',llbc)['fun_decls']:
 if f is not None and isinstance(f['body'],dict):
  name='::'.join(v['Ident'][0] for v in f['item_meta']['name'] if 'Ident' in v)
  if name.endswith('owned::stage2_owned'):
   n=loops(f['body']);assert n==0;selected.append(dict(name=name,structured_loops=n))
assert len(selected)==1
# Verify the sole source-block change independently of the generator.
original=get('NMS_Effect241.lean').decode();old=original[original.index('def stage2 '):original.index('\ndef raw ')]
actual=(E/'NMX_R8_Code241.lean').read_text();new=actual[actual.index('def body '):actual.index('\nend NMX_R8_Code241')]
group=json.loads((E/'NMX_R8_SOURCE_GROUP.json').read_text())
assert group['original_block'] in old
expected=old.replace(group['original_block'],'                let r5 ← effects.op22 val.statement\n')
expected=expected.replace('def stage2 ','def body ').replace('mapError r6','NMS_Effect241.mapError r6')
norm=lambda s:re.sub(r'\s+','',s)
assert norm(expected)==norm(new),'unreviewed grouped-body control change'
# Child242 must be the complete source meaning, never its chosen graph.
children=(E/'NMX_R9_Children241.lean').read_text()
assert 'NMS_R2N_Native242Children.meaning false (NMX_R4_NMS233.typed choices)' in children
assert 'NMX_R5_Native242.full choices p a d s' in children
mapping=[
 dict(row='TX2:242',original='program_id, accounts, data, current_slot',implementation='NMX_R9_Children241.validate',law='NMX_R5_Native242.full',mode='ALL source observations'),
 dict(row='TX2:229',original='accounts[0] and accounts[6]',implementation='NMS_R2N_GetterMeaning.meaning',law='NMS_R2GetterLink.full',mode='all ProgramError/clone outcomes'),
 dict(row='TX2:165',original='validated.statement',implementation='LIBB_PoolEncode.code/terminal',law='LIBB_PoolEncode.root + NMX_R8_CodecGroup.context',mode='full encoder + ACTUAL constant map_err context, fail/div included'),
 dict(row='TX2:064',original='encoded.to_slice, proof[688..checked_end], checkpointData, SolanaDigest, None',implementation='LIBB_ObservationModel.law',law='LIBB_Tx2Auth.same/native + NMX_R8_Digest241.descriptor',mode='full law including C04 independent abort prefixes; no Functional inference'),
 dict(row='TX2:211',original='actual verifier Err',implementation='NMS_R2ErrorSource.callback',law='NMX_R7_Error241.full + LIB_ErrorDebug.native_format/native_source',mode='format allocation BEFORE log, all errors'),
 dict(row='TX2:219',original='validated.statement',implementation='LIBB_PoolEmit.code/observation',law='LIBB_PoolEmit.root + NMX_R8_Emit241.full',mode='exact return-data chronology'),
]
modules=['NMS_Effect241.lean','NMS_241EmittedLink.lean','NMS_Emitted241.lean','NMS_R2Domains.lean','NMS_R2Fold241.lean']
result=dict(status='PASS',row='TX2:241',route='bm emitted, fixed LIBB pool + V0-star, no retained Ops/library/child laws',
 reused_extraction='NMS_E003',source_revision=rev,extraction_pins_sha256=sha(get('NMS_extract_stage2/NMS_PINS.json')),
 parent_token_sha256=sha(norm(root).encode()),bc_audit=selected,flagged_exits=[],source_group='encoder + immediate constant map_err only; kernel GroupHead equality',
 same_argument_calls=mapping,source_links=[dict(path=base+p,revision=rev,sha256=sha(get(p))) for p in modules],
 full_source='NMX_R9_Native241.full',source_observation='NMX_R9_StageTwo.source',own_domain='exact canonical D1/D2',
 extent_source='actual native242 success + actual length guard; no retained extent clause',
 retired_shapes=['NMX_L1311 whole unification; split named continuations','NMX_L1341 unnormalized head rfl; replace by continuation function equality'],
 limits_changed=False,shipped_changes=False,trust_changes=False,explanation='NMX_R9_SOURCE_ROUTE.md')
(E/'NMX_R9_SOURCE_AUDIT.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(dict(status='PASS',row='TX2:241',bc_exits=0,other_source_control_changes=0)))
