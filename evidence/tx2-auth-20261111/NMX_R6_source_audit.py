from pathlib import Path
import subprocess,json,lzma,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
base='evidence/tx2-owned-20261111/'
def get(p):return subprocess.check_output(['git','show',rev+':'+base+p])
pins=json.loads(get('NMS_extract_stage2/NMS_PINS.json'))
assert pins['charon_exit']==pins['aeneas_exit']==0
raw=get('NMS_extract_stage2/raw/NMS_stage2/Funs.lean').decode()
start=raw.index('def r1_pool_adapter.owned.validate_asq8\n');end=raw.index('\n/--',start)
root=raw[start:end]
llbc=json.loads(lzma.decompress(get('NMS_extract_stage2/stage2.llbc.xz')))
def loops(x):
 if isinstance(x,dict):return sum(k=='Loop' for k in x)+sum(loops(v) for v in x.values())
 if isinstance(x,list):return sum(loops(v) for v in x)
 return 0
selected=[]
for f in llbc.get('translated',llbc)['fun_decls']:
 if f is not None and isinstance(f['body'],dict):
  name='::'.join(v['Ident'][0] for v in f['item_meta']['name'] if 'Ident' in v)
  if name.endswith('owned::validate_asq8'):
   n=loops(f['body']);assert n==0;selected.append(dict(name=name,loops=n))
assert len(selected)==1
# Actual typed source body and source-support links remain immutable. The
# Lean emitted equality, full source refinement and exact native observation
# association, rather than this text inventory, discharge composition.
modules=['NMS_R2N_242Code.lean','NMS_R2N_Native242Children.lean','NMS_R2N_Effect242Fold.lean',
'NMS_Effect242.lean','NMS_EmittedValidate.lean','NMS_EmittedLinks.lean']
provenance=[]
for p in modules:
 b=get(p);provenance.append(dict(path=base+p,revision=rev,sha256=sha(b)))
expected=['decode_pool_v1_pair_forest_terminal_request_v1','nullifier','pool_v1_pair_forest_output_lane_v1',
'pool_program_id','authenticate_asq8_accounts','OwnedAccount.data','scan_proof_buffer','reconstruct_asq8_statement']
# Getters may appear with the fully qualified actual owned method name.
for name in expected:assert name in root,name
result=dict(status='PASS',row='TX2:242',route='bm emitted; complete typed source meaning; exact original native tuple',
extraction='NMS_E003 (reused, no new extraction)',source_revision=rev,extraction_pins_sha256=sha(get('NMS_extract_stage2/NMS_PINS.json')),
parent_token_sha256=sha(re.sub(r'\s+','',root).encode()),bc_audit=selected,flagged_exits=[],
source_links=provenance,full_source_law='NMX_R5_Native242.full',exact_native_observation='NMX_R6_SourceExact242.source',
source_selection='NMX_R6_NativeLive242.source_member; choice over SOURCE relation, never target Ref',
all_args='NMX_R6_Validation.root; no representation domain clause',shipped_changes=False,trust_changes=False)
(E/'NMX_R6_SOURCE_AUDIT.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(dict(status='PASS',row='TX2:242',bc_exits=0)))
