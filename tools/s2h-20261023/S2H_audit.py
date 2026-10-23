"""Validate receipts and claim scope; never rerun a prover."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2h-20261023'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((E/'object-base.json').read_text());rows=[];receipts=[]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for p in sorted(E.glob('*/receipt.json')):
 x=json.loads(p.read_text());receipts.append(x);assert x['limits']==limits
 reservation=json.loads((E/(x['attempt']+'-reservation.json')).read_text())
 assert reservation['allowed'] and reservation['bounded_reserved_bytes']+reservation['requested_bytes']<=reservation['safe_limit_bytes']
 for f,h in x['source_hashes'].items():assert sha(p.parent/'sources'/f)==h,(p,f)
 assert x['peak_rss_kib'] is not None and x['wall_seconds']>0 and x['swaps']=='0'
 if x['kind']=='lean':
  delta=json.loads((p.parent/'objects-delta.json').read_text());objs=dict(base);objs.update(delta['changed'])
  for key in delta['removed']:objs.pop(key)
  serialized=(json.dumps(objs,sort_keys=True,indent=2)+'\n').encode()
  assert hashlib.sha256(serialized).hexdigest()==delta['original_sha256']==x['deps_fingerprint']['selected_overlay_sha256']
  if x['exit_status']==0:
   for line in x['print_axioms']:
    assert 'sorryAx' not in line,line
    match=re.search(r'axioms: \[(.*)\]',line)
    if match:assert set(match[1].split(', '))<={'propext','Classical.choice','Quot.sound'},line
  assert objs['ImportUnionNamedDiscriminant.olean']['path'].startswith('/home/dombarker/project-offloads/codex-cx-import-union-20261022/objects/')
 rows.append({k:x[k] for k in ['attempt','kind','source_revision','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
latest={}
for x in receipts:
 if x['kind']=='lean' and x['exit_status']==0:latest[x['command'][-1]]=x
names=[]
for p in sorted((D/'lean').glob('S2H_*.lean')):
 text=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M),p
 assert p.name in latest and latest[p.name]['source_hashes'][p.name]==sha(p),p
 for name in re.findall(r'^theorem (\w+)',text,re.M):
  assert '#print axioms '+name in text,(p,name);names.append('AspisR1.S2H.'+name)
final=latest['S2H_Exports.lean'];assert final['attempt']=='lean-025'
assert len(final['print_axioms'])==len(names)==23
assert all(any("'"+n+"'" in line for line in final['print_axioms']) for n in names)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<5*1024**2 and p.suffix not in ['.olean','.elf','.tar','.gz'],p
stage0=json.loads((E/'S2H-stage0.json').read_text());initial=stage0['revision']
paths=set(subprocess.check_output(['git','diff','--name-only',initial],cwd=R,text=True).splitlines())
paths.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
prefix='docs/research/100bit-spend-path-20261013/'
assert all(p.startswith((prefix+'evidence/s2h-20261023/',prefix+'lean/S2H_',prefix+'design/S2H-20261023.md','tools/s2h-20261023/')) for p in paths),paths
catalog=json.loads((E/'S2H-child-obligations.json').read_text());original=json.loads((D/'evidence/s2g-20261023/contracts.json').read_text())
assert catalog['new_native_Required14_fields']==[] and len(catalog['children'])==len(original['all_children'])==13
for h,g in zip(catalog['children'],original['all_children']):assert h['missing_statement_verbatim']==g['missing_theorem'] and not h['h_native_proved']
candidate=D/'lean-candidates/s126-caller-boundary-20261021'
old=[str(p) for p in candidate.glob('*.lean') if re.search(r'@\[discriminant\b',p.read_text())]
assert not old,old
pins={str(p.relative_to(R)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(candidate.glob('*.lean'))}
(E/'S2H-candidate-source-pins.json').write_text(json.dumps({'D178_old_attribute_count':0,'pins':pins,'qualification':'Read-only current s126 root census; selected compiled objects are pinned in each receipt, not a coherent release replay.'},indent=2)+'\n')
manifest={'schema':'focused-extractor-proof-packet-v1','status':'PARTIAL; native same-cuts theorem not established','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'lean_attempts':sum(x['kind']=='lean' for x in receipts),'kani_runs':0,'limits':{'lean':100,'kani':60},'new_native_Required14_fields':[],'full_frozen_manifest_run':False,'shipped_changes':False,'new_trust_fields':False,'final_focused_audit':'lean-025/receipt.json','all_23_new_theorem_axioms_standard':True,'tool_cache_audit':'audit-001/receipt.json','claim_and_remaining_obligations':'../../design/S2H-20261023.md','attempts':rows}
assert manifest['lean_attempts']==25
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'valid':True,'lean_attempts':25,'kani_runs':0,'standard_axiom_audits':23,'new_native_Required14_fields':0,'shipped_changes':False}))
