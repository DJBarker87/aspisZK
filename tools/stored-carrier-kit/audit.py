#!/usr/bin/env python3
"""Read-only packet checks and deterministic signature artifacts; no proof reruns."""
from pathlib import Path
import difflib,hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/stored-carrier-20261021'
subprocess.run(['python3',str(R/'tools/stored-carrier-kit/generate.py'),'--check'],check=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=['StoredCarrierBindingObstruction','StoredCarrierRawLayout','StoredCarrierBindingComponents','StoredCarrierPresentedModel','StoredCarrierPresentedHeadline']
man=json.loads((E/'manifest.json').read_text()); accepted=[]
for m in mods:
 src=B/'lean'/f'{m}.lean'
 assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b|^\s*axiom\s',src.read_text(),re.M),m
 rows=[a for a in man['attempts'] if a['module']==m and a['final_current']]
 assert len(rows)==1,m
 a=rows[0];assert a['exit']==0 and a['source_sha256']==sha(src) and a['swaps']==0,m
 n=len(re.findall(r'^theorem ',src.read_text(),re.M));assert len(a['axioms'])==n,(m,n,a['axioms'])
 for line in a['axioms']:
  if 'does not depend' in line:continue
  names=set(re.search(r'\[([\s\S]*)\]',line)[1].replace('\n',' ').replace(' ','').split(','))
  assert names<={'propext','Classical.choice','Quot.sound'},(m,names)
 accepted.append(dict(module=m,theorems=n,receipt_attempt=a['attempt'],wall=a['wall_seconds'],peak_rss_bytes=a['peak_rss_bytes'],swaps=a['swaps']))
roots=['route-v3','readonly-v1','stage1-v1','stage2-v1']
for root in roots:
 d=json.loads((E/'host/receipts'/root/'receipt.json').read_text());assert d['exit_status']==0 and d['swaps']==0
 assert d['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 for key,val in d['source_sha256'].items():
  if Path(key).suffix in ['.rs','.toml','.lock']:assert sha(R/key)==val,(root,key)
 for metric in ['wall_seconds','peak_rss_kib','source_revision','deps_fingerprint','print_axioms']:assert metric in d
pins=json.loads((E/'source-pins.json').read_text());assert not pins['validation']['mismatches']
for key,val in pins['pins'].items():assert sha(R/key)==val['sha256'],key
for row in json.loads((E/'reused-evidence.json').read_text()):
 p=R/row.get('receipt',row.get('path'));assert sha(p)==row['sha256']
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000,p
changes=subprocess.check_output(['git','diff','--name-only','0a7ee2dcc^','--','crates','programs'],cwd=R,text=True).splitlines();assert not changes,changes
# The deliberately nonempty diff records the model specialization honestly.
def sig(path):
 s=path.read_text();a=s.index('theorem final_soundness\n');b=s.index(':=',a)
 return s[a:b].rstrip()+'\n'
before=sig(B/'lean/OraclePortHeadlineFrozenPerAttempt.lean');after=sig(B/'lean/StoredCarrierPresentedHeadline.lean')
(E/'headline-signature-before.lean.txt').write_text(before)
(E/'headline-signature-model-after.lean.txt').write_text(after)
(E/'headline-signature-model.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='arbitrary-runtime endpoint',tofile='constructed presented model')))
result=dict(status='proved focused components and logical instance; deployed carrier binding remains open',modules=accepted,kani_roots=roots,new_theorems=sum(x['theorems'] for x in accepted),shipped_files_changed=changes,original_endpoint_edited=False,deployed_premise_removed=False,deployed_strict_weakening_proved=False,constructed_model_binding_proved=True,constructed_model_p2_prime_only_runtime_remainder=True,source_observation_join_proved=False,full_frozen_manifest_replayed=False,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip())
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
