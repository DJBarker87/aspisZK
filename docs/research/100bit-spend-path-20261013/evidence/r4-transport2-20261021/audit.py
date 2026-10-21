#!/usr/bin/env python3
"""Receipt/source/axiom audit only; never launches Lean, Rust or Kani."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;P=E.parent.parent;R=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
M=json.loads((E/'manifest.json').read_text());accepted=[]
for a in M['attempts']:
 d=E/(a['module']+'-'+str(a['attempt']))
 assert sha(d/'source.lean.txt')==a['source_sha256']
 saved=json.loads((d/'receipt.json').read_text())
 assert all(saved[k]==a[k] for k in ['module','attempt','exit','source_sha256','deps_fingerprint','wall_seconds','peak_rss_bytes','swaps','axioms'])
 for key in ['argv','source_revision','deps_fingerprint','peak_rss_bytes','swaps']:
  assert a[key] is not None
 if not a['final_current']:continue
 assert a['exit']==0 and a['swaps']==0
 source=P/'lean'/(a['module']+'.lean');text=source.read_text()
 assert sha(source)==a['source_sha256']
 assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b',text)
 assert not re.search(r'^\s*axiom\s',text,re.M)
 names=re.findall(r'^(?:private\s+)?theorem\s+(\w+)',text,re.M)
 printed=re.findall(r'^#print axioms (\w+)',text,re.M)
 assert sorted(names)==sorted(printed),(a['module'],names,printed)
 assert len(a['axioms'])==len(names)
 for line in a['axioms']:
  if 'does not depend' in line:continue
  ax=set(re.findall(r'\b[A-Za-z][A-Za-z.]*\b',line.split('[',1)[1]))
  assert ax<={'propext','Classical.choice','Quot.sound'},line
 accepted.append(dict(module=a['module'],attempt=a['attempt'],theorems=len(names),wall_seconds=a['wall_seconds'],peak_rss_bytes=a['peak_rss_bytes']))
assert len(accepted)==len(list((P/'lean').glob('R4Transport2*.lean')))
host=[];rejected=[]
for a in json.loads((E/'host-manifest.json').read_text()):
 assert a['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert a['swaps']==0
 inputs=a['inputs'];source=E/'host-sources'/(inputs['source_sha256']+'.rs.txt')
 assert sha(source)==inputs['source_sha256']
 log=(E/'host-receipts'/a['attempt']/'stdout.log').read_text()
 count=log.count('VERIFICATION:- SUCCESSFUL')
 if a['exit_status']==0:
  assert count>0 and 'VERIFICATION:- FAILED' not in log
  host.append(dict(attempt=a['attempt'],roots=count,wall_seconds=a['wall_seconds'],peak_rss_kib=a['peak_rss_kib']))
 else:
  assert a['exit_status'] in [2,124]
  rejected.append(dict(attempt=a['attempt'],exit=a['exit_status'],partial_successes_not_counted=count))
for filename in ['source-cut-final.json','prefix-source.json']:
 data=json.loads((E/filename).read_text())
 for f,h in data['sources'].items():assert sha(R/f)==h
baseline='54054b905';endpoints={}
for module in ['R1FinalSoundnessHeadline','R1FinalSoundnessBinPerQueryR19']:
 f=P/'lean'/(module+'.lean');relative=str(f.relative_to(R))
 original=subprocess.check_output(['git','show',baseline+':'+relative],cwd=R)
 assert original==f.read_bytes()
 endpoints[module]=dict(source_sha256=sha(f),byte_identical_to_base=True)
assert not subprocess.check_output(['git','diff',baseline,'--','crates','programs'],cwd=R)
changes=subprocess.check_output(['git','diff','--name-only',baseline],cwd=R,text=True).splitlines()
assert all('/lean-candidates/' not in p and 'M10' not in p for p in changes)
result=dict(status='R4_transport open; no boundary premise removed',baseline=baseline,audit_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),lean=accepted,lean_modules=len(accepted),theorem_audits=sum(x['theorems'] for x in accepted),host=host,accepted_kani_roots=sum(x['roots'] for x in host),rejected_host_attempts=rejected,endpoints=endpoints,shipped_source_unchanged=True,protected_candidate_files_unchanged=True,scope='Focused cached-object receipts and source-step checks; no coherent frozen release replay')
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','lean_modules','theorem_audits','accepted_kani_roots']}))
