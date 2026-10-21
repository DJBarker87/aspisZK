#!/usr/bin/env python3
"""Offline source/receipt/axiom audit. Never invokes Lean, Kani or compilation."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[4];P=E.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=json.loads((E/'manifest.json').read_text());accepted=[]
for a in manifest['attempts']:
 assert sha(E/(a['module']+'-'+str(a['attempt']))/'source.lean.txt')==a['source_sha256']
 if not a['final_current']:continue
 assert a['exit']==0 and a['swaps']==0
 assert sha(P/'lean'/(a['module']+'.lean'))==a['source_sha256']
 source=(P/'lean'/(a['module']+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option (maxHeartbeats|maxRecDepth)',source,re.M)
 assert len(a['axioms'])==len(re.findall(r'^#print axioms ',source,re.M))
 for line in a['axioms']:
  assert 'sorryAx' not in line
  if 'depends on axioms:' in line:
   names=re.search(r'\[([\s\S]*?)\]',line)[1]
   assert set(re.findall(r'[\w.]+',names))<= {'propext','Classical.choice','Quot.sound'}
 accepted.append(dict(module=a['module'],axioms=a['axioms'],exit=a['exit'],source_sha256=a['source_sha256']))
for name in ['header','caller','parser','opening']:
 c=json.loads((E/(name+'-source-cut.json')).read_text())
 for p,h in c['sources'].items():assert sha(R/p)==h,(p,name)
for n in ['R1FinalSoundnessHeadline','R1FinalSoundnessBinPerQueryR19']:
 p='docs/research/100bit-spend-path-20261013/lean/'+n+'.lean'
 assert subprocess.check_output(['git','show','5b6193eec:'+p])==(R/p).read_bytes()
host=json.loads((E/'host-manifest.json').read_text());passes=[]
for a in host['attempts']:
 assert a['source_sha256'] and a['deps_fingerprint']
 assert int(a['limits']['memory.max'])<=8*2**30 and a['limits']['memory.swap.max']=='0' and a['limits']['pids.max']=='64'
 assert a['source_revision']
 if a['exit_status']!=0:continue
 assert a['swaps']==0
 if 'kani' in a['command']:
  inp=json.loads((R/a['inputs']).read_text());h=inp['source_sha256']
  snapshot=E/'host/source-snapshots'/(h+'.rs.txt');assert sha(snapshot)==h
  log=(R/a['receipt']).parent/'stdout.log';s=log.read_text()
  assert 'VERIFICATION:- SUCCESSFUL' in s and re.search(r'0 failures',s)
  passes.append(a['attempt'])
generated=(E/'header-extraction/generated/AspisS2HeaderRef/Funs.lean').read_text();definition=generated.split('def header_reference',1)[1].split('end AspisS2HeaderRef',1)[0].strip()
module=(P/'lean/S2KaniHeaderReference.lean').read_text();copied=module.split('def header_reference',1)[1].split('theorem header_rejects',1)[0].strip();assert definition==copied
binding=json.loads((E/'parser-binding.json').read_text());assert all(x['normalized_equal'] for x in binding['declarations'])
linked=json.loads((E/'linked-source-pins.json').read_text())
assert json.loads((E/'linked-freeze-diff.json').read_text())==[]
for path,h in linked.items():
 assert hashlib.sha256(subprocess.check_output(['git','show','b2727acd3:'+path])).hexdigest()==h,path
result=dict(schema='s2-kani-offline-audit-v1',status='pass',formal_modules=accepted,accepted_kani_batches=passes,headline_deletion='not claimed: missing decision/public-tag binding',existing_endpoints_unchanged=True,scope='Focused checks only; no frozen manifest/C2/P6/R21 replay or full source/model boundary discharge.')
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'pass','formal_modules':len(accepted),'accepted_kani_batches':passes}))
