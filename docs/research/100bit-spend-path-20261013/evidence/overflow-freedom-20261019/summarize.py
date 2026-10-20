#!/usr/bin/env python3
"""Summarize immutable focused receipts, including wrapped Lean axiom lists."""
import hashlib,json,re,subprocess
from pathlib import Path
here=Path(__file__).resolve().parent
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
manifest=json.loads((here/'manifest.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
latest={};audit=[]
for name in manifest['attempts']:
 p=here/name;r=json.loads(p.read_text());latest[r['module']]=(name,r)
 log=p.parent/'out.log'
 if not log.exists():continue
 for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text()):
  axioms=[x.strip() for x in (m.group(2) or '').split(',') if x.strip()]
  audit.append({'receipt':name,'module':r['module'],'theorem':m.group(1),'axioms':axioms,'compile_exit':r['exit'],'allowed':set(axioms)<=allowed,'raw':m.group(0)})
(here/'axioms-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
targets=[]
for module,(name,r) in latest.items():
 if r['exit']!=0:continue
 src=repo/r['source'];current=hashlib.sha256(src.read_bytes()).hexdigest()
 targets.append({'module':module,'receipt':name,'source':r['source'],'source_sha256':r['source_sha256'],'current_source_matches':current==r['source_sha256'],'exit':r['exit'],'wall_s':r['wall_s'],'peak_rss_bytes':r['peak_rss_bytes'],'process_swaps':r.get('process_swaps', next((int(m.group(1)) for m in [re.search(r'(\d+)\s+swaps',(here/name).parent.joinpath('time.log').read_text())] if m), None)),'axiom_reports':sum(x['receipt']==name for x in audit)})
manifest.update(status='focused_proofs_verified_R22_open',targets=targets,
 scope='Focused stage-1 arithmetic proofs; not a complete deployed verifier overflow-freedom certificate',
 historical_memory_blocker_resolved=True)
manifest.pop('uncompiled_drafts',None);manifest.pop('new_proved_theorems',None)
lean=here.parent.parent/'lean'
new=['R22FastPairingRawRanges','R22ControlBounds','R22DecodeValueTotal','R22DecodeLoopTotal','R22BatchedPushTotal','R22BatchedValueTotal','R22OverflowAudit']
index=[]
for n in new:
 p=lean/(n+'.lean');src=p.read_text();namespace=re.search(r'^namespace (\S+)',src,re.M)
 if namespace is None:continue
 ns=namespace.group(1)
 receipt=latest.get(n)
 for m in re.finditer(r'^(private )?theorem (\w+)',src,re.M):
  index.append({'name':ns+'.'+m.group(2),'file':str(p.relative_to(repo)),'line':src.count('\n',0,m.start())+1,'private':bool(m.group(1)),
   'status':'freshly_compiled' if receipt and receipt[1]['exit']==0 and hashlib.sha256(p.read_bytes()).hexdigest()==receipt[1]['source_sha256'] else 'not_verified',
   'receipt':receipt[0] if receipt else None})
old=json.loads((here/'theorem-index.json').read_text())
old=[x for x in old if not x['name'].startswith('AspisR1.R22FastPairingRawRanges.')]
for x in old:
 n=Path(x['file']).stem
 if n in latest and latest[n][1]['exit']==0:x.update(status='freshly_compiled',receipt=latest[n][0])
(here/'theorem-index.json').write_text(json.dumps(old+index,indent=2)+'\n')
files=list(here.rglob('*'))+[lean/(n+'.lean') for n in new]+[here.parent.parent/'design/OVERFLOW-FREEDOM-INVENTORY-20261019.md']
manifest['files']=[{'path':str(p.relative_to(repo)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size_bytes':p.stat().st_size} for p in sorted(files) if p.is_file() and p.name!='manifest.json' and '__pycache__' not in str(p)]
manifest['axioms_audit']='axioms-audit.json'
(here/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
accepted=[x for x in audit if x['compile_exit']==0]
assert all(x['allowed'] for x in accepted)
assert all(x['current_source_matches'] for x in targets)
print(json.dumps({'successful_targets':len(targets),'accepted_axiom_reports':len(accepted),'peak_rss_bytes':max(t['peak_rss_bytes'] for t in targets),'new_theorems_verified':sum(x['status']=='freshly_compiled' for x in index)}))
