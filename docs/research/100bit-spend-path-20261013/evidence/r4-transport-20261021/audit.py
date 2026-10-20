#!/usr/bin/env python3
"""Audit committed focused receipts and unchanged frozen sources; no builds."""
from pathlib import Path
import hashlib,json,re,subprocess,tempfile
here=Path(__file__).resolve().parent
packet=here.parent.parent
repo=packet.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
modules=['R4TransportGammaFold','R4TransportGammaRank','R4TransportWideReference','R4TransportBoundaryFreedom','R4TransportPrefixFrame','R4TransportCircleCoordinates','R4TransportRhoSource']
manifest=json.loads((here/'manifest.json').read_text())
rows=[]
for m in modules:
 src=packet/'lean'/f'{m}.lean';txt=src.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',txt,re.M),m
 green=[r for r in manifest['attempts'] if r['module']==m and r['final_current'] and r['exit']==0 and r['source_sha256']==sha(src)]
 assert len(green)==1,(m,len(green));r=green[0]
 assert (here/f'{m}-{r["attempt"]}'/'source.lean.txt').read_text()==txt
 commands=re.findall(r'^#print axioms (\S+)',txt,re.M)
 assert len(commands)==len(r['axioms']),(m,commands,r['axioms'])
 for line in r['axioms']:
  if 'depends on axioms:' in line:
   vals=set(re.search(r'\[([\s\S]*?)\]',line)[1].replace('\n',' ').replace(' ','').split(','))
   assert vals<={'propext','Classical.choice','Quot.sound'},line
  else:assert 'does not depend on any axioms' in line,line
 rows.append({k:r[k] for k in ['module','attempt','source_revision','source_sha256','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms']})
source=json.loads((here/'source-inventory.json').read_text())
for name,v in source['files'].items():assert sha(repo/name)==v['sha256'],name
unchanged=json.loads((here/'headline-unchanged.json').read_text())
for e in unchanged['endpoints']:
 assert sha(repo/e['path'])==e['sha256']
 assert subprocess.check_output(['git','show',e['base_revision']+':'+e['path']],cwd=repo)==(repo/e['path']).read_bytes()
host=json.loads((here/'host-manifest.json').read_text())
for r in host['attempts']:
 d=here/Path(r['receipt']).parent
 assert sha(d/'stdout.log')==r['stdout_sha256']
 assert sha(d/'stderr.log')==r['stderr_sha256']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
expected={'words-1':1,'finish-1':1,'contains-fixed-1':23,'contains-fixed-2':23}
for name,count in expected.items():
 r=next(a for a in host['attempts'] if a['attempt']==name)
 assert r['exit']==0
 assert any(f'{count} successfully verified harnesses' in s for s in r['verified_harness_summary'])
with tempfile.TemporaryDirectory(prefix='r4-source-audit-') as d:
 subprocess.run(['python3',str(repo/'tools/r4-transport-kit/prepare.py'),d],check=True)
 assert Path(d,'src/lib.rs').read_text()==(here/'scanner-final.rs.txt').read_text()
 assert Path(d,'source-cut.json').read_text()==(here/'scanner-source-cut.json').read_text()
result={'status':'R4_transport open; focused results and explicit obstructions only','focused_theorems':sum(len(r['axioms']) for r in rows),'modules':rows,'source_inventory_checked':True,'headline_unchanged':True,'unique_passing_kani_component_roots':25,'full_scan_proved':False,'full_prefix_transport_proved':False}
(here/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='modules'},indent=2))
