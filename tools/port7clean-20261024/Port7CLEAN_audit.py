#!/usr/bin/env python3
"""Check final focused receipts, resource policy, hashes and protected scope."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/port7clean-20261024'; L=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[(p,json.loads(p.read_text())) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(receipts)<=100
allowed={'propext','Classical.choice','Quot.sound'}
final={}; statements=[]
for source in sorted(L.glob('Port7CLEAN_*.lean')):
 matches=[(p,r) for p,r in receipts if r['exit_status']==0 and r['source_hashes'].get(source.name)==sha(source)]
 assert matches,source
 p,r=matches[-1]; final[source.name]={'receipt':str(p.relative_to(R)),'source_sha256':sha(source)}
 for name in re.findall(r'^theorem (\w+)',source.read_text(),re.M):
  statements.append('AspisR1.'+source.stem+'.'+name)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',source.read_text()),source
 for line in r['print_axioms']:
  axioms=set(re.search(r'\[(.*?)\]',line,re.S).group(1).replace('\n','').split(', ')) if '[' in line else set()
  assert axioms<=allowed,(source,line)
for p,r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 admission=json.loads((E/(r['attempt']+'-reservation.json')).read_text())
 assert admission['reserved_bytes']+admission['additional_bytes']<=admission['limit_bytes']==55*1024**3
 assert r['command'][1:4]==['env','lean','-j1']
 for name,h in r['source_hashes'].items():assert sha(p.parent/'sources'/name)==h
final_audit=json.loads((E/'lean-027/receipt.json').read_text());assert final_audit['exit_status']==0
assert set(statements)=={re.match(r"'([^']+)'",x).group(1) for x in final_audit['print_axioms']}
changes=subprocess.check_output(['git','diff','--name-only','915db3ef07'],cwd=R,text=True).splitlines()
assert all(x.startswith(('docs/research/100bit-spend-path-20261013/lean/Port7CLEAN_','evidence/port7clean-20261024/','tools/port7clean-20261024/')) for x in changes),changes
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=5_000_000,(p,'large derived file must be hash+size only')
manifest={'schema':'focused-extractor-proof-packet-v1','base_revision':'915db3ef07','lean_budget':100,'kani_budget':20,'lean_attempts':len(receipts),'kani_runs':0,'final_sources':final,'theorems_audited':len(statements),'final_audit':'lean-027','receipts':[{'path':str(p.relative_to(R)),'sha256':sha(p),'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps']} for p,r in receipts],'assessment':'Focused cached development; inherited dependency closure reused, no coherent release replay or new ELF identity gate'}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
# Current dependency source assessment supplements older receipt formats. This
# inventories source hashes; it does not claim cached objects were rebuilt.
source_assessment={}
for p,r in receipts:
 rows={}
 for key,obj in r['deps_fingerprint']['selected_objects'].items():
  if not key.endswith('.olean'):continue
  local=L/key.replace('.olean','.lean')
  if local.is_file():rows[key]={'current_source_sha256':sha(local),'object_sha256':obj['sha256'],'object_bytes':obj['bytes']}
 source_assessment[r['attempt']]=rows
(E/'dependency-source-assessment.json').write_text(json.dumps({'assessment':'Current local source hashes mapped to recorded direct object pins. Historical failed own-module source versions are preserved in receipts. Inherited transitive cache is assessed via the inherited receipt; this inventory does not establish coherent source/object replay.','attempts':source_assessment},indent=2)+'\n')
print(json.dumps({'lean_attempts':len(receipts),'kani_runs':0,'final_sources':len(final),'axioms_audited':len(statements),'audit_exit':0}))
