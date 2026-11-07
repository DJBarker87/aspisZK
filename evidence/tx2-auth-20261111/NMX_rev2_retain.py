from NMX_formal import *
import re
accepted=json.loads((E/'NMX_REV2_ACCEPTED.json').read_text());mods=set(accepted)|{'NMX_R2_COMBINED_IMPORT'}
rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
queue=list(mods)
while queue:
 m=queue.pop();p=E/(m+'.lean');assert p.is_file(),m
 for d in re.findall(r'^import (NMX_\w+)',p.read_text(),re.M):
  if d not in mods:
   q=E/(d+'.lean');h=sha(q.read_bytes())
   assert any(r.get('module')==d and r.get('exit_status')==0 and h in r.get('source_hashes',{}).values() for r in rows),d
   mods.add(d);queue.append(d)
(E/'NMX_REV2_EXPORT_MODULES.json').write_text(json.dumps(sorted(mods),indent=1)+'\n')
env=json.loads((E/'NMX_REV2_ENV.json').read_text())
n=903
while (E/('NMX_L'+str(n)+'.json')).exists():n+=1
r=run('NMX_L'+str(n),'inspect','retention_rev2',['python3','NMX_rev2_retain_host.py'],{f:(E/f).read_text() for f in ['NMX_rev2_retain_host.py','NMX_REV2_EXPORT_MODULES.json','NMX_REV2_CANONICAL.json']},env_extra=env)
assert r['exit_status']==0,'STOP retention failed; recover and isolate before retry'
