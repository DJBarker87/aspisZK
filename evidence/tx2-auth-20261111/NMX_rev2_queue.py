"""Compile only changed canonical-dependent modules, one admitted scope each."""
from NMX_formal import *
mods=set(json.loads((E/'NMX_REV2_MODULES.json').read_text()))|{'NMX_R2_CloneTransport'}
env=json.loads((E/'NMX_REV2_ENV.json').read_text())
rows=[json.loads(l) for l in (E/'NMX_ATTEMPTS.jsonl').read_text().splitlines()]
n=488
# Successful current-source objects only; failed modules need a reviewed source change.
seen=set()
def go(m):
 global n
 if m in seen:return
 seen.add(m)
 for dep in re.findall(r'^import (NMX_\w+)',(E/(m+'.lean')).read_text(),re.M):
  if dep in mods:go(dep)
 h=sha((E/(m+'.lean')).read_bytes())
 if any(r.get('module')==m and r.get('exit_status')==0 and h in r.get('source_hashes',{}).values() for r in rows):return
 while (E/('NMX_L'+str(n)+'.json')).exists():n+=1
 attempt='NMX_L'+str(n);n+=1
 r=run(attempt,'lean',m,env_extra=env)
 if r['exit_status']:raise RuntimeError('STOP failed required predecessor '+m)
go('NMX_R2_SevenSourceFold')
