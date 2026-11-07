"""Serial focused compiler for resumed modules; preserves every failed scope."""
from NMT_formal import run,E
import json,sys,hashlib,re
for m in sys.argv[1:]:
 rows=[json.loads(l)for l in (E/'NMT_ATTEMPTS.jsonl').read_text().splitlines()]
 h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()
 same=[r for r in rows if r.get('module')==m and h in r.get('source_hashes',{}).values()]
 if same:
  if same[-1]['exit_status']==0:continue
  print('SKIP unchanged failed source: '+m,flush=True);continue
 deps=re.findall(r'^import (NMT_[\w.]+)',(E/(m+'.lean')).read_text(),re.M)
 blocked=[]
 for dep in deps:
  dh=hashlib.sha256((E/(dep+'.lean')).read_bytes()).hexdigest()
  if not any(r.get('module')==dep and r.get('exit_status')==0 and dh in r.get('source_hashes',{}).values() for r in rows):blocked.append(dep)
 if blocked:
  print('SKIP unproved dependency: '+m+' '+str(blocked),flush=True);continue
 n=max(int(r['attempt'][-3:])for r in rows if r.get('attempt','').startswith('NMT_L') and 'exit_status'in r)+1
 assert 61<=n<=486
 r=run(f'NMT_L{n:03}','lean',m)
 if r['exit_status']:print('FAILED, continue independent targets: '+m,flush=True)
