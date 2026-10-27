"""Collect text-only recovery evidence, never compiled artifacts."""
import subprocess,tarfile,io,json,collections,shlex
from pathlib import Path
O=Path(__file__).parent
remote="""from pathlib import Path
import fnmatch,os
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
patterns=['EJR_*.json','EJR-*.json','EJR-*.log','EJR_attempts.jsonl','EJR_reuses.jsonl','out-3*.log','time-3*.log','sha-3*.txt']
names=sorted(p.name for p in T.iterdir() if p.is_file() and any(fnmatch.fnmatch(p.name,x) for x in patterns))
os.execvp('tar',['tar','-cf','-','-C',str(T),'--']+names)
"""
cmd='python3 -c '+shlex.quote(remote)
p=subprocess.Popen(['ssh','dombarker@100.108.41.90',cmd],stdout=subprocess.PIPE)
with tarfile.open(fileobj=p.stdout,mode='r|') as t:
 for m in t:
  if not m.isfile():continue
  name=Path(m.name).name
  if name in ['EJR_restored-sources.json']:continue
  (O/'receipts').mkdir(exist_ok=True);(O/'receipts'/name).write_bytes(t.extractfile(m).read())
assert p.wait()==0
rs=[json.loads(l) for l in (O/'receipts/EJR_attempts.jsonl').read_text().splitlines()]
latest={r['key']:r for r in rs}
reuses=[json.loads(l) for l in (O/'receipts/EJR_reuses.jsonl').read_text().splitlines()] if (O/'receipts/EJR_reuses.jsonl').exists() else []
for r in reuses:latest.pop(r['key'],None)
summary=dict(reused_objects=len(reuses),latest_failed_keys=[dict(key=r['key'],attempt=r['attempt'],lean_exit=int(__import__('re').search(r'Exit status:\s*(\d+)',r['time_log'])[1]),validation_exit=r['exit'],errors=r['errors']) for r in latest.values() if r['exit']],attempts=len(rs),successful=sum(r['exit']==0 for r in rs),failures=[dict(attempt=r['attempt'],module=r['module'],exit=r['exit'],errors=r['errors']) for r in rs if r['exit']],peak_rss_kib=max((r['peak_rss_kib'] or 0 for r in rs),default=0),swaps=sum((r['swaps'] or 0 for r in rs)),axiom_lines=sum(len(r['axioms']) for r in rs),last_attempt=rs[-1]['attempt'] if rs else None)
(O/'EJR_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k not in ['failures','latest_failed_keys']}))
