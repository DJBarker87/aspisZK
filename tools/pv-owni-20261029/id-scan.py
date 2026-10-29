"""Read-only receipt-name and shared sent-file scan; no compiler invocation."""
from pathlib import Path
import os,re,json,time,resource,sys
start=time.monotonic();base=Path('/home/dombarker/project-offloads');own=base/'codex-pv-owni-20261029';hits=[];directories=0
for root in base.glob('codex-pv-*'):
 if root==own:continue
 for parent,dirs,files in os.walk(root):
  directories+=1
  dirs[:]=[d for d in dirs if d not in ['src','.git','node_modules'] and not d.startswith(('target','objects','lean-objects','lean-sources'))]
  for name in [*dirs,*files]:
   if re.search(r'(?:lean-|out-|receipt-|time-|^)(642\d\d)(?:\D|$)',name):hits.append(str(Path(parent)/name))
for rel in ['r1-privacy-build-integration-20261019/evidence/sent.txt','aspis-joint-20261019/evidence/sent.txt']:
 p=base/rel
 if p.exists():
  for line in p.read_text(errors='replace').splitlines():
   if re.search(r'\b642\d\d\b',line):hits.append(dict(path=str(p),line=line))
u=resource.getrusage(resource.RUSAGE_SELF)
r=dict(range=[64200,64299],other_job_hits=hits,directories_scanned=directories,source_revision=sys.argv[1],target='read-only id-scan.py, other Stream B receipt trees and shared sent files',exit=0 if not hits else 1,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swap=u.ru_nswap,print_axioms='N/A read-only scan',scope='supplemental final scan; initial scan covered direct receipt directories and shared sent files')
print(json.dumps(r,indent=2));raise SystemExit(r['exit'])
