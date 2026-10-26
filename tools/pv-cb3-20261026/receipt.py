"""Collect evidence from the existing launcher; never launches or changes it."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
attempt,module=sys.argv[1:3]
root=Path(__file__).resolve().parents[2]
output=root/'evidence/pv-cb3-20261026'
base='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
for stem,ext in [('out','log'),('time','log'),('sha','txt')]:
 p=f'{stem}-{attempt}.{ext}'
 data=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat',f'{base}/{p}'],text=True)
 (output/p).write_text(data)
out=(output/f'out-{attempt}.log').read_text();time=(output/f'time-{attempt}.log').read_text()
def field(pattern):
 m=re.search(pattern,time);return m.group(1) if m else None
source=root/'docs/research/v8-r0-zk-20261009/lean'/f'{module}.lean'
# Direct import object identities are captured separately, with the collection time explicit.
imports=re.findall(r'^import (\S+)',source.read_text(),re.M)
identities={}
for imp in imports:
 remote=f'/home/dombarker/project-offloads/aspis-joint-20261019/objects/{imp.replace(".","/")}.olean'
 if imp == 'Aeneas':
  remote='/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend/.lake/build/lib/lean/Aeneas.olean'
 identities[imp]=subprocess.check_output(['ssh','dombarker@100.108.41.90','sha256sum',remote],text=True).split()[0]
r=dict(attempt=int(attempt),module=module,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_sha256=(output/f'sha-{attempt}.txt').read_text().split()[0],deps_fingerprint=hashlib.sha256(json.dumps(identities,sort_keys=True).encode()).hexdigest(),dependency_object_hashes=identities,dependency_collection='post-run read-only snapshot; no dependencies changed by this worker',exit=int(re.search(r'^exit=(\d+)',out,re.M)[1]),wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=int(field(r'Maximum resident set size \(kbytes\): (\d+)')),swap=int(field(r'Swaps: (\d+)')),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.S),limits=dict(lean_M=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=128),launcher='r1-privacy-build-integration-20261019/tools/run-joint.sh')
(output/f'{attempt}.json').write_text(json.dumps(r,indent=2)+'\n')
print(attempt,r['exit'],r['wall'])
