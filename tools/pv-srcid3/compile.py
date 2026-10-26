#!/usr/bin/env python3
"""One focused compile via the existing launcher, with task receipts."""
import hashlib,json,pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[2]
a=int(sys.argv[1]); m=sys.argv[2]
assert 25300 <= a <= 25599 and m.startswith('PV_Src_')
host='dombarker@100.108.41.90'
job='/home/dombarker/project-offloads/codex-pv-srcid-20261026'
joint='/home/dombarker/project-offloads/aspis-joint-20261019'
t='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
e=root/'evidence/pv-srcid3-20261026';e.mkdir(exist_ok=True)
src=root/f'docs/research/v8-r0-zk-20261009/lean/R1Z/{m}.lean'
(e/'sources').mkdir(exist_ok=True)
(e/f'sources/{a}.lean.txt').write_bytes(src.read_bytes())
def ssh(s): return subprocess.run(['ssh',host,s],capture_output=True,text=True)
g=ssh(f'mkdir -p {job}; python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {job}/reservation-{a}.json > {job}/reservation-{a}.log 2>&1; cat {job}/reservation-{a}.log; test -f {job}/reservation-{a}.json && python3 -c \'import json; raise SystemExit(0 if json.load(open("{job}/reservation-{a}.json"))["allowed"] else 78)\'')
(e/f'reservation-{a}.log').write_text(g.stdout+g.stderr)
subprocess.run(['scp','-q',f'{host}:{job}/reservation-{a}.json',str(e/f'reservation-{a}.json')],check=False)
if g.returncode: print(g.stdout,g.stderr);sys.exit(g.returncode)
subprocess.run(['scp','-q',str(src),f'{host}:{joint}/sources/R1Z/{m}.lean'],check=True)
imports=re.findall(r'^import (\S+)',src.read_text(),re.M)
# Fingerprint exact imported objects; retain the individual hashes too.
paths=' '.join(f'{joint}/objects/{i.replace(".","/")}.olean' for i in imports)
d=ssh(f'sha256sum {paths}')
if d.returncode: print(d.stdout,d.stderr);sys.exit(d.returncode)
fp=hashlib.sha256(d.stdout.encode()).hexdigest()[:16]
r=ssh(f'sh /home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh {a} R1Z/{m} J 7000 8 {fp}')
(e/f'launcher-{a}.log').write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr,flush=True)
for name in [f'out-{a}.log',f'time-{a}.log',f'sha-{a}.txt']:
 subprocess.run(['scp','-q',f'{host}:{t}/{name}',str(e/name)],check=False)
out=(e/f'out-{a}.log').read_text() if (e/f'out-{a}.log').exists() else r.stdout
time=(e/f'time-{a}.log').read_text() if (e/f'time-{a}.log').exists() else ''
def metric(pattern):
 x=re.search(pattern,time);return x.group(1) if x else None
ex=re.search(r'exit=(\d+)',out)
record=dict(attempt=a,module='R1Z/'+m,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),deps_fingerprint=fp,dependency_objects=d.stdout.splitlines(),exit=int(ex.group(1)) if ex else r.returncode,wall=metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)'),swaps=metric(r'Swaps: (\d+)'),axioms=[' '.join(s.split()) for s in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",out,re.M|re.S)],errors=[s for s in out.splitlines() if 'error' in s],caps=dict(lean_M=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=128))
with (e/'attempts.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
sys.exit(record['exit'])
