from pathlib import Path
import re,json,subprocess,sys
E=Path(__file__).resolve().parent.parent;L=Path('docs/research/v8-r0-zk-20261009/lean')
d={str(p.relative_to(L))[:-5].replace('/','.'):re.findall(r'^import (\S+)',p.read_text(),re.M) for p in L.rglob('*.lean')}
changed={'AspisR1ProducerRelease47.Samples49'}
while True:
 nxt=changed|{k for k,v in d.items() if set(v)&changed}
 if nxt==changed:break
 changed=nxt
exclude={'AspisR1ProducerRelease47.Samples49','AspisR1ProducerRelease47.KernelCallers49','R1Z.ProverCommitHalf49','R1Z.ProverCommitLibra49'}
ordered=[];seen=set(exclude)
def visit(m):
 if m in seen:return
 seen.add(m)
 for c in d[m]:
  if c in changed:visit(c)
 ordered.append(m)
for m in sorted(changed-exclude):visit(m)
start=int(sys.argv[1]);schedule=[dict(module=m,attempt=start+i) for i,m in enumerate(ordered)]
assert schedule[-1]['attempt']<10190
(E/'pins/sample-import-rebuild.json').write_text(json.dumps(dict(reason='Samples49 reuses identical M31.ZERO from Interpolate48, removing duplicate declaration on caller composition. All affected retained dependents are rebuilt.',schedule=schedule),indent=2)+'\n')
for item in schedule:
 print(item,flush=True)
 subprocess.run([sys.executable,str(E/'harness/lean.py'),item['module'],str(item['attempt']),'--wait'],check=True)
