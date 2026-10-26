#!/usr/bin/env python3
"""Rebuild a dependency-ordered task slice, one authorized scope at a time."""
import json,pathlib,re,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026';base=root/'docs/research/v8-r0-zk-20261009/lean'
missing=set(json.loads((e/'restored-object-inventory.json').read_text())['missing'])
a=[json.loads(x) for x in (e/'attempts.jsonl').read_text().splitlines()]
for r in a:
 if r['attempt']>=27400 and r['exit']==0 and not r.get('nonstandard_axioms'):
  missing.discard(r['module'].replace('/','.'))
order=[];seen=set()
def visit(m):
 if m in seen or m not in missing:return
 seen.add(m);p=base/(m.replace('.','/')+'.lean')
 if not p.exists():p=e/'pending-proof-sources'/(m.split('.')[-1]+'.lean.txt')
 assert p.is_file(),m
 for d in re.findall(r'^import (\S+)',p.read_text(),re.M):visit(d)
 order.append(m)
visit(sys.argv[1]);(e/'focused-rebuild-plan.json').write_text(json.dumps(order,indent=2)+'\n')
number=int(sys.argv[2]);limit=int(sys.argv[3])
for m in order[:limit]:
 charged=len((e/'attempts.jsonl').read_text().splitlines())+4
 assert charged<130,'Lean budget exhausted'
 print(f'START {number} {m}',flush=True)
 p=subprocess.run([sys.executable,str(root/'tools/pv-srcid3/compile.py'),str(number),m.split('.')[-1]],cwd=root,capture_output=True,text=True)
 (e/f'client-{number}.log').write_text(p.stdout+p.stderr)
 print(f'END {number} client_exit={p.returncode}',flush=True)
 if p.returncode:
  print((p.stdout+p.stderr)[-2500:],flush=True);sys.exit(p.returncode)
 number+=1
print('NEXT_ID '+str(number),flush=True)
