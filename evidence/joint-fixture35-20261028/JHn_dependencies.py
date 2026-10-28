from pathlib import Path
import re,json,shlex,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
cfg=json.loads((P/'JHn35_014/receipt.json').read_text()); paths=cfg['env']['LEAN_PATH'].split(':')
targets=['JHh_C_TX1Candidate','JHh_ChildBridge','JHn_ProofEquation','JHn_PublicEquation','JHn_ChecksumEquation']
seen=set();order=[]
def visit(m):
 if m in seen:return
 seen.add(m);f=R/'lean'/(m.replace('.','/')+'.lean')
 if f.exists():
  for n in re.findall(r'^import (\S+)',f.read_text(),re.M):visit(n)
 order.append(m)
for m in targets:visit(m)
code='from pathlib import Path\nimport json\npaths='+repr(paths)+'\nnames='+repr(order)+'\nobjects={}\nfor name in names:\n p=next((Path(root)/(name.replace(".","/")+".olean") for root in paths if (Path(root)/(name.replace(".","/")+".olean")).is_file()),None)\n objects[name]=str(p) if p else None\nprint(json.dumps(objects))'
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
if r.returncode:
 print(r.stderr[:2000]);raise SystemExit(r.returncode)
obj=json.loads(r.stdout);(P/'JHn_DEPENDENCIES.json').write_text(json.dumps(dict(targets=targets,order=order,objects=obj),indent=2)+'\n')
print('\n'.join(m for m in order if not obj[m]))
