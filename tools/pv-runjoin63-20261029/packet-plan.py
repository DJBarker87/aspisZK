from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin63-20261029'
plan=json.loads((E/'build-plan.json').read_text());fixture=json.loads((E/'fixture-pins.json').read_text());external={v['module'].replace('/','.') for v in json.loads((E/'external-authority.json').read_text())};rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();order=[];seen=set()
files=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines()
def visit(m):
 if m in seen or m in plan['modules'] or m in external:return
 seen.add(m)
 candidates=[p for p in files if p.endswith('/'+m.replace('.','/')+'.lean')]
 assert len(candidates)==1,(m,candidates)
 path=candidates[0];b=(R/path).read_bytes();imports=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 for d in imports:visit(d)
 pin=dict(authority='h5 unique git-tracked source, no EJR entry for PV_B3P modules',path=path,revision=rev,sha256=hashlib.sha256(b).hexdigest(),git_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),imports=imports,tracked_conflicts=[])
 plan['modules'][m]=pin;fixture['modules'][m]=pin;order.append(m)
visit('PV_B3P_Install132')
(E/'packet-order.json').write_text(json.dumps(order,indent=2)+'\n');(E/'build-plan.json').write_text(json.dumps(plan,indent=2)+'\n');(E/'fixture-pins.json').write_text(json.dumps(fixture,indent=2)+'\n');print(len(order),order)
