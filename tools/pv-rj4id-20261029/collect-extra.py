from pathlib import Path
import json,subprocess,shlex
E=Path('evidence/pv-rj4id-20261029')
code=r'''import pathlib,json,sys
known=set(json.load(sys.stdin));p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin32-lean');plan=json.load(open(p/'build-plan.json'));mods={};records={}
for m,v in plan['modules'].items():
 if m not in known:mods[m]=v
for f in (p/'evidence').glob('results-*.json'):
 for v in json.load(open(f)):
  if v.get('module') in mods and v.get('accepted'):records[v['module']]=v
print(json.dumps(dict(modules=mods,records=records)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(list(json.loads((E/'inherited-plan.json').read_text())['modules'])),text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'extra-records.json').write_text(r.stdout);x=json.loads(r.stdout);print(len(x['modules']),len(x['records']))
