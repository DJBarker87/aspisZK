#!/usr/bin/env python3
import pathlib,json,subprocess,os
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
d=json.loads((e/'resume6-final-merge-gate.json').read_text());rows={r['module']:r for r in d['objects']};todo=set(json.loads((e/'resume7-sampler-cone.json').read_text()))-set(d['projection_cone'])-{'AspisV8R19.SamplerWordRead'};order=[]
def visit(m):
 if m in order:return
 for dep in rows[m]['imports']:
  if dep in todo:visit(dep)
 order.append(m)
for m in sorted(todo):visit(m)
(e/'resume7-stage1-dependents.json').write_text(json.dumps(order,indent=2)+'\n')
for m in order:
 with (e/('resume7-dependent-'+m+'.log')).open('w') as f:r=subprocess.run(['python3',str(root/'tools/pv-srcid3/resume7-run-one.py'),m],stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ,PV_SRCID7_CLOSURE='1'))
 print(m,r.returncode,flush=True)
 if r.returncode not in [0,67]:break
