#!/usr/bin/env python3
"""Rebuild remaining changed-sampler consumers, respecting the final audit reserve."""
import pathlib,json,subprocess,os
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
d=json.loads((e/'resume6-final-merge-gate.json').read_text());rows={r['module']:r for r in d['objects']}
cone=set(json.loads((e/'resume7-sampler-cone.json').read_text()));forbidden={'R1NaturalProjection','R1Z.EventsR1P2','R1Z.SimCostOuterRetry6','EventsR1P2','SimCostOuterRetry6'}
# Axioms audit roots are reserved; source proofs already compiled are not repeated.
todo={m for m in cone if m not in forbidden and 'FinalAudit' not in m and m in rows and rows[m]['source_kind']!='external package/toolchain'}
order=[]
def visit(m):
 if m in order:return
 for dep in rows[m]['imports']:
  if dep in todo:visit(dep)
 order.append(m)
for m in sorted(todo):visit(m)
(e/'resume7-changed-sampler-order.json').write_text(json.dumps(order,indent=2)+'\n')
for m in order:
 prior=[json.loads(x) for x in (e/'resume7-attempts.jsonl').read_text().splitlines()]
 if len(prior)>=97:break
 if any(r['module']==m.replace('.','/') for r in prior):continue
 with (e/('resume7-cohort-'+m+'.log')).open('w') as f:r=subprocess.run(['python3',str(root/'tools/pv-srcid3/resume7-run-one.py'),m],stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ,PV_SRCID7_CLOSURE='1'))
 print(m,r.returncode,flush=True)
 if r.returncode not in [0,67]:break
