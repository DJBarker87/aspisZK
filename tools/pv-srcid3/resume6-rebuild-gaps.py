#!/usr/bin/env python3
"""Rebuild missing hash-bearing provenance evidence once, dependency first.

AGENTS.md cadence permits a replay to recover a missing evidence artifact.
The launcher's unchanged-input refusal is respected; no nonce/fake dependency
fingerprint is used to bypass it. Failed sources are never retried here.
"""
import pathlib,json,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
d=json.loads((e/'resume6-project-provenance.json').read_text());rows={r['module']:r for r in d['project_modules']}
missing={r['module'] for r in d['project_modules'] if r['provenance_gap'] and r['module']!='R1NaturalProjection'}
order=[]
def visit(m):
 if m in order:return
 for dep in rows[m]['imports']:
  if dep in missing:visit(dep)
 order.append(m)
for m in sorted(missing):visit(m)
(e/'resume6-gap-rebuild-order.json').write_text(json.dumps(order,indent=2)+'\n')
for m in order:
 prior=[json.loads(x) for x in (e/'resume6-attempts.jsonl').read_text().splitlines()]
 if len(prior)>=int(sys.argv[1]):break
 if any(r['module']==m.replace('.','/') for r in prior):continue
 done=e/'resume6-gap-launch-results.jsonl'
 launched=[json.loads(x) for x in done.read_text().splitlines()] if done.exists() else []
 if any(r['module']==m for r in launched):continue
 r=subprocess.run([sys.executable,str(root/'tools/pv-srcid3/resume6-run-one.py'),m])
 with done.open('a') as f:f.write(json.dumps(dict(module=m,exit=r.returncode,reason='recover missing compiled source/object hash receipt artifact'))+'\n')
 if r.returncode==78:sys.exit(78)
 # Refusal 67 is not bypassed; a source failure is retained and skipped.
