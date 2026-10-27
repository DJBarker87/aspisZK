#!/usr/bin/env python3
import pathlib,json,subprocess,os
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
order=json.loads((e/'resume7-gap-order.json').read_text())
for m in order:
 prior=[json.loads(x) for x in (e/'resume7-attempts.jsonl').read_text().splitlines()] if (e/'resume7-attempts.jsonl').exists() else []
 if any(r['module']==m.replace('.','/') for r in prior):continue
 log=e/('resume7-gap-'+m+'.log')
 with log.open('w') as f:r=subprocess.run(['python3',str(root/'tools/pv-srcid3/resume7-run-one.py'),m],stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ,PV_SRCID7_CLOSURE='1'))
 print(m,r.returncode,flush=True)
 if r.returncode not in [0,67]:break
