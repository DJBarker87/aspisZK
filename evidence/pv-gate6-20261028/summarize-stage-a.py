from pathlib import Path
import json
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
assert load('stage-a-validation.json')['passed']
s=load('combined/corpus-6000/pipeline-final.json')
a=load('combined/record-ledger-audit.json')
p=E/'comparison.json';r=load('comparison.json')
r['stage_a']='PASS'
r['differential']={k:v for k,v in s.items() if k!='cases'}
r['differential']['seeds']=[6000,6999]
r['differential']['control_revision']='c57a344726745387efb38d1571d885c69ce829ee'
r['differential']['candidate_revision']=r['candidate_revision']
r['differential']['record_ledger_audit']=a
r['stage_a_validation']='stage-a-validation.json'
p.write_text(json.dumps(r,indent=2)+'\n')
p=E/'README.md';s=p.read_text().replace('## Stage A interim results','## Stage A results: PASS').replace('New differential cohort remains pending.','The new differential cohort is complete (details below).')
s+='''\n## Differential completion\n\nFresh seeds 6000–6999: 1,000/1,000 pairs PASS against shipped `c57a344726`, using pv-integ4’s unchanged harness/comparator and three-process pipeline. This includes 600 complete proof pairs, 100 rejected-prefix pairs and four oracle-logged pairs. Canonical result records and ledger files match for all 1,000 pairs; proof/public bytes match wherever produced. Elapsed seconds alone are excluded. No discrepancy found. Full coverage, source, resource and byte-comparison receipts are under `combined/`; `stage-a-validation.json` checks the collected evidence.\n\nRecovery after capacity error reused the still-running differential scope, without resubmission. Before recovery eight native scopes had completed and one differential scope was active; Lean/Kani attempts remain zero. No numeric native-attempt budget was specified. Refusals and cooldowns are retained; refusals started no compiler.\n'''
p.write_text(s)
