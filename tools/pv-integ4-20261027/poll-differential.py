"""Read-only progress report. Never submits or resumes a corpus."""
import subprocess,json
D='/home/dombarker/project-offloads/codex-pv-integ4-20261027/combined'
code=f'''from pathlib import Path
import json
D=Path({D!r});O=D/'corpus-6000'
p=O/'pipeline-progress.json'
r=json.loads(p.read_text()) if p.exists() else {{}}
keys=['completed_pairs','fully_executed_proof_pairs','rejected_prefix_pairs','oracle_logged_pairs','passed','complete','elapsed_pipeline_seconds']
s={{k:r[k] for k in keys if k in r}}
s['failure']=(O/'pipeline-failure.json').exists()
p=D/'combined-differential-001/receipt/receipt.json'
if p.exists():s['receipt']=json.loads(p.read_text())
print(json.dumps(s))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);print(r.stdout or r.stderr,end='');raise SystemExit(r.returncode)
