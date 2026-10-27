"""Restore only the missing focused mask-reference dependency artifacts."""
from pathlib import Path
import json,subprocess,sys
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
manifest=json.loads((ev/'RESUME4-MASK-DEPENDENCY-PREFLIGHT.json').read_text())
next_id=int(sys.argv[1]);limit=int(sys.argv[2]) if len(sys.argv)>2 else 27
accepted=set()
for receipt in ev.glob('38*.json'):
 try:r=json.loads(receipt.read_text())
 except ValueError:continue
 if r.get('exit')==0 and 'module' in r:accepted.add(r['module'].replace('/','.'))
missing=[m for m in manifest['ordered_modules'] if not manifest['object_locations'][m] and m not in accepted]
for m in missing[:limit]:
 assert next_id<=38599
 p=ev/f'{next_id}.json'
 if p.exists() or (ev/f'{next_id}-submission.json').exists():raise SystemExit('ID already consumed')
 transcript=ev/f'{next_id}-restore-transport.log'
 with transcript.open('w') as f:
  r=subprocess.run([sys.executable,str(root/'tools/pv-cb-20261026/resume4_lean.py'),str(next_id),m.replace('.','/')],stdout=f,stderr=subprocess.STDOUT)
 if not p.exists():raise SystemExit(f'{next_id} preflight/refusal; inspect {transcript}; do not reuse ID')
 receipt=json.loads(p.read_text())
 print(next_id,m,'exit',receipt['exit'],flush=True)
 if receipt['exit']:raise SystemExit('Stop focused dependency queue and repair the changed failing target; no unchanged retry')
 next_id+=1
print('next unused ID',next_id)
