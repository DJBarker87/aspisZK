"""Final two serial scopes; only after every required raw group is retained."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
plan=json.loads((E/'NLX_AUDIT_GROUPS.json').read_text())
for row in plan['required']:
 assert(E/'NLX_audit'/row['mode']/('proof'+str(row['group'])+'.json')).exists()
for i,target in [(39,'review-close'),(40,'retention')]:
 a=f'NLX_L{i:03}';assert not(E/a).exists(),'Never resubmit '+a
 r=subprocess.run([sys.executable,str(E/'NLX_run.py'),a,'audit',target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 if r.returncode:print(a+' STOP inspect retained verdict',flush=True);sys.exit(r.returncode)
 print(a+' '+target+' PASS',flush=True)
