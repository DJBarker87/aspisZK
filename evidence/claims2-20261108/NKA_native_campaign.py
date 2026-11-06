from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for entry in json.loads((E/'NKA_KMX_CAMPAIGN.json').read_text()):
 a=entry['attempt'];r=subprocess.run([sys.executable,str(E/'NKA_run.py'),a],text=True,capture_output=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(json.dumps(dict(attempt=a,exit=r.returncode,expected=entry['expected_exit'])),flush=True)
 if r.returncode!=entry['expected_exit']:sys.exit(1)
