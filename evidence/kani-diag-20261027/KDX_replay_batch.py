from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for x in json.loads((E/'KDX_REPLAY_PLAN.json').read_text()):
 if (E/x['attempt']/'receipt.json').exists():continue
 print(x['attempt'],x['original'],flush=True)
 r=subprocess.run([sys.executable,str(E/'KDX_run.py'),x['attempt'],x['harness'],'--verbose'])
 if r.returncode:raise SystemExit(r.returncode)
 if 'Checking harness' not in (E/x['attempt']/'stdout.log').read_text():raise SystemExit('STOP replay compile failure')
 # A failed verification is a result; infrastructure wrapper returns 0 after recovery.
