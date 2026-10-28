from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
version=sys.argv[1]
for index in map(int,sys.argv[2:]):
 r=subprocess.run([sys.executable,str(E/'KNH_run.py'),version,str(index)])
 if r.returncode:raise SystemExit(r.returncode)
 a=f'KNH_{"N" if version=="new" else "O"}{index:03d}'
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 # Queue stops on caps/timeouts to permit shape review; never blindly continues a failing timed shape.
 if rc['exit_status'] in [124,137] or 'Timed out' in log or 'TIMEOUT' in log:
  raise SystemExit('REVIEW timeout before another launch: '+a)
