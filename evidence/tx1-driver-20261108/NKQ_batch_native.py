from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
for r in json.loads((E/sys.argv[1]).read_text()):
 subprocess.run([sys.executable,str(E/'NKQ_kconfig.py'),r['attempt'],r['harness']],check=True)
 p=subprocess.run([sys.executable,str(E/'NKQ_run.py'),r['attempt']])
 if p.returncode!=r['expected_exit']:raise SystemExit('STOP unexpected verdict '+r['attempt'])
 # Compile/codegen errors are not negative controls; continue only an actual verdict.
 log=(E/r['attempt']/'stdout.log').read_text()
 assert ('VERIFICATION:- FAILED' if r['expected_exit'] else 'VERIFICATION:- SUCCESSFUL') in log,'STOP missing proof verdict'
