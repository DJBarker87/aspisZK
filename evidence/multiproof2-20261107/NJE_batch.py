"""Sequential focused launches; stop at the first unexpected verdict. No resubmission."""
import json,pathlib,subprocess,sys
E=pathlib.Path(__file__).resolve().parent
for name in sys.argv[1:]:
 cfg=json.loads((E/(name+'.json')).read_text())
 expected=1 if cfg.get('expected_failure') else 0
 rc=subprocess.call([sys.executable,str(E/'NJE_run.py'),name])
 if rc!=expected:
  print('STOP '+name+' unexpected client status '+str(rc),flush=True);sys.exit(2)
