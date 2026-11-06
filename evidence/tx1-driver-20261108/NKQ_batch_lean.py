from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;results=[]
for r in json.loads((E/sys.argv[1]).read_text()):
 subprocess.run([sys.executable,str(E/'NKQ_config.py'),r['attempt'],r['module']],check=True)
 p=subprocess.run([sys.executable,str(E/'NKQ_run.py'),r['attempt']])
 results.append(dict(r,exit=p.returncode))
 if not (E/r['attempt']/'receipt.json').exists():raise SystemExit('STOP infrastructure or unresolved receipt')
(E/(Path(sys.argv[1]).stem+'_RESULTS.json')).write_text(json.dumps(results,indent=2))
