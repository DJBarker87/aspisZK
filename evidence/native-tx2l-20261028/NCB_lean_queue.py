from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,module in json.loads(Path(sys.argv[1]).read_text()):
 r=subprocess.run([sys.executable,str(E/'NCB_build.py'),a,'lean/'+module+'.lean',module],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit(r.stdout+r.stderr)
 x=json.loads(p.read_text());print(json.dumps({k:x[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}),flush=True)
 if x['exit_status'] or r.returncode:raise SystemExit(r.stdout+r.stderr)
