from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=json.loads(Path(sys.argv[1]).read_text())
for a,crate,harness,patch in jobs:
 if (E/a/'receipt.json').exists():raise SystemExit('Refuse existing attempt '+a)
 r=subprocess.run([sys.executable,str(E/'NCB_kani.py'),a,crate,harness,str(E/patch)],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():print(r.stdout+r.stderr,flush=True);raise SystemExit('No receipt; infrastructure/input review required')
 x=json.loads(p.read_text());print(json.dumps({k:x[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
 print('\n'.join((E/a/'stdout.log').read_text().splitlines()[-12:]),flush=True)
 if 'timed out' in (E/a/'stdout.log').read_text().lower():
  z=subprocess.run([sys.executable,str(E/'NCB_cleanup_solver.py'),a],capture_output=True,text=True)
  if z.returncode:raise SystemExit(z.stdout+z.stderr)
  raise SystemExit('Timed-out shape retained; split before another launch')
 if 'could not compile' in (E/a/'stdout.log').read_text():raise SystemExit('Own harness codegen failure; repair before further launch')
 if r.returncode:raise SystemExit(r.stdout+r.stderr)
