from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
rows=json.loads(Path(sys.argv[1]).read_text())
for n,h in rows:
 r=subprocess.run([sys.executable,str(E/'NCJ_run.py'),f'NCJ_K{n:03}',h],capture_output=True,text=True)
 (E/f'NCJ_K{n:03}-driver.log').write_text(r.stdout+r.stderr)
 print(r.stdout[-1800:],flush=True)
 p=E/f'NCJ_K{n:03}/receipt.json'
 if r.returncode or not p.exists():raise SystemExit('runner stop '+r.stderr)
 log=(p.parent/'stdout.log').read_text()
 if 'could not compile' in log or 'TIMEOUT' in log or 'VERIFICATION:- TIMEOUT' in log or 'Timed out' in log or 'Failed to execute cargo' in log:raise SystemExit('adaptive queue stop; isolate failed shape')
