from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for n,m in json.loads(Path(sys.argv[1]).read_text()):
 a=f'NCJ_L{n:03}'
 r=subprocess.run([sys.executable,str(E/'NCJ_build.py'),a,'lean/'+m+'.lean',m],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 print(r.stdout[-2400:],flush=True)
 p=E/a/'receipt.json'
 if not p.exists() or r.returncode:raise SystemExit('own runner failure '+r.stderr)
 if json.loads(p.read_text())['exit_status']:raise SystemExit('repair smallest module before dependent targets')
