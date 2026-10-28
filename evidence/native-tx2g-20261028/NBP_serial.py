from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);modules=sys.argv[2:]
for n,m in enumerate(modules,start):
 a=f'NBP_L{n:03}'
 r=subprocess.run([sys.executable,str(E/'NBP_build.py'),a,'lean/'+m+'.lean',m],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if r.returncode or not p.exists():print('STOP driver',a,r.stdout[-1500:],r.stderr[-1500:],flush=True);break
 d=json.loads(p.read_text());print(a,d['exit_status'],d['wall_seconds'],d['peak_rss_kib'],flush=True)
 if d['exit_status']:print((E/a/'stdout.log').read_text()[-5000:],flush=True);break
