"""Serial independent modules: a failed member never holds unrelated work."""
from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent;num=int(sys.argv[1])
for target in sys.argv[2:]:
 a=f'NEC_L{num:03d}';num+=1
 r=subprocess.run([sys.executable,str(E/'NEC_run.py'),a,'lean',target],capture_output=True,text=True)
 if r.returncode:print(r.stdout[-1600:]+r.stderr[-1600:],flush=True);raise SystemExit(r.returncode)
 p=E/a/'receipt.json';rc=json.loads(p.read_bytes() if p.exists() else lzma.decompress(p.with_name(p.name+'.xz').read_bytes()))
 print(json.dumps({k:rc[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','print_axioms']}),flush=True)
 if rc['exit_status']:print(r.stdout[-2800:],flush=True)
print('next attempt',num,flush=True)
