from pathlib import Path
import hashlib,json,subprocess
B=Path(__file__).resolve().parent
paths=['/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.kani/kani-0.67.0/toolchain/bin/rustc','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'S2W_run_host.py')]
rows=[]
for name in paths:
 p=Path(name);assert p.is_file(),name
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1048576):h.update(b)
 rows.append(dict(path=name,resolved=str(p.resolve()),sha256=h.hexdigest(),bytes=p.stat().st_size))
versions=[]
for p,args in [(paths[0],['--version']),(paths[1],['--version','--verbose']),(paths[2],['--version'])]:
 r=subprocess.run([p,*args],capture_output=True,text=True);assert r.returncode==0,(p,r.stderr);versions.append(dict(path=p,command=[p,*args],exit=r.returncode,stdout=r.stdout,stderr=r.stderr))
x=dict(pins=rows,versions=versions,interpretation='Read-only end-of-stage pin of retained tool/infra binaries; native and extraction source/graph/lock receipts remain per-run evidence')
(B/'NGL_TOOL_PINS.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({'pins':len(rows),'versions':len(versions)}))
