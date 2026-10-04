import hashlib,json,os,pathlib,subprocess
ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a'); workspace=ROOT/'focus-workspace'; src=ROOT/'source/AspisR569MaskedClaimCompleteConsts/Axioms.lean'; log=ROOT/'R569-Axioms.compile.log'; result=ROOT/'R569-Axioms.result.json'
lib=ROOT/'lib'; aeneas=pathlib.Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean'); packages=pathlib.Path('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages'); pkgs=sorted(p for p in packages.glob('*/.lake/build/lib/lean') if p.is_dir()); core=pathlib.Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'); paths=[str(lib),str(aeneas),*[str(p) for p in pkgs],str(core)]; lp=':'.join(paths)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src)=='acb6dab6b5c1138341090404c4402014c64bf47e201df8376ddfb1bd8643e852'
for n,h in [('Types.olean','b226603b0b4971fbbeb11dd35be900817811ba52768e572029d310af4e71bbae'),('Funs.olean','219cf1d7522d47ffce1b0282d187bb26b9243b3b7150a68b242eea1e92a155de')]: assert sha(lib/'AspisR569MaskedClaimCompleteConsts'/n)==h
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True); reservations=[]
for line in units.splitlines():
 f=line.split()
 if f and f[0].startswith('aspis'):
  v=subprocess.check_output(['systemctl','--user','show',f[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  if v.isdigit():reservations.append((f[0],int(v)))
assert sum(v for _,v in reservations)+7*1024**3<=40*1024**3,reservations
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r569-axioms-20261004','--working-directory='+str(workspace),'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','/usr/bin/time','-v','/usr/bin/env','LEAN_PATH='+lp,'PATH=/home/dombarker/.elan/bin:/usr/bin:/bin','/home/dombarker/.elan/bin/lake','--dir',str(workspace),'env','lean','-j1','-M4500',str(src)]
with log.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
d={'target':str(src),'target_sha256':sha(src),'imports':'AspisR569MaskedClaimCompleteConsts.Funs','Funs_olean_sha256':sha(lib/'AspisR569MaskedClaimCompleteConsts/Funs.olean'),'Types_olean_sha256':sha(lib/'AspisR569MaskedClaimCompleteConsts/Types.olean'),'command':cmd,'exit_status':r.returncode,'log_sha256':sha(log),'reservations':reservations,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'Lean':'-j1 -M4500'},'formal_axioms':'full #print axioms output in log' if r.returncode==0 else 'failed'}
result.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d),flush=True);print(log.read_text(errors='replace')[-3000:],flush=True)
raise SystemExit(r.returncode)
