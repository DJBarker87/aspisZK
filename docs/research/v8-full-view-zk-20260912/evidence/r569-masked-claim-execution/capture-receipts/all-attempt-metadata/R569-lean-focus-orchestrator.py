import glob,hashlib,json,os,pathlib,re,subprocess,sys
ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r569-lean-focus-20261004-a')
NS='AspisR569MaskedClaimCompleteConsts'; SRC=ROOT/'source'; LIB=ROOT/'lib'; workspace=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/focus-workspace'); release_lib=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib')
aeneas=pathlib.Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean')
packages_root=pathlib.Path('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages')
lake='/home/dombarker/.elan/bin/lake'; lean='/home/dombarker/.elan/bin/lean'
expected={'Types.lean':'af6114fc5a59fdf1b5834cb4b1acaf72b028a83f2d09097b790e0a1972dda015','Funs.lean':'76fdc41e055509da697a29b8a14541ed65142e019649ea2dc32e27349de84f5d'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in expected.items():assert sha(SRC/NS/n)==h,(n,sha(SRC/NS/n),h)
assert not list(LIB.rglob('*.olean')), 'scratch cache namespace must start empty'
assert pathlib.Path(lake).is_file() and pathlib.Path(lean).is_file() and aeneas.is_dir()
assert aeneas.is_dir() and any(aeneas.rglob('Std.olean'))
pkg_libs=[]
for p in sorted(packages_root.glob('*/.lake/build/lib/lean')):
 if p.is_dir():pkg_libs.append(p)
assert pkg_libs, 'pinned package library set is empty'
core_lean=pathlib.Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
paths=[str(LIB),str(release_lib),str(aeneas),*[str(p) for p in pkg_libs],str(core_lean)]
base_env=os.environ.copy();base_env.update({'PATH':'/home/dombarker/.elan/bin:/usr/bin:/bin','LEAN_PATH':':'.join(paths),'LEAN_ABORT_ON_PANIC':'1'})
version=subprocess.check_output([lean,'--version'],text=True)
assert '4.32.0' in version,version
lake_path=subprocess.check_output([lake,'--dir',str(workspace),'env','printenv','LEAN_PATH'],text=True,env=base_env).strip()
assert str(LIB) in lake_path and str(aeneas) in lake_path and str(release_lib) in lake_path, lake_path
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True)
reservations=[]
for line in units.splitlines():
 p=line.split()
 if p and p[0].startswith('aspis'):
  v=subprocess.check_output(['systemctl','--user','show',p[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  if v.isdigit():reservations.append((p[0],int(v)))
assert sum(v for _,v in reservations)+7*1024**3<=40*1024**3,reservations
pre={'namespace':NS,'source_revision':'95261201338bfba305516455f07bfb55d014f17d','frozen_selected_source_revision':'6677d5f1310ff7373301fbd79f186278f772e68a','source_sha256':expected,'source_files_identical_to_generated_translation':True,'remote_stage':str(ROOT),'lake_workspace':str(workspace),'release_cache':str(release_lib),'aeneas_library':str(aeneas),'package_libraries':[str(p) for p in pkg_libs],'lean_version':version.strip(),'effective_lean_path':lake_path,'other_active_aspis_reservations':reservations,'aggregate_reserved_max_bytes':40*1024**3,'per_job_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'},'dependency_build':'disabled; invoke lean only through lake env; no lake build'}
(ROOT/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
def compile_one(name):
 src=SRC/NS/name; out=LIB/NS/(name[:-5]+'.olean'); unit='aspis-r569-lean-'+name.split('.')[0].lower()+'-20261004'
 assert not out.exists()
 cmd=['systemd-run','--user','--wait','--collect','--pipe',f'--unit={unit}',f'--working-directory={workspace}','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','/usr/bin/time','-v','/usr/bin/env','LEAN_PATH='+':'.join(paths),'PATH=/home/dombarker/.elan/bin:/usr/bin:/bin',lake,'--dir',str(workspace),'env','lean','-j1','-M4500','-R',str(SRC),'-o',str(out),str(src)]
 logfile=ROOT/(name.split('.')[0]+'.compile.log')
 with logfile.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 report={'target':str(src),'target_sha256':sha(src),'command':cmd,'exit_status':r.returncode,'olean_exists':out.is_file(),'olean_sha256':sha(out)if out.is_file()else None,'log_sha256':sha(logfile),'formal_axioms':'pending separate full declaration audit' if r.returncode==0 else 'not available; compile failed'}
 (ROOT/(name.split('.')[0]+'.result.json')).write_text(json.dumps(report,indent=2)+'\n')
 log=logfile.read_text(errors='replace');print(name,report,flush=True)
 if r.returncode:print(log[-6000:],flush=True);sys.exit(r.returncode)
compile_one('Types.lean')
compile_one('Funs.lean')
