#!/usr/bin/env python3
"""Focused cache compiles with the lead-approved import-only Aeneas adapter."""
import difflib,hashlib,json,pathlib,shlex,subprocess
HERE=pathlib.Path(__file__).resolve().parent; HOST='dombarker@100.108.41.90'
SSH=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
SCP=['scp','-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
NS='AspisR569MaskedClaimCompleteConsts'; RAW=HERE/'R569-complete-consts-generated/generated'/NS
RAW_HASH={'Types.lean':'af6114fc5a59fdf1b5834cb4b1acaf72b028a83f2d09097b790e0a1972dda015','Funs.lean':'76fdc41e055509da697a29b8a14541ed65142e019649ea2dc32e27349de84f5d'}
ADAPT=HERE/'R569-import-adapted-input'/NS; ADAPT.mkdir(parents=True,exist_ok=True)
newimports=b'import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n'
patch=[]; adapted_hash={}
for name,expected in RAW_HASH.items():
 raw=(RAW/name).read_bytes(); assert hashlib.sha256(raw).hexdigest()==expected
 assert raw.count(b'import Aeneas\n')==1
 out=raw.replace(b'import Aeneas\n',newimports,1); (ADAPT/name).write_bytes(out); adapted_hash[name]=hashlib.sha256(out).hexdigest()
 patch.extend(difflib.unified_diff(raw.decode().splitlines(True),out.decode().splitlines(True),fromfile='generated/'+NS+'/'+name,tofile='import-adapted/'+NS+'/'+name))
(HERE/'R569-import-only-adaptation.patch').write_text(''.join(patch))
PATCH_SHA=hashlib.sha256((HERE/'R569-import-only-adaptation.patch').read_bytes()).hexdigest()
ROOT='/home/dombarker/project-offloads/aspis-r569-lean-focus-import-adapted-20261004-a'
subprocess.run([*SSH,HOST,'mkdir','-m','700','-p',ROOT+'/source-import-adapted/'+NS,ROOT+'/lib/'+NS],check=True)
for n in RAW_HASH:subprocess.run([*SCP,str(ADAPT/n),f'{HOST}:{ROOT}/source-import-adapted/{NS}/{n}'],check=True)
remote=r'''import hashlib,json,os,pathlib,subprocess,sys
ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r569-lean-focus-import-adapted-20261004-a');NS='AspisR569MaskedClaimCompleteConsts';SRC=ROOT/'source-import-adapted';LIB=ROOT/'lib'
workspace=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/focus-workspace');release_lib=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib')
aeneas=pathlib.Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean'); packages_root=pathlib.Path('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages')
lake='/home/dombarker/.elan/bin/lake';lean='/home/dombarker/.elan/bin/lean'; expected=EXPECTED
raw_expected=RAW_EXPECTED

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in expected.items(): assert sha(SRC/NS/n)==h,(n,sha(SRC/NS/n),h)
assert not list(LIB.rglob('*.olean')), 'import-adapted scratch cache is not empty'
pkg_libs=sorted(p for p in packages_root.glob('*/.lake/build/lib/lean') if p.is_dir()); assert pkg_libs
core_lean=pathlib.Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
paths=[str(LIB),str(release_lib),str(aeneas),*[str(p) for p in pkg_libs],str(core_lean)]
env=os.environ.copy();env.update({'PATH':'/home/dombarker/.elan/bin:/usr/bin:/bin','LEAN_PATH':':'.join(paths),'LEAN_ABORT_ON_PANIC':'1'})
version=subprocess.check_output([lean,'--version'],text=True);assert '4.32.0' in version,version
lake_path=subprocess.check_output([lake,'--dir',str(workspace),'env','printenv','LEAN_PATH'],text=True,env=env).strip();assert str(LIB) in lake_path and str(aeneas) in lake_path and str(release_lib) in lake_path,lake_path
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True);reservations=[]
for line in units.splitlines():
 p=line.split()
 if p and p[0].startswith('aspis'):
  v=subprocess.check_output(['systemctl','--user','show',p[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  if v.isdigit():reservations.append((p[0],int(v)))
assert sum(v for _,v in reservations)+7*1024**3<=40*1024**3,reservations
pre={'namespace':NS,'current_repository_head':'95261201338bfba305516455f07bfb55d014f17d','frozen_selected_source_revision':'6677d5f1310ff7373301fbd79f186278f772e68a','raw_generated_sha256':raw_expected,'import_adapted_sha256':expected,'only_source_delta':'replace only first-line import Aeneas with Aeneas.Std, Aeneas.Data.Discriminant, Aeneas.Tactic.RustAttributes','remote_stage':str(ROOT),'workspace':str(workspace),'release_cache':str(release_lib),'aeneas_lib':str(aeneas),'package_libs':[str(p) for p in pkg_libs],'lean_version':version.strip(),'effective_lean_path':lake_path,'other_active_aspis_reservations':reservations,'aggregate_reserved_max_bytes':40*1024**3,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'Lean':'-j1 -M4500'},'no_dependency_build':True}
(ROOT/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
for name in ['Types.lean','Funs.lean']:
 src=SRC/NS/name; out=LIB/NS/(name[:-5]+'.olean'); assert not out.exists()
 unit='aspis-r569-importadapted-'+name.split('.')[0].lower()+'-20261004'
 cmd=['systemd-run','--user','--wait','--collect','--pipe',f'--unit={unit}',f'--working-directory={workspace}','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','/usr/bin/time','-v','/usr/bin/env','LEAN_PATH='+':'.join(paths),'PATH=/home/dombarker/.elan/bin:/usr/bin:/bin',lake,'--dir',str(workspace),'env','lean','-j1','-M4500','-R',str(SRC),'-o',str(out),str(src)]
 log=ROOT/(name.split('.')[0]+'.compile.log')
 with log.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 result={'target':str(src),'target_sha256':sha(src),'raw_generated_sha256':raw_expected[name],'import_only_adapted_sha256':expected[name],'command':cmd,'exit_status':r.returncode,'olean_exists':out.is_file(),'olean_sha256':sha(out)if out.is_file()else None,'log_sha256':sha(log),'formal_axioms':'separate full audit pending'if r.returncode==0 else 'not available; compile failed'}
 (ROOT/(name.split('.')[0]+'.result.json')).write_text(json.dumps(result,indent=2)+'\n'); print(name,json.dumps(result),flush=True)
 if r.returncode:print(log.read_text(errors='replace')[-6000:],flush=True);sys.exit(r.returncode)
'''
# Convert known placeholders via names isolated by @delimiters@.
remote=remote.replace('EXPECTED@', '@EXPECTED@').replace('RAW_EXPECTED@','@RAW_EXPECTED@')
remote=remote.replace('expected=EXPECTED','expected=@EXPECTED@').replace('raw_expected=RAW_EXPECTED','raw_expected=@RAW_EXPECTED@')
remote=remote.replace("'current_repository_head':'95261201338bfba305516455f07bfb55d014f17d'", "'current_repository_head':'95261201338bfba305516455f07bfb55d014f17d'")
remote=remote.replace('@EXPECTED@',repr(adapted_hash)).replace('@RAW_EXPECTED@',repr(RAW_HASH))
local_summary={'namespace':NS,'raw_hashes':RAW_HASH,'adapted_hashes':adapted_hash,'patch_sha256':PATCH_SHA,'files_unchanged_beyond_import_line':True,'remote_stage':ROOT,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'lean_flags':'-j1 -M4500','sequence':['Types.lean','Funs.lean'],'no_dependency_build':True}
(HERE/'R569-import-adapted-compile-launch.json').write_text(json.dumps(local_summary,indent=2)+'\n')
remote_cmd='python3 -c '+shlex.quote(remote)
with (HERE/'R569-import-adapted-compile-ssh-output.log').open('w') as o:r=subprocess.run([*SSH,HOST,remote_cmd],stdout=o,stderr=subprocess.STDOUT)
(HERE/'R569-import-adapted-compile-launch-exit.txt').write_text(str(r.returncode)+'\n')
for rel in ['preflight.json','Types.compile.log','Types.result.json','Funs.compile.log','Funs.result.json']:
 scp=subprocess.run([*SCP,f'{HOST}:{ROOT}/{rel}',str(HERE/('import-adapted-'+rel))])
 if scp.returncode and r.returncode==0:raise SystemExit(scp.returncode)
if r.returncode:raise SystemExit(r.returncode)
