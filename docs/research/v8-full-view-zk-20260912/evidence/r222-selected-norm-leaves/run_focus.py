import sys, pathlib, subprocess, shlex, time
root=pathlib.Path(__file__).resolve().parent.parent
src=pathlib.Path(sys.argv[1]); rel=sys.argv[2] if len(sys.argv)>2 else src.name
host='dombarker@100.108.41.90'; opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
remote='/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a'
cache='/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib'
runid='aspis-focus-'+str(time.time_ns()); log=root/'.r21-scratch'/f'{runid}.log'
subprocess.run(['ssh',*opts,host,'mkdir -p '+shlex.quote(str(pathlib.PurePosixPath(remote,rel).parent))],check=True)
subprocess.run(['scp',*opts,str(src),host+':'+remote+'/'+rel],check=True)
script=f'''import os, glob, subprocess, pathlib
p={cache!r}
deps=sorted(glob.glob('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal/.lake/packages/*/.lake/build/lib/lean'))
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/.lake/build/lib/lean'
os.environ['LEAN_PATH']=':'.join([p,*deps,aeneas])
obj=p+'/'+{rel!r}[:-5]+'.olean'
os.makedirs(os.path.dirname(obj),exist_ok=True)
workspace=pathlib.Path('/home/dombarker/project-offloads/aspis-r126-release-20260930-a/focus-workspace')
workspace.mkdir(exist_ok=True)
(workspace/'lakefile.toml').write_text('name = \"aspis_focus\"\\nversion = \"0.0.0\"\\n')
(workspace/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\\n')
cmd=['/home/dombarker/.elan/bin/lake','--dir',str(workspace),'env','lean','-j1','-M4500','-R',{remote!r},'-o',obj,{remote!r}+'/'+{rel!r}]
raise SystemExit(subprocess.call(['/usr/bin/time','-v',*cmd]))
'''
command=['systemd-run','--user','--wait','--collect','--pipe','--unit='+runid,'--working-directory='+remote,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',script]
with log.open('w') as f:
 r=subprocess.run(['ssh',*opts,host,shlex.join(command)],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text());print('LOG',log,'EXIT',r.returncode)
sys.exit(r.returncode)
