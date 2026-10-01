import pathlib,subprocess,shlex,json
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
script='''import pathlib,subprocess,json,hashlib
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r179-freeze-return-trace-20261001-a');root.mkdir(exist_ok=True)
src=pathlib.Path('/home/dombarker/project-offloads/aspis-r156fullfreeze-extract-20260930-a/R156FullFreeze.llbc')
assert src.is_file(),src
binary='/home/dombarker/project-offloads/aspis-switch-global-20261001-a/aeneas-switch-global'
cmd=[binary,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR179FreezeReturnTrace','-dest',str(root/'generated'),'-subdir','AspisR179FreezeReturnTrace','-split-files','-emit-json','-log','PrePasses',str(src)]
(root/'command.json').write_text(json.dumps({'command':cmd,'input_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'binary_sha256':hashlib.sha256(pathlib.Path(binary).read_bytes()).hexdigest(),'purpose':'Missing pass-by-pass evidence identifying where actual nested callback error returns are lost; no new source extraction or regression replay.'},indent=2))
with (root/'trace.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'trace.log').read_text()[-3200:]);print('TRACE_EXIT',r.returncode)
raise SystemExit(r.returncode)
'''
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r179-return-trace','--working-directory=/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',script]
p=pathlib.Path('.r21-scratch/r179-return-trace.log')
with p.open('w') as f:r=subprocess.run(['ssh',*opts,host,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());print('EXIT',r.returncode)
