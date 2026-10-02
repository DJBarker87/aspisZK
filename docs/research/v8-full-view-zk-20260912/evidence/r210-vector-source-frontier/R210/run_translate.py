import pathlib,subprocess,shlex,json
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
script='''import pathlib,subprocess,json,hashlib
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r210-vector-leaf-diagnostic-20261002-a');root.mkdir(exist_ok=True)
src=pathlib.Path('/home/dombarker/project-offloads/aspis-r210-vector-leaf-diagnostic-20261002-a/R210VectorLeaf.llbc')
assert src.is_file(),src
binary='/home/dombarker/project-offloads/aspis-return-continuation-20261002-a/aeneas-return-continuation'
cmd=[binary,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR210VectorLeaf','-dest',str(root/'generated'),'-subdir','AspisR210VectorLeaf','-split-files','-emit-json',str(src)]
(root/'command.json').write_text(json.dumps({'command':cmd,'input_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'binary_sha256':hashlib.sha256(pathlib.Path(binary).read_bytes()).hexdigest(),'purpose':'Diagnostic projected vector leaves: only five preserved source bodies. No opaque assumptions are accepted as proof premises.'},indent=2))
with (root/'trace.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'trace.log').read_text()[-3200:]);print('TRACE_EXIT',r.returncode)
raise SystemExit(r.returncode)
'''
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r210-vector-leaf-diagnostic','--working-directory=/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',script]
p=pathlib.Path('.r21-scratch/r210-vector-leaf-diagnostic/translate-launch.log')
with p.open('w') as f:r=subprocess.run(['ssh',*opts,host,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());print('EXIT',r.returncode)
