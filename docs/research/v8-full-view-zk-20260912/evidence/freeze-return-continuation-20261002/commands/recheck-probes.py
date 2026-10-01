import pathlib,subprocess,shlex
opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null'];host='dombarker@100.108.41.90'
code=r'''import pathlib,subprocess,json,hashlib
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r180-return-probes-20261002-a');root.mkdir(exist_ok=False)
binary=pathlib.Path('/home/dombarker/project-offloads/aspis-return-continuation-20261002-a/aeneas-return-continuation')
for suffix in ['a','b']:
 old=pathlib.Path('/home/dombarker/project-offloads/aspis-freeze-return-probe-20261001-'+suffix);src=old/'after_loop.llbc';out=root/suffix;out.mkdir()
 cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisReturnRepairProbe','-dest',str(out/'generated'),'-subdir','AspisReturnRepairProbe','-split-files','-emit-json','-log','PrePasses',str(src)]
 (out/'command.json').write_text(json.dumps({'command':cmd,'input_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'reason_for_rerun':'Changed extraction return restoration; reuse frozen tiny LLBC, no Rust rebuild'},indent=2))
 with (out/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
 print('PROBE',suffix,'EXIT',r.returncode);print((out/'translate.log').read_text()[-2600:])
'''
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r180-return-probes','--working-directory=/home/dombarker/project-offloads/aspis-return-continuation-20261002-a','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',code]
p=pathlib.Path('.r21-scratch/r180-return-probes.log')
with p.open('w') as f:r=subprocess.run(['ssh',*opts,host,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text());raise SystemExit(r.returncode)
