import pathlib,subprocess,shlex
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
root='/home/dombarker/project-offloads/aspis-switch-global-20261001-a'
code=r'''import pathlib,subprocess,json,hashlib
root=pathlib.Path('/home/dombarker/project-offloads/aspis-switch-global-20261001-a')
src=pathlib.Path('/home/dombarker/project-offloads/aspis-r160freezestd-extract-20260930-a/R160FreezeStd.llbc')
out=root/'translation-r1';out.mkdir(exist_ok=False)
cmd=[str(root/'aeneas-switch-global'),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisSwitchGlobalFreeze','-dest',str(out/'generated'),'-subdir','AspisSwitchGlobalFreeze','-split-files','-emit-json',str(src)]
(out/'command.json').write_text(json.dumps({'command':cmd,'input_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'binary_sha256':hashlib.sha256((root/'aeneas-switch-global').read_bytes()).hexdigest()},indent=2))
with (out/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((out/'translate.log').read_text());print('TRANSLATE_EXIT',r.returncode);raise SystemExit(r.returncode)
'''
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-switch-global-translate-r1','--working-directory='+root,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',code]
log=pathlib.Path('.r21-scratch/switch-global-translate-r1.log')
with log.open('w') as f:r=subprocess.run(['ssh',*opts,host,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text());raise SystemExit(r.returncode)
