import pathlib,subprocess,shlex,json,sys
root=pathlib.Path(__file__).resolve().parent
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
remote='/home/dombarker/project-offloads/aspis-r232-coefficient-translation-20261002-a'
script=r"""import pathlib,hashlib,subprocess,json
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r232-coefficient-translation-20261002-a');assert not root.exists();root.mkdir()
source=pathlib.Path('/home/dombarker/project-offloads/aspis-r231-coefficient-extract-20261002-a/R231NormLeaves.llbc')
binary=pathlib.Path('/home/dombarker/project-offloads/aspis-return-continuation-20261002-a/aeneas-return-continuation')
assert hashlib.sha256(source.read_bytes()).hexdigest()=='ab72ee9cb72ec543bc8a86f5fc2a627cd3c5847eeed46c049d78ab25182294f8'
assert hashlib.sha256(binary.read_bytes()).hexdigest()=='63b04a88532b8fb0aaa0d274881b5cacf00bc4f449243ece905178f0de9cc495'
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR232CoeffLeaves','-dest',str(root/'generated'),'-subdir','AspisR232CoeffLeaves','-split-files','-emit-json',str(source)]
(root/'translate-command.json').write_text(json.dumps({'command':cmd,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest()},indent=2))
with (root/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'translate.log').read_text());print('TRANSLATE_EXIT',r.returncode)
(root/'result.json').write_text(json.dumps({'exit_status':r.returncode,'generated':(root/'generated').exists()},indent=2));raise SystemExit(r.returncode)
"""
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r232-coefficient-translation','--working-directory=/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',script]
(root/'launch.json').write_text(json.dumps({'command':cmd,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}},indent=2))
with (root/'launch.log').open('w') as f:r=subprocess.run(['ssh',*opts,host,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
print((root/'launch.log').read_text())
subprocess.run(['scp','-r',*opts,host+':'+remote+'/.',str(root)],check=True)
sys.exit(r.returncode)
