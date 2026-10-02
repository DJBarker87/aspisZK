#!/usr/bin/env python3
"""Run exactly one capped R388 translation with the reviewed stable R363 binary."""
import hashlib,json,pathlib,shlex,subprocess
HERE=pathlib.Path(__file__).resolve().parent
WORKTREE=HERE.parents[1]
SOURCE=HERE/'R388ReduceU62Ordered.llbc'
SOURCE_SHA='95480c0a8938629f770f7c381fe61a71f44e8275fe2e7275e9edfd4a4bb7f040'
BINARY=WORKTREE/'.r21-scratch/r363-instantiated-pattern-candidate/build-evidence/7c588ebcd629-20261002T130406Z/aeneas-r363-instantiated-pattern-candidate'
BINARY_SHA='3dc9ad6de1af901c8ead41940ba97097a0cf06f82d27dbc7d7c5eac03695e329'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==SOURCE_SHA
assert hashlib.sha256(BINARY.read_bytes()).hexdigest()==BINARY_SHA
REV=subprocess.check_output(['git','-C',str(WORKTREE),'rev-parse','HEAD'],text=True).strip()
HOST='dombarker@100.108.41.90'; SSH_OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
REMOTE='/home/dombarker/project-offloads/aspis-r388-reduce-u62-translation-20261002-a'
REMOTE_BINARY='/home/dombarker/project-offloads/aspis-r363-instantiated-pattern-candidate-20261002-a/aeneas-r363-instantiated-pattern-candidate'
preflight="python3 -c 'import pathlib,hashlib; p=pathlib.Path(\""+REMOTE+"\"); f=p/\"R388ReduceU62Ordered.llbc\"; assert sorted(x.name for x in p.iterdir())==[\"R388ReduceU62Ordered.llbc\"]; assert hashlib.sha256(f.read_bytes()).hexdigest()==\""+SOURCE_SHA+"\"'"
subprocess.run(['ssh',*SSH_OPTS,HOST,preflight],check=True)
remote_script=r'''import pathlib,hashlib,json,subprocess,re
root=pathlib.Path(REMOTE);src=root/'R388ReduceU62Ordered.llbc';binary=pathlib.Path(BINARY)
assert hashlib.sha256(src.read_bytes()).hexdigest()==SOURCE_SHA
assert hashlib.sha256(binary.read_bytes()).hexdigest()==BINARY_SHA
mem=pathlib.Path('/proc/meminfo').read_text();av=int(re.search(r'MemAvailable:\s+(\d+)',mem)[1]);assert av>=24*1024*1024
services=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps({'meminfo':mem,'available_kib':av,'active_user_services':services,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}},indent=2)+'\n')
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR388ReduceU62','-dest',str(root/'generated'),'-subdir','AspisR388ReduceU62','-split-files','-emit-json',str(src)]
(root/'command.json').write_text(json.dumps({'command':cmd,'input_sha256':SOURCE_SHA,'binary_sha256':BINARY_SHA,'campaign_revision':REV,'namespace':'AspisR388ReduceU62','scope':'R388 ordered reduce_u62 extraction only; translation diagnostic, no Lean compilation or template filling.'},indent=2)+'\n')
with (root/'translate.log').open('w') as out:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=out,stderr=subprocess.STDOUT)
files={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.rglob('*')) if p.is_file() and p.name!='result.json'}
(root/'result.json').write_text(json.dumps({'exit_status':r.returncode,'input_sha256':SOURCE_SHA,'binary_sha256':BINARY_SHA,'campaign_revision':REV,'generated_files':files,'Lean_compiled':False,'print_axioms':'N/A; translation only','template_filling':'not performed'},indent=2)+'\n')
print((root/'translate.log').read_text());print('R388_TRANSLATION_EXIT',r.returncode)
raise SystemExit(r.returncode)
'''
script='REMOTE='+repr(REMOTE)+'\nBINARY='+repr(REMOTE_BINARY)+'\nSOURCE_SHA='+repr(SOURCE_SHA)+'\nBINARY_SHA='+repr(BINARY_SHA)+'\nREV='+repr(REV)+'\n'+remote_script
argv=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r388-reduce-u62-translation','--working-directory=/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',script]
(HERE/'translation-launch-receipt.json').write_text(json.dumps({'argv':argv,'ssh_options':SSH_OPTS,'remote_root':REMOTE,'remote_binary':REMOTE_BINARY,'input_sha256':SOURCE_SHA,'binary_sha256':BINARY_SHA,'campaign_revision':REV,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'launcher_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'status':'second launcher run; first wrapper stopped before Aeneas due preflight regex; this invocation runs the single authorized translation'},indent=2)+'\n')
with (HERE/'translation-service.log').open('w') as log:r=subprocess.run(['ssh',*SSH_OPTS,HOST,shlex.join(argv)],stdout=log,stderr=subprocess.STDOUT)
print((HERE/'translation-service.log').read_text())
subprocess.run(['scp','-r',*SSH_OPTS,HOST+':'+REMOTE+'/.',str(HERE)],check=True)
raise SystemExit(r.returncode)
