import pathlib,subprocess,shlex,json,hashlib
here=pathlib.Path(__file__).resolve().parent
src=here.parent/'r339-controlflow-output-source-projection/R339ControlFlowOutputSourceProjection.llbc'
sha=hashlib.sha256(src.read_bytes()).hexdigest();assert sha=='0860e61790d9a0d5a750999a816fb378f8aa3f5b2c9073ae428945ea3325417d'
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
host='dombarker@100.108.41.90';opts=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
remote='/home/dombarker/project-offloads/aspis-r343-controlflow-output-source-translation-20261002-a'
binary='/home/dombarker/project-offloads/aspis-r312-slice-length-candidate-20261002-a/aeneas-r312-slice-length-candidate'
bsha='fff3717072567f291fc1444f52a3dc7c1f8ba4ddc5c3980e94c863cdceb60f4f'
subprocess.run(['ssh',*opts,host,'test ! -e '+shlex.quote(remote)+' && mkdir '+shlex.quote(remote)],check=True)
subprocess.run(['scp',*opts,str(src),host+':'+remote+'/R339ControlFlowOutputSourceProjection.llbc'],check=True)
script='''import pathlib,hashlib,json,subprocess,re
root=pathlib.Path(REMOTE);src=root/'R339ControlFlowOutputSourceProjection.llbc';binary=pathlib.Path(BINARY)
assert hashlib.sha256(src.read_bytes()).hexdigest()==SHA
assert hashlib.sha256(binary.read_bytes()).hexdigest()==BSHA
mem=pathlib.Path('/proc/meminfo').read_text();av=int(re.search(r'MemAvailable:\\s+(\\d+)',mem)[1]);assert av>=24*1024*1024
services=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps({'meminfo':mem,'available_kib':av,'active_user_services':services,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}},indent=2)+'\\n')
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR343ControlFlowOutputSource','-dest',str(root/'generated'),'-subdir','AspisR343ControlFlowOutputSource','-split-files','-emit-json',str(src)]
(root/'command.json').write_text(json.dumps({'command':cmd,'source_sha256':SHA,'binary_sha256':BSHA,'source_revision':REV,'scope':'Single exact source ControlFlow from_output projection; not a batch/traversal translation.'},indent=2)+'\\n')
with (root/'translate.log').open('w') as out:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=out,stderr=subprocess.STDOUT)
print((root/'translate.log').read_text())
files={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((root/'generated').rglob('*')) if p.is_file()}
(root/'result.json').write_text(json.dumps({'exit_status':r.returncode,'source_sha256':SHA,'binary_sha256':BSHA,'source_revision':REV,'generated_files':files,'Lean_compiled':False,'print_axioms':'N/A; translation only','first_remaining':'Audit emitted source bindings and every external dependency before any proof.'},indent=2)+'\\n')
raise SystemExit(r.returncode)
'''
prefix='REMOTE='+repr(remote)+'\nBINARY='+repr(binary)+'\nSHA='+repr(sha)+'\nBSHA='+repr(bsha)+'\nREV='+repr(rev)+'\n'
argv=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-r343-controlflow-output-source-translation','--working-directory=/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',prefix+script]
(here/'launch.json').write_text(json.dumps({'argv':argv,'source_revision':rev,'runner_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'lead_review':'Lead reviewed exact Fun39-only projection: full recognized decoded closure includes original ADTs; no source row/signature/body/region/langitem altered; no loops; original metadata-only traits lacking order entries remain without invented ordering.'},indent=2)+'\n')
with (here/'launch.log').open('w') as out:r=subprocess.run(['ssh',*opts,host,shlex.join(argv)],stdout=out,stderr=subprocess.STDOUT)
print((here/'launch.log').read_text());subprocess.run(['scp','-r',*opts,host+':'+remote+'/.',str(here)],check=True);raise SystemExit(r.returncode)
