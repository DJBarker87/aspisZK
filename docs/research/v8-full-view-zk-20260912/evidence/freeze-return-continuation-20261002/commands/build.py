import pathlib,subprocess,shlex,time
host='dombarker@100.108.41.90'; opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
script=r'''import pathlib,shutil,subprocess,hashlib,difflib,json,os
base=pathlib.Path('/home/dombarker/project-offloads/aspis-switch-global-20261001-a')
root=pathlib.Path('/home/dombarker/project-offloads/aspis-return-continuation-20261002-a')
root.mkdir(exist_ok=False)
shutil.copytree(base/'src',root/'src',symlinks=True)
p=root/'src/PrePasses.ml';old=p.read_text()
new=pathlib.Path('/home/dombarker/project-offloads/PrePasses-return-continuation-20261002.ml').read_text();p.write_text(new)
(root/'return-continuation.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/src/PrePasses.ml',tofile='b/src/PrePasses.ml')))
(root/'source-adapter.json').write_text(json.dumps({'base_source':str(base),'original_PrePasses_sha256':hashlib.sha256(old.encode()).hexdigest(),'patched_PrePasses_sha256':hashlib.sha256(new.encode()).hexdigest(),'change':'Track syntactically cleanup-only parent and loop-break continuations to function Return. Restore nested return-place writes that otherwise fall through to that known function return. Tighten existing Break restoration to a justified returning continuation. Candidate extraction repair; no Rust source change or execution axiom.','expected_cost':'Optimized OCaml compilation from retained compiled cache; no arithmetic gate'},indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisreturncontinuation.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
image='ef96e46342a4'
build='set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; AENEAS_VERSION=aspis-return-continuation-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-return-continuation; chmod 755 /work/aeneas-return-continuation'
cmd=['docker','run','--name','aspis-return-continuation-20261002-a','--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','--cgroup-parent=aspisreturncontinuation.slice','-v',str(root)+':/work',image,'bash','-lc',build]
with (root/'build.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
(root/'docker-inspect.json').write_bytes(subprocess.check_output(['docker','inspect','aspis-return-continuation-20261002-a']))
(root/'slice-properties.txt').write_bytes(subprocess.check_output(['systemctl','show','aspisreturncontinuation.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryPeak','-p','MemorySwapPeak']))
print((root/'build.log').read_text()[-5000:]); print('BUILD_EXIT',r.returncode)
if r.returncode==0:
 binary=root/'aeneas-return-continuation';(root/'binary.sha256').write_text(hashlib.sha256(binary.read_bytes()).hexdigest()+'  aeneas-return-continuation\n')
 print(subprocess.check_output([str(binary),'-version'],text=True))
raise SystemExit(r.returncode)
'''
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-return-continuation-build-20261002-a','--working-directory=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',script]
log=pathlib.Path('.r21-scratch/return-continuation-build.log')
with log.open('w') as f:r=subprocess.run(['ssh',*opts,host,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text()); raise SystemExit(r.returncode)
