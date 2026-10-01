import pathlib,subprocess,shlex,time
host='dombarker@100.108.41.90'; opts=['-o','BatchMode=yes','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
script=r'''import pathlib,shutil,subprocess,hashlib,difflib,json,os
base=pathlib.Path('/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/reconstruct.oJL55K')
root=pathlib.Path('/home/dombarker/project-offloads/aspis-switch-global-20261001-a')
root.mkdir(exist_ok=False)
shutil.copytree(base/'src',root/'src',symlinks=True)
p=root/'src/PrePasses.ml'; old=p.read_text()
needle='''+'"""'+r'''            | SetDiscriminant _ | StorageLive _ | StorageDead _ | PlaceMention _
            | Drop (_, _, _, _)
            | Abort _
            | Return
            | UnwindResume
            | Break _
            | Continue _
            | Nop
            | Switch _
            | Loop _
            | Error _ -> st.kind'''+'"""'+r'''
replacement='''+'"""'+r'''            | Switch (If (cond, yes, no)) ->
                Switch (If (visitor#visit_operand mk_unit_ty cond, yes, no))
            | Switch (SwitchInt (op, ty, branches, otherwise)) ->
                Switch (SwitchInt
                  (visitor#visit_operand mk_unit_ty op, ty, branches, otherwise))
            | Switch (Match (scrut, branches, otherwise)) ->
                Switch (Match
                  (visitor#visit_place mk_unit_ty scrut, branches, otherwise))
            | SetDiscriminant _ | StorageLive _ | StorageDead _ | PlaceMention _
            | Drop (_, _, _, _)
            | Abort _
            | Return
            | UnwindResume
            | Break _
            | Continue _
            | Nop
            | Loop _
            | Error _ -> st.kind'''+'"""'+r'''
assert old.count(needle)==1
new=old.replace(needle,replacement);p.write_text(new)
(root/'switch-global.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/src/PrePasses.ml',tofile='b/src/PrePasses.ml')))
(root/'source-adapter.json').write_text(json.dumps({'base_source':str(base),'original_PrePasses_sha256':hashlib.sha256(old.encode()).hexdigest(),'patched_PrePasses_sha256':hashlib.sha256(new.encode()).hexdigest(),'change':'Apply existing decompose_global_accesses visitor to switch scrutinees; branch bodies remain for existing recursive pass; no execution axiom or Rust source change','expected_cost':'Optimized OCaml compilation of PrePasses and dependent translator modules from retained source/cache; no Rust arithmetic or certificate gate'},indent=2))
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisswitchglobal.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
image='ef96e46342a4'
build='set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; AENEAS_VERSION=aspis-switch-global-20261001-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-switch-global; chmod 755 /work/aeneas-switch-global'
cmd=['docker','run','--name','aspis-switch-global-20261001-a','--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','--cgroup-parent=aspisswitchglobal.slice','-v',str(root)+':/work',image,'bash','-lc',build]
with (root/'build.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
(root/'docker-inspect.json').write_bytes(subprocess.check_output(['docker','inspect','aspis-switch-global-20261001-a']))
(root/'slice-properties.txt').write_bytes(subprocess.check_output(['systemctl','show','aspisswitchglobal.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryPeak','-p','MemorySwapPeak']))
print((root/'build.log').read_text()[-5000:]); print('BUILD_EXIT',r.returncode)
if r.returncode==0:
 binary=root/'aeneas-switch-global';(root/'binary.sha256').write_text(hashlib.sha256(binary.read_bytes()).hexdigest()+'  aeneas-switch-global\n')
 print(subprocess.check_output([str(binary),'-version'],text=True))
raise SystemExit(r.returncode)
'''
cmd=['systemd-run','--user','--wait','--collect','--pipe','--unit=aspis-switch-global-build-20261001-a','--working-directory=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',script]
log=pathlib.Path('.r21-scratch/switch-global-build.log')
with log.open('w') as f:r=subprocess.run(['ssh',*opts,host,shlex.join(cmd)],stdout=f,stderr=subprocess.STDOUT)
print(log.read_text()); raise SystemExit(r.returncode)
