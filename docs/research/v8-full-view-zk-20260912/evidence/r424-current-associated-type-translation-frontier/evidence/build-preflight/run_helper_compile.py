import hashlib,json,pathlib,subprocess,time,sys
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r424-concrete-associated-types-candidate-20261002-a')
parent=pathlib.Path('/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a')
audit=root/'candidate-audit/r424-helper-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected=json.loads(pathlib.Path('/tmp/aspis-r424-helper-inputs.json').read_text())
assert not audit.exists();audit.mkdir(parents=True)
assert sha(parent/'aeneas-r385-private-return-carrier-v2-candidate')=='f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
assert sha(root/'src/interp/InterpUtils.ml')==sha(parent/'src/interp/InterpUtils.ml')=='23c4394d0a7328d590e9092f813a1c372d7ef989d646375db65bb4ec9d5d03e1'
for rel,h in expected['source_sha256'].items():
 assert sha(root/rel)==h,(rel,'source mismatch')
 target=audit/'source'/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((root/rel).read_bytes())
mem={k:v for k,v in (l.split(':',1) for l in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemAvailable','MemTotal','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024
services=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
containers=subprocess.check_output(['docker','ps','--no-trunc'],text=True)
assert 'aspis-r424-typed-helper-v1' not in subprocess.check_output(['docker','ps','-a','--format','{{.Names}}'],text=True)
image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
assert subprocess.check_output(['docker','image','inspect','ef96e46342a4','--format','{{.Id}}'],text=True).strip()==image
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr424.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
(audit/'reservation-before.json').write_text(json.dumps({'meminfo':mem,'active_services':services,'active_containers':containers,'root_slice':subprocess.check_output(['systemctl','show','aspisr424.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax'],text=True)},indent=2)+'\n')
inner='set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v -o /work/candidate-audit/r424-helper-v1/gnu-time.txt env AENEAS_VERSION=aspis-r424-concrete-associated-types-candidate OCAMLPARAM=_,ccopt=-static opam exec -- dune build .aeneas.objs/byte/aeneas__ConcreteAssociatedTypes.cmo --profile release -j 1'
argv=['docker','run','--name','aspis-r424-typed-helper-v1','--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','--cgroup-parent=aspisr424.slice','-v',str(root)+':/work',image,'bash','-lc',inner]
(audit/'command.json').write_text(json.dumps({'argv':argv,'inner_command':inner,'source_revision':expected['source_revision'],'source_sha256':expected['source_sha256'],'target':'.aeneas.objs/byte/aeneas__ConcreteAssociatedTypes.cmo','expected_work':'Typecheck smallest new helper module using pinned cache. No main executable, integration, translation, or Lean job.','axioms':'NA: OCaml compilation only'},indent=2)+'\n')
start=time.monotonic()
with (audit/'build.log').open('w') as f:r=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT)
(audit/'docker-inspect.json').write_text(subprocess.check_output(['docker','inspect','aspis-r424-typed-helper-v1'],text=True))
(audit/'result.json').write_text(json.dumps({'exit_status':r.returncode,'wrapper_wall_seconds':time.monotonic()-start,'metrics':'Complete compiler GNU-time report in gnu-time.txt; wrapper wall time is not compiler wall/RSS.','source_revision':expected['source_revision'],'source_sha256':expected['source_sha256'],'boundary':'Helper typechecking only; no fixtures executed and no semantic claim'},indent=2)+'\n')
print((audit/'build.log').read_text());print((audit/'result.json').read_text())
assert sha(parent/'src/interp/InterpUtils.ml')=='23c4394d0a7328d590e9092f813a1c372d7ef989d646375db65bb4ec9d5d03e1'
sys.exit(r.returncode)
