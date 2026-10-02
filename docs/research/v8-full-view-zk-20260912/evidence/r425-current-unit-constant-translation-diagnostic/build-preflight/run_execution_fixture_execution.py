"""PREPARED ONLY: execute the eight-check direct evaluator fixture once."""
import hashlib,json,pathlib,subprocess,sys,time,re

ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a')
PARENT=pathlib.Path('/home/dombarker/project-offloads/aspis-r424-concrete-associated-types-candidate-20261002-a')
R385=pathlib.Path('/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a')
R419_INPUT=pathlib.Path('/home/dombarker/project-offloads/aspis-r419-native-20261002-a/aspis-r419-candidate-1790967913444473000/candidate.llbc')
BUILD=ROOT/'candidate-audit/r425-unit-execution-fixture-build-v2'
AUDIT=ROOT/'candidate-audit/r425-unit-execution-fixture-run-v1'
INPUT=pathlib.Path('/tmp/aspis-r425-unit-execution-fixture-run-inputs.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected=json.loads(INPUT.read_text())
assert not AUDIT.exists(),'refuse to overwrite existing run evidence'
assert expected['lead_approved'] is True,'lead approval gate not set'
build=json.loads((BUILD/'result.json').read_text())
assert build['exit_status']==0 and build['fixture_executable_sha256']
assert build['source_sha256']==expected['source_sha256']
assert sha(PARENT/'src/interp/InterpExpressions.ml')=='531b0ee1c6d26d463d07c6e1dbdc75a7cce32cf970adcbc59dfafd75bfdd914f'
assert sha(PARENT/'src/dune')=='8c83177da0f8e73850c8cb44d69c5bfb905a0ff29f2180eee272416d6d975e23'
assert sha(R385/'aeneas-r385-private-return-carrier-v2-candidate')=='f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
assert expected['source_sha256']['R419_candidate.llbc']=='7f82eaabe855e89d735b21f9af5f6a983abea6b2f4d93d4b8bae747abd2829e2'
assert sha(R419_INPUT)==expected['source_sha256']['R419_candidate.llbc']
exe=ROOT/'src/_build/default/UnitConstantExecutionFixture.exe'
assert sha(exe)==build['fixture_executable_sha256']
for rel,want in expected['source_sha256'].items():
    source=R419_INPUT if rel=='R419_candidate.llbc' else ROOT/rel
    assert want and sha(source)==want,(rel,'source changed since the focused build')
    dest=AUDIT/'source'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(source.read_bytes())
assert expected['expected_assertions']==8 and expected['success_marker']=='R425 unit execution checks passed: 8'
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemAvailable','MemTotal','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
active_units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
active_containers=subprocess.check_output(['docker','ps','--no-trunc'],text=True)
name='aspis-r425-unit-execution-fixture-run-v1'
assert name not in subprocess.check_output(['docker','ps','-a','--format','{{.Names}}'],text=True)
image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
assert subprocess.check_output(['docker','image','inspect','ef96e46342a4','--format','{{.Id}}'],text=True).strip()==image
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr425.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
(AUDIT/'reservation-before.json').write_text(json.dumps({'meminfo':mem,'active_units':active_units,'active_containers':active_containers},indent=2)+'\n')
inner='set -eu; /usr/bin/time -v -o /work/candidate-audit/r425-unit-execution-fixture-run-v1/gnu-time.txt /work/src/_build/default/UnitConstantExecutionFixture.exe /input/candidate.llbc'
argv=['docker','run','--name',name,'--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','--cgroup-parent=aspisr425.slice','-v',str(ROOT)+':/work','-v',str(R419_INPUT.parent)+':/input:ro',image,'bash','-lc',inner]
(AUDIT/'command.json').write_text(json.dumps({'argv':argv,'inner_command':inner,'source_revision':expected['source_revision'],'source_sha256':expected['source_sha256'],'fixture_executable_sha256':build['fixture_executable_sha256'],'expected_assertions':8,'expected_marker':expected['success_marker'],'lead_approved':expected['lead_approved'],'expected_work':'Execute the focused evaluator fixture once on the exact R419 LLBC after its build passes. No rebuild, translation, or Lean job.','axioms':'NA: OCaml runtime fixture, not Lean.'},indent=2)+'\n')
start=time.monotonic()
with (AUDIT/'raw.log').open('w') as f:result=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT)
(AUDIT/'docker-inspect.json').write_text(subprocess.check_output(['docker','inspect',name],text=True))
raw=(AUDIT/'raw.log').read_text();markers=re.findall(r'R425 unit execution checks passed: (\d+)',raw)
ok=result.returncode==0 and markers==['8']
(AUDIT/'result.json').write_text(json.dumps({'exit_status':result.returncode,'wrapper_wall_seconds':time.monotonic()-start,'assertions_passed':int(markers[0]) if markers else None,'success_marker_count':len(markers),'all_checks_passed':ok,'raw_log_sha256':sha(AUDIT/'raw.log'),'source_revision':expected['source_revision'],'source_sha256':expected['source_sha256'],'boundary':'Finite evaluator/context/continuation checks on exact R419 LLBC; not universal interpreter correctness or callback execution.'},indent=2)+'\n')
print(raw);print((AUDIT/'result.json').read_text());sys.exit(0 if ok else (result.returncode or 1))
