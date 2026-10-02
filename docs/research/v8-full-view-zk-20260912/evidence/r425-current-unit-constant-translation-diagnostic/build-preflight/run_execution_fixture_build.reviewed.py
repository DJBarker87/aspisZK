"""PREPARED ONLY: build the focused native R425 unit-constant fixture."""
import hashlib, json, pathlib, subprocess, sys, time

ROOT = pathlib.Path('/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a')
PARENT = pathlib.Path('/home/dombarker/project-offloads/aspis-r424-concrete-associated-types-candidate-20261002-a')
R385 = pathlib.Path('/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a')
R419_INPUT = pathlib.Path('/home/dombarker/project-offloads/aspis-r419-native-20261002-a/aspis-r419-candidate-1790967913444473000/candidate.llbc')
AUDIT = ROOT / 'candidate-audit/r425-unit-execution-fixture-build-v1'
INPUT = pathlib.Path('/tmp/aspis-r425-unit-execution-fixture-build-inputs.json')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
expected = json.loads(INPUT.read_text())
assert not AUDIT.exists(), 'refuse to overwrite prior phase evidence'
for rel, h in {
    'src/interp/InterpExpressions.ml':'531b0ee1c6d26d463d07c6e1dbdc75a7cce32cf970adcbc59dfafd75bfdd914f',
    'src/dune':'8c83177da0f8e73850c8cb44d69c5bfb905a0ff29f2180eee272416d6d975e23',
}.items(): assert sha(PARENT/rel)==h, ('R424 parent source changed',rel)
assert sha(R385/'aeneas-r385-private-return-carrier-v2-candidate') == 'f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
for required in ('candidate-audit/r425-unit-helper-v1/result.json','candidate-audit/r425-unit-integration-v1/result.json'):
    receipt=json.loads((ROOT/required).read_text()); assert receipt['exit_status']==0, required
for rel,want in expected['source_sha256'].items():
    source = R419_INPUT if rel == 'R419_candidate.llbc' else ROOT/rel
    assert want and sha(source)==want, (rel,'source hash mismatch')
    dest=AUDIT/'source'/rel; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(source.read_bytes())
assert expected['source_sha256']['src/UnitConstantExecutionFixture.ml'] == 'a9bab4cc922e59626755995d37bd080b8c227a42ede7b1987f33a38228214dbb'
assert expected['expected_assertions'] == 8
assert expected['source_sha256']['R419_candidate.llbc'] == '7f82eaabe855e89d735b21f9af5f6a983abea6b2f4d93d4b8bae747abd2829e2'
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemAvailable','MemTotal','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
active_units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
active_containers=subprocess.check_output(['docker','ps','--no-trunc'],text=True)
name='aspis-r425-unit-execution-fixture-build-v1'
assert name not in subprocess.check_output(['docker','ps','-a','--format','{{.Names}}'],text=True)
image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
assert subprocess.check_output(['docker','image','inspect','ef96e46342a4','--format','{{.Id}}'],text=True).strip()==image
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr425.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
(AUDIT/'reservation-before.json').write_text(json.dumps({'meminfo':mem,'active_units':active_units,'active_containers':active_containers,'slice':subprocess.check_output(['systemctl','show','aspisr425.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax'],text=True)},indent=2)+'\n')
inner='set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v -o /work/candidate-audit/r425-unit-execution-fixture-build-v1/gnu-time.txt env AENEAS_VERSION=aspis-r425-unit-constant-candidate OCAMLPARAM=_,ccopt=-static opam exec -- dune build UnitConstantExecutionFixture.exe --profile release -j 1'
argv=['docker','run','--name',name,'--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','--cgroup-parent=aspisr425.slice','-v',str(ROOT)+':/work',image,'bash','-lc',inner]
(AUDIT/'command.json').write_text(json.dumps({'argv':argv,'inner_command':inner,'source_revision':expected['source_revision'],'source_sha256':expected['source_sha256'],'target':'UnitConstantExecutionFixture.exe','expected_assertions':8,'expected_marker':'R425 unit execution checks passed: 8','expected_work':'Build only the focused native test executable. Do not execute the fixture, build main.exe, translate, or run Lean.','axioms':'NA: OCaml compilation only'},indent=2)+'\n')
start=time.monotonic()
with (AUDIT/'build.log').open('w') as f: result=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT)
(AUDIT/'docker-inspect.json').write_text(subprocess.check_output(['docker','inspect',name],text=True))
exe=ROOT/'src/_build/default/UnitConstantExecutionFixture.exe'
exe_hash=sha(exe) if exe.is_file() else None
(AUDIT/'result.json').write_text(json.dumps({'exit_status':result.returncode,'wrapper_wall_seconds':time.monotonic()-start,'metrics':'Compiler GNU-time report in gnu-time.txt; wrapper wall/RSS are not substituted.','source_revision':expected['source_revision'],'source_sha256':expected['source_sha256'],'fixture_executable':str(exe),'fixture_executable_sha256':exe_hash,'boundary':'Focused fixture build only; no assertions have been executed.'},indent=2)+'\n')
print((AUDIT/'build.log').read_text()); print((AUDIT/'result.json').read_text()); sys.exit(result.returncode)
