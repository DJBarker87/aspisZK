"""PREPARED ONLY: build a uniquely named R425 main binary after fixture pass."""
import hashlib,json,pathlib,subprocess,sys,time

ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a')
PARENT=pathlib.Path('/home/dombarker/project-offloads/aspis-r424-concrete-associated-types-candidate-20261002-a')
R385=pathlib.Path('/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a')
R419_INPUT=pathlib.Path('/home/dombarker/project-offloads/aspis-r419-native-20261002-a/aspis-r419-candidate-1790967913444473000/candidate.llbc')
AUDIT=ROOT/'candidate-audit/r425-main-build-v1'
INPUT=pathlib.Path('/tmp/aspis-r425-main-build-inputs.json')
EXEC=ROOT/'candidate-audit/r425-unit-fixture-execution-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected=json.loads(INPUT.read_text())
assert not AUDIT.exists(),'refuse to overwrite prior main-build evidence'
assert expected['lead_approved_fixture_gate'] is True,'lead-approved fixture gate missing'
fixture=json.loads((EXEC/'result.json').read_text())
assert fixture['exit_status']==0 and fixture['all_checks_passed'] is True
assert fixture['assertions_passed']==11 and fixture['success_marker_count']==1
assert fixture['source_sha256']['src/dune']=='ab5b25c59440e7cfe1c1ca6fb83ccba46e14368bf2dafa60c4a8d18e8d5c0ded'
assert expected['source_sha256']['src/dune']=='0d37f4f57c2920077ec9594da2e8881c91408afb000e01e6222e73695f808ef0'
for rel,h in fixture['source_sha256'].items():
    if rel != 'src/dune': assert expected['source_sha256'].get(rel)==h, (rel,'11-check fixture source changed')
raw=(EXEC/'raw.log').read_text()
assert 'R425 unit constant fixture assertions passed: 11' in raw
assert sha(EXEC/'raw.log')==fixture['raw_log_sha256']
secondary=expected['secondary_fixture']
assert secondary['receipt_relative_path'] not in ('','UNRESOLVED')
assert secondary['expected_assertions']==8
assert secondary['expected_marker'] not in ('','UNRESOLVED')
assert secondary['source_sha256'] and all(v not in ('','UNRESOLVED') for v in secondary['source_sha256'].values())
secondary_dir=ROOT/secondary['receipt_relative_path']
fixture8=json.loads((secondary_dir/'result.json').read_text())
assert fixture8['exit_status']==0 and fixture8['all_checks_passed'] is True
assert fixture8['assertions_passed']==8 and fixture8['success_marker_count']==1
assert fixture8['source_sha256']==secondary['source_sha256']
raw8=(secondary_dir/'raw.log').read_text()
assert secondary['expected_marker'] in raw8
assert sha(secondary_dir/'raw.log')==fixture8['raw_log_sha256']
assert sha(PARENT/'src/interp/InterpExpressions.ml')=='531b0ee1c6d26d463d07c6e1dbdc75a7cce32cf970adcbc59dfafd75bfdd914f'
assert sha(PARENT/'src/dune')=='8c83177da0f8e73850c8cb44d69c5bfb905a0ff29f2180eee272416d6d975e23'
assert sha(R385/'aeneas-r385-private-return-carrier-v2-candidate')=='f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
for rel,want in expected['source_sha256'].items():
    source=R419_INPUT if rel=='R419_candidate.llbc' else ROOT/rel
    assert want and sha(source)==want,(rel,'source hash mismatch')
    dest=AUDIT/'source'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(source.read_bytes())
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemAvailable','MemTotal','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
active_units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
active_containers=subprocess.check_output(['docker','ps','--no-trunc'],text=True)
name='aspis-r425-main-build-v1'
assert name not in subprocess.check_output(['docker','ps','-a','--format','{{.Names}}'],text=True)
image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
assert subprocess.check_output(['docker','image','inspect','ef96e46342a4','--format','{{.Id}}'],text=True).strip()==image
binary=ROOT/'aeneas-r425-unit-constant-candidate'
assert not binary.exists(),'refuse to overwrite an existing candidate binary'
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr425.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
(AUDIT/'reservation-before.json').write_text(json.dumps({'meminfo':mem,'active_units':active_units,'active_containers':active_containers},indent=2)+'\n')
inner='set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v -o /work/candidate-audit/r425-main-build-v1/gnu-time.txt env AENEAS_VERSION=aspis-r425-unit-constant-candidate OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-r425-unit-constant-candidate; chmod 755 /work/aeneas-r425-unit-constant-candidate'
argv=['docker','run','--name',name,'--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','--cgroup-parent=aspisr425.slice','-v',str(ROOT)+':/work',image,'bash','-lc',inner]
(AUDIT/'command.json').write_text(json.dumps({'argv':argv,'inner_command':inner,'source_revision':expected['source_revision'],'source_sha256':expected['source_sha256'],'target':'main.exe plus unique aeneas-r425-unit-constant-candidate','fixture11_receipt_sha256':sha(EXEC/'result.json'),'fixture11_log_sha256':sha(EXEC/'raw.log'),'fixture11_assertions':11,'fixture8_receipt_sha256':sha(secondary_dir/'result.json'),'fixture8_log_sha256':sha(secondary_dir/'raw.log'),'fixture8_assertions':8,'expected_work':'Build main.exe only after exact 11-check unit fixture and 8-check context fixture receipts pass; unique binary output avoids replacing earlier candidates. No translation or Lean job.','axioms':'NA: OCaml compilation only'},indent=2)+'\n')
start=time.monotonic()
with (AUDIT/'build.log').open('w') as f:result=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT)
(AUDIT/'docker-inspect.json').write_text(subprocess.check_output(['docker','inspect',name],text=True))
outsha=sha(binary) if binary.is_file() else None
(AUDIT/'result.json').write_text(json.dumps({'exit_status':result.returncode,'wrapper_wall_seconds':time.monotonic()-start,'metrics':'Compiler GNU-time report in gnu-time.txt; wrapper wall/RSS are not substituted.','source_revision':expected['source_revision'],'source_sha256':expected['source_sha256'],'binary_path':str(binary),'binary_sha256':outsha,'fixture11_receipt_sha256':sha(EXEC/'result.json'),'fixture8_receipt_sha256':sha(secondary_dir/'result.json'),'boundary':'Main executable build only; no translation or Lean job.'},indent=2)+'\n')
print((AUDIT/'build.log').read_text());print((AUDIT/'result.json').read_text());sys.exit(result.returncode)
