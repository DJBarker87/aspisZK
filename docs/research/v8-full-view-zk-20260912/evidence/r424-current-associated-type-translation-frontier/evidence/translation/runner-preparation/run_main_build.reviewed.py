#!/usr/bin/env python3
"""R424 main.exe changed-source build runner. Preparation artifact; do not execute before lead approval."""
import hashlib, json, os, pathlib, subprocess, time

ROOT = pathlib.Path('/home/dombarker/project-offloads/aspis-r424-concrete-associated-types-candidate-20261002-a')
PARENT = pathlib.Path('/home/dombarker/project-offloads/aspis-r385-private-return-carrier-candidate-20261002-a')
AUDIT = ROOT / 'candidate-audit/r424-main-build-v1'
BINARY_OUT = ROOT / 'aeneas-r424-concrete-associated-types-candidate'
IMAGE = 'ef96e46342a4'
IMAGE_ID = 'sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
LAUNCH_REVISION = os.environ.get('R424_BUILD_LAUNCH_REVISION', '')
EXPECTED = {
    'src/llbc/ConcreteAssociatedTypes.ml': '48336b273fafc9fec71686f15896976cddf1a41367a5556749af0f13437ef4cf',
    'src/dune': '8c83177da0f8e73850c8cb44d69c5bfb905a0ff29f2180eee272416d6d975e23',
    'src/ConcreteAssociatedTypesFixture.ml': 'c9e5bd6ee4da45efab2f9406d4d1022c42a77286d2096816746a37359c378177',
    'source-fixtures/R396PrivateBatchUnmonomorphized.llbc': '399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae',
    'src/interp/InterpUtils.ml': '8b885a725def3c7a923cc634f05a7b91bd25b4334b62b2ba6a1d09faf0d8a65a',
}
PARENT_INTERP = '23c4394d0a7328d590e9092f813a1c372d7ef989d646375db65bb4ec9d5d03e1'
PARENT_BINARY = 'f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
CANDIDATE_SOURCE_REVISION = 'a3fe5df6b53caa52322339906642de5064fc2bbb'
FIXTURE_EXE = ROOT / 'src/_build/default/ConcreteAssociatedTypesFixture.exe'
FIXTURE_RECEIPT = ROOT / 'candidate-audit/r424-fixture-execution-v1/receipt.json'
FIXTURE_LOG = ROOT / 'candidate-audit/r424-fixture-execution-v1/raw.log'
FIXTURE_LLBC_SHA = '399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert len(LAUNCH_REVISION) == 40 and all(c in '0123456789abcdef' for c in LAUNCH_REVISION), LAUNCH_REVISION
assert LAUNCH_REVISION == CANDIDATE_SOURCE_REVISION
assert ROOT.is_dir() and PARENT.is_dir() and (ROOT / 'src').is_dir()
assert not AUDIT.exists() and not BINARY_OUT.exists()
for rel, expected in EXPECTED.items():
    assert sha(ROOT / rel) == expected, (rel, sha(ROOT / rel), expected)
assert sha(PARENT / 'src/interp/InterpUtils.ml') == PARENT_INTERP
assert sha(PARENT / 'aeneas-r385-private-return-carrier-v2-candidate') == PARENT_BINARY
assert sha(ROOT / 'src/_build/default/main.exe') == PARENT_BINARY
# Mandatory evidence gate: the exact reviewed fixture must have run successfully
# against this candidate source, fixture executable, and frozen R396 input.
assert FIXTURE_RECEIPT.is_file(), f'missing PASS fixture execution receipt: {FIXTURE_RECEIPT}'
assert FIXTURE_LOG.is_file(), f'missing fixture execution log: {FIXTURE_LOG}'
fixture_receipt = json.loads(FIXTURE_RECEIPT.read_text())
assert fixture_receipt.get('all_checks_passed') is True, fixture_receipt
assert fixture_receipt.get('exit_status') == 0, fixture_receipt
assert fixture_receipt.get('source_revision') == CANDIDATE_SOURCE_REVISION, fixture_receipt
assert fixture_receipt.get('source_sha256', {}).get('source-fixtures/R396PrivateBatchUnmonomorphized.llbc') == FIXTURE_LLBC_SHA, fixture_receipt
assert fixture_receipt.get('exe_sha256') == sha(FIXTURE_EXE), fixture_receipt
assert fixture_receipt.get('raw_log_sha256') == sha(FIXTURE_LOG), fixture_receipt
assert 'R424 fixture assertions passed: 14' in FIXTURE_LOG.read_text()
assert fixture_receipt.get('assertions_passed') == 14, fixture_receipt
assert fixture_receipt.get('target') == 'ConcreteAssociatedTypesFixture.exe against exact frozen R396 input', fixture_receipt
assert fixture_receipt.get('argv', [])[-1:] == [str(ROOT / 'source-fixtures/R396PrivateBatchUnmonomorphized.llbc')], fixture_receipt
expected_fixture_sources = {
    'src/llbc/ConcreteAssociatedTypes.ml': EXPECTED['src/llbc/ConcreteAssociatedTypes.ml'],
    'src/dune': EXPECTED['src/dune'],
    'src/interp/InterpUtils.ml': EXPECTED['src/interp/InterpUtils.ml'],
    'src/ConcreteAssociatedTypesFixture.ml': EXPECTED['src/ConcreteAssociatedTypesFixture.ml'],
    'source-fixtures/R396PrivateBatchUnmonomorphized.llbc': FIXTURE_LLBC_SHA,
}
assert fixture_receipt.get('source_sha256') == expected_fixture_sources, fixture_receipt
FIXTURE_RECEIPT_SHA = sha(FIXTURE_RECEIPT)
image = subprocess.check_output(['docker','image','inspect',IMAGE,'--format','{{.Id}} {{.Size}}'],text=True).strip()
assert image.startswith(IMAGE_ID + ' '), image
AUDIT.mkdir(parents=True)
mem = lambda: {k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
before = mem(); assert int(before['MemAvailable'].split()[0]) >= 24*1024*1024, before
services = subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
docker_before = subprocess.check_output(['docker','ps','--no-trunc','--format','{{.ID}} {{.Names}} {{.Status}}'],text=True)
assert not subprocess.check_output(['docker','ps','-a','--filter','name=aspis-r424-main-build-v1','--format','{{.ID}} {{.Names}}'],text=True).strip()
pre = {'source_revision': LAUNCH_REVISION, 'candidate_root':str(ROOT), 'parent_root':str(PARENT),
       'candidate_source_sha256':{rel:sha(ROOT/rel) for rel in EXPECTED},
       'parent_InterpUtils_sha256':sha(PARENT/'src/interp/InterpUtils.ml'),
       'parent_binary_sha256':sha(PARENT/'aeneas-r385-private-return-carrier-v2-candidate'),
       'candidate_cached_main_exe_sha256':sha(ROOT/'src/_build/default/main.exe'),
       'meminfo_before':before, 'active_user_services':services, 'active_docker_containers':docker_before,
       'docker_image_inspect':image,
       'systemd_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},
       'docker_caps':{'memory_reservation':'5g','memory':'7g','memory_swap':'7g (equal to memory; no swap)','pids_limit':128,'network':'none','cgroup_parent':'aspisr424.slice'},
       'expected_work':'Dune release build of main.exe from cached candidate; static native link. No source edits, translation, or Lean.',
       'fixture_execution_gate':{'receipt_path':str(FIXTURE_RECEIPT),'receipt_sha256':FIXTURE_RECEIPT_SHA,'raw_log_sha256':sha(FIXTURE_LOG),'fixture_executable_sha256':sha(FIXTURE_EXE),'input_llbc_sha256':FIXTURE_LLBC_SHA,'assertions_passed':14,'all_checks_passed':True,'exit_status':0,'receipt_schema':'R424 fixture execution v1'}}
(AUDIT/'build-host-reservation-before.json').write_text(json.dumps(pre,indent=2)+'\n')
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr424.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
pre['R424_slice_before']=subprocess.check_output(['systemctl','show','aspisr424.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(AUDIT/'build-host-reservation-before.json').write_text(json.dumps(pre,indent=2)+'\n')
inner = "set -eu; cd /work/src; export OPAMJOBS=1 DUNEJOBS=1; /usr/bin/time -v -o /work/candidate-audit/r424-main-build-v1/compiler-gnu-time.txt env AENEAS_VERSION=aspis-r424-concrete-associated-types-candidate-20261002-a OCAMLPARAM=_,ccopt=-static opam exec -- dune build main.exe --profile release -j 1; cp _build/default/main.exe /work/aeneas-r424-concrete-associated-types-candidate; chmod 755 /work/aeneas-r424-concrete-associated-types-candidate"
docker_cmd = ['docker','run','--name','aspis-r424-main-build-v1','--network','none','--memory-reservation=5g','--memory=7g','--memory-swap=7g','--pids-limit=128','--cgroup-parent=aspisr424.slice','-v',str(ROOT)+':/work',IMAGE,'bash','-lc',inner]
(AUDIT/'build-command.json').write_text(json.dumps({'docker_argv':docker_cmd,'inner_build_command':inner,'docker_image_id':IMAGE_ID,'profile':'dune build main.exe --profile release -j 1','optimization':'Dune release; static native link','parallelism':{'OPAMJOBS':1,'DUNEJOBS':1,'dune_jobs':1},'source_revision':LAUNCH_REVISION,'source_hashes':pre['candidate_source_sha256'],'parent_interputils_sha256':PARENT_INTERP,'fixture_execution_receipt_sha256':FIXTURE_RECEIPT_SHA,'fixture_executable_sha256':sha(FIXTURE_EXE),'fixture_input_llbc_sha256':FIXTURE_LLBC_SHA,'parent_binary_sha256':PARENT_BINARY,'container_cgroup_peak_authoritative':True,'docker_cli_rss_label':'Docker CLI parent-process RSS only; not compiler or container RSS','compiler_gnu_time':'candidate-audit/r424-main-build-v1/compiler-gnu-time.txt','translation_or_Lean':False},indent=2)+'\n')
cli_time=AUDIT/'docker-cli-time.txt'; log=AUDIT/'build.log'
with log.open('w') as f:
    proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(cli_time),*docker_cmd],stdout=f,stderr=subprocess.STDOUT,text=True)
    samples=[]; paths=set()
    while proc.poll() is None:
        try:
            info=json.loads(subprocess.check_output(['docker','inspect','aspis-r424-main-build-v1'],stderr=subprocess.DEVNULL,text=True))[0]
            pid=info.get('State',{}).get('Pid',0)
            if pid:
                line=next((x for x in pathlib.Path(f'/proc/{pid}/cgroup').read_text().splitlines() if x.startswith('0::')),'')
                if line:
                    cg=pathlib.Path('/sys/fs/cgroup')/line.split('::',1)[1].lstrip('/'); paths.add(str(cg)); sample={'pid':pid,'cgroup':str(cg)}
                    for key in ('memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events'):
                        try: sample[key]=(cg/key).read_text().strip()
                        except OSError: pass
                    samples.append(sample)
        except Exception as e: samples.append({'sample_error':type(e).__name__})
        time.sleep(.2)
status=proc.returncode
try: inspect=json.loads(subprocess.check_output(['docker','inspect','aspis-r424-main-build-v1'],text=True))
except subprocess.CalledProcessError: inspect=[]
(AUDIT/'docker-inspect.json').write_text(json.dumps(inspect,indent=2)+'\n')
(AUDIT/'cgroup-samples.json').write_text(json.dumps({'samples':samples,'observed_container_cgroup_paths':sorted(paths)},indent=2)+'\n')
def maxval(k):
    vals=[]
    for s in samples:
        try: vals.append(int(s[k]))
        except (KeyError,ValueError): pass
    return max(vals) if vals else None
binary_sha=sha(BINARY_OUT) if BINARY_OUT.is_file() else None
assert sha(PARENT/'src/interp/InterpUtils.ml')==PARENT_INTERP
assert {rel:sha(ROOT/rel) for rel in EXPECTED}==EXPECTED
result={'build_exit_status':status,'source_revision':LAUNCH_REVISION,'docker_image_id':IMAGE_ID,
        'candidate_source_sha256':{rel:sha(ROOT/rel) for rel in EXPECTED},'fixture_execution_receipt_sha256':FIXTURE_RECEIPT_SHA,'fixture_execution_status':fixture_receipt['all_checks_passed'],'fixture_executable_sha256':sha(FIXTURE_EXE),'fixture_input_llbc_sha256':FIXTURE_LLBC_SHA,'parent_InterpUtils_sha256_after':sha(PARENT/'src/interp/InterpUtils.ml'),
        'compiler_gnu_time_report_path':'candidate-audit/r424-main-build-v1/compiler-gnu-time.txt',
        'docker_cli_time_rss_boundary':'Docker CLI parent-process RSS only; not aggregate compiler or container RSS',
        'container_cgroup_samples':len(samples),'observed_container_cgroup_paths':sorted(paths),
        'sampled_container_memory_peak_bytes':maxval('memory.peak'),'sampled_container_memory_swap_peak_bytes':maxval('memory.swap.peak'),
        'candidate_binary_exists':BINARY_OUT.is_file(),'candidate_binary_sha256':binary_sha,
        'candidate_binary_size_bytes':BINARY_OUT.stat().st_size if BINARY_OUT.is_file() else None,
        'translation_or_Lean_run':False}
(AUDIT/'build-result.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(status)
