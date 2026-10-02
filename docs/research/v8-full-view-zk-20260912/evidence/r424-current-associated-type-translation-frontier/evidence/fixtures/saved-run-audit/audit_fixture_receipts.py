#!/usr/bin/env python3
"""Read-only validation of saved R424 fixture build and execution records."""
import hashlib,json,pathlib,re,subprocess
base=pathlib.Path('.r21-scratch/r424-trait-projection-regions-frontier/build-preflight')
fx=pathlib.Path('.r21-scratch/r424-trait-projection-regions-frontier/fixtures')
root=base.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
expected_rev='a3fe5df6b53caa52322339906642de5064fc2bbb'
expected_inputs={
 'src/llbc/ConcreteAssociatedTypes.ml':'48336b273fafc9fec71686f15896976cddf1a41367a5556749af0f13437ef4cf',
 'src/dune':'8c83177da0f8e73850c8cb44d69c5bfb905a0ff29f2180eee272416d6d975e23',
 'src/interp/InterpUtils.ml':'8b885a725def3c7a923cc634f05a7b91bd25b4334b62b2ba6a1d09faf0d8a65a',
 'src/ConcreteAssociatedTypesFixture.ml':'c9e5bd6ee4da45efab2f9406d4d1022c42a77286d2096816746a37359c378177',
 'source-fixtures/R396PrivateBatchUnmonomorphized.llbc':'399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae',
}
def load(name,file):return json.loads((base/name/file).read_text())
def parse_gnu(path):
 t=path.read_text()
 return {'wall':re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)',t).group(1),
 'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t).group(1)),
 'swaps':int(re.search(r'Swaps: (\d+)',t).group(1)),
 'exit':int(re.search(r'Exit status: (\d+)',t).group(1)), 'sha256':sha(path)}
runs=[]
for name,wall,rss,status,signature in [
 ('r424-fixture-build-v1','1:25.40',590092,1,'TraitImplId.Map.find_exn'),
 ('r424-fixture-build-v2','0:00.66',211416,1,'AssocTypeId.Map.find'),
 ('r424-fixture-build-v3','0:01.34',254976,0,''),
]:
 p=base/name; cmd=load(name,'command.json'); rec=load(name,'metrics-receipt.json'); result=load(name,'result.json'); g=parse_gnu(p/'gnu-time.txt')
 snapshot={rel:sha(p/'source'/rel) for rel in cmd['source_sha256']}
 checks={
  'source_revision_is_campaign_head':cmd.get('source_revision')==rec.get('source_revision')==result.get('source_revision')==head==expected_rev,
  'source_hashmaps_match':cmd.get('source_sha256')==rec.get('source_sha256')==result.get('source_sha256'),
  'source_snapshots_match_declared_hashes':snapshot==cmd.get('source_sha256'),
  'raw_GNUtime_matches_receipt':g['wall']==rec.get('wall_time') and g['rss_kib']==rec.get('peak_rss_kib') and g['swaps']==rec.get('swaps')==0 and g['exit']==rec.get('exit_status')==result.get('exit_status')==status and g['sha256']==rec.get('raw_metrics_sha256'),
  'unique_target_and_caps':cmd.get('target')=='ConcreteAssociatedTypesFixture.exe' and 'aspis-r424-typed-fixture-build-'+name[-2:] in cmd['argv'] and '--memory-reservation=5g' in cmd['argv'] and '--memory=7g' in cmd['argv'] and '--memory-swap=7g' in cmd['argv'] and '--pids-limit=128' in cmd['argv'] and '--network' in cmd['argv'] and 'none' in cmd['argv'],
  'log_matches_attempt':(signature in (p/'build.log').read_text()) if status else ('Error:' not in (p/'build.log').read_text()),
  'docker_inspect_matches_exit_and_caps':False,
 }
 docker=json.loads((p/'docker-inspect.json').read_text());docker=docker[0] if isinstance(docker,list) else docker
 hc=docker.get('HostConfig',{});st=docker.get('State',{})
 checks['docker_inspect_matches_exit_and_caps']=st.get('ExitCode')==status and st.get('OOMKilled') is False and hc.get('MemoryReservation')==5368709120 and hc.get('Memory')==7516192768 and hc.get('MemorySwap')==7516192768 and hc.get('PidsLimit')==128 and hc.get('CgroupParent')=='aspisr424.slice' and hc.get('NetworkMode')=='none'
 reservation=json.loads((p/'reservation-before.json').read_text())
 checks['systemd_caps_match']=reservation.get('root_slice')=='MemoryHigh=5368709120\nMemoryMax=7516192768\nMemorySwapMax=0\nTasksMax=128\n'
 checks['result_boundary_says_build_only']='build only' in result.get('boundary','').lower()
 expected_boundary={'r424-fixture-build-v1':'Fixture executable compilation failed at the Map API call. No fixture executable was produced and no assertions ran.','r424-fixture-build-v2':'Fixture executable compilation failed on the associated-item map type annotation. No fixture executable was produced and no assertions ran.','r424-fixture-build-v3':'The focused ConcreteAssociatedTypesFixture executable compiled successfully. This build phase did not run fixture assertions.'}[name]
 checks['corrected_boundary_matches_phase']=rec.get('proved_boundary')==expected_boundary
 runs.append({'name':name,'target':cmd['target'],'status':status,'metrics':g,'source_snapshots':snapshot,'checks':checks,
  'receipt_boundary_text':rec.get('proved_boundary'),'result_boundary':result.get('boundary'),'checks_pass':all(checks.values())})
# final launch source equality and successful executable/input receipts
v3inputs=json.loads((base/'fixture-build-v3-inputs.json').read_text())
exe_record=(base/'fixture-v3-executable-checksum.txt').read_text().splitlines()
exe_sha='a8f7fec43708590d256b7a4f313bb63814f9075deb77ef064768ba13318c055f'
exe_match=any(line.startswith(exe_sha+'  ') and line.endswith('/ConcreteAssociatedTypesFixture.exe') for line in exe_record)
ep=base/'r424-fixture-execution-v1'; ec=load('r424-fixture-execution-v1','command.json'); er=load('r424-fixture-execution-v1','receipt.json'); em=load('r424-fixture-execution-v1','metrics-receipt.json')
raw=(ep/'raw.log').read_bytes(); rawtext=raw.decode(errors='replace'); g=parse_gnu(ep/'raw.log')
exec_checks={
 'source_and_input_hashes_match_build_v3':ec.get('source_sha256')==er.get('source_sha256')==em.get('source_sha256')==v3inputs.get('source_sha256')==expected_inputs,
 'source_revision_matches_head':ec.get('source_revision')==er.get('source_revision')==em.get('source_revision')==head==expected_rev,
 'exe_digest_matches_all_receipts':ec.get('exe_sha256')==er.get('exe_sha256')==em.get('exe_sha256')==exe_sha,
 'saved_exe_checksum_matches':exe_match,
 'command_targets_exe_and_exact_R396_file':ec.get('argv',[None,None,None,None])[2].endswith('/ConcreteAssociatedTypesFixture.exe') and ec.get('argv',[None,None,None,None])[3].endswith('/R396PrivateBatchUnmonomorphized.llbc'),
 'raw_log_hash_matches_receipts':sha(ep/'raw.log')==er.get('raw_log_sha256')==em.get('raw_metrics_sha256'),
 'raw_GNUtime_matches_execution_metrics':g['wall']==em.get('wall_time')=='0:00.08' and g['rss_kib']==em.get('peak_rss_kib')==42944 and g['swaps']==em.get('swaps')==0 and g['exit']==em.get('exit_status')==er.get('exit_status')==0,
 'all_14_assertions_passed': 'R424 fixture assertions passed: 14' in rawtext and er.get('assertions_passed')==em.get('assertions_passed')==14 and er.get('all_checks_passed') is True,
 'run_receipt_caps_match':er.get('caps')=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},
}
# Versioned fixture sources: reviewed.ml is v1, reviewed-v2 is v2, reviewed-v3 is the successful build source.
fixture_source=fx/'ConcreteAssociatedTypesFixture.reviewed-v3.ml'
exec_checks['reviewed_v3_source_matches_build_snapshot']=sha(fixture_source)==expected_inputs['src/ConcreteAssociatedTypesFixture.ml']
exec_checks['v1_v2_source_copies_match_failed_attempts']=sha(fx/'ConcreteAssociatedTypesFixture.reviewed.ml')==load('r424-fixture-build-v1','command.json')['source_sha256']['src/ConcreteAssociatedTypesFixture.ml'] and sha(fx/'ConcreteAssociatedTypesFixture.reviewed-v2.ml')==load('r424-fixture-build-v2','command.json')['source_sha256']['src/ConcreteAssociatedTypesFixture.ml']
exec_checks['R396_local_input_hash_matches']=sha(pathlib.Path('.r21-scratch/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc'))==expected_inputs['source-fixtures/R396PrivateBatchUnmonomorphized.llbc']
# Execution has a named systemd service launch record but no separate cgroup/Docker inspect receipt.
launch=(base/'fixture-execution-v1-launch.log').read_text()
exec_checks['launch_record_names_execution_unit']='aspis-r424-fixture-execution-v1.service' in launch
obj={
 'scope':'Read-only saved-evidence audit for R424 fixture build attempts v1-v3 and one fixture execution.',
 'repository_head':head,'expected_source_revision':expected_rev,'build_attempts':runs,
 'build_receipt_correction_history':'The original misleading build-receipt bytes are archived under build-preflight/history/fixture-boundary-correction-v1 and checksummed. Current phase-specific receipts distinguish failed v1/v2 compile, successful v3 executable build, and separate execution.',
 'fixture_execution':{'exe_sha256':exe_sha,'assertions':14,'raw_metrics':g,'checks':exec_checks,'checks_pass':all(exec_checks.values()),'execution_cap_evidence':'receipt records 5G/7G/0swap/128; launch transcript identifies systemd unit. There is no separate systemctl property snapshot or Docker inspect for this native execution scope.'},
 'artifact_checksum_file_sha256':sha(base/'fixture-v3-executable-checksum.txt'),
 'fixture_v3_source_hashes':v3inputs['source_sha256'],
 'boundary':'Finite fixture executable built and run once; exactly fourteen assertions passed against the frozen R396 LLBC. This does not prove universal GAT/binder correctness, compiler semantics/source correspondence, actual callback execution, translation success, Lean theorems, or security.',
 'missing_or_inconsistent_metadata':['The execution receipt records systemd limits, and launch log names the service, but no separate captured systemctl properties/after-run cgroup inspection is present.','Artifact hash is saved; executable bytes are not included in this evidence folder.'],
 'all_run_checks_pass':all(x['checks_pass'] for x in runs) and all(exec_checks.values()) and exe_match,
}
out=fx/'saved-run-audit/audit.json';out.write_text(json.dumps(obj,indent=2)+'\n')
lines=['# R424 fixture build and execution audit','',f"Saved receipt/source/metric checks: {'PASS' if obj['all_run_checks_pass'] else 'FAIL'}.",'',
 'Three build attempts are retained. v1 failed at `TraitImplId.Map.find_exn`; v2 failed on the associated-item map type annotation; v3 built the dedicated `ConcreteAssociatedTypesFixture.exe` target successfully. The v3 target/source revision and all five source/input hashes match the saved input manifest and snapshots.', '',
 '- v1: exit 1, 1:25.40, 590,092 KiB RSS, 0 swaps.',
 '- v2: exit 1, 0.66 s, 211,416 KiB RSS, 0 swaps.',
 '- v3: exit 0, 1.34 s, 254,976 KiB RSS, 0 swaps.', '',
 'The saved execution command used executable SHA256 `'+exe_sha+'` with exact R396 input SHA256 `'+expected_inputs['source-fixtures/R396PrivateBatchUnmonomorphized.llbc']+'`. It exited 0 in 0.08 s at 42,944 KiB RSS with zero swaps; the raw output reports all 14 assertions passed. The command/receipt source hashes agree with the successful v3 build inputs. The execution receipt records the 5G/7G/zero-swap/128-task limits, and the launch transcript names the systemd unit; there is no separate cgroup-property snapshot for that execution scope.', '',
 'The original v1/v2/v3 metrics receipts are preserved byte-for-byte under `build-preflight/history/fixture-boundary-correction-v1/`; their stale boundary strings claimed assertion success during build phases. Current metrics receipts now state phase-correct boundaries. The v1 and v2 failure logs remain unchanged, and the separate execution log is the sole 14-assertion result. Fixture source revisions are archived: `reviewed.ml` is v1 (Map API failure), `reviewed-v2.ml` is v2 (type annotation failure), and `reviewed-v3.ml` is the exact successful v3 source.', '',
 'This establishes only a finite fixture build and one execution against the frozen LLBC. It does not establish universal binder/GAT correctness, compiler/source correspondence, actual callback execution, translation success, Lean theorems, or security.', '']
(fx/'saved-run-audit/REPORT.md').write_text('\n'.join(lines))
print(json.dumps({'all_run_checks_pass':obj['all_run_checks_pass'],'build_runs':[{'name':r['name'],'metrics':r['metrics'],'checks_pass':r['checks_pass'],'failed_checks':[k for k,v in r['checks'].items() if not v]} for r in runs],'execution':{'metrics':g,'checks':exec_checks,'checks_pass':all(exec_checks.values())},'exe_checksum_record':exe_match},indent=2))
