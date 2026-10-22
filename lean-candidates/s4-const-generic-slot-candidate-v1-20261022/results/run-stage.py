from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, time
W=Path(__file__).resolve().parent
C=json.loads((W/'config.json').read_text())
PHASE=sys.argv[1]
assert PHASE in C['phases']
G=1024**3
CG=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits={k:(CG/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
want=C['phases'][PHASE]
assert limits=={'memory.high':str(want['memory_high_bytes']),'memory.max':str(want['memory_max_bytes']),'memory.swap.max':'0'},limits
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
H=Path(C['baseline_root']); O=Path(C['candidate_root'])

def run(cmd,cwd,env,folder,timeout):
    folder.mkdir(parents=True,exist_ok=False)
    (folder/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
    before=(CG/'memory.events').read_text();start=time.monotonic()
    with (folder/'output.log').open('w') as log:
        result=subprocess.run(['/usr/bin/time','-v','-o',str(folder/'time.log'),*cmd],cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
    timing=(folder/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
    rec={'exit_status':result.returncode,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m[1]) if m else None,'scope_peak_bytes':int((CG/'memory.peak').read_text()),'swap_current_bytes':int((CG/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(CG/'memory.events').read_text(),'limits':limits}
    (folder/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
    if result.returncode: raise SystemExit(result.returncode)
    return rec

if PHASE=='native':
    assert (O/'src/crates/aspis-r1-cost-probe/src/fast_dots.rs').is_file()
    assert sha(O/'src/crates/aspis-r1-cost-probe/src/fast_dots.rs')==C['candidate_sources']['crates/aspis-r1-cost-probe/src/fast_dots.rs']
    env=dict(os.environ);env.update(CARGO_TARGET_DIR=str(O/'native-target'),CARGO_NET_OFFLINE='true',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin')
    for k in ('RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID'):env.pop(k,None)
    cmd=['cargo','test','--release','--offline','--locked','-p','aspis-r1-cost-probe','--test','dots_equivalence']
    rec=run(cmd,O/'src',env,W/'native-evidence',600)
    fd=O / "src/crates/aspis-r1-cost-probe/src/fast_dots.rs"
    rec.update({"candidate_fast_dots_sha256":sha(fd),"classification":"candidate-only optimized native dots equivalence"})
    (W/'native-evidence/receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec),flush=True)
elif PHASE=='build':
    assert sha(H/'src/crates/aspis-r1-cost-probe/src/fast_dots.rs')==C['baseline_fast_dots_sha256']
    base=json.loads((W/C['baseline_source_manifest']).read_text())
    assert base['source_revision']==C['baseline_source_revision']
    for rel,expected in base['files'].items(): assert sha(H/'src'/rel)==expected,rel
    assert sha(H/'artifacts/default/aspis_r1_cost_probe_program.so')==C['baseline_artifact_sha256']
    assert not (O/'src').exists() and not (O/'sbf-target-verifier').exists()
    start=time.monotonic()
    O.mkdir(parents=True,exist_ok=False)
    shutil.copytree(H/'src',O/'src',symlinks=True,ignore=shutil.ignore_patterns('.git','target'))
    subprocess.run(['cp','-a','--reflink=auto',str(H/'sbf-target-verifier'),str(O/'sbf-target-verifier')],check=True,timeout=120)
    subprocess.run(['cp','-a','--reflink=auto','/home/dombarker/project-offloads/s4-combined-candidate-20261021/work/native-target',str(O/'native-target')],check=True,timeout=120)
    candidate_hashes={}
    for rel,expected in C['candidate_sources'].items():
        candidate=W/'candidate-files'/Path(rel).name
        assert candidate.is_file() and sha(candidate)==expected,(rel,sha(candidate),expected)
        dest=O/'src'/rel
        assert dest.is_file()
        dest.write_bytes(candidate.read_bytes())
        candidate_hashes[rel]=expected
    changes={}
    for rel,expected in base['files'].items():
        actual=sha(O/'src'/rel)
        if actual!=expected: changes[rel]={'before':expected,'after':actual}
    assert set(changes)==set(C['candidate_sources']),changes
    assert {p:changes[p]['after'] for p in changes}==C['candidate_sources']
    artifact_dir=O/'artifacts';artifact_dir.mkdir()
    env=dict(os.environ);env.update(CARGO_TARGET_DIR=str(O/'sbf-target-verifier'),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin')
    for k in ('RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID'):env.pop(k,None)
    cmd=[C['build_tool'],'--manifest-path',str(O/'src/programs/r1-cost-probe/Cargo.toml'),'--sbf-out-dir',str(artifact_dir),'--features','pool-adapter,private-leaf-salts','--skip-tools-install','--offline','-j','4','--','--locked']
    (W/'build-preflight.json').write_text(json.dumps({'candidate_source_revision':C['source_revision'],'baseline_revision':C['baseline_source_revision'],'baseline_source_hashes_sha256':C['baseline_source_hashes_sha256'],'candidate_sources':candidate_hashes,'baseline_artifact_sha256':C['baseline_artifact_sha256'],'changed_files':changes,'cache_seed':str(H/'sbf-target-verifier'),'limits':limits,'preparation_seconds':round(time.monotonic()-start,3),'time_expected':C['expected_work']['build'],'command':cmd},indent=2)+'\n')
    env_run=env.copy()
    rec=run(cmd,O/'src',env_run,W/'build-evidence',300)
    so=artifact_dir/'aspis_r1_cost_probe_program.so'
    rec.update({'candidate_artifact_sha256':sha(so),'candidate_artifact_bytes':so.stat().st_size,'classification':'candidate-only optimized build; no equivalence claim'})
    (W/'build-evidence/receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec),flush=True)
else:
    artifact=O/'artifacts/aspis_r1_cost_probe_program.so'
    assert artifact.is_file()
    assert sha(artifact)==json.loads((W/'build-evidence/receipt.json').read_text())['candidate_artifact_sha256']
    assert sha(W/C['baseline_runs_file'])==C['baseline_runs_sha256']
    assert sha(W/'verifier-strict-stack.py')==C['strict_stack_script_sha256']
    cases=[x for x in json.loads((W/C['baseline_runs_file']).read_text()) if x['name'].startswith('cu-')]
    b1_rows=json.loads((W/C['b1_file']).read_text())
    b1={x['fixture']:x for x in b1_rows}
    assert len(cases)==6
    env=dict(os.environ);env['PATH']='/home/dombarker/.cargo/bin:/usr/bin:/bin'
    rows=[];E=W/'gate-evidence';E.mkdir(exist_ok=True)
    for case in cases:
        name=case['name'];cmd=case['command'].copy();baseline=json.loads(Path(cmd[4]).read_text())
        out=O/'runs'/name;out.mkdir(parents=True,exist_ok=True)
        cmd[0]=C['gate_tool'];cmd[2]=str(artifact);cmd[4]=str(out/'evidence.json');cmd[5]=str(out/'task')
        if (E/name/'receipt.json').is_file() and (out/'evidence.json').is_file():
            rec=json.loads((E/name/'receipt.json').read_text())
        else:
            rec=run(cmd,W,env,E/name,60)
        data=json.loads((out/'evidence.json').read_text());actual=data['execution'];expected=baseline['execution']
        fixture=name.removeprefix('cu-')
        limits_b1=b1[fixture]
        stage1=actual.get('stage1_compute_units');settlement=actual.get('compute_units')
        row={'name':name,'execution_error':actual.get('error'),'stage1_error':actual.get('stage1_error'),'baseline_stage1_cu':expected['stage1_compute_units'],'candidate_stage1_cu':stage1,'stage1_delta':stage1-expected['stage1_compute_units'] if stage1 is not None else None,'b1_stage1_cu':limits_b1['b1_stage1'],'stage1_item1_pass':stage1 is not None and stage1<=limits_b1['b1_stage1'],'baseline_settlement_cu':expected['compute_units'],'candidate_settlement_cu':settlement,'settlement_delta':settlement-expected['compute_units'] if settlement is not None else None,'b1_settlement_cu':limits_b1['b1_settlement'],'settlement_item1_pass':settlement is not None and settlement<=limits_b1['b1_settlement']+10000,'stage1_checkpoint_tail_same':actual.get('stage1_checkpoint_tail_sha256')==expected['stage1_checkpoint_tail_sha256'],'return_data_same':actual.get('return_data_sha256')==expected['return_data_sha256'],'gate_receipt':rec}
        row['item1_pass']=row['stage1_item1_pass'] and row['settlement_item1_pass']
        rows.append(row)
    stack=W/'stack';stack.mkdir(exist_ok=True)
    shutil.copy(O/'sbf-target-verifier/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so',stack/'linked.elf')
    shutil.copy(artifact,stack/'stripped.so')
    shutil.copy(W/'build-evidence/output.log',stack/'build.log')
    strict=W/'verifier-strict-stack.py'
    stackrec=run(['python3',str(strict),str(stack)],W,env,E/'strict-stack',60)
    result={'classification':'isolated candidate; not adopted; frozen/live workspace unchanged','baseline_revision':C['baseline_source_revision'],'candidate_base_revision':C['source_revision'],'baseline_fast_dots_sha256':C['baseline_fast_dots_sha256'],'candidate_sources':C['candidate_sources'],'candidate_artifact_sha256':sha(artifact),'candidate_artifact_bytes':artifact.stat().st_size,'six_fixture_rows':rows,'item1_all_six_pass':all(x['item1_pass'] for x in rows),'all_six_outputs_match':all(x['stage1_checkpoint_tail_same'] and x['return_data_same'] for x in rows),'strict_stack_receipt':stackrec,'limits':limits}
    (W/'gate-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
