#!/usr/bin/env python3
"""One capped candidate validation stage; caller must run inside a systemd scope."""
import argparse, hashlib, json, os, pathlib, signal, subprocess, time

p=argparse.ArgumentParser()
p.add_argument('workspace',type=pathlib.Path)
p.add_argument('stage',choices=['counter','native-gate','r18-harness','sbf','replay'])
p.add_argument('--label',required=True)
a=p.parse_args()
w=a.workspace.resolve(); src=w/'source'; runs=w/'runs'; out=runs/a.label
assert src.is_dir() and (w/'input-manifest.json').is_file()
assert not out.exists(), f'refusing existing output {out}'
manifest=json.loads((w/'input-manifest.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
sha_file=lambda f:sha(pathlib.Path(f).read_bytes())
assert manifest['base_revision']=='a8930e677bc745854b9f693b5628c8a8bd2ac848'
for rel,digest in manifest['files'].items():
    assert sha_file(src/rel)==digest, rel
# Inputs outside the source archive are individually pinned here.
fixtures=w/'full-random-fixtures'
fixture_pins={
 'transfer.proof.bin':'c34c1c6e30f7ad2751b5872801845a8ee0aca9959056d84058c234c4415575c6',
 'transfer.public.bin':'d2241c5432fa3d5b34084c06e9c3f510cc61542a793287aad471287563761557',
 'withdrawal.proof.bin':'c6a15d1063f060b3ff1f7edbfd88301429c2a9a9ed8da47482556971a863ac07',
 'withdrawal.public.bin':'aacd276edc3cdfedfb8bcba5ebb443305b6c8be72a4262704181fd2b6ffaac01',
}
for name,digest in fixture_pins.items(): assert sha_file(fixtures/name)==digest,name
p3=src/'docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task'
assert sha_file(p3/'r1-s2-proof.bin')=='8569435667420b36a980493477f8fef7ef47e7351122647cf3747054079d4d62'
assert sha_file(p3/'r1-s2-public-asf8.bin')=='72f067d263af326b017284579f30e3da7c843c6cbb29f1c6df94c8afbb1f2172'
# Verify exact retained baseline artifact and original source-build receipt before any stage.
baseline=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-regression-20261016/after-sbf-fresh-artifacts/aspis_r1_cost_probe_program.so')
assert sha_file(baseline)=='2c031d0040a3bf739b58591b2a20dc68f04722550fd49b79d4fd7eb8e5dfee9f'
baseline_receipt=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-regression-20261016/runs/after-sbf-fresh/receipt.json')
assert json.loads(baseline_receipt.read_text())['artifacts']['after-sbf-fresh-artifacts/aspis_r1_cost_probe_program.so']==sha_file(baseline)
# Verify current scope cap and stop if any other Rust/Lean/Aeneas compiler is active.
cg=pathlib.Path('/sys/fs/cgroup')/next(x.split(':',2)[2].lstrip('/') for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
read=lambda n:(cg/n).read_text().strip()
limits={n:read(n) for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':'8589934592','memory.max':'10737418240','memory.swap.max':'0','pids.max':'128'},limits
ps=subprocess.check_output(['ps','-eo','pid=,rss=,comm=,args='],text=True)
active=[]; allowed_lean=[]; scopes={}
for line in ps.splitlines():
    cols=line.strip().split(None,3)
    if len(cols)<3: continue
    pid,rss,comm=cols[:3]; args=cols[3] if len(cols)>3 else ''
    if comm not in {'cargo','rustc','lean','lean4','aeneas','charon','charon-driver','cargo-build-sbf'}: continue
    if str(w) in args: raise RuntimeError('refusing concurrent writer in candidate workspace: '+line)
    cgroup_rel=next(x.split(':',2)[2].lstrip('/') for x in pathlib.Path(f'/proc/{pid}/cgroup').read_text().splitlines() if x.startswith('0::'))
    cgroup_path=pathlib.Path('/sys/fs/cgroup')/cgroup_rel
    other_limits={k:(cgroup_path/k).read_text().strip() for k in ['memory.max','memory.swap.max']}
    assert other_limits['memory.max']!='max' and other_limits['memory.swap.max']=='0',(line,other_limits)
    item={'pid':int(pid),'rss_kib':int(rss),'comm':comm,'args':args,'cgroup':cgroup_rel,'limits':other_limits}
    scopes[cgroup_rel]=int(other_limits['memory.max'])
    if comm=='lean': allowed_lean.append(item)
    else: active.append(item)
lean_scope_maxima={x['cgroup']:scopes[x['cgroup']] for x in allowed_lean}
own_mask_scopes={path:value for path,value in lean_scope_maxima.items() if 'aspis-r1-mask-lean432-20261015' in path}
other_lean_max=sum(value for path,value in lean_scope_maxima.items() if path not in own_mask_scopes)/(1024**3)
own_mask_max=sum(own_mask_scopes.values())/(1024**3)
external_max=sum(value for key,value in scopes.items() if not any(x['cgroup']==key for x in allowed_lean))/(1024**3)
external_reserve=max(24,external_max)
aggregate_reservation=external_reserve+other_lean_max+6+10
assert own_mask_max<=6 and external_max<=24 and aggregate_reservation<=50,(own_mask_max,other_lean_max,external_max,aggregate_reservation,active,allowed_lean)
source_rev=manifest['base_revision']
target=w/'cargo-target'; assert target.is_dir()
sol=pathlib.Path('/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin')
cargo=pathlib.Path('/home/dombarker/.cargo/bin/cargo')
env=dict(os.environ)
env.update(PATH=f'{sol}:/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(target),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',ASPIS_SOURCE_REVISION=source_rev)
for key in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS']: env.pop(key,None)
if a.stage=='counter':
    command=[str(cargo),'test','--release','--locked','--offline','--manifest-path',str(src/'Cargo.toml'),'-p','aspis-r1-cost-probe-program','--features','pool-adapter,private-leaf-salts','--jobs','1','measured_core_call_counts_include_zero_progress_checkpoint','--','--test-threads=1']
    expected='cached optimized compilation and focused call-count regression; no proof generation'
elif a.stage=='native-gate':
    out.mkdir(parents=True)
    nativeout=out/'native-gate';
    command=[str(cargo),'run','--release','--locked','--offline','--manifest-path',str(src/'Cargo.toml'),'-p','aspis-r1-cost-probe','--features','prover,private-leaf-salts','--jobs','1','--example','native_gate','--','S2',str(nativeout),str(fixtures)]
    expected='optimized native full-random transfer/withdrawal verifier, dense comparison, 5,675-case mutation corpus; saved proofs only, no proof generation'
elif a.stage=='r18-harness':
    command=[str(cargo),'build','--release','--locked','--offline','--manifest-path',str(src/'tools/r1-cost-probe/Cargo.toml'),'--features','private-leaf-salts','--jobs','1','--bin','r18_replay']
    expected='compile current pinned 3/7 r18 replay harness only; no proof generation'
elif a.stage=='sbf':
    out.mkdir(parents=True); artifacts=out/'artifacts'; artifacts.mkdir()
    command=[str(sol/'cargo-build-sbf'),'--manifest-path',str(src/'programs/r1-cost-probe/Cargo.toml'),'--sbf-out-dir',str(artifacts),'--features','pool-adapter,private-leaf-salts','--tools-version','v1.52','--skip-tools-install','--offline','--','--locked','-j','1']
    expected='incremental candidate SBF compilation/link only; no proof generation or deployment'
else:
    out.mkdir(parents=True); replayout=out/'r18-output'
    binary=target/'release/r18_replay'; assert binary.is_file()
    after=w/'runs/candidate-sbf/artifacts/aspis_r1_cost_probe_program.so'; assert sha_file(after)!='2c031d0040a3bf739b58591b2a20dc68f04722550fd49b79d4fd7eb8e5dfee9f'
    after_receipt=w/'runs/candidate-sbf/receipt.json'; assert after_receipt.is_file()
    env.update(ASPIS_R18_BEFORE_REVISION='42e5ca2011c39ee9770afc798282ff861b092428',ASPIS_R18_AFTER_REVISION=source_rev,ASPIS_R18_BEFORE_BUILD_RECEIPT=str(baseline_receipt),ASPIS_R18_AFTER_BUILD_RECEIPT=str(after_receipt))
    command=[str(binary),str(baseline),str(after),str(p3/'r1-s2-proof.bin'),str(p3/'r1-s2-public-asf8.bin'),str(replayout)]
    expected='one before/after paired 3/7 route CU comparison on retained transfer-1023 fixture; no proof generation'
out.mkdir(parents=True,exist_ok=True)
(out/'runner.py').write_bytes(pathlib.Path(__file__).read_bytes())
timepath=out/'time.log'
timed=['/usr/bin/time','-v','-o',str(timepath),*command]
resource={
 'unit_cgroup':str(cg),'limits':limits,'current_memory_bytes':int(read('memory.current')),
 'memory_events_before':read('memory.events'),'process_table_compiler_filter':active,'allowed_concurrent_lean_job':allowed_lean,'observed_other_compiler_scopes_gib':external_max,'observed_lean_scopes_gib':other_lean_max,'observed_own_mask_scope_gib':own_mask_max,
 'host_memory':subprocess.check_output(['free','-b'],text=True),
 'disk':subprocess.check_output(['df','-B1',str(w)],text=True),
 'reservation_contract_gib':{'external_floor':24,'observed_external_max':external_max,'observed_external_reserve':external_reserve,'unrelated_lean_max':other_lean_max,'own_mask_lean_reserve':6,'this_stage_max':10,'aggregate':aggregate_reservation,'safe_limit':50},
 'active_build_processes_before':active,'allowed_concurrent_lean_job':allowed_lean,'observed_other_compiler_scopes_gib':external_max,'observed_lean_scopes_gib':other_lean_max,'observed_own_mask_scope_gib':own_mask_max,
}
(out/'resource-preflight.json').write_text(json.dumps(resource,indent=2)+'\n')
record={'stage':a.stage,'label':a.label,'source_revision':source_rev,'source_input_manifest_sha256':sha_file(w/'input-manifest.json'),'candidate_files':manifest['candidate_overlay'],'workspace_relative_file_count':len(manifest['files']),'baseline_elf_sha256':sha_file(baseline),'baseline_receipt_sha256':sha_file(baseline_receipt),'fixture_pins':fixture_pins,'p3_replay_fixture':{'proof_sha256':sha_file(p3/'r1-s2-proof.bin'),'public_sha256':sha_file(p3/'r1-s2-public-asf8.bin')},'command':timed,'cwd':str(src),'environment':{k:env[k] for k in ['PATH','CARGO_TARGET_DIR','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','ASPIS_SOURCE_REVISION']},'rustc_version':subprocess.check_output(['rustc','-Vv'],env=env,text=True),'cargo_version':subprocess.check_output([str(cargo),'-V'],env=env,text=True),'cargo_build_sbf_sha256':sha_file(sol/'cargo-build-sbf'),'expected_work':expected,'resource_preflight_sha256':sha_file(out/'resource-preflight.json'),'keys_retained':True,'proof_generation':False}
(out/'preflight.json').write_text(json.dumps(record,indent=2)+'\n')
start=time.monotonic(); peak=0
with (out/'build.log').open('w') as log:
    proc=subprocess.Popen(timed,cwd=src,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    while proc.poll() is None:
        peak=max(peak,int(read('memory.current')))
        if time.monotonic()-start>600:
            os.killpg(proc.pid,signal.SIGKILL)
            record['review_point']='600 seconds; terminated for mandatory review; no automatic retry'
            break
        time.sleep(.5)
    proc.wait()
record.update(exit=proc.returncode,wall_seconds=time.monotonic()-start,sampled_peak_bytes=peak,cgroup_peak_bytes=int(read('memory.peak')),swap_current_bytes=int(read('memory.swap.current')),memory_events_after=read('memory.events'))
if a.stage=='sbf':
    artifact=out/'artifacts/aspis_r1_cost_probe_program.so'
    record['artifact_sha256']=sha_file(artifact) if artifact.exists() else None
    record['keypair_files']=[str(p) for p in (out/'artifacts').glob('*keypair*')]
if a.stage=='r18-harness':
    binary=target/'release/r18_replay';record['harness_sha256']=sha_file(binary) if binary.exists() else None
if a.stage=='replay' and (out/'r18-output').exists(): record['replay_files']={p.name:sha_file(p) for p in (out/'r18-output').iterdir() if p.is_file()}
(out/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record.get(k) for k in ['stage','exit','wall_seconds','sampled_peak_bytes','cgroup_peak_bytes','swap_current_bytes','artifact_sha256','harness_sha256']},indent=2),flush=True)
raise SystemExit(proc.returncode)
