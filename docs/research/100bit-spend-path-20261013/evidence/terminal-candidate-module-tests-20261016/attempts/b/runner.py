#!/usr/bin/env python3
import hashlib, json, os, pathlib, subprocess, time

W = pathlib.Path('/home/dombarker/project-offloads/aspis-r1-terminal-copy-indexed-20261016')
SRC = W / 'source'
OUT = W / 'runs/candidate-terminal-module-tests-b'
MANIFEST = W / 'input-manifest.json'
EXPECT = {
 'crates/aspis-statement/src/lib.rs': 'fd7a32a1dd9755925f318388f5895d2cd129c6697aa5969a403014e86249353b',
 'crates/aspis-statement/src/state_only_poseidon.rs': '4324116f9e652d31190037ab7c5205f3107991143e4a2bbca701346b0bba66ba',
 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs': '41da553efb32cc342a7002ecdee8ba1909e1531dfa2b6facc95983495135c7cc',
}
sha = lambda b: hashlib.sha256(b).hexdigest()
sha_file = lambda p: sha(pathlib.Path(p).read_bytes())
assert not OUT.exists(), f'refusing existing output: {OUT}'
manifest = json.loads(MANIFEST.read_text())
assert manifest['base_revision'] == 'a8930e677bc745854b9f693b5628c8a8bd2ac848'
assert manifest['candidate_overlay'] == EXPECT
for rel, digest in manifest['files'].items():
    assert sha_file(SRC / rel) == digest, f'input manifest mismatch: {rel}'
for rel, digest in EXPECT.items():
    assert sha_file(SRC / rel) == digest, f'candidate source mismatch: {rel}'

cg = pathlib.Path('/sys/fs/cgroup') / next(x.split(':',2)[2].lstrip('/') for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
read = lambda name: (cg/name).read_text().strip()
limits = {name:read(name) for name in ('memory.high','memory.max','memory.swap.max','pids.max')}
assert limits == {'memory.high':'8589934592','memory.max':'10737418240','memory.swap.max':'0','pids.max':'128'}, limits

# The explicit non-repository build scope is recorded separately from the 24 GiB external floor.
active_build_scopes=[]
for line in subprocess.check_output(['ps','-eo','pid=,rss=,comm=,args='], text=True).splitlines():
    cols=line.strip().split(None,3)
    if len(cols)<3: continue
    pid,rss,comm=cols[:3]; args=cols[3] if len(cols)>3 else ''
    if comm not in {'cargo','rustc','lean','lean4','aeneas','charon','charon-driver','cargo-build-sbf'}: continue
    proccg=pathlib.Path(f'/proc/{pid}/cgroup').read_text()
    rel=next(x.split(':',2)[2].lstrip('/') for x in proccg.splitlines() if x.startswith('0::'))
    maxv=(pathlib.Path('/sys/fs/cgroup')/rel/'memory.max').read_text().strip()
    if maxv!='max': active_build_scopes.append({'pid':int(pid),'rss_kib':int(rss),'comm':comm,'args':args,'cgroup':rel,'memory_max':maxv})
assert not active_build_scopes, active_build_scopes

cargo=pathlib.Path('/home/dombarker/.cargo/bin/cargo')
target=W/'cargo-target'
env=dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(target),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',ASPIS_SOURCE_REVISION=manifest['base_revision'])
for key in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS'): env.pop(key,None)
filters=['state_only_poseidon::tests','pool_v1::pair_forest_semantic_terminal::tests']
commands=[]
for filter_name in filters:
    commands.append([str(cargo),'test','--release','--locked','--offline','--manifest-path',str(SRC/'Cargo.toml'),'-p','aspis-statement','--features','pool-v1-kernel','--lib',filter_name,'--','--test-threads=1'])
OUT.mkdir(parents=True)
preflight={
 'label':'candidate-terminal-module-tests-a', 'source_revision':manifest['base_revision'],
 'source_input_manifest_sha256':sha_file(MANIFEST), 'source_file_pins':{rel:sha_file(SRC/rel) for rel in EXPECT},
 'workspace_relative_file_count':len(manifest['files']), 'commands':commands,
 'cwd':str(SRC), 'cargo_version':subprocess.check_output([str(cargo),'-V'],env=env,text=True),
 'rustc_version':subprocess.check_output(['rustc','-Vv'],env=env,text=True),
 'environment':{k:env[k] for k in ('PATH','CARGO_TARGET_DIR','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','ASPIS_SOURCE_REVISION')},
 'cgroup':str(cg), 'limits':limits, 'active_external_compiler_scopes':active_build_scopes,
 'reservation_contract_gib':{'external_minimum':24,'other_active_build_scope':0,'own_lean_reserved':6,'this_rust_scope_max':10,'aggregate':40,'safe_limit':50},
 'expected_work':'incremental optimized statement unit-test compilation if needed, then focused module tests; no SBF build, proof generation, or key generation',
 'test_scope':'state-only Poseidon tests including random off-domain reference checks; pair-forest semantic terminal module tests including randomized off-domain factorization and Boolean-row checks'
}
(OUT/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
results=[]
for i,command in enumerate(commands):
    log=OUT/f'test-{i+1}.log'; tlog=OUT/f'test-{i+1}-time.log'
    timed=['/usr/bin/time','-v','-o',str(tlog),*command]
    start=time.monotonic(); peak=0
    with log.open('w') as f:
        proc=subprocess.Popen(timed,cwd=SRC,env=env,stdout=f,stderr=subprocess.STDOUT)
        while proc.poll() is None:
            peak=max(peak,int(read('memory.current')))
            if time.monotonic()-start>600:
                proc.kill(); proc.wait(); raise TimeoutError(f'600 second review point exceeded for {filter_name}')
            time.sleep(.5)
    result={'filter':filters[i],'exit':proc.returncode,'wall_seconds':time.monotonic()-start,'sampled_peak_bytes':peak,'cgroup_peak_bytes':int(read('memory.peak')),'swap_current_bytes':int(read('memory.swap.current')),'command':timed,'log_sha256':sha_file(log),'time_log_sha256':sha_file(tlog)}
    results.append(result)
    if proc.returncode != 0: break
receipt={'preflight_sha256':sha_file(OUT/'preflight.json'),'results':results,'all_passed':len(results)==len(commands) and all(x['exit']==0 for x in results),'memory_events_after':read('memory.events')}
(OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
raise SystemExit(0 if receipt['all_passed'] else 1)
