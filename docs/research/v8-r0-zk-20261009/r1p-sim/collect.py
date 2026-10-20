#!/usr/bin/env python3
"""Collect host timing, test, pin and final Lean packet evidence; no builds."""
import pathlib, subprocess, json, hashlib, re
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
HOST='dombarker@100.108.41.90'
H='/home/dombarker/project-offloads/codex-cx-sim-bin-20261020'
files=['crates/aspis-r1-cost-probe/'+x for x in ['src/sim.rs','src/sim_tests.rs','examples/r1p_sim_gate.rs','src/compact.rs','src/multiproof.rs','src/prover.rs','src/verifier.rs','src/dense.rs']]
script='''import pathlib,json,hashlib,platform,subprocess
H=pathlib.Path(HH); files=FILES
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
logs={n:(H/n).read_text() for n in ['time-build.txt','time-tests.txt','time-gate.txt','time-overlap.txt','rust.log','overlap.log']}
print(json.dumps(dict(host=platform.node(),platform=platform.platform(),rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-Vv'],text=True),logs=logs,gate=json.loads((H/'gate.json').read_text()),sources={f:pin(H/'repo'/f) for f in files},artifacts={'r1p_sim_gate':pin(H/'target/release/examples/r1p_sim_gate')})))
'''.replace('HH',repr(H)).replace('FILES',repr(files))
r=subprocess.run(['ssh',HOST,'python3 -'],input=script,text=True,capture_output=True,check=True)
e=json.loads(r.stdout)
for f,pin in e['sources'].items():
    assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==pin['sha256'],f
logs=e.pop('logs'); times={}
for name in ['build','tests','gate','overlap']:
    log=logs[f'time-{name}.txt']
    def value(pattern):
        m=re.search(pattern,log);return m.group(1) if m else None
    times[name]=dict(wall=value(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=int(value(r'Maximum resident set size \(kbytes\): (\d+)')),swaps=int(value(r'Swaps: (\d+)')),exit=int(value(r'Exit status: (\d+)')),time_log=log)
assert all(v['exit']==0 for v in times.values())
for row in e['gate']['runs']:
    assert row['verified_strict_and_dense_under_programmed_oracle'] and row['real_hash_strict_rejected'] and row['real_hash_dense_rejected']
    assert row['programmed_addresses']==row['programmed_addresses_read_by_verifier']==row['transcript_reads']+row['commitment_reads']
    assert row['proof_bytes']==57607 and row['transcript_reads']==115
assert '3 passed; 0 failed; 0 ignored' in logs['rust.log']
assert '1 passed; 0 failed; 0 ignored' in logs['overlap.log']
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
e.update(schema='aspis-binary-simulator-evidence-v1',source_revision=rev,source_dirty=True,times=times,host_workspace=H,
    build_scope=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,parallel_jobs=4,RUSTFLAGS='-C link-arg=-Wl,--threads=4',profile='release',initial_reservation_gib=28.375,overlap_reservation_gib=32.375),
    commands=dict(build='cargo build --release -j 4 -p aspis-r1-cost-probe --features r1p-check --example r1p_sim_gate',tests='cargo test --release -j 4 -p aspis-r1-cost-probe --features r1p-check --lib sim::tests -- --nocapture',gate=f'{H}/target/release/examples/r1p_sim_gate 4 {H}/gate.json',overlap='cargo test --release -j 4 -p aspis-r1-cost-probe --features r1p-check --lib sim::tests::binary_batches_share_consistent_programmed_nodes -- --exact --nocapture'),
    test_output='\n'.join(l for l in logs['rust.log'].splitlines() if l.startswith(('test sim::','test result:','R1SIM_RUN'))),
    overlap_output='\n'.join(l for l in logs['overlap.log'].splitlines() if l.startswith(('test sim::','test result:'))))
(HERE/'evidence.json').write_text(json.dumps(e,indent=2)+'\n')
records=[json.loads(x) for x in (HERE/'attempts.jsonl').read_text().splitlines()]
modules=['R1Z.SimulatorSupportBin','R1Z.SimulatorLogR1PBin','R1Z.PrivacySimulatorBin']
targets=[]
for m in modules:
    p=ROOT/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean')
    sha=hashlib.sha256(p.read_bytes()).hexdigest()
    r=next(r for r in reversed(records) if r['module']==m and r['source_sha256']==sha and r['exit']==0)
    assert r['axioms']
    for line in r['axioms']:
        reported=re.search(r'depends on axioms: \[(.*?)\]',line)
        assert reported and set(reported.group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'},line
    targets.append({k:r[k] for k in ['module','attempt','source_sha256','deps_fingerprint','exit','wall','peak_rss_kib','swaps','axioms','source_revision']})
manifest=dict(schema='focused-extractor-proof-packet-v1',tree='privacy',environment='J',source_revision=rev,source_dirty=True,targets=targets,attempts='attempts.jsonl',rust='evidence.json',checks=dict(source_hashes_match=True,standard_axioms_only=True,no_existing_lean_module_changed=True),note='No package replay: only new support, binary log bridge, and dependent privacy root; inherited Bin objects retained. Final root rebuilt after strengthened log bridge (6105 -> 6106).')
(HERE/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(times=times,runs=e['gate']['runs'],lean=targets),indent=2))
