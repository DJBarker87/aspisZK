#!/usr/bin/env python3
"""Host-only, serial D83 gates. Every cargo command has its own capped scope."""
import hashlib, json, os, pathlib, shutil, subprocess, sys, time
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref2-20261021')
S=R/'gates-source'; E=R/'gates'; E.mkdir(exist_ok=True)
env=os.environ.copy(); env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(R/'gate-target'),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
C=['--release','--locked','--offline','-j','4']
def run(label, args):
    d=E/label
    if (d/'receipt.json').exists():
        assert json.loads((d/'receipt.json').read_text())['exit']==0
        print(label, 'reuse completed receipt (no rerun)', flush=True); return
    d.mkdir(exist_ok=True)
    while True:
        reserved=0
        for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
            try:
                v=p.read_text().strip()
                if v!='max' and (p.parent/'cgroup.procs').read_text().strip(): reserved+=int(v)
            except OSError: pass
        if reserved+8*2**30 <=55*2**30: break
        with (E/'reservation-waits.jsonl').open('a') as f:
            f.write(json.dumps(dict(label=label,reservation_bytes=reserved,time=time.time()))+'\n')
        print(label, 'waiting for 8 GiB reservation:', reserved, flush=True)
        time.sleep(20)
    cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(d/'time.log'),'timeout','1800']+args
    t=time.monotonic()
    with (d/'stdout.log').open('w') as out, (d/'stderr.log').open('w') as err:
        ex=subprocess.run(cmd,cwd=S,env=env,stdout=out,stderr=err).returncode
    rec=dict(label=label,command=args,cwd=str(S),exit=ex,wall=time.monotonic()-t,reservation_bytes=reserved,source_revision='5b1a6582b + candidate validator when labelled after',validator_sha256=hashlib.sha256((S/'crates/aspis-statement/src/pool_v1/pair_forest_trace.rs').read_bytes()).hexdigest(),time_log=(d/'time.log').read_text(),stdout_sha256=hashlib.sha256((d/'stdout.log').read_bytes()).hexdigest(),stdout_bytes=(d/'stdout.log').stat().st_size,axioms='N/A: Rust gate',scope=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
    (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n'); print(label,ex,flush=True)
    assert ex==0,(label,(d/'stderr.log').read_text()[-4000:])
def masked(label): run(label,['cargo','run']+C+['-p','aspis-r1-cost-probe','--features','prover,private-leaf-salts','--example','masked_fixture_gate','--',str(E/label/'fixtures')])
def codec(label): run(label,['cargo','run']+C+['-p','aspis-statement','--features','r0,pool-v1-kernel','--example','j1_terminal_codec_trace'])
F=pathlib.Path('/home/dombarker/project-offloads/codex-cx-pin-20261020/runs/adopt/transfer-1023/task')
def ordered(label): run(label,['cargo','run']+C+['--manifest-path','tools/r1-hash-input-counter/Cargo.toml','--',str(F/'r1-s2-proof.bin'),str(F/'r1-s2-public-asf8.bin'),str(E/label/'counter.json'),'D83'])
masked('before-masked'); codec('before-codec'); ordered('before-ordered')
(S/'crates/aspis-statement/src/pool_v1/pair_forest_trace.rs').write_bytes((R/'candidate-validator.rs').read_bytes())
masked('after-masked'); codec('after-codec'); ordered('after-ordered')
for name in ['S2-transfer','S2-withdrawal']:
    for f in ['proof.bin','public.bin']:
        assert (E/'before-masked/fixtures'/name/f).read_bytes()==(E/'after-masked/fixtures'/name/f).read_bytes(),(name,f)
assert (E/'before-codec/stdout.log').read_bytes()==(E/'after-codec/stdout.log').read_bytes()
before=json.loads((E/'before-ordered/counter.json').read_text())
after=json.loads((E/'after-ordered/counter.json').read_text())
# This summary is emitted from a randomized HashMap; D70 compares it as a multiset.
# The actual ordered_digest_calls list is left in its original order.
for doc in [before, after]:
    doc['hash_input_counts']['repeated_exact_inputs'].sort(key=lambda x: json.dumps(x,sort_keys=True))
assert before==after
(E/'identity-comparison.json').write_text(json.dumps(dict(masked_proofs='byte-identical S2 transfer and withdrawal',publics='byte-identical',codec='byte-identical',ordered_trace='all ordered entries identical; only repeated_exact_inputs summary compared as multiset per D70'),indent=2)+'\n')
# Standalone harness uses the pinned sibling crate layout expected by its manifest.
G=R/'glue-workspace'; G.mkdir(exist_ok=True)
(G/'Cargo.toml').write_text('[workspace]\nmembers=["diffharness"]\nresolver="2"\n')
harness=G/'diffharness'
if harness.is_symlink(): harness.unlink()
if not harness.exists(): shutil.copytree(S/'docs/research/v8-r0-zk-20261009/refine/diffharness',harness)
# Only dependency paths change; the two glue test sources stay byte-identical.
manifest=(harness/'Cargo.toml').read_text()
for old,new in [('../../crates/aspis-core',S/'crates/aspis-core'),('../../crates/aspis-statement',S/'crates/aspis-statement'),('../writers',S/'docs/research/v8-r0-zk-20261009/refine/writers'),('../blockwriters',S/'docs/research/v8-r0-zk-20261009/refine/blockwriters'),('../poseidon',S/'docs/research/v8-r0-zk-20261009/refine/poseidon')]:
    manifest=manifest.replace('"'+old+'"','"'+str(new)+'"')
(harness/'Cargo.toml').write_text(manifest)
run('after-glue',['cargo','test','--release','--offline','-j','4','--manifest-path',str(G/'Cargo.toml'),'-p','aspis-r0-writer-diff','--test','glue','--','--nocapture','--test-threads=3'])
run('after-migration',['cargo','test']+C+['-p','aspis-statement','--features','pool-v1-pair-forest-writer-reference','--test','pair_forest_writer_migration','--','--nocapture','--test-threads=2'])
run('after-pr1',['cargo','run']+C+['-p','aspis-r1-cost-probe','--features','r1p-check','--example','r1p_retry_gate','--','8',str(E/'nonce-ledger'),str(E/'pr1.json')])
p=json.loads((E/'pr1.json').read_text()); assert p['accepted']>=8 and p['accepted_proofs_verified_strict_and_dense']>=8
(E/'PASS').write_text('D83 fixed-seed proof/public identity, codec identity, ordered trace identity, glue 512, migration, P_R1 >=8/8\n')
