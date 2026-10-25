#!/usr/bin/env python3
"""Focused typecheck of isolated safe-storage candidate, not equivalence."""
from pathlib import Path
import hashlib, json, os, re, signal, subprocess, time
R = Path(__file__).resolve().parents[2]
B = R/'docs/research/100bit-spend-path-20261013'
A = B/'evidence/s126-current-caller-20261021/s1-claims-safe-typecheck-v1'
A.mkdir(exist_ok=False)
W = Path('/private/tmp/s126-kani-local-diagnostic-20261025-v1')
C = W/'min'
N = Path('/Users/dominic/.rustup/toolchains/nightly-2025-11-21-aarch64-apple-darwin')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
lock = Path('/tmp/aspis-local-lean.lock.d')
try:
    lock.mkdir()
except FileExistsError:
    (A/'preflight.json').write_text(json.dumps(dict(compiler_launched=False,reason='existing shared local compiler lock'))+'\n')
    raise SystemExit('Existing compiler lock; untouched.')
(lock/'owner.json').write_text(json.dumps(dict(pid=os.getpid(),target='S1 isolated safe Claims native typecheck'))+'\n')
try:
    env = dict(os.environ)
    for key in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','RUSTC_BOOTSTRAP']:
        env.pop(key,None)
    env.update(PATH=str(N/'bin')+':/Users/dominic/.cargo/bin:/usr/bin:/bin:/usr/sbin:/sbin',
        RUSTUP_TOOLCHAIN='nightly-2025-11-21-aarch64-apple-darwin',CARGO_BUILD_JOBS='1',
        CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(W/'native-target'),
        RUSTFLAGS='-C opt-level=3 -C overflow-checks=yes',DYLD_LIBRARY_PATH=str(N/'lib'))
    sources = {str(p.relative_to(W)):sha(p) for p in (W/'core-workspace').rglob('*') if p.is_file()}
    for rel in ['Cargo.toml','Cargo.lock','src/probe_safe.rs','src/candidate_claims.rs','src/sampler.rs','src/r1_wire.rs']:
        sources['min/'+rel] = sha(C/rel)
    tools = [N/'bin/rustc',N/'bin/cargo']+list((N/'lib').glob('*.dylib'))
    tools += [p for p in (N/'lib/rustlib/aarch64-apple-darwin/lib').glob('*') if p.is_file()]
    pins = {str(p):sha(p) for p in tools}
    cmd = [str(N/'bin/cargo'),'check','--manifest-path',str(C/'Cargo.toml'),'--lib','--offline','--locked','-j1']
    data = dict(schema='focused-extractor-proof-packet-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
        command=cmd,cwd=str(C),environment={k:env[k] for k in ['PATH','RUSTUP_TOOLCHAIN','DYLD_LIBRARY_PATH','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','RUSTFLAGS']},
        source_files=sources,tool_pins=pins,expected_time='Native compilation/typecheck, bounded optimized core build-script table generation; no extraction/SAT/aggregation or equivalence proof.',
        limits=dict(aggregate_rss_watchdog_bytes=2*2**30,processes=64,wall_seconds=180),
        qualification='Candidate syntax/types only; actual shipped function and equivalence/adoption/re-pin obligations unchanged.',print_axioms='N/A: Rust typecheck')
    (A/'input.json').write_text(json.dumps(data,indent=2)+'\n')
    for rel in ['min/Cargo.toml','min/Cargo.lock','min/src/probe_safe.rs','min/src/candidate_claims.rs','core-workspace/Cargo.toml']:
        p=A/'source'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((W/rel).read_bytes())
    (A/'source/typecheck.py').write_bytes(Path(__file__).read_bytes())
    start=time.monotonic();peak=0;stop=None
    with (A/'stdout.log').open('w') as out,(A/'time.log').open('w') as err:
        child=subprocess.Popen(['/usr/bin/time','-l',*cmd],cwd=C,env=env,stdout=out,stderr=err,start_new_session=True)
        while child.poll() is None:
            rows=[list(map(int,l.split())) for l in subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True).splitlines() if len(l.split())==3]
            own=[r for r in rows if r[1]==child.pid];rss=sum(r[2] for r in own)*1024;peak=max(peak,rss)
            if rss>2*2**30:stop='RSS watchdog'
            elif len(own)>64:stop='process watchdog'
            elif time.monotonic()-start>180:stop='wall watchdog'
            if stop:
                os.killpg(child.pid,signal.SIGTERM)
                try:child.wait(timeout=2)
                except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL)
                break
            time.sleep(.2)
        status=child.wait()
    wall=time.monotonic()-start;timing=(A/'time.log').read_text()
    def metric(key):
        m=re.search(r'(\d+)\s+'+key,timing);return int(m[1]) if m else None
    receipt=dict(schema='focused-extractor-proof-packet-v1',command=cmd,exit_status=status,wall_seconds=wall,
        peak_rss_bytes=metric('maximum resident set size'),aggregate_rss_peak_observed_bytes=peak,swaps=metric('swaps'),watchdog_stop=stop,
        source_unchanged={p:sha(W/p)==h for p,h in sources.items()},tools_unchanged={p:sha(Path(p))==h for p,h in pins.items()},
        input_sha256=sha(A/'input.json'),stdout_sha256=sha(A/'stdout.log'),stderr_time_sha256=sha(A/'time.log'),
        print_axioms='N/A: Rust typecheck',verification_launched=False,host_SSH_operations=0)
    (A/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['exit_status','wall_seconds','peak_rss_bytes','aggregate_rss_peak_observed_bytes','swaps','watchdog_stop']}))
    assert all(receipt['source_unchanged'].values()) and all(receipt['tools_unchanged'].values())
finally:
    (lock/'owner.json').unlink();lock.rmdir()
