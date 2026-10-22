from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, time

work = Path(__file__).resolve().parent
evidence = Path(sys.argv[1])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
cgroup = Path('/sys/fs/cgroup' + Path('/proc/self/cgroup').read_text().split('0::', 1)[1].strip())
limits = {n: (cgroup/n).read_text().strip() for n in ('memory.high', 'memory.max', 'memory.swap.max')}
assert limits == {'memory.high': str(2*2**30), 'memory.max': str(4*2**30), 'memory.swap.max': '0'}, limits
source = work/'src/lib.rs'
binding = json.loads((work/'source-binding.json').read_text())
assert sha(source) == binding['source_sha256']
kani = Path('/home/dombarker/.cargo/bin/cargo-kani')
cmd = [str(kani), '--manifest-path', str(work/'Cargo.toml'), '--lib', '--exact',
       '--harness', 'std_from_fn_twenty_nine_matches_explicit_ordered_calls',
       '--solver', 'kissat', '--output-format', 'regular', '-Z', 'unstable-options', '-j', '1',
       '--cbmc-args', '--unwinding-assertions']
env = dict(os.environ, PATH='/home/dombarker/.cargo/bin:'+os.environ.get('PATH', '/usr/bin:/bin'),
           CARGO_BUILD_JOBS='1', CARGO_NET_OFFLINE='true',
           CARGO_PROFILE_DEV_OPT_LEVEL='3', CARGO_PROFILE_TEST_OPT_LEVEL='3',
           CARGO_TARGET_DIR=str(work/'target'))
tool_paths = [kani] + [Path('/home/dombarker/.kani/kani-0.67.0/bin')/n for n in ('kani-driver','kani-compiler','cbmc','kissat')]
pre = {'command':cmd, 'source_sha256':sha(source), 'cargo_manifest_sha256':sha(work/'Cargo.toml'),
       'binding_sha256':sha(work/'source-binding.json'), 'candidate_revision':(work/'source-revision.txt').read_text().strip(),
       'tool_sha256':{str(p):sha(p) for p in tool_paths}, 'limits':limits,
       'expected_cost':'Rust/Kani MIR lowering and two small symbolic fixed-array constructor checks; no field arithmetic or large elimination.',
       'claim_boundary':'The harness directly invokes std::array::from_fn under Kani and checks arbitrary precomputed output/state traces. This is a named Kani/std operational result, not a Lean or Aeneas source-correspondence theorem.'}
(evidence/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
start=time.monotonic(); watchdog=None
with (evidence/'kani.log').open('w') as out:
    proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(evidence/'time.log')]+cmd,cwd=work,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
    try: code=proc.wait(timeout=180)
    except subprocess.TimeoutExpired:
        watchdog='focused 180-second review threshold'
        os.killpg(proc.pid,signal.SIGTERM)
        try: code=proc.wait(timeout=4)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid,signal.SIGKILL); code=proc.wait()
txt=(evidence/'time.log').read_text() if (evidence/'time.log').exists() else ''
def metric(label):
    m=re.search(re.escape(label)+r':\s*(\d+)',txt)
    return int(m.group(1)) if m else None
rec={'exit_status':code,'wall_seconds':round(time.monotonic()-start,3),
     'peak_process_rss_kib':metric('Maximum resident set size (kbytes)'),
     'swaps':metric('Swaps'),'scope_memory_peak_bytes':int((cgroup/'memory.peak').read_text()),
     'scope_swap_peak_bytes':int((cgroup/'memory.swap.peak').read_text()),'limits':limits,
     'source_sha256':pre['source_sha256'],'watchdog_abort':watchdog,
     'print_axioms':'N/A: Kani symbolic verification; no Lean axiom claim'}
(evidence/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec)); raise SystemExit(code)
