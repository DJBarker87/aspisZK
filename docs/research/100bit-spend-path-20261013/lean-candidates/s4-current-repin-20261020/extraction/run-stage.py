#!/usr/bin/env python3
"""Run one fresh-admitted S4 source extraction phase on the NUC."""
from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, time

HERE = Path(__file__).resolve().parent
CFG = json.loads((HERE / "config.json").read_text())
PHASE = sys.argv[1]
assert PHASE in [s['phase'] for s in CFG["stages"]]
G = 1024 ** 3
assert int(CFG["scope_memory_high_bytes"]) == 2 * G
assert int(CFG["scope_memory_max_bytes"]) == 4 * G
assert int(CFG["scope_memory_max_bytes"]) < 8 * G
cgline = Path('/proc/self/cgroup').read_text().strip()
assert cgline.startswith('0::')
cg = Path('/sys/fs/cgroup') / cgline[3:].lstrip('/')
limits = {n: (cg / n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max')}
assert limits == {'memory.high':str(2*G),'memory.max':str(4*G),'memory.swap.max':'0'}, limits

workspace = Path(CFG["source_workspace"])
for rel, expected in CFG["sources"].items():
    actual = hashlib.sha256((workspace / rel).read_bytes()).hexdigest()
    assert actual == expected, (rel, expected, actual)
for name, expected in (("charon", CFG["charon_sha256"]), ("aeneas", CFG["aeneas_sha256"])):
    actual = hashlib.sha256(Path(CFG[name]).read_bytes()).hexdigest()
    assert actual == expected, (name, expected, actual)

outroot = Path(CFG["output_root"])
out = outroot / ("runs-" + PHASE)
out.mkdir(parents=True, exist_ok=False)
if PHASE == 'charon':
    target = outroot / 'four_dots.llbc'
    cmd = [CFG['charon'], 'cargo', '--preset','aeneas','--mir','built','--sysroot','default',
           '--include','core::option::Option','--include','core::result::Result',
           '--include','core::result::_::map_err','--start-from','crate::fast_dots::four_dots',
           '--opaque','crate::fast_pairing','--opaque','crate::aspis_core::field',
           '--dest-file',str(target),'--','--manifest-path',
           str(workspace/'crates/aspis-r1-cost-probe/Cargo.toml'),
           '--locked','--offline','--release','--lib','--no-default-features',
           '--features','private-leaf-salts','--jobs','1']
else:
    llbc = outroot / 'four_dots.llbc'
    assert llbc.is_file()
    parsed = json.loads(llbc.read_text())
    assert parsed and not parsed.get('has_errors', True), 'LLBC absent or has errors'
    generated = outroot / 'generated'
    cmd = [CFG['aeneas'],'-sequential','-no-progress-bar','-abort-on-error','-backend','lean',
           '-namespace','AspisR1FastDotsCurrent','-dest',str(generated),
           '-subdir','AspisR1FastDotsCurrent','-split-files','-emit-json',str(llbc)]

env = dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
           RUSTUP_TOOLCHAIN='nightly-2026-06-01', CARGO_BUILD_JOBS='1',
           CARGO_NET_OFFLINE='true', CARGO_TARGET_DIR=CFG['target_dir'],
           CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH'):
    env.pop(k,None)
(out/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
(out/'environment.json').write_text(json.dumps({k:env.get(k) for k in ('PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')},indent=2)+'\n')
(out/'source-pins.json').write_text(json.dumps(CFG,indent=2)+'\n')
before = (cg/'memory.events').read_text()
start = time.monotonic(); peak=0; timed_out=False
with (out/'stdout.log').open('x') as log:
    p = subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],cwd=workspace,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    while p.poll() is None:
        peak=max(peak,int((cg/'memory.current').read_text()))
        if time.monotonic()-start > 180:
            timed_out=True; os.killpg(p.pid,signal.SIGTERM)
            try: p.wait(timeout=3)
            except subprocess.TimeoutExpired: os.killpg(p.pid,signal.SIGKILL)
            break
        time.sleep(.2)
    p.wait()
timing=(out/'time.log').read_text() if (out/'time.log').exists() else ''
def number(label):
    m=re.search(re.escape(label)+r':\s*(\d+)',timing); return int(m[1]) if m else None
outputs={}
llbc=outroot/'four_dots.llbc'
if llbc.is_file(): outputs['four_dots.llbc']=hashlib.sha256(llbc.read_bytes()).hexdigest()
gen=outroot/'generated'
if gen.exists():
    for f in gen.rglob('*'):
        if f.is_file(): outputs[str(f.relative_to(outroot))]=hashlib.sha256(f.read_bytes()).hexdigest()
receipt={'phase':PHASE,'exit_status':p.returncode,'wall_seconds':time.monotonic()-start,
         'peak_process_rss_kib':number('Maximum resident set size (kbytes)'),
         'process_swaps':number('Swaps'),'sampled_cgroup_peak_bytes':peak,
         'scope_memory_events_before':before,'scope_memory_events_after':(cg/'memory.events').read_text(),
         'scope_memory_peak_cumulative':int((cg/'memory.peak').read_text()),
         'scope_swap_current':int((cg/'memory.swap.current').read_text()),'limits':limits,
         'timed_out':timed_out,'source_revision':'f2c084bc8f51c02f4c58b6d0a4e3dd450867e1f5',
         'command':cmd,'outputs':outputs,'source_workspace':str(workspace),
         'target_dir':CFG['target_dir'],'scope':'s4-current-four-dots-20261020',
         'expected_time':'Cargo target cache reuse + one-function Charon/Aeneas lowering only; no proof generation'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
raise SystemExit(p.returncode)
