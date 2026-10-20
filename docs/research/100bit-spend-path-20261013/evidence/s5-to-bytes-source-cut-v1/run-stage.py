#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, time

W = Path(__file__).resolve().parent
PHASE = sys.argv[1]
ROOT = Path('/home/dombarker/project-offloads')
TOOLS = ROOT / 'aspis-r1-r18-tools-20261016'
CHARON = TOOLS / 'charon-target/release/charon'
AENEAS = ROOT / 'v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
PINS = {
    str(CHARON): 'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',
    str(TOOLS / 'charon-target/release/charon-driver'): 'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45',
    str(AENEAS): '4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5',
}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for name, expected in PINS.items():
    if sha(Path(name)) != expected: raise SystemExit(f'tool hash mismatch: {name}')

inp = W / 'input'
pins = json.loads((W / 'source-pins.json').read_text())
for key in ('cut_field_rs', 'cut_wide_exact_rs', 'entry_lib_rs', 'cargo_toml', 'cargo_lock'):
    item = pins['source_files'][key]
    p = Path(item['path'])
    if not p.is_absolute(): p = W / p
    # Source pin files may use their original absolute workstation path; verify the bundled name instead.
    bundled = inp / {'cut_field_rs':'field.rs','cut_wide_exact_rs':'field/wide_exact.rs','entry_lib_rs':'lib.rs','cargo_toml':'Cargo.toml','cargo_lock':'Cargo.lock'}[key]
    if sha(bundled) != item['sha256']: raise SystemExit(f'input hash mismatch: {key}')

cgroup = Path('/sys/fs/cgroup') / Path('/proc/self/cgroup').read_text().strip()[3:].lstrip('/')
limits = {n:(cgroup/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max')}
expected_limits = {'memory.high':'2147483648','memory.max':'4294967296','memory.swap.max':'0'}
if limits != expected_limits: raise SystemExit(f'wrong scope limits: {limits}')

out = W / 'attempt' / PHASE
out.mkdir(parents=True, exist_ok=False)
llbc = W / 'WideExactToBytes.llbc'
if PHASE == 'charon':
    cmd = [str(CHARON), 'cargo', '--preset','aeneas','--mir','built','--sysroot','default',
           '--include','core::option::Option','--include','core::result::Result',
           '--start-from','crate::wide_exact_to_le_bytes_entry',
           '--dest-file',str(llbc),'--','--manifest-path',str(inp/'Cargo.toml'),
           '--locked','--offline','--release','--lib','--no-default-features','--jobs','1']
else:
    if not llbc.is_file(): raise SystemExit('missing Charon LLBC')
    blob = json.loads(llbc.read_text())
    if blob.get('has_errors', True): raise SystemExit('invalid LLBC; Aeneas not run')
    cmd = [str(AENEAS),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean',
           '-namespace','AspisR1WideToBytesSource','-dest',str(W/'generated'),
           '-subdir','AspisR1WideToBytesSource','-split-files','-emit-json',str(llbc)]

env = dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',
           CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(W/'target'),
           CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH'):
    env.pop(k,None)
(out/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
(out/'tool-pins.json').write_text(json.dumps(PINS,indent=2)+'\n')
start = time.monotonic(); peak = 0
with (out/'stdout.log').open('w') as log:
    p = subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],cwd=inp,env=env,stdout=log,stderr=subprocess.STDOUT)
    while p.poll() is None:
        peak=max(peak,int((cgroup/'memory.current').read_text()))
        time.sleep(.2)
    rc=p.wait()
timing=(out/'time.log').read_text() if (out/'time.log').exists() else ''
def metric(label):
    m=re.search(re.escape(label)+r':\s*(\d+)',timing);return int(m.group(1)) if m else None
outputs={}
if llbc.exists(): outputs['WideExactToBytes.llbc']=sha(llbc)
if (W/'generated').exists():
    for f in (W/'generated').rglob('*'):
        if f.is_file(): outputs[str(f.relative_to(W))]=sha(f)
receipt={'phase':PHASE,'exit_status':rc,'wall_seconds':round(time.monotonic()-start,3),
         'peak_process_rss_kib':metric('Maximum resident set size (kbytes)'),
         'process_swaps':metric('Swaps'),'sampled_cgroup_peak_bytes':peak,
         'scope_memory_peak_bytes':int((cgroup/'memory.peak').read_text()),
         'scope_swap_current_bytes':int((cgroup/'memory.swap.current').read_text()),
         'limits':limits,'source_revision':pins['source_revision'],
         'source_pins_sha256':sha(W/'source-pins.json'),'tool_pins':PINS,
         'runner_sha256':sha(Path(__file__)),'command':cmd,'outputs':outputs,
         'note':'Focused source extraction only; no Lean refinement or stdlib correspondence claimed.'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
raise SystemExit(rc)
