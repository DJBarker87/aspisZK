#!/usr/bin/env python3
"""Run one admitted full-current S5 Pair candidate extraction phase."""
from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, time

HERE=Path(__file__).resolve().parent
C=json.loads((HERE/'config.json').read_text())
phase=sys.argv[1]
assert phase in {x['phase'] for x in C['stages']}
G=1024**3
assert int(C['scope_memory_high_bytes'])==2*G
assert int(C['scope_memory_max_bytes'])==4*G
assert int(C['scope_memory_max_bytes'])<8*G
cgline=Path('/proc/self/cgroup').read_text().strip(); assert cgline.startswith('0::')
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max')}
assert limits=={'memory.high':str(2*G),'memory.max':str(4*G),'memory.swap.max':'0'},limits
workspace=Path(C['source_workspace'])
for rel,expected in C['sources'].items():
    actual=hashlib.sha256((workspace/rel).read_bytes()).hexdigest()
    assert actual==expected,(rel,expected,actual)
for key in ('charon','aeneas'):
    actual=hashlib.sha256(Path(C[key]).read_bytes()).hexdigest()
    assert actual==C[key+'_sha256'],(key,actual)
outroot=Path(C['output_root']);outroot.mkdir(parents=True,exist_ok=True)
out=outroot/('runs-'+phase);out.mkdir(parents=True,exist_ok=False)
(out/'input-snapshot').mkdir()
for rel in C['sources']:
    dest=out/'input-snapshot'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((workspace/rel).read_bytes())
(out/'config.json').write_text(json.dumps(C,indent=2,sort_keys=True)+'\n')
llbc=outroot/'Pair.llbc';generated=outroot/'generated'
if phase=='charon':
    cmd=[C['charon'],'cargo','--preset','aeneas','--mir','built']
    for inc in C['charon_includes']: cmd += ['--include',inc]
    cmd += ['--start-from',C['start_from']]
    for opaque in C['opaque_paths']: cmd += ['--opaque',opaque]
    cmd += ['--dest-file',str(llbc),'--','--manifest-path',str(workspace/'crates/aspis-r1-cost-probe/Cargo.toml'),
            '--locked','--offline','--release','--lib','--no-default-features','--features',','.join(C['features']),'--jobs','1']
else:
    assert llbc.is_file(), 'missing Pair.llbc'
    data=json.loads(llbc.read_text())
    assert data and data.get('has_errors') is False, 'LLBC absent/empty or has_errors'
    # Charon serializes item paths as arrays of Ident/Impl nodes rather than a
    # rendered `Weights.pair` string. Validate the exact selected root by its
    # item_names key and final identifier.
    names=data['translated'].get('item_names', [])
    pair_roots=[x for x in names if x.get('key')=={'Fun':0}]
    assert len(pair_roots)==1, 'expected unique Fun 0 root missing from LLBC'
    path=pair_roots[0]['value']
    assert path[-1].get('Ident',[None])[0]=='pair', path
    cmd=[C['aeneas'],'-sequential','-no-progress-bar','-abort-on-error','-backend','lean',
         '-namespace','AspisR1CurrentPairLoopHelpers','-dest',str(generated),
         '-subdir','AspisR1CurrentPairLoopHelpers','-split-files','-emit-json',str(llbc)]
env=dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN=C['rustup_toolchain'],
           CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=C['target_dir'],
           CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH'):env.pop(k,None)
rustc=subprocess.run(['rustc','--version'],env=env,text=True,stdout=subprocess.PIPE,check=True).stdout.strip()
rustsysroot=Path(subprocess.run(['rustc','--print','sysroot'],env=env,text=True,stdout=subprocess.PIPE,check=True).stdout.strip())
stdlib=rustsysroot/'lib/rustlib/src/rust/library'
stdlib_pins={}
for name,rel in [('core_iterator','core/src/iter/traits/iterator.rs'),('core_result','core/src/result.rs'),('core_array','core/src/array/mod.rs')]:
    f=stdlib/rel
    if f.is_file():stdlib_pins[name]={'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()}
(out/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
(out/'environment.json').write_text(json.dumps({k:env.get(k) for k in ('PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS')},indent=2)+'\n')
source_before={rel:hashlib.sha256((workspace/rel).read_bytes()).hexdigest() for rel in C['sources']}
before=(cg/'memory.events').read_text();start=time.monotonic();peak=0;timed_out=False
with (out/'stdout.log').open('x') as log:
    p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],cwd=workspace,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    while p.poll() is None:
        peak=max(peak,int((cg/'memory.current').read_text()))
        if time.monotonic()-start>180:
            timed_out=True;os.killpg(p.pid,signal.SIGTERM)
            try:p.wait(timeout=3)
            except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
            break
        time.sleep(.2)
    p.wait()
timing=(out/'time.log').read_text() if (out/'time.log').exists() else ''
def number(label):
    m=re.search(re.escape(label)+r':\s*(\d+)',timing);return int(m[1]) if m else None
source_after={rel:hashlib.sha256((workspace/rel).read_bytes()).hexdigest() for rel in C['sources']}
assert source_before==source_after,'source workspace changed during extraction'
outputs={}
if llbc.is_file():outputs['Pair.llbc']=hashlib.sha256(llbc.read_bytes()).hexdigest()
if generated.exists():
    for f in generated.rglob('*'):
        if f.is_file():outputs[str(f.relative_to(outroot))]=hashlib.sha256(f.read_bytes()).hexdigest()
receipt={'phase':phase,'exit_status':p.returncode,'wall_seconds':time.monotonic()-start,
 'peak_process_rss_kib':number('Maximum resident set size (kbytes)'),'process_swaps':number('Swaps'),
 'sampled_cgroup_peak_bytes':peak,'scope_memory_events_before':before,'scope_memory_events_after':(cg/'memory.events').read_text(),
 'scope_memory_peak_cumulative':int((cg/'memory.peak').read_text()),'scope_swap_current':int((cg/'memory.swap.current').read_text()),
 'limits':limits,'timed_out':timed_out,'source_revision':C['source_revision'],'source_hashes_before':source_before,
 'source_hashes_after':source_after,'command':cmd,'outputs':outputs,'source_workspace':str(workspace),
 'rustc_version':rustc,'rust_sysroot':str(rustsysroot),'stdlib_source_pins':stdlib_pins,
 'charon_sha256':C['charon_sha256'],'aeneas_sha256':C['aeneas_sha256'],
 'expected_time':'warm Cargo target dependency reuse and one full-MIR Charon/Aeneas lowering phase only; no proof/CU build'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
raise SystemExit(p.returncode)
