#!/usr/bin/env python3
"""At most two extraction commands; no backend build or unbounded retry."""
import hashlib,json,pathlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[2]; B=pathlib.Path(__file__).resolve().parent
E=R/'evidence/port21projection-20261024'; HOST='dombarker@100.108.41.90'; H='/home/dombarker/project-offloads/port21projection-20261024'
phase=sys.argv[1];assert phase in ['charon','aeneas']; attempt='extract-003' if phase=='charon' else 'extract-004'
assert not (E/attempt).exists(), 'extraction phase already attempted; no retry'
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
if phase=='charon':
    cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default']
    for root in ['crate::verifier::Port21PROJECTION_acc','crate::verifier::Port21PROJECTION_rows']:
        cmd+=['--start-from',root]
    cmd+=['--dest-file',H+'/Port21PROJECTION.llbc','--','--manifest-path',H+'/Port21PROJECTION-native/Cargo.toml','--offline','--release','--lib','--jobs','1']
elif phase=='aeneas':
    cmd=[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','Port21PROJECTION','-dest',H+'/Port21PROJECTION-generated','-split-files','-emit-json',H+'/Port21PROJECTION.llbc']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['rsync','-az',str(B/'Port21PROJECTION-native')+'/',HOST+':'+H+'/Port21PROJECTION-native/'],check=True)
for f in ['Port21PROJECTION_gate.py','Port21PROJECTION_run.py']:
    subprocess.run(['scp','-q',str(B/f),HOST+':'+H+'/'],check=True)
pin_code='''from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu')
paths=[root/'bin/rustc',root/'bin/cargo',Path(CHARON),Path(CHARON+'-driver'),Path(AENEAS)]
paths+=sorted(p for p in (root/'lib').rglob('*') if p.is_file())
src=root/'lib/rustlib/src/rust/library'
paths+=sorted(p for p in src.rglob('*.rs') if p.is_file())
paths+=[Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon/charon/src/transform/add_missing_info/reorder_decls.rs')]
pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
print(json.dumps(dict(tool_sysroot_hashes=pins,rustc=subprocess.check_output([str(root/'bin/rustc'),'--version'],text=True).strip(),sysroot=str(root))))
'''.replace('CHARON',repr(charon)).replace('AENEAS',repr(aeneas))

pins=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=pin_code,text=True))
inputs={str(p.relative_to(B)):sha(p) for p in (B/'Port21PROJECTION-native').rglob('*') if p.is_file()}
inputs.update({f:sha(B/f) for f in ['Port21PROJECTION_gate.py','Port21PROJECTION_run.py']})
if phase=='aeneas':
    llbc=subprocess.check_output(['ssh',HOST,'cat',H+'/Port21PROJECTION.llbc'])
    assert not json.loads(llbc)['has_errors']
    inputs['Port21PROJECTION.llbc']=hashlib.sha256(llbc).hexdigest()
cfg=dict(attempt=attempt,kind=phase,command=cmd,input_hashes=inputs,**pins,
         source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
         source_pins_sha256=sha(E/'source-pins.json'),
         expected_time='optimized compilation and focused source extraction; no arithmetic elimination',
         env=dict(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=H+'/Port21PROJECTION-target',CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',RUSTFLAGS='-C link-arg=-Wl,--threads=1'))
p=E/(attempt+'.json');p.write_text(json.dumps(cfg,indent=2)+'\n');subprocess.run(['scp','-q',str(p),HOST+':'+H+'/'],check=True)
# Two fresh, fail-closed snapshots. No compiler reservation before these pass.
for label in ['preflight','go']:
    with (E/(attempt+'-'+label+'.json')).open('w') as f:
        r=subprocess.run(['ssh',HOST,'python3',H+'/Port21PROJECTION_gate.py'],stdout=f)
    if r.returncode:sys.exit(r.returncode)
r=subprocess.run(['ssh',HOST,'systemd-run','--user','--scope','-q','-p','MemoryHigh=1536M','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',H+'/Port21PROJECTION_run.py',attempt+'.json'])
subprocess.run(['scp','-qr',HOST+':'+H+'/'+attempt,str(E/attempt)],check=True)
if phase=='charon' and r.returncode==0:
    subprocess.run(['scp','-q',HOST+':'+H+'/Port21PROJECTION.llbc',str(E/'Port21PROJECTION.llbc')],check=True)
if phase=='aeneas':
    subprocess.run(['scp','-qr',HOST+':'+H+'/Port21PROJECTION-generated',str(E/'Port21PROJECTION-generated')])
sys.exit(r.returncode)
