#!/usr/bin/env python3
"""At most two extraction commands; no backend build or unbounded retry."""
import hashlib,json,pathlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[2]; B=pathlib.Path(__file__).resolve().parent
E=R/'evidence/port23push-20261024'; HOST='dombarker@100.108.41.90'; H='/home/dombarker/project-offloads/port23push-20261024'
subprocess.run(['ssh',HOST,'mkdir','-p',H],check=True)
phase=sys.argv[1];assert phase in ['charon','aeneas']; attempt='extract-001' if phase=='charon' else 'extract-002'
assert not (E/attempt).exists(), 'extraction phase already attempted; no retry'
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
if phase=='charon':
    cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default']
    for root in ['crate::verifier::Port23PUSH_push']:
        cmd+=['--start-from',root]
    cmd+=['--dest-file',H+'/Port23PUSH.llbc','--','--manifest-path',H+'/Port23PUSH-native/Cargo.toml','--offline','--release','--lib','--jobs','1']
elif phase=='aeneas':
    cmd=[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','Port23PUSH','-dest',H+'/Port23PUSH-generated','-split-files','-emit-json',H+'/Port23PUSH.llbc']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['rsync','-az',str(B/'Port23PUSH-native')+'/',HOST+':'+H+'/Port23PUSH-native/'],check=True)
for f in ['Port23PUSH_gate.py','Port23PUSH_run.py']:
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
inputs={str(p.relative_to(B)):sha(p) for p in (B/'Port23PUSH-native').rglob('*') if p.is_file()}
inputs.update({f:sha(B/f) for f in ['Port23PUSH_gate.py','Port23PUSH_run.py']})
if phase=='aeneas':
    llbc=subprocess.check_output(['ssh',HOST,'cat',H+'/Port23PUSH.llbc'])
    assert not json.loads(llbc)['has_errors']
    inputs['Port23PUSH.llbc']=hashlib.sha256(llbc).hexdigest()
cfg=dict(attempt=attempt,kind=phase,command=cmd,input_hashes=inputs,**pins,
         source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
         source_pins_sha256=sha(E/'source-pins.json'),
         expected_time='optimized compilation and focused source extraction; no arithmetic elimination',
         env=dict(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=H+'/Port23PUSH-target',CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',RUSTFLAGS='-C link-arg=-Wl,--threads=1'))
p=E/(attempt+'.json');p.write_text(json.dumps(cfg,indent=2)+'\n');subprocess.run(['scp','-q',str(p),HOST+':'+H+'/'],check=True)
# Two fresh, fail-closed snapshots. No compiler reservation before these pass.
for label in ['preflight','go']:
    with (E/(attempt+'-'+label+'.json')).open('w') as f:
        r=subprocess.run(['ssh',HOST,'python3',H+'/Port23PUSH_gate.py'],stdout=f)
    if r.returncode:sys.exit(r.returncode)
r=subprocess.run(['ssh',HOST,'systemd-run','--user','--scope','-q','-p','MemoryHigh=1536M','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',H+'/Port23PUSH_run.py',attempt+'.json'])
subprocess.run(['scp','-qr',HOST+':'+H+'/'+attempt,str(E/attempt)],check=True)
if phase=='charon' and r.returncode==0:
    subprocess.run(['scp','-q',HOST+':'+H+'/Port23PUSH.llbc',str(E/'Port23PUSH.llbc')],check=True)
if phase=='aeneas':
    subprocess.run(['scp','-qr',HOST+':'+H+'/Port23PUSH-generated',str(E/'Port23PUSH-generated')])
sys.exit(r.returncode)
