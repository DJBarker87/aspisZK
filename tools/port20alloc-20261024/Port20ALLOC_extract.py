#!/usr/bin/env python3
"""At most two extraction commands; no backend build or unbounded retry."""
import hashlib,json,pathlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[2]; B=pathlib.Path(__file__).resolve().parent
E=R/'evidence/port20alloc-20261024'; HOST='dombarker@100.108.41.90'; H='/home/dombarker/project-offloads/port20alloc-20261024'
phase=sys.argv[1];assert phase in ['charon','aeneas','kani']; attempt=('kani-'+sys.argv[2]) if phase=='kani' else ('extract-001' if phase=='charon' else 'extract-002')
if phase=='kani': assert sys.argv[2] in ['001','002','003','004']
assert not (E/attempt).exists()
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
if phase=='charon':
    cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default']
    for root in ['crate::Port20ALLOC_qm31','crate::Port20ALLOC_row','crate::verifier::Accumulator::new','crate::verifier::BatchedWeights::new']:
        cmd+=['--start-from',root]
    cmd+=['--dest-file',H+'/Port20ALLOC.llbc','--','--manifest-path',H+'/Port20ALLOC-native/Cargo.toml','--offline','--release','--lib','--jobs','1']
elif phase=='aeneas':
    cmd=[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','Port20ALLOC','-dest',H+'/Port20ALLOC-generated','-split-files','-emit-json',H+'/Port20ALLOC.llbc']
else:
    lib=B/'Port20ALLOC-native/src/lib.rs'
    extra='\n#[cfg(kani)]\nmod Port20ALLOC_kani;\n'
    if extra not in lib.read_text():
        (E/'extraction-lib.rs.txt').write_bytes(lib.read_bytes())
        lib.write_text(lib.read_text()+extra)
    harness='Port20ALLOC_constructor_all_variants' if sys.argv[2] in ['001','002'] else 'Port20ALLOC_real_capacity_errors'
    cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',H+'/Port20ALLOC-native/Cargo.toml','--target-dir',H+'/Port20ALLOC-kani-target','-j','1','-Z','unstable-options','--harness-timeout','120s','--exact','--harness','Port20ALLOC_kani::'+harness,'--output-format','terse']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['rsync','-az',str(B/'Port20ALLOC-native')+'/',HOST+':'+H+'/Port20ALLOC-native/'],check=True)
for f in ['Port20ALLOC_gate.py','Port20ALLOC_run.py']:
    subprocess.run(['scp','-q',str(B/f),HOST+':'+H+'/'],check=True)
pin_code='''from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu')
paths=[root/'bin/rustc',root/'bin/cargo',Path(CHARON),Path(CHARON+'-driver'),Path(AENEAS)]
paths+=sorted(p for p in (root/'lib').rglob('*') if p.is_file())
src=root/'lib/rustlib/src/rust/library'
paths+=sorted(p for p in src.rglob('*.rs') if p.is_file())
pins={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
print(json.dumps(dict(tool_sysroot_hashes=pins,rustc=subprocess.check_output([str(root/'bin/rustc'),'--version'],text=True).strip(),sysroot=str(root))))
'''.replace('CHARON',repr(charon)).replace('AENEAS',repr(aeneas))
if phase=='kani':
    pin_code=pin_code.replace("/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu","/home/dombarker/.kani/kani-0.67.0/toolchain")
    pin_code=pin_code.replace("paths+=sorted(p for p in (root/'lib').rglob('*') if p.is_file())", "paths+=list(Path('/home/dombarker/.kani/kani-0.67.0/bin').glob('*'))\npaths+=[Path('/home/dombarker/.cargo/bin/cargo-kani')]\npaths+=sorted(p for p in (root/'lib').rglob('*') if p.is_file())")
pins=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=pin_code,text=True))
inputs={str(p.relative_to(B)):sha(p) for p in (B/'Port20ALLOC-native').rglob('*') if p.is_file()}
inputs.update({f:sha(B/f) for f in ['Port20ALLOC_gate.py','Port20ALLOC_run.py']})
if phase=='aeneas':
    llbc=subprocess.check_output(['ssh',HOST,'cat',H+'/Port20ALLOC.llbc'])
    assert not json.loads(llbc)['has_errors']
    inputs['Port20ALLOC.llbc']=hashlib.sha256(llbc).hexdigest()
cfg=dict(attempt=attempt,kind=phase,command=cmd,input_hashes=inputs,**pins,
         source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
         source_pins_sha256=sha(E/'source-pins.json'),
         expected_time=('optimized compilation then SAT for '+harness+'; no arithmetic elimination' if phase=='kani' else 'optimized compilation and focused source extraction; no arithmetic elimination'),
         env=dict(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=H+'/Port20ALLOC-target',CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',RUSTFLAGS='-C link-arg=-Wl,--threads=1'))
p=E/(attempt+'.json');p.write_text(json.dumps(cfg,indent=2)+'\n');subprocess.run(['scp','-q',str(p),HOST+':'+H+'/'],check=True)
# Two fresh, fail-closed snapshots. No compiler reservation before these pass.
for label in ['preflight','go']:
    with (E/(attempt+'-'+label+'.json')).open('w') as f:
        r=subprocess.run(['ssh',HOST,'python3',H+'/Port20ALLOC_gate.py'],stdout=f)
    if r.returncode:sys.exit(r.returncode)
r=subprocess.run(['ssh',HOST,'systemd-run','--user','--scope','-q','-p','MemoryHigh=1536M','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',H+'/Port20ALLOC_run.py',attempt+'.json'])
subprocess.run(['scp','-qr',HOST+':'+H+'/'+attempt,str(E/attempt)],check=True)
if phase=='charon' and r.returncode==0:
    subprocess.run(['scp','-q',HOST+':'+H+'/Port20ALLOC.llbc',str(E/'Port20ALLOC.llbc')],check=True)
if phase=='aeneas':
    subprocess.run(['scp','-qr',HOST+':'+H+'/Port20ALLOC-generated',str(E/'Port20ALLOC-generated')])
sys.exit(r.returncode)
