#!/usr/bin/env python3
"""Extract the actual selected transcript sampler; no protocol/body rewrite.
Expected work: dependency-free Rust compilation, then focused MIR translation.
Run in a 5G/7G, zero-swap, TasksMax=128 systemd scope.
"""
import argparse, hashlib, json, os, shutil, subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
p.add_argument('--include-result',action='store_true')
p.add_argument('--include-map-err',action='store_true');a=p.parse_args()
assert not (a.include_result and a.include_map_err)
root=Path('/home/dombarker/project-offloads')
stage=root/'aspis-r20-r69-explicit-20260929-b'
charon=root/'ZK-v5-formal/toolchains/charon/bin/charon'
aeneas=root/'aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def write(f,v):f.write_text(json.dumps(v,indent=2)+'\n')
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
resources={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert resources=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'}
resources['cgroup']=str(cg)
assert sha(charon)=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
assert sha(aeneas)=='e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813'
manifest=json.loads((stage/'r18-stage.json').read_text())
for n,h in manifest['files'].items():assert sha(stage/n)==h,n
assert not a.output.exists();a.output.mkdir();src=a.output/'source';src.mkdir()
shutil.copy2(__file__,a.output/'extractor.py')
write(a.output/'resources.json',resources)
shutil.copy2(stage/'r18-stage.json',a.output/'r18-stage.json')
build=stage/'crates/aspis-core/build.rs'
assert sha(build)=='7905b8c2a92c72a79a8a6c785a91ce162fb338569a02867f671d1910e21b6e0d'
shutil.copy2(build,src/'build.rs')
prefix='crates/aspis-core/src/'
copied={}
for n,h in manifest['files'].items():
    if n.startswith(prefix):
        rel=n[len(prefix):];dst=src/'src'/rel;dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(stage/n,dst);copied[rel]=h
assert all(n in copied for n in ['lib.rs','transcript.rs','circle.rs','field.rs'])
# The only source delta is an extraction entry appended to lib.rs. Reachable
# protocol functions, hash function pointer, samplers and loops are unchanged.
entry='''
pub fn sampler_probe(t: &mut transcript::Transcript)
    -> Result<circle::SecureCirclePoint, transcript::CirclePointSampleError> {
    t.challenge_secure_circle_point()
}
'''
(src/'src/lib.rs').write_text((src/'src/lib.rs').read_text()+entry)
(src/'Cargo.toml').write_text('''[package]
name = "aspis-core"
version = "0.0.0"
edition = "2021"
publish = false
[lib]
path = "src/lib.rs"
[workspace]
''')
write(a.output/'source-pins.json',{'base_revision':'bc92dd5675b58ba3076b999429f7cbdfc6675baf',
    'stage_manifest_sha256':sha(stage/'r18-stage.json'),'unchanged_source_files':copied,
    'lib_append':entry,'extraction_lib_sha256':sha(src/'src/lib.rs'),
    'cargo_sha256':sha(src/'Cargo.toml'),'build_sha256':sha(src/'build.rs'),
    'charon_sha256':sha(charon),'aeneas_sha256':sha(aeneas)})
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',
    CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=str(a.output/'target'),NO_DNA='1')
write(a.output/'environment.json',{k:env[k]for k in ['RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS',
    'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','CARGO_TARGET_DIR']})
records=[]
def run(label,cmd):
    with (a.output/(label+'.log')).open('w')as f:
        r=subprocess.run(['/usr/bin/time','-v',*map(str,cmd)],cwd=src,env=env,stdout=f,stderr=subprocess.STDOUT)
    records.append({'label':label,'command':list(map(str,cmd)),'exit':r.returncode})
    write(a.output/'commands.json',records);print((a.output/(label+'.log')).read_text(),flush=True)
    if r.returncode:raise SystemExit(r.returncode)
run('lock',['cargo','generate-lockfile','--offline'])
run('extract',[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default',
    '--start-from','crate::sampler_probe','--include','core::option',
    *(['--include','core::result']if a.include_result else []),
    *(['--include','core::result::_::map_err']if a.include_map_err else []),
    '--dest-file',a.output/'R72Sampler.llbc',
    '--','--locked','--offline','--release','--lib'])
run('translate',[aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean',
    '-namespace','AspisR72Sampler','-dest',a.output/'generated','-subdir','AspisR72Sampler',
    '-split-files','-emit-json',a.output/'R72Sampler.llbc'])
write(a.output/'generated-pins.json',{str(f.relative_to(a.output)):sha(f)
    for f in (a.output/'generated').rglob('*')if f.is_file()})
