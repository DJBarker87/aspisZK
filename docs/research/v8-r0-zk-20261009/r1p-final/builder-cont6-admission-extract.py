#!/usr/bin/env python3
"""Build-host only: isolate the actual records function, with all copy crates.
A different, smaller target than the previous whole-compiler borrow failure.
No shipped edits, no full-compiler or unchanged failed-target rerun.
"""
import hashlib,json,os,pathlib,shutil,subprocess,sys,time
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref6-20261021')
OLD=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref5-20261021')
KIT=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
SRC=R/'source'; E=R/'admission-common'
assert not E.exists()
shutil.copytree(OLD/'source',SRC,ignore=shutil.ignore_patterns('target'),dirs_exist_ok=True)
capped=(OLD/'capped.py').read_text().replace("source_revision='9e3edfbaf'", "source_revision=os.environ['ASPIS_SOURCE_REV']").replace("'SBF_TRACE_DIR']", "'SBF_TRACE_DIR','RUSTFLAGS','RUSTUP_TOOLCHAIN']")
(R/'capped.py').write_text(capped)
E.mkdir();(E/'generated').mkdir()
env=os.environ.copy();env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(R/'extraction-target'),ASPIS_SOURCE_REV=sys.argv[1])
def reserve():
    total=0
    for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip(): total+=int(v)
        except OSError: pass
    assert total+8*2**30<=55*2**30, f'reservation hold: {total}'
def run(name,cmd):
    reserve()
    rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(E/name),'Focused validate_common compilation/translation; no arithmetic release gate','--','timeout','180',*cmd],cwd=SRC,env=env).returncode
    print(name,rc,flush=True)
    return rc
cmd=[str(KIT/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--start-from','crate::pool_v1::pair_trace::validate_common']
for dep in ['aspis_r0_block_writer_copies::*','aspis_r0_poseidon_copy::*','aspis_r0_writer_copies::*']:cmd+=['--include',dep]
cmd+=['--dest-file',str(E/'admission.llbc'),'--','--lib','-p','aspis-statement','--release','--offline','-j','4']
rc=run('charon',cmd)
if rc==0:
    rc=run('aeneas',[str(KIT/'bin/aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisBuilderAdmissionSource','-dest',str(E/'generated'),'-loops-to-rec','-print-unknown-externals',str(E/'admission.llbc')])
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
rec=dict(source_revision=sys.argv[1],target='crate::pool_v1::pair_trace::validate_common',exit=rc,source_pins={str(p.relative_to(SRC)):pin(p) for root in ['crates/aspis-core','crates/aspis-statement','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon'] for p in (SRC/root).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']},tools={str(p):pin(p) for p in [KIT/'charon-target/release/charon',KIT/'bin/aeneas']},artifacts={str(p.relative_to(E)):pin(p) for p in E.rglob('*') if p.is_file()})
(E/'summary.json').write_text(json.dumps(rec,indent=2)+'\n')
print('final exit',rc,flush=True)
