#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,sys,hashlib,json
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=R/'extraction';O.mkdir(exist_ok=True)
C=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
phase,attempt=sys.argv[1:3]
mode=sys.argv[3] if len(sys.argv)>3 else 'main'
assert mode in ['main','parser','sort']
parser=mode=='parser'
sort=mode=='sort'
namespace='MultiproofSortRef' if sort else ('MultiproofParserRef' if parser else 'MultiproofConeRef')
if mode!='main':O=R/(mode+'-extraction');O.mkdir(exist_ok=True)
if phase=='charon':
 cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option','--include','core::option::Option']
 for name in (['insert_rows','sort_rows'] if sort else ['canonical_words','opening_scan','opening_rows','scan','header','semantic_rows','parse'] if parser else ['verify_owned','valid_indices','binary_step','leaf_step','level_rows','levels','canonical_word','canonical_qm','expand_chunk','row_shape','semantic_offsets','check_values','expand_rows']):cmd+=['--start-from',('crate::sort_reference::' if sort else 'crate::parser_reference::' if parser else 'crate::reference::')+name]
 cmd+=['--dest-file',str(O/'MultiproofCone.llbc'),'--','--manifest-path',str(T/'Cargo.toml'),'--offline','--release','--lib','--jobs','4']
else:
 assert not json.loads((O/'MultiproofCone.llbc').read_text())['has_errors']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',namespace,'-dest',str(O/'generated'),'-subdir',namespace,'-split-files','-emit-json',str(O/'MultiproofCone.llbc')]
env={**os.environ,'PATH':'/home/dombarker/.cargo/bin:'+os.environ['PATH'],'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'4','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':str(R/'charon-target'),'CARGO_NET_OFFLINE':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=4'}
for n in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(n,None)
(O/(phase+'-'+attempt+'-inputs.json')).write_text(json.dumps({'command':cmd,'source_sha256':hashlib.sha256((T/('src/sort_reference.rs' if sort else 'src/reference.rs')).read_bytes()).hexdigest(),'tools':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [C,C.with_name('charon-driver'),A]},'expected_work':'pinned compilation/translation; row and level recursion, no arithmetic gate'},indent=2)+'\n')
subprocess.run(['python3',str(T/'reservation.py'),str(R/('reservation-'+(mode+'-' if mode!='main' else '')+phase+'-'+attempt+'.json'))],check=True,stdout=subprocess.DEVNULL)
os.chdir(R)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(T/'host-run.py'),(mode+'-' if mode!='main' else '')+phase+'-'+attempt,*cmd],env=env))
