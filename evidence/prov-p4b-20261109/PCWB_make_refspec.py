#!/usr/bin/env python3
"""Build sources/<set>/ from git blobs of research and a PCWB_<run>_spec.json. Usage: PCWB_make_refspec.py <key> <run>"""
import sys,json,hashlib,subprocess
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
XRA='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/'
CH=XRA+'charon';AE=XRA+'aeneas-b59d5188-extended'
INC=['--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
def tiny_env(tc):return {'RUSTUP_TOOLCHAIN':tc,'CARGO_TARGET_DIR':'{WS}/../PCWB_target','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','RUSTFLAGS':'-Zthreads=1 -C link-arg=-Wl,--threads=1','RAYON_NUM_THREADS':'1','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'}
def tiny(name,rs_git,rs_sha,pkg,roots,ns):
    return dict(frozen_workspace=False,crate_dir='crate',gitfiles={'src/lib.rs':rs_git},
      textfiles={'Cargo.toml':'[package]\nname="%s"\nversion="0.1.0"\nedition="2021"\n[workspace]\n'%pkg},expect={'src/lib.rs':rs_sha},
      charon_command=[CH,'cargo','--preset','aeneas','--mir','built','--sysroot','default']+INC+sum([['--start-from','crate::'+r] for r in roots],[])+['--dest-file','{OUT}/repro.llbc','--','--manifest-path','{CRATE}/Cargo.toml','--offline','--release','--lib','--jobs','1'],
      aeneas_command=[AE,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest','{OUT}/raw','-subdir',ns,'-split-files','{OUT}/repro.llbc'],
      env=tiny_env('nightly-2026-09-17'),namespace=ns)
D2='evidence/slice-q-compose2-20261102/';D1='evidence/slice-q-compose-20261029/'
SETS={
 'neo_window':tiny('neo_window',('research',D2+'NEO_E009/sources/NEO_window_reference.rs'),'2e0240558aeaf9b15337057bea3b93c190503d71b06dd80102bdf5894aa247f7','neb_q_reference',['word','complex','quadratic','wide'],'NEO_WindowV2'),
 'neo_parser':tiny('neo_parser',('research',D2+'NEO_E001/sources/NEO_parser_reference.rs'),'1943f54c2276e8aa663d7cfc0e0f1c1f07ad01b115cccb94c18e4c5f9a0380ee','neb_parser_reference',['m_ref','limbs_ref'],'NEO_ParserRef'),
 'neb_additive':tiny('neb_additive',('research',D1+'NEB_E003/sources/NEB_additive_reference.rs'),'c0941595b7b8eddea92f6376d3bdc78fe32414053a4942cda83bab71d762f6c9','neb_additive_reference',['add_word','sub_word','normalize_word','add2','add4','add8','sub2','sub4','sub8'],'NEB_AdditiveRef'),
}

# ---- multiproof cone crate (tools/multiproof-cone-20261021) at a recorded commit
R18='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/'
def mp(commit,roots_mod,roots,ns,names=None):
    tree=subprocess.check_output(['git','-C','/Users/dominic/ZK','ls-tree','-r',commit,'tools/multiproof-cone-20261021']).decode().split('\n')
    paths=[l.split('\t')[1] for l in tree if l and (l.split('\t')[1].endswith(('Cargo.toml','Cargo.lock')) or '/src/' in l.split('\t')[1])]
    gitfiles={};expect={}
    for p in paths:
        rel=p[len('tools/multiproof-cone-20261021/'):];b=subprocess.check_output(['git','-C','/Users/dominic/ZK','show',f'{commit}:{p}'])
        gitfiles[rel]=(commit,p);expect[rel]=sha(b)
    env={'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'4','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':'{WS}/../PCWB_target_mp','CARGO_NET_OFFLINE':'true','RUSTFLAGS':'-C link-arg=-Wl,--threads=4','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'}
    return dict(frozen_workspace=True,crate_dir='tools/multiproof-cone-20261021',gitfiles=gitfiles,textfiles={},expect=expect,
      charon_command=[CH,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option','--include','core::option::Option']+sum([['--start-from','crate::'+roots_mod+'::'+r] for r in roots],[])+['--dest-file','{OUT}/repro.llbc','--','--manifest-path','{CRATE}/Cargo.toml','--offline','--release','--lib','--jobs','4'],
      aeneas_command=[AE,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest','{OUT}/raw','-subdir',ns,'-split-files','-emit-json','{OUT}/repro.llbc'],env=env,namespace=ns,
      recorded_original_tools=dict(charon=R18+'charon (sha256 daad69be..., identical to XRa_bin/charon)',aeneas='aeneas-b59d5188-lean432-extended-static sha256 4632746d... (NOT available on the host); substitute XRa_bin/aeneas-b59d5188-extended sha256 c0cf4fcc...'))
CONE_ROOTS=['verify_owned','valid_indices','binary_step','leaf_step','level_rows','levels','canonical_word','canonical_qm','expand_chunk','row_shape','semantic_offsets','check_values','expand_rows']
SETS['mp_cone_A']=mp('d28944b2a05','reference',CONE_ROOTS,'MultiproofConeRef')
SETS['mp_parser_A']=mp('d28944b2a05','parser_reference',['canonical_words','opening_scan','opening_rows','scan','header','semantic_rows','parse'],'MultiproofParserRef')
SETS['mp_sort_B']=mp('8c029994865','sort_reference',['insert_rows','sort_rows'],'MultiproofSortRef')
SETS['mp_cone_B']=mp('8c029994865','reference',CONE_ROOTS,'MultiproofConeRef')

def build(key,run,sets=SETS):
    s=sets[key];d=E/'sources'/key;files={}
    for rel,(rev,path) in s['gitfiles'].items():
        b=subprocess.check_output(['git','-C','/Users/dominic/ZK','show',f'{rev}:{path}']);assert sha(b)==s['expect'][rel],(rel,sha(b))
        (d/rel).parent.mkdir(parents=True,exist_ok=True);(d/rel).write_bytes(b);files[rel]=dict(sha256=sha(b),local=f'sources/{key}/{rel}',git=f'{rev}:{path}')
    for rel,t in s['textfiles'].items():
        b=t.encode();(d/rel).parent.mkdir(parents=True,exist_ok=True);(d/rel).write_bytes(b);files[rel]=dict(sha256=sha(b),local=f'sources/{key}/{rel}',git='reconstructed from the recorded extraction script literal')
    # the host side reads PCWB_crate/<rel>; the client uploads files under that name
    spec=dict(run=run,spec_id=key,**{k:v for k,v in s.items() if k not in('gitfiles','textfiles','expect')},files=files)
    (E/(run+'_spec.json')).write_text(json.dumps(spec,indent=1)+'\n');print(run,key,{k:v['sha256'][:12] for k,v in files.items()})
if __name__=='__main__':build(sys.argv[1],sys.argv[2])
