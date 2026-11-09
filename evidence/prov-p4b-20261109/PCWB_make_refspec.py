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

# ---- withdrawal-caller cut crate: sources come from the retained archive evidence/withdrawal-caller-extraction-20261016
WC_ARCH='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/wc_x/input/'
SETS['wc']=dict(frozen_workspace=False,crate_dir='crate',gitfiles={},textfiles={},expect={},
  localfiles={'Cargo.toml':('416796c3bb52f23ed3335b6a217dd5752509d8cd8c0271bc3c00ea894a9b4807','caller-extraction-evidence.tar.gz:input/Cargo.toml'),
              'Cargo.lock':('5781c880361f3041f83d648c883bcf014b679f2d559bfd12178eca2588f2a1ac','caller-extraction-evidence.tar.gz:input/Cargo.lock'),
              'lib.rs':('166185cd1986e82a5ec27d85f5f549067cd0afa4917e24226c19450cffe739dc','caller-extraction-evidence.tar.gz:input/lib.rs')},
  charon_command=[CH,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::pool_v1::payment_relation::encode_pool_v1_withdrawal_public_v1','--dest-file','{OUT}/repro.llbc','--','--locked','--offline','--release','--lib','--no-default-features'],
  aeneas_command=[AE,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1WithdrawalCaller','-dest','{OUT}/raw','-subdir','AspisR1WithdrawalCaller','-split-files','-emit-json','{OUT}/repro.llbc'],
  env={'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':'{WS}/../PCWB_target_wc','CARGO_NET_OFFLINE':'true','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'},
  namespace='AspisR1WithdrawalCaller',recorded_original_tools=dict(charon='r18 charon (sha daad69be per archive pins; XRa_bin/charon identical)',aeneas='aspis-r1-r18-tools-20261016/bin/aeneas (b59d5188 unpatched native); substituted XRa_bin/aeneas-b59d5188-extended'))

# ---- archive-based standalone cut crates (input/ tree of a retained extraction packet)
import tarfile,io
SPL='docs/research/100bit-spend-path-20261013/evidence/source-proof-loop-extraction-20261019/'
def arch(key,archive,starts,includes,ns,extra_charon_tail,prefix='input/'):
    blob=subprocess.check_output(['git','-C','/Users/dominic/ZK','show','research:'+archive]);t=tarfile.open(fileobj=io.BytesIO(blob))
    files={}
    for ti in t:
        nm=ti.name[2:] if ti.name.startswith('./') else ti.name
        if ti.isfile() and nm.startswith(prefix):
            rel=nm[len(prefix):]
            if rel in('Cargo.toml','Cargo.lock') or (rel.startswith('src/') and rel.endswith('.rs')):files[rel]=t.extractfile(ti).read()
    d=dict(frozen_workspace=False,crate_dir='crate',gitfiles={},textfiles={},expect={},rawfiles={k:(sha(v),archive+':'+prefix+k,v) for k,v in files.items()},
      charon_command=[CH,'cargo','--preset','aeneas','--mir','built','--sysroot','default']+includes+sum([['--start-from',x] for x in starts],[])+['--dest-file','{OUT}/repro.llbc','--']+extra_charon_tail,
      aeneas_command=[AE,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest','{OUT}/raw','-subdir',ns,'-split-files','-emit-json','{OUT}/repro.llbc'],
      env={'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':'{WS}/../PCWB_target_'+key,'CARGO_NET_OFFLINE':'true','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'},namespace=ns,
      recorded_original_tools=dict(charon='r18 charon (daad69be; XRa_bin/charon identical)',aeneas='aspis-r1-r18-tools-20261016/bin/aeneas sha 959659a6 (NOT on host); substituted XRa_bin/aeneas-b59d5188-extended c0cf4fcc'))
    return d
TAIL=['--locked','--offline','--release','--lib','--no-default-features','--jobs','1']
INC2=['--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err']
SETS['sem_calls']=arch('sem_calls',SPL+'semantic-calls-root-v5-results-20261019.tar.gz',['crate::r1_semantic::semantic_boundary_entry','crate::r1_semantic::semantic_value_entry'],INC2,'AspisR1SemanticCallExtraction',['--manifest-path','{CRATE}/Cargo.toml']+TAIL)
SETS['batched_w']=arch('batched_w',SPL+'batched-calls-root-v5-results-20261019.tar.gz',['crate::batched_weights::push_entry','crate::batched_weights::value_entry'],INC2,'AspisR1BatchedWeightsExtraction',['--manifest-path','{CRATE}/Cargo.toml']+TAIL)

def build(key,run,sets=SETS):
    s=sets[key];d=E/'sources'/key;files={}
    for rel,(rev,path) in s['gitfiles'].items():
        b=subprocess.check_output(['git','-C','/Users/dominic/ZK','show',f'{rev}:{path}']);assert sha(b)==s['expect'][rel],(rel,sha(b))
        (d/rel).parent.mkdir(parents=True,exist_ok=True);(d/rel).write_bytes(b);files[rel]=dict(sha256=sha(b),local=f'sources/{key}/{rel}',git=f'{rev}:{path}')
    for rel,(h,prov) in s.get('localfiles',{}).items():
        b=(Path(WC_ARCH)/rel).read_bytes();assert sha(b)==h,(rel,sha(b))
        (d/rel).parent.mkdir(parents=True,exist_ok=True);(d/rel).write_bytes(b);files[rel]=dict(sha256=h,local=f'sources/{key}/{rel}',git=prov)
    for rel,(h,prov,raw) in s.get('rawfiles',{}).items():
        (d/rel).parent.mkdir(parents=True,exist_ok=True);(d/rel).write_bytes(raw);files[rel]=dict(sha256=h,local=f'sources/{key}/{rel}',git=prov)
    for rel,t in s['textfiles'].items():
        b=t.encode();(d/rel).parent.mkdir(parents=True,exist_ok=True);(d/rel).write_bytes(b);files[rel]=dict(sha256=sha(b),local=f'sources/{key}/{rel}',git='reconstructed from the recorded extraction script literal')
    # the host side reads PCWB_crate/<rel>; the client uploads files under that name
    spec=dict(run=run,spec_id=key,**{k:v for k,v in s.items() if k not in('gitfiles','textfiles','expect','localfiles','rawfiles')},files=files)
    (E/(run+'_spec.json')).write_text(json.dumps(spec,indent=1)+'\n');print(run,key,{k:v['sha256'][:12] for k,v in files.items()})
if __name__=='__main__':build(sys.argv[1],sys.argv[2])
