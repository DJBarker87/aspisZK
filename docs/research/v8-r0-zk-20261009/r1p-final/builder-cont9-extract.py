#!/usr/bin/env python3
"""Host-only continuation: preserve inherited reference substitutions; opaque one Drop."""
import pathlib, subprocess, os, json, hashlib, sys, time, fcntl
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref9-20261021')
S=R/'source'; E=R/sys.argv[2]; E.mkdir(exist_ok=True)
lock=(R/'rust-stage.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
KIT=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
env=os.environ.copy();env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',RUSTFLAGS='-C link-arg=-Wl,--threads=4 --cfg aeneas_ref',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(R/'extraction-target'),ASPIS_SOURCE_REV=sys.argv[1])
def run(name,cmd):
    while True:
        total=0
        for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
            try:
                v=p.read_text().strip()
                if v!='max' and (p.parent/'cgroup.procs').read_text().strip():total+=int(v)
            except OSError:pass
        if total+8*2**30<=55*2**30:break
        print('reservation hold',total,flush=True);time.sleep(20)
    (E/(name+'-reservation.json')).write_text(json.dumps(dict(reserved_bytes=total,time=time.time()))+'\n')
    rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(E/name),'Charon compilation or Aeneas translation; no arithmetic release gate','--','timeout','180',*cmd],cwd=S,env=env).returncode
    print(name,rc,flush=True)
    print((E/name/'stderr.log').read_text()[-5000:],flush=True)
    return rc
pattern='crate::state_only_trace::{impl core::ops::drop::Drop for crate::state_only_trace::StateOnlyTraceFoundation}::drop'
cmd=[str(KIT/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--start-from','crate::pool_v1::pair_forest_trace::compile_forest_from_copies']
for dep in ['aspis_core::*','aspis_r0_block_writer_copies::*','aspis_r0_poseidon_copy::*','aspis_r0_writer_copies::*']:cmd+=['--include',dep]
cmd+=['--opaque','crate::pool_v1::pair_forest_copy_builder::records','--opaque','crate::poseidon2::external_linear_lazy','--opaque',pattern]
cmd+=['--dest-file',str(E/'admission.llbc'),'--','--lib','-p','aspis-statement','--release','--offline','-j','4']
rc=0 if '--resume-charon' in sys.argv[3:] else run('charon',cmd)
if rc==0:
    d=json.loads((E/'admission.llbc').read_text())
    drops=[f for f in d['translated']['fun_decls'] if f and f['item_meta']['name'][-1]=={'Ident':['drop',0]} and 'state_only_trace' in str(f['item_meta']['name'])]
    (E/'drop-selection.json').write_text(json.dumps(drops,indent=2)+'\n')
    assert len(drops)==1 and drops[0]['body'] == 'Opaque', 'Drop was not made opaque'
    decl=next(x for x in d['translated']['fun_decls'] if x and x['item_meta']['name'][-2:]==[{'Ident':['PoolV1PairTraceErrorV1',0]},{'Ident':['PairLeaf',0]}])
    old=decl['item_meta']['name'];new=old[:-1]+[{'Ident':['PairLeafCtor',0]}];changes=[]
    def visit(x,path):
        if isinstance(x,dict):
            for k,v in x.items():
                if v==old:x[k]=new;changes.append(path+'/'+k)
                elif isinstance(v,(list,dict)):visit(v,path+'/'+k)
        elif isinstance(x,list):
            for i,v in enumerate(x):
                if v==old:x[i]=new;changes.append(path+'/'+str(i))
                elif isinstance(v,(list,dict)):visit(v,path+'/'+str(i))
    visit(d,'')
    if '--rename-constructors' in sys.argv:
        enum_names={json.dumps(t['item_meta']['name']):{v['name'] for v in t['kind']['Enum']} for t in d['translated']['type_decls'] if t and isinstance(t['kind'],dict) and 'Enum' in t['kind']}
        constructors=[f['item_meta']['name'] for f in d['translated']['fun_decls'] if f and f['item_meta']['name'][-1].get('Ident',[None])[0] in enum_names.get(json.dumps(f['item_meta']['name'][:-1]),set())]
        for name in constructors:
            old=name; new=old[:-1]+[{'Ident':[old[-1]['Ident'][0]+'Ctor',0]}];visit(d,'')
    if '--rename-tuple-constructors' in sys.argv:
        type_names={json.dumps(t['item_meta']['name']) for t in d['translated']['type_decls'] if t}
        for f in d['translated']['fun_decls']:
            if f and json.dumps(f['item_meta']['name']) in type_names:
                f['item_meta']['attr_info']['rename']=f['item_meta']['name'][-1]['Ident'][0]+'Ctor'
                changes.append('/translated/fun_decls/'+str(f['def_id'])+'/item_meta/attr_info/rename')
    adapted=E/'admission-renamed.llbc';adapted.write_text(json.dumps(d))
    (E/'metadata-rename.json').write_text(json.dumps(dict(old=old,new=new,paths=changes),indent=2)+'\n')
    (E/'generated').mkdir(exist_ok=True)
    rc=run('aeneas-types' if '--rename-tuple-constructors' in sys.argv else ('aeneas-names' if '--rename-constructors' in sys.argv else 'aeneas'),[str(KIT/'bin/aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisBuilderForestDropP6','-dest',str(E/'generated'),'-loops-to-rec','-print-unknown-externals',str(adapted)])
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
(E/('summary-types.json' if '--rename-tuple-constructors' in sys.argv else ('summary-renamed.json' if '--rename-constructors' in sys.argv else 'summary.json'))).write_text(json.dumps(dict(source_revision=sys.argv[1],exit=rc,opaque_flag=['--opaque',pattern],source_pins={str(p.relative_to(S)):pin(p) for p in S.rglob('*.rs') if 'target' not in p.parts},tool_pins={str(p):pin(p) for p in [KIT/'charon-target/release/charon',KIT/'bin/aeneas']}),indent=2)+'\n')
sys.exit(rc)
