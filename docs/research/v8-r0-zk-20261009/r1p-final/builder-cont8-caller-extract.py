#!/usr/bin/env python3
"""Build-host only: isolate the actual records function, with all copy crates.
A different, smaller target than the previous whole-compiler borrow failure.
No shipped edits, no full-compiler or unchanged failed-target rerun.
"""
import fcntl,hashlib,json,os,pathlib,shutil,subprocess,sys,time
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref8-20261021')
OLD=R
lock=(R/'rust-worker.lock').open('w');fcntl.flock(lock,fcntl.LOCK_EX)
KIT=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
SRC=R/'forest-tree-source'; E=R/'forest-tree-p6'
assert not (E/"charon/receipt.json").exists()
shutil.copytree(R/'source',SRC,ignore=shutil.ignore_patterns('target'),dirs_exist_ok=True)
p=SRC/'crates/aspis-statement/src/spend.rs'
before=p.read_text(); old='derive_nullifier_with(nullifier_key, salt, &mut hash_fields)'
new='nullifier_reference::derive_nullifier_owned(*nullifier_key, *salt)'
assert before.count(old)==1
p.write_text(before.replace(old,new))
(E).mkdir(exist_ok=True)
(E/'source-replacement.json').write_text(json.dumps(dict(
 before_sha256=hashlib.sha256(before.encode()).hexdigest(),after_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
 old=old,new=new,reason='P6 nullifier public equality route; reference extraction only, not production source'),indent=2)+'\n')
E.mkdir(exist_ok=True);(E/'generated').mkdir(exist_ok=True)
tree=SRC/'crates/aspis-statement/src/pool_v1/incremental_merkle.rs'
original=tree.read_text()
old_map="""ValidatedIncrementalMerkleTreeV1::from_parts(next_leaf_index, root, frontier, empty)
            .map(ValidatedIncrementalMerkleTreeV1::into_inner)"""
new_map="""match tree_reference::OwnedTree::from_parts(next_leaf_index, root, frontier, *empty) {
            Ok(value) => Ok(value.into_inner()), Err(error) => Err(error),
        }"""
assert original.count(old_map)==1
changed=original.replace(old_map,new_map)
old_ctor="""let validated = ValidatedIncrementalMerkleTreeV1::from_parts(
            self.next_leaf_index,
            self.root,
            self.frontier,
            empty,
        )?;"""
new_ctor=old_ctor.replace('ValidatedIncrementalMerkleTreeV1','tree_reference::OwnedTree').replace('            empty,','            *empty,')
assert changed.count(old_ctor)==2
changed=changed.replace(old_ctor,new_ctor)
tree.write_text(changed)
(E/'tree-replacement.json').write_text(json.dumps(dict(before_sha256=hashlib.sha256(original.encode()).hexdigest(),after_sha256=hashlib.sha256(changed.encode()).hexdigest(),old_map=old_map,new_map=new_map,old_ctor=old_ctor,new_ctor=new_ctor,status='Reference-source substitution; source-equality route separately audited, rejected output never a certificate'),indent=2)+'\n')
env=os.environ.copy();env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',RUSTFLAGS='-C link-arg=-Wl,--threads=4 --cfg aeneas_ref',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(R/'extraction-target'),ASPIS_SOURCE_REV=sys.argv[1])
def reserve():
    total=0
    for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip(): total+=int(v)
        except OSError: pass
    if total+8*2**30>55*2**30:
        with (E/'reservation-waits.jsonl').open('a') as f:f.write(json.dumps(dict(reserved_bytes=total,time=time.time()))+'\n')
        print('reservation hold',total,flush=True)
        time.sleep(20)
        return reserve()
def run(name,cmd):
    reserve()
    rc=subprocess.run(['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'capped.py'),str(E/name),'P6-owned-nullifier forest reference compilation/translation; records/lazy external opaque; no arithmetic release gate','--','timeout','180',*cmd],cwd=SRC,env=env).returncode
    print(name,rc,flush=True)
    return rc
cmd=[str(KIT/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--start-from','crate::pool_v1::pair_forest_trace::compile_forest_from_copies']
for dep in ['aspis_core::*','aspis_r0_block_writer_copies::*','aspis_r0_poseidon_copy::*','aspis_r0_writer_copies::*']:cmd+=['--include',dep]
cmd+=['--opaque','crate::pool_v1::pair_forest_copy_builder::records','--opaque','crate::poseidon2::external_linear_lazy']
cmd+=['--dest-file',str(E/'admission.llbc'),'--','--lib','-p','aspis-statement','--release','--offline','-j','4']
rc=run('charon',cmd)
if rc==0:
    llbc=E/'admission.llbc'; d=json.loads(llbc.read_text())
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
    adapted=E/'admission-renamed.llbc';adapted.write_text(json.dumps(d))
    (E/'metadata-rename.json').write_text(json.dumps(dict(old=old,new=new,paths=changes),indent=2)+'\n')
    rc=run('aeneas',[str(KIT/'bin/aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisBuilderForestTreeP6','-dest',str(E/'generated'),'-loops-to-rec','-print-unknown-externals',str(adapted)])
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
rec=dict(source_revision=sys.argv[1],target='crate::pool_v1::pair_forest_trace::compile_forest_from_copies',exit=rc,source_pins={str(p.relative_to(SRC)):pin(p) for root in ['crates/aspis-core','crates/aspis-statement','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon'] for p in (SRC/root).rglob('*') if p.is_file() and p.suffix in ['.rs','.toml']},tools={str(p):pin(p) for p in [KIT/'charon-target/release/charon',KIT/'bin/aeneas']},artifacts={str(p.relative_to(E)):pin(p) for p in E.rglob('*') if p.is_file()})
(E/'summary.json').write_text(json.dumps(rec,indent=2)+'\n')
print('final exit',rc,flush=True)
