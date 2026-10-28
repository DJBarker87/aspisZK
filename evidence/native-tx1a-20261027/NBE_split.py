"""Split the timed-out row observation into state and callback obligations."""
from pathlib import Path
import sys,json,difflib,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBE_host as h
base='crates/aspis-r1-cost-probe/src/';R=E.parents[1]
r=h.remote_py(f'from pathlib import Path\nimport json\nb=Path({(h.B+"/NBE_src")!r});print(json.dumps({{n:(b/n).read_text() for n in [{(base+"NBE_multiproof.rs")!r},{(base+"NBE_keys.rs")!r},{(base+"multiproof.rs")!r},{(base+"candidate.rs")!r}]}}))');assert r.returncode==0,r.stderr
files=json.loads(r.stdout);s=files[base+'NBE_multiproof.rs'];assert 'fn NBE_row_state' not in s,'refuse duplicate source extension';start=s.index('#[kani::proof] #[kani::unwind(18)]\nfn NBE_row_check')
new=s[start:].replace('fn NBE_row_check','fn NBE_row_state')
a=new.index(' // A missing sibling');b=new.index(' let (ok,next_at',a)
new=new[:a]+' let hash=Counter{answer,calls:&calls};\n'+new[b:]
s+='''
#[derive(Clone,Copy)]struct Counter<'a>{answer:[u8;32],calls:&'a Cell<usize>}
impl Digest32 for Counter<'_>{fn digest(&self,_:&[&[u8]])->[u8;32]{self.calls.set(self.calls.get()+1);self.answer}}
'''+new+r'''
#[kani::proof] #[kani::unwind(18)]
fn NBE_last_sibling(){
 let values:[[u8;32];16]=kani::any();let sibling:[u8;32]=kani::any();let c:usize=kani::any();let left:bool=kani::any();kani::assume(c<32);
 let answer:[u8;32]=kani::any();let calls=Cell::new(0);
 let hash=Hash{answer,left:if left{&values[15]}else{&sibling},right:if left{&sibling}else{&values[15]},coordinate:c,calls:&calls};
 assert_eq!(sibling_binary_parent(hash,&values,15,&sibling,left)[c],answer[c]);assert_eq!(calls.get(),1);
}
'''
files[base+'NBE_multiproof.rs']=s
# One slot_offset iteration, with source order and original constants.
compact=(R/(base+'compact.rs')).read_text();a=compact.index('        at += 32 * SLOT_NODES[i];');b=compact.index('\n    }',a);body=compact[a:b]
s=files[base+'NBE_keys.rs'];s+='\nfn NBE_offset_step(mut at:usize,mut i:usize)->(usize,usize){\n'+body+'\n(at,i)\n}\n'+r'''
#[kani::proof] #[kani::unwind(2)]
fn NBE_offset(){
 let at:usize=kani::any();let i:usize=kani::any();kani::assume(at<=57607 && i<6);
 let (next,j)=NBE_offset_step(at,i);
 let cap=match i{0=>146,1=>146,2=>128,3=>172,4=>172,_=>150};
 assert_eq!(next,at+32*cap);assert_eq!(j,i+1);
}
''';files[base+'NBE_keys.rs']=s
(E/'NBE_harness_v2.patch').write_bytes((E/'NBE_harness.patch').read_bytes());patch=''
for name,new in files.items():
 old=(R/name).read_text() if (R/name).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
(E/'NBE_harness.patch').write_text(patch)
r=h.remote_py(f'from pathlib import Path\nimport json\nb=Path({(h.B+"/NBE_src")!r});x=json.loads({json.dumps(json.dumps(files))})\nfor n,s in x.items():(b/n).write_text(s)');assert r.returncode==0,r.stderr
for num,mod,name in [(12,'multiproof::NBE_multiproof','NBE_row_state'),(13,'multiproof::NBE_multiproof','NBE_last_sibling'),(14,'verifier::candidate::NBE_keys','NBE_offset')]:
 x=json.loads((E/'NBE_K011.json').read_text());a=f'NBE_K{num:03}';x['attempt']=a;x['command'][2]=a;x['command'][3]=mod+'::'+name;x['deps_fingerprint']['graph_receipt']=a+'-graph.json';(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
(E/'NBE_TIMEOUT_SPLIT.json').write_text(json.dumps(dict(excluded='NBE_K011: combined row state and callback address timed out; not rerun',replacement='NBE_K012: exact same native row, check state/cursor/frame and one call; callback byte-address checks separated into K010 plus K013 last index',slot_step_body_sha256=hashlib.sha256(body.encode()).hexdigest(),field_stubs=[]),indent=2)+'\n')
# Remove only solver temp owned by this run; retain all source/evidence.
r=h.remote_py(f'from pathlib import Path\nimport json\np=Path({(h.B+"/NBE_tmp")!r});removed=[]\nfor f in p.iterdir():\n if f.is_file() and (f.name.startswith("external-sat") or f.name.startswith("smt2_dec_problem")):removed.append(f.name);f.unlink()\nprint(json.dumps(dict(removed=removed,remaining=[f.name for f in p.iterdir()])))');assert r.returncode==0
(E/'NBE_K011_TMP_CLEANUP.json').write_text(r.stdout)
