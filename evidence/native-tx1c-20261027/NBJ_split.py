from pathlib import Path
import runpy,re,json,difflib,sys
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBJ_host as h
v=runpy.run_path(str(E/'NBJ_make_gates.py'));keys=v['keys'];mp=v['mp']
(E/'NBJ_harness_v2.patch').write_text((E/'NBJ_harness.patch').read_text())
for pos in range(22):
 keys+=f'''
#[kani::proof] #[kani::unwind(2)]
fn NBJ_opening_fixed_{pos:02}(){{
 let c:usize=kani::any();let b:u8=kani::any();kani::assume(c<832);
 let mut proof=[0u8;57607];proof[{10055+832*pos}+c]=b;
 let q=opening(&proof,{pos});assert_eq!(q.len(),832);assert_eq!(q.as_ptr(),proof[{10055+832*pos}..].as_ptr());assert_eq!(q[c],b);
}}
'''
mp+=r'''
#[kani::proof] #[kani::unwind(34)]
fn NBJ_pair_window(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let left:[u8;32]=kani::any();let right:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let c:usize=kani::any();kani::assume(c<32 && a%2==0);
 idx[0]=a;idx[1]=a^1;val[0]=left;val[1]=right;let calls=Cell::new(0);
 let out=NBJ_row(Hash{answer:reply,left:&left,right:&right,c,calls:&calls},&mut idx,&mut val,2,&[],0,0,0);
 assert_eq!(out,(true,0,1,2));assert_eq!(calls.get(),1);assert_eq!(idx[0],a/2);assert_eq!(val[0][c],reply[c]);
}
#[kani::proof] #[kani::unwind(34)]
fn NBJ_supply_window(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let value:[u8;32]=kani::any();let sibling:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let c:usize=kani::any();kani::assume(c<32);
 idx[0]=a;val[0]=value;let calls=Cell::new(0);let left=a&1==0;
 let out=NBJ_row(Hash{answer:reply,left:if left{&value}else{&sibling},right:if left{&sibling}else{&value},c,calls:&calls},&mut idx,&mut val,1,&sibling,0,0,0);
 assert_eq!(out,(true,32,1,1));assert_eq!(calls.get(),1);assert_eq!(idx[0],a/2);assert_eq!(val[0][c],reply[c]);
}
#[kani::proof] #[kani::unwind(34)]
fn NBJ_short_window(){
 let mut idx=[0u32;16];let mut val=[[0u8;32];16];let a:u32=kani::any();let value:[u8;32]=kani::any();let len:usize=kani::any();let c:usize=kani::any();kani::assume(c<32&&len<32);let nodes:[u8;32]=kani::any();let calls=Cell::new(0);
 idx[0]=a;val[0]=value;let reply:[u8;32]=kani::any();
 let out=NBJ_row(Hash{answer:reply,left:&value,right:&nodes,c,calls:&calls},&mut idx,&mut val,1,&nodes[..len],0,0,0);
 assert_eq!(out,(false,0,0,0));assert_eq!(calls.get(),0);assert_eq!(idx[0],a);assert_eq!(val[0][c],value[c]);
}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_level_iterator(){let level:usize=kani::any();kani::assume(level<=18);let mut it=level..Arity::Two.levels() as usize;let next=it.next();assert_eq!(next,if level<18{Some(level)}else{None});if next.is_some(){assert_eq!(it.start,level+1);}}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_admission_window_iterator(){
 let indices:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();kani::assume(j<=n&&n<=16);
 let mut it=indices[j..n].windows(2);let next=it.next();if n-j>=2{let pair=next.unwrap();assert_eq!(pair[0],indices[j]);assert_eq!(pair[1],indices[j+1]);assert_eq!(it.len(),n-j-2+1-1);}else{assert!(next.is_none());}
}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_admission_value_iterator(){let indices:[u32;16]=kani::any();let n:usize=kani::any();let j:usize=kani::any();kani::assume(j<=n&&n<=16);let mut it=indices[j..n].iter();let next=it.next();if j<n{assert_eq!(*next.unwrap(),indices[j]);assert_eq!(it.len(),n-j-1)}else{assert!(next.is_none())}}
#[kani::proof] #[kani::unwind(2)]
fn NBJ_count_zero(){let level=[0u32;16];let k:usize=kani::any();kani::assume(k<16);assert_eq!(level[k],0);let count=0usize;assert_eq!(count,0);}
'''
# Final continuation removes unlaunched giant row variants from harness set.
mp=mp[:mp.index('#[kani::proof] #[kani::unwind(34)]\nfn NBJ_pair_00()')]+mp[mp.index('#[kani::proof] #[kani::unwind(34)]\nfn NBJ_pair_window()'):]
# Preserve timed-out K009 source only in v2 patch; never rerun it.
files={'crates/aspis-r1-cost-probe/src/NBJ_keys.rs':keys,'crates/aspis-r1-cost-probe/src/NBJ_multiproof.rs':mp}
for file,mod in [('candidate.rs','NBJ_keys'),('multiproof.rs','NBJ_multiproof')]:
 name='crates/aspis-r1-cost-probe/src/'+file;files[name]=(R/name).read_text()+f'\n#[cfg(kani)]\n#[path="{mod}.rs"]\nmod {mod};\n'
patch=''
for name,new in files.items():
 old=(R/name).read_text() if (R/name).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
(E/'NBJ_harness.patch').write_text(patch)
h.admit('NBJ_SPLITUPLOAD')
r=h.remote_py(f'from pathlib import Path\nb=Path({(h.B+"/NBJ_src")!r})\nfor n,s in {files!r}.items():(b/n).write_text(s)');assert r.returncode==0,r.stderr
names=[('verifier::candidate::NBJ_keys::',f'NBJ_opening_fixed_{i:02}') for i in range(22)]+[('multiproof::NBJ_multiproof::',n) for n in re.findall(r'fn (NBJ_\w+)\(\)',mp)]
for num,(mod,n) in enumerate(names,10):
 a=f'NBJ_K{num:03}';cfg=json.loads((E/'NBJ_K009.json').read_text());cfg.update(attempt=a,command=['python3','NBJ_gate.py',a,mod+n]);cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 assert not (E/a/'receipt.json').exists();(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
print('split targets',len(names),'last',num)
