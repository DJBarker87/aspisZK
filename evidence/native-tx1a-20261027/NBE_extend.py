"""Add one frozen binary row cut; exact arm and write order, no shared edits."""
import pathlib,json,sys,difflib,hashlib
E=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBE_host as h
R=E.parents[1];base='crates/aspis-r1-cost-probe/src/'
mp=(R/(base+'multiproof.rs')).read_text();a=mp.index('                    if i + 1 < n',mp.index('pub fn verify_in_place'))
b=mp.index('\n                Arity::Eight =>',a);arm=mp[a:b];arm=arm[:arm.rfind('\n                }')]
cut='''fn NBE_row<H:Digest32>(hash:H,idx:&mut [u32;16],val:&mut [[u8;32];16],n:usize,nodes:&[u8],mut at:usize,mut w:usize,mut i:usize)->(bool,usize,usize,usize) {
 let parent=index_at(idx,i)>>1;
 let digest={
'''+arm.replace('return false','return (false,at,w,i)')+'''
 };
 idx[w]=parent;val[w]=digest;w+=1;
 (true,at,w,i)
}
'''
checks=r'''
#[kani::proof] #[kani::unwind(18)]
fn NBE_row_check(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();
 let old_idx=idx;let old_val=val;let nodes:[u8;64]=kani::any();
 let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let at:usize=kani::any();
 let length:usize=kani::any();let c:usize=kani::any();let k:usize=kani::any();
 kani::assume(n>0 && n<=16 && i<n && w<=i && length<=64 && at<=length && c<32 && k<16);
 let paired=i+1<n && idx[i+1]==idx[i]^1;
 let answer:[u8;32]=kani::any();let calls=Cell::new(0);
 // A missing sibling returns before the hash; pass arbitrary expected slices,
 // which will be checked only if digest is actually called.
 let sibling=if length-at>=32{&nodes[at..at+32]}else{&nodes[0..32]};
 let (left,right):(&[u8],&[u8])=if paired{(&old_val[i],&old_val[i+1])}else if idx[i]&1==0{(&old_val[i],sibling)}else{(sibling,&old_val[i])};
 let hash=Hash{answer,left,right,coordinate:c,calls:&calls};
 let (ok,next_at,next_w,next_i)=NBE_row(hash,&mut idx,&mut val,n,&nodes[..length],at,w,i);
 if !paired && length-at<32{
  assert!(!ok);assert_eq!(next_at,at);assert_eq!(next_w,w);assert_eq!(next_i,i);assert_eq!(calls.get(),0);
  assert_eq!(idx[k],old_idx[k]);assert_eq!(val[k][c],old_val[k][c]);
 }else{
  assert!(ok);assert_eq!(next_at,if paired{at}else{at+32});assert_eq!(next_w,w+1);assert_eq!(next_i,i+if paired{2}else{1});assert_eq!(calls.get(),1);
  assert_eq!(idx[k],if k==w{old_idx[i]>>1}else{old_idx[k]});assert_eq!(val[k][c],if k==w{answer[c]}else{old_val[k][c]});
 }
}
'''
r=h.remote_py(f'from pathlib import Path\nimport json\nb=Path({(h.B+"/NBE_src")!r});print(json.dumps({{n:(b/n).read_text() for n in [{(base+"NBE_multiproof.rs")!r},{(base+"NBE_keys.rs")!r},{(base+"multiproof.rs")!r},{(base+"candidate.rs")!r}]}}))');assert r.returncode==0,r.stderr
files=json.loads(r.stdout);assert 'fn NBE_row<' not in files[base+'NBE_multiproof.rs'],'refuse duplicate source extension';files[base+'NBE_multiproof.rs']+=cut+checks
r=h.remote_py(f'from pathlib import Path\nb=Path({(h.B+"/NBE_src")!r});(b/{(base+"NBE_multiproof.rs")!r}).write_text({files[base+"NBE_multiproof.rs"]!r})');assert r.returncode==0,r.stderr
(E/'NBE_harness_v1.patch').write_bytes((E/'NBE_harness.patch').read_bytes())
patch=''
for name,new in files.items():
 old=(R/name).read_text() if (R/name).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
(E/'NBE_harness.patch').write_text(patch)
(E/'NBE_ROW_ASSOCIATION.json').write_text(json.dumps(dict(source_file=base+'multiproof.rs',source_arm_byte_range=[a,b],source_arm_sha256=hashlib.sha256(arm.encode()).hexdigest(),generated_row_sha256=hashlib.sha256(cut.encode()).hexdigest(),substitutions=['Arity Two selected; parent computation before the arm unchanged','mut scalar locals passed/returned explicitly','false becomes (false,at,w,i); scratch mutations unchanged','idx[w],val[w],w increment copied in chronological order'],domain='RowDomain with physical window<=64; physical-slot rebase still OPEN'),indent=2)+'\n')
x=json.loads((E/'NBE_K001.json').read_text());x['attempt']='NBE_K011';x['command'][2]='NBE_K011';x['command'][3]='multiproof::NBE_multiproof::NBE_row_check';x['deps_fingerprint']['graph_receipt']='NBE_K011-graph.json';(E/'NBE_K011.json').write_text(json.dumps(x,indent=2)+'\n')
