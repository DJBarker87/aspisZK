from pathlib import Path
import sys,json,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBY_host as h
attrs='''#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
cases=[];files={};texts={}
def pair(mod,name,body,expr,scope):
 texts.setdefault(mod,'use super::*;\n')
 for neg in [False,True]:
  nn='NBY_'+name+('_wrong' if neg else '')
  texts[mod]+=attrs+'fn '+nn+'(){'+body+('assert!(!('+expr+'));' if neg else 'assert!('+expr+');')+'}\n'
  cases.append((mod,nn,scope,neg))
# Count: full arbitrary prestate, one complete binary group scan/commit.
body='''let mut level:[u32;16]=kani::any();let n:usize=kani::any();let i0:usize=kani::any();let w0:usize=kani::any();let k:usize=kani::any();let count0:usize=kani::any();kani::assume(i0<n&&n<=16&&w0<=i0&&k<16&&count0<=288);for a in i0..n-1{kani::assume(level[a]<level[a+1]);}let old=level[k];let expected=if i0+1<n&&level[i0+1]/2==level[i0]/2{i0+2}else{i0+1};let arity=Arity::Two;let mut i=i0;let mut w=w0;let mut count=count0;let parent=index_at(&level,i)>>arity.bits();let mut j=i;while j<n&&index_at(&level,j)>>arity.bits()==parent{j+=1;}count+=arity.width()-(j-i);level[w]=parent;w+=1;i=j;'''
pair('NBY_count','count_row',body,'i==expected&&w==w0+1&&count==count0+2-(expected-i0)&&level[k]==if k==w0{parent}else{old}','multiproof')
body='''let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(0<n&&n<=16&&k<16);for a in 0..n{kani::assume(input[a]<262144);if a+1<n{kani::assume(input[a]<input[a+1]);}}let accepted=well_formed(&input[..n]);assert!(accepted);let mut level=[0u32;MAX_BATCH];level[..n].copy_from_slice(&input[..n]);let count=0usize;let mut levels=0..Arity::Two.levels();let depth=levels.next();let w=0usize;let i=0usize;'''
pair('NBY_count','count_admitted_start',body,'level[k]==if k<n{input[k]}else{0}&&count==0&&depth==Some(0)&&levels.start==1&&w==0&&i==0','multiproof')
body='''let idx:[u32;16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&i==n&&w<=n&&k<16);let before=idx[k];let mut levels=kani::any::<u32>()..Arity::Two.levels();kani::assume(levels.start<=18);let depth=levels.start;let next_n=w;let next=levels.next();let next_w=0usize;let next_i=0usize;'''
pair('NBY_count','count_outer_transition',body,'next_n<=16&&next_w<=next_i&&next_i<=next_n&&idx[k]==before&&next==if depth<18{Some(depth)}else{None}','multiproof')
# Caller row: actual full scratch carrier, arbitrary i,w, node cursor.
texts['NBY_row']='''use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]
struct Port<'a>{left:*const u8,right:*const u8,c:usize,l:u8,r:u8,reply:[u8;32],calls:&'a Cell<usize>}
impl Digest32 for Port<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{assert_eq!(p.len(),3);assert_eq!(p[0],&[BINARY_NODE_TAG]);assert_eq!(p[1].len(),32);assert_eq!(p[2].len(),32);assert_eq!(p[1].as_ptr(),self.left);assert_eq!(p[2].as_ptr(),self.right);assert_eq!(p[1][self.c],self.l);assert_eq!(p[2][self.c],self.r);self.calls.set(self.calls.get()+1);self.reply}}
fn NBY_row<H:Digest32>(hash:H,idx:&mut[u32;16],val:&mut[[u8;32];16],n:usize,nodes:&[u8],mut at:usize,mut w:usize,mut i:usize)->(bool,usize,usize,usize){
 let parent=index_at(idx,i)>>Arity::Two.bits();
 let digest=if i+1<n&&index_at(idx,i+1)==index_at(idx,i)^1{let d=occupied_binary_parent(hash,val,i);i+=2;d}else{let Some(sibling)=nodes.get(at..at+32)else{return(false,at,w,i)};at+=32;let d=sibling_binary_parent(hash,val,i,sibling,index_at(idx,i)&1==0);i+=1;d};idx[w]=parent;val[w]=digest;w+=1;(true,at,w,i)
}
'''
common='''let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();let observed:usize=kani::any();let at:usize=kani::any();let prior:usize=kani::any();kani::assume(i<n&&n<=16&&w<=i&&k<16&&c<32&&observed<32&&at<=64&&prior<1000);let reply:[u8;32]=kani::any();let old_idx=idx[k];let old_val=val[k][observed];let parent=idx[i]/2;let calls=Cell::new(prior);'''
body=common+'''kani::assume(i+1<n&&idx[i+1]==idx[i]^1);let hash=Port{left:val[i].as_ptr(),right:val[i+1].as_ptr(),c,l:val[i][c],r:val[i+1][c],reply,calls:&calls};let out=NBY_row(hash,&mut idx,&mut val,n,&[],at,w,i);'''
pair('NBY_row','paired_frame',body,'out==(true,at,w+1,i+2)&&calls.get()==prior+1&&idx[k]==if k==w{parent}else{old_idx}&&val[k][observed]==if k==w{reply[observed]}else{old_val}','multiproof')
for side in [True,False]:
 body=common+f'''kani::assume(!(i+1<n&&idx[i+1]==idx[i]^1));kani::assume((idx[i]&1==0)=={str(side).lower()});let nodes:[u8;96]=kani::any();let selected=&nodes[at..at+32];let hash=Port{{left:{'val[i].as_ptr()' if side else 'selected.as_ptr()'},right:{'selected.as_ptr()' if side else 'val[i].as_ptr()'},c,l:{'val[i][c]' if side else 'selected[c]'},r:{'selected[c]' if side else 'val[i][c]'},reply,calls:&calls}};let out=NBY_row(hash,&mut idx,&mut val,n,&nodes,at,w,i);'''
 pair('NBY_row','supplied_'+('left' if side else 'right')+'_frame',body,'out==(true,at+32,w+1,i+1)&&calls.get()==prior+1&&idx[k]==if k==w{parent}else{old_idx}&&val[k][observed]==if k==w{reply[observed]}else{old_val}','multiproof')
body=common+'''kani::assume(!(i+1<n&&idx[i+1]==idx[i]^1));let nodes:[u8;96]=kani::any();let len:usize=kani::any();kani::assume(len<=96&&len<at+32);let hash=Port{left:val[i].as_ptr(),right:nodes.as_ptr(),c,l:val[i][c],r:nodes[c],reply,calls:&calls};let out=NBY_row(hash,&mut idx,&mut val,n,&nodes[..len],at,w,i);'''
pair('NBY_row','short_frame',body,'out==(false,at,w,i)&&calls.get()==prior&&idx[k]==old_idx&&val[k][observed]==old_val','multiproof')
for mod,s in texts.items():files['crates/aspis-r1-cost-probe/src/'+mod+'.rs']=s
for owner,mods in [('multiproof.rs',['NBY_count','NBY_row'])]:
 r=h.remote_py(f'from pathlib import Path\nprint(Path({(h.B+"/NBY_src/crates/aspis-r1-cost-probe/src/"+owner)!r}).read_text(),end="")');assert r.returncode==0,r.stderr
 files['crates/aspis-r1-cost-probe/src/'+owner]=r.stdout+''.join(f'\n#[cfg(kani)]\n#[path="{m}.rs"]\nmod {m};\n' for m in mods)
h.admit('NBY_UPLOAD2')
r=h.remote_py(f'from pathlib import Path\nb=Path({h.B!r})\nfor n,s in {files!r}.items():(b/"NBY_src"/n).write_text(s)');assert r.returncode==0,r.stderr
patch=''
for n,s in files.items():
 old=(R/n).read_text() if (R/n).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NBY_count_row.patch').write_text(patch)
base=json.loads((E/'NBY_K001.json').read_text())
for num,(mod,name,scope,neg) in enumerate(cases,9):
 a=f'NBY_K{num:03}';cfg=json.loads(json.dumps(base));cfg.update(attempt=a,command=['python3','NBY_gate.py',a,scope+'::'+mod+'::'+name,'--cbmc-args','--unwinding-assertions'],sources=base['sources']+['NBY_src/'+n for n in files],expected_negative=neg)
 cfg['sources']=list(dict.fromkeys(cfg['sources']));cfg['deps_fingerprint']['graph_receipt']=a+'-graph.json'
 for k in ['reservation_retries','source_revision','source_tree_dirty']:cfg.pop(k,None)
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
