from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
path='crates/aspis-r1-cost-probe/src/candidate.rs'
src=subprocess.check_output(['git','show',REV+':'+path],text=True)
start=src.index('        let key = batch_key_at(&keys, key_position);');end=src.index('\n    let count = multiproof::node_count',start)
body=src[start:end];assert body.endswith('\n    }');body=body[:-6]
# Local records replace only the leaf call; continue maps to the one-step cut exit.
cut=body.replace('let leaf = batch_leaf(hash, tree, q);','let leaf = log.leaf(tree,q);').replace('continue;','return Ok(());').replace('key_position += 1;','*key_position += 1;').replace('batch_key_at(&keys, key_position)','batch_key_at(&keys, *key_position)').replace('d > 0','*d > 0').replace('d - 1','*d - 1').replace('idx[d]','idx[*d]').replace('val[d]','val[*d]').replace('d += 1;','*d += 1;')
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
struct Log<'a>{proof:&'a[u8],lo:usize,position:usize,tree:usize,reply:[u8;32],calls:usize}
impl<'a> Log<'a>{fn leaf(&mut self,tree:usize,q:&[u8])->[u8;32]{let expected=opening(self.proof,self.lo+self.position);assert_eq!(tree,self.tree);assert_eq!(q.as_ptr(),expected.as_ptr());assert_eq!(q.len(),832);self.calls+=1;self.reply}}
fn step(proof:&[u8],lo:usize,tree:usize,keys:[u64;16],key_position:&mut usize,d:&mut usize,idx:&mut[u32;16],val:&mut[[u8;32];16],log:&mut Log)->Result<(),Error>{
'''+cut+'\nOk(())}\n'+'''
fn check<const T:usize,const C:usize>(){
 let proof:[u8;57607]=kani::any();let pos:usize=kani::any();kani::assume(pos<12);
 let u:u32=kani::any();kani::assume(u<262144);let index=if T==2{u/4}else{u};
 let mut keys:[u64;16]=kani::any();let kp:usize=kani::any();kani::assume(kp<12);keys[kp]=((index as u64)<<8)|(pos as u64);
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let oldidx=idx;let oldval=val;
 let before:usize=kani::any();kani::assume(before<12);let mut d=before;let mut at=kp;
 let leaf:[u8;32]=kani::any();let mut log=Log{proof:&proof,lo:10,position:pos,tree:T,reply:leaf,calls:0};
 let duplicate=before>0&&oldidx[before-1]==index;let unequal=duplicate&&oldval[before-1]!=leaf;
 let mut result=step(&proof,10,T,keys,&mut at,&mut d,&mut idx,&mut val,&mut log);
 let j:usize=kani::any();kani::assume(j<16);let b:usize=kani::any();kani::assume(b<32);
 if cfg!(NIL_invert){match C{0=>log.calls^=1,1=>result=if result.is_ok(){Err(Error::Merkle)}else{Ok(())},2=>d^=1,3=>idx[j]^=1,4=>val[j][b]^=1,_=>d=if duplicate{before^1}else{before}}}
 let good=match C{
 0=>log.calls==1&&at==kp+1,
 1=>if unequal{matches!(result,Err(Error::Merkle))}else{result.is_ok()},
 2=>d==before+if duplicate{0}else{1},
 3=>idx[j]==if !duplicate&&j==before{index}else{oldidx[j]},
 4=>val[j][b]==if !duplicate&&j==before{leaf[b]}else{oldval[j][b]},
 _=>if duplicate{d==before&&idx[j]==oldidx[j]&&val[j][b]==oldval[j][b]}else{d==before+1}
 };assert!(good);}
'''
rows=[]
for t in range(3):
 for c in range(6):
  n=f'tree{t}_facet{c}'
  for suffix in ['', '_renamed']:
   s+='#[kani::proof]\n#[kani::unwind(36)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn '+n+suffix+'(){check::<'+str(t)+','+str(c)+'>();}\n'
  rows.append(dict(family=n,function='verifier::candidate::NIL_tree_native::'+n,rename='verifier::candidate::NIL_tree_native::'+n+'_renamed',status='planned',domain='SAME proof57607, batch1 lo10, position<12, key_position<12, d<12; index from SAME canonical query; full arbitrary idx/val and leaf reply'))
inputs=json.loads((E/'NIL_NATIVE_INPUTS.json').read_text());inputs[path]=src+'\n#[cfg(kani)]\n#[path="NIL_tree_native.rs"]\nmod NIL_tree_native;\n';inputs['crates/aspis-r1-cost-probe/src/NIL_tree_native.rs']=s
(E/'NIL_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=2)+'\n');(E/'NIL_tree_native.rs.txt').write_text(s)
pins=json.loads((E/'NIL_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in inputs.items()});(E/'NIL_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(E/'NIL_TREE_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'NIL_TREE_CUT.json').write_text(json.dumps(dict(frozen=REV,path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),fragment_sha256=hashlib.sha256(body.encode()).hexdigest(),fragment=body,changes=['leaf call to explicit LOCAL record oracle','one-iteration continue maps to cut return','key_position and d are mutable caller state parameters'],callees=['batch_key_at','opening','same_batch_index','same_batch_leaf'],missing='Full sorted-key producer, tree induction, padding/node_count/verify and parent composition remain OPEN'),indent=2)+'\n')
patch=''
for n,s in inputs.items():
 try:old=subprocess.check_output(['git','show',REV+':'+n],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NIL_native.patch').write_text(patch)
