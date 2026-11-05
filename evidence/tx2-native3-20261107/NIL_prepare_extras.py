from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-r1-cost-probe/src/candidate.rs';src=subprocess.check_output(['git','show',REV+':'+path],text=True)
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn build(){let queries:[u32;22]=kani::any();let j:usize=kani::any();kani::assume(j<12);let tree:usize=kani::any();kani::assume(tree<3);let mut keys:[u64;16]=kani::any();let before=keys;
 let u=queries[10+j];let index=if tree==2{u/4}else{u};keys[j]=((index as u64)<<8)|(j as u64);
 let k:usize=kani::any();kani::assume(k<16);if cfg!(NIL_invert){keys[k]^=1;}assert_eq!(keys[k],if k==j{(index as u64)*256+j as u64}else{before[k]});}
fn sort(){let mut keys:[u64;16]=kani::any();let before=keys;let mut j:usize=kani::any();kani::assume(j<12);let old=j;
 let more=j>0&&batch_key_at(&keys,j-1)>batch_key_at(&keys,j);
 if j>0&&batch_key_at(&keys,j-1)>batch_key_at(&keys,j){keys.swap(j-1,j);j-=1;}
 let k:usize=kani::any();kani::assume(k<16);if cfg!(NIL_invert){keys[k]^=1;}
 assert_eq!(j,if more{old-1}else{old});assert_eq!(keys[k],if more&&k==old{before[old-1]}else if more&&k+1==old{before[old]}else{before[k]});}
'''
keyrows=[]
for name in ['build','sort']:
 for suffix in ['', '_renamed']:
  s+='#[kani::proof]\n#[kani::unwind(36)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u64]>::copy_from_slice,KMX_copy_from_slice)]\nfn key_'+name+suffix+'(){'+name+'();}\n'
 keyrows.append(dict(family='key_'+name,function='verifier::candidate::NIL_key_native::key_'+name,rename='verifier::candidate::NIL_key_native::key_'+name+'_renamed',status='planned',domain='batch1 lo10/n12; all u32 query words; arbitrary16 keys; one build or insertion-sort iteration on arbitrary j<12 and selected k<16'))
# Literal 3-call values body, with only child calls routed to LOCAL record oracle.
a=src.index('    let mut idx = [0u32; multiproof::MAX_BATCH];',src.index('fn batch_merkle_values<'));z=src.index('\n}\n',a);body=src[a:z].replace('batch_tree(proof, queries, root0, batch, 0, &mut idx, &mut val, hash)','log.tree(proof, queries, root0, batch, 0, &mut idx, &mut val)').replace('batch_tree(proof, queries, root1, batch, 1, &mut idx, &mut val, hash)','log.tree(proof, queries, root1, batch, 1, &mut idx, &mut val)').replace('batch_tree(proof, queries, root2, batch, 2, &mut idx, &mut val, hash)','log.tree(proof, queries, root2, batch, 2, &mut idx, &mut val)')
p='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn error()->Error{match kani::any::<u8>()%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
struct Log<'a>{proof:&'a[u8],queries:[u32;22],roots:[[u8;32];3],replies:[Option<Error>;3],after_idx:[[u32;16];3],after_val:[[[u8;32];16];3],calls:usize,row:usize,byte:usize,query:usize,abort:usize}
impl<'a> Log<'a>{fn tree(&mut self,proof:&[u8],queries:[u32;22],root:[u8;32],batch:usize,tree:usize,idx:&mut[u32;16],val:&mut[[u8;32];16])->Result<(),Error>{let c=self.calls;assert!(c<3);assert_eq!(tree,c);assert_eq!(batch,1);assert_eq!(proof.as_ptr(),self.proof.as_ptr());assert_eq!(proof.len(),self.proof.len());assert_eq!(queries[self.query],self.queries[self.query]);let byte=if cfg!(NIL_invert){root[self.byte]^1}else{root[self.byte]};assert_eq!(byte,self.roots[c][self.byte]);assert_eq!(idx[self.row],if c==0{0}else{self.after_idx[c-1][self.row]});assert_eq!(val[self.row][self.byte],if c==0{0}else{self.after_val[c-1][self.row][self.byte]});self.calls+=1;if c==self.abort{kani::assume(false);}*idx=self.after_idx[c];*val=self.after_val[c];match self.replies[c]{None=>Ok(()),Some(e)=>Err(e)}}}
fn values(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],batch:usize,log:&mut Log)->Result<(),Error>{
'''+body+'''\n}
fn parent(proof:&[u8],p:&Prepared,folded_root:&[u8;32],batch:usize,log:&mut Log)->Result<(),Error>{let [root0,root1]=p.roots;values(proof,p.queries,[root0,root1,*folded_root],batch,log)}
fn check(){let proof:[u8;57607]=kani::any();let queries:[u32;22]=kani::any();let roots:[[u8;32];3]=kani::any();let replies=[if kani::any(){Some(error())}else{None},if kani::any(){Some(error())}else{None},if kani::any(){Some(error())}else{None}];let row:usize=kani::any();kani::assume(row<16);let byte:usize=kani::any();kani::assume(byte<32);let query:usize=kani::any();kani::assume(query<22);let abort:usize=kani::any();kani::assume(abort<=3);
 let p=Prepared{variant:Variant::S2,roots:[roots[0],roots[1]],gamma:E::ZERO,kappa:E::ZERO,alpha:[E::ZERO;2],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let after_idx:[[u32;16];3]=kani::any();let after_val:[[[u8;32];16];3]=kani::any();let mut log=Log{proof:&proof,queries,roots,replies,after_idx,after_val,calls:0,row,byte,query,abort};let out=parent(&proof,&p,&roots[2],1,&mut log);let expected=if replies[0].is_some(){replies[0]}else if replies[1].is_some(){replies[1]}else{replies[2]};assert_eq!(log.calls,if replies[0].is_some(){1}else if replies[1].is_some(){2}else{3});assert_eq!(out,match expected{None=>Ok(()),Some(e)=>Err(e)});}
'''
for suffix in ['', '_renamed']:
 p+='#[kani::proof]\n#[kani::unwind(36)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn parent_result'+suffix+'(){check();}\n'
rows=keyrows+[dict(family='parent_result',function='verifier::candidate::NIL_parent_native::parent_result',rename='verifier::candidate::NIL_parent_native::parent_result_renamed',status='planned',domain='batch1/proof57607, arbitrary queries/roots and all8 child errors, arbitrary complete idx/val mutations and abort cut; unused Prepared fields literal and source projection footprint checked separately')]
inputs=json.loads((E/'NIL_NATIVE_INPUTS.json').read_text());assert 'mod NIL_key_native;' not in inputs[path];inputs[path]+='\n#[cfg(kani)]\n#[path="NIL_key_native.rs"]\nmod NIL_key_native;\n#[cfg(kani)]\n#[path="NIL_parent_native.rs"]\nmod NIL_parent_native;\n';inputs['crates/aspis-r1-cost-probe/src/NIL_key_native.rs']=s;inputs['crates/aspis-r1-cost-probe/src/NIL_parent_native.rs']=p
(E/'NIL_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=2)+'\n');(E/'NIL_key_native.rs.txt').write_text(s);(E/'NIL_parent_native.rs.txt').write_text(p)
pins=json.loads((E/'NIL_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in inputs.items()});(E/'NIL_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(E/'NIL_EXTRA_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'NIL_EXTRA_CUTS.json').write_text(json.dumps({'frozen':REV,'path':path,'three_call_fragment':src[a:z],'fragment_sha256':hashlib.sha256(src[a:z].encode()).hexdigest(),'changes':'child tree calls become full LOCAL Result/mutation/abort oracles; key build and inner sort are one native iteration; callers establish all packet domains','remaining':'Model step/sort induction and full node_count/padding/verify/tree native packet remain required'},indent=2)+'\n')
patch=''
for n,s in inputs.items():
 try:old=subprocess.check_output(['git','show',REV+':'+n],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NIL_native.patch').write_text(patch)
