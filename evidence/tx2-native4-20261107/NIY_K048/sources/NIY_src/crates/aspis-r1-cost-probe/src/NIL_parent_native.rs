use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn error()->Error{match kani::any::<u8>()%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
struct Log<'a>{proof:&'a[u8],queries:[u32;22],roots:[[u8;32];3],replies:[Option<Error>;3],after_idx:[u32;3],after_val:[u8;3],calls:usize,row:usize,byte:usize,query:usize,abort:usize}
impl<'a> Log<'a>{fn tree(&mut self,proof:&[u8],queries:[u32;22],root:[u8;32],batch:usize,tree:usize,idx:&mut[u32;16],val:&mut[[u8;32];16])->Result<(),Error>{let c=self.calls;assert!(c<3);assert_eq!(tree,c);assert_eq!(batch,1);assert_eq!(proof.as_ptr(),self.proof.as_ptr());assert_eq!(proof.len(),self.proof.len());assert_eq!(queries[self.query],self.queries[self.query]);let byte=if cfg!(NIL_invert){root[self.byte]^1}else{root[self.byte]};assert_eq!(byte,self.roots[c][self.byte]);assert_eq!(idx[self.row],if c==0{0}else{self.after_idx[c-1]});assert_eq!(val[self.row][self.byte],if c==0{0}else{self.after_val[c-1]});self.calls+=1;if c==self.abort{kani::assume(false);}idx[self.row]=self.after_idx[c];val[self.row][self.byte]=self.after_val[c];match self.replies[c]{None=>Ok(()),Some(e)=>Err(e)}}}
fn values(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],batch:usize,log:&mut Log)->Result<(),Error>{
    let mut idx = [0u32; multiproof::MAX_BATCH];
    let mut val = [[0u8; 32]; multiproof::MAX_BATCH];
    let [root0, root1, root2] = roots;
    log.tree(proof, queries, root0, batch, 0, &mut idx, &mut val)?;
    log.tree(proof, queries, root1, batch, 1, &mut idx, &mut val)?;
    log.tree(proof, queries, root2, batch, 2, &mut idx, &mut val)?;
    Ok(())
}
fn parent(proof:&[u8],p:&Prepared,folded_root:&[u8;32],batch:usize,log:&mut Log)->Result<(),Error>{let [root0,root1]=p.roots;values(proof,p.queries,[root0,root1,*folded_root],batch,log)}
fn check(){let proof:[u8;1]=kani::any();let queries:[u32;22]=kani::any();let roots:[[u8;32];3]=kani::any();let replies=[if kani::any(){Some(error())}else{None},if kani::any(){Some(error())}else{None},if kani::any(){Some(error())}else{None}];let row:usize=kani::any();kani::assume(row<16);let byte:usize=kani::any();kani::assume(byte<32);let query:usize=kani::any();kani::assume(query<22);let abort:usize=kani::any();kani::assume(abort<=3);
 let p=Prepared{variant:Variant::S2,roots:[roots[0],roots[1]],gamma:E::ZERO,kappa:E::ZERO,alpha:[E::ZERO;2],rho:K::ZERO,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};
 let after_idx:[u32;3]=kani::any();let after_val:[u8;3]=kani::any();let mut log=Log{proof:&proof,queries,roots,replies,after_idx,after_val,calls:0,row,byte,query,abort};let out=parent(&proof,&p,&roots[2],1,&mut log);let expected=if replies[0].is_some(){replies[0]}else if replies[1].is_some(){replies[1]}else{replies[2]};assert_eq!(log.calls,if replies[0].is_some(){1}else if replies[1].is_some(){2}else{3});assert_eq!(out,match expected{None=>Ok(()),Some(e)=>Err(e)});}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn parent_result(){check();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn parent_result_renamed(){check();}
