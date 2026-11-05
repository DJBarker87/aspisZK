use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
struct Log<'a>{proof:&'a[u8],lo:usize,position:usize,tree:usize,reply:[u8;32],calls:usize}
impl<'a> Log<'a>{fn leaf(&mut self,tree:usize,q:&[u8])->[u8;32]{let expected=opening(self.proof,self.lo+self.position);assert_eq!(tree,self.tree);assert_eq!(q.as_ptr(),expected.as_ptr());assert_eq!(q.len(),832);self.calls+=1;self.reply}}
fn step(proof:&[u8],lo:usize,tree:usize,keys:[u64;16],key_position:&mut usize,d:&mut usize,idx:&mut[u32;16],val:&mut[[u8;32];16],log:&mut Log)->Result<(),Error>{
        let key = batch_key_at(&keys, *key_position);
        *key_position += 1;
        let index = (key >> 8) as u32;
        let q = opening(proof, lo + (key & 0xff) as usize);
        let leaf = log.leaf(tree,q);
        if *d > 0 && same_batch_index(idx, *d - 1, index) {
            if !same_batch_leaf(val, *d - 1, leaf) {
                return Err(Error::Merkle);
            }
            return Ok(());
        }
        idx[*d] = index;
        val[*d] = leaf;
        *d += 1;
Ok(())}

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
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet0(){check::<0,0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet0_renamed(){check::<0,0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet1(){check::<0,1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet1_renamed(){check::<0,1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet2(){check::<0,2>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet2_renamed(){check::<0,2>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet3(){check::<0,3>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet3_renamed(){check::<0,3>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet4(){check::<0,4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet4_renamed(){check::<0,4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet5(){check::<0,5>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree0_facet5_renamed(){check::<0,5>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet0(){check::<1,0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet0_renamed(){check::<1,0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet1(){check::<1,1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet1_renamed(){check::<1,1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet2(){check::<1,2>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet2_renamed(){check::<1,2>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet3(){check::<1,3>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet3_renamed(){check::<1,3>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet4(){check::<1,4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet4_renamed(){check::<1,4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet5(){check::<1,5>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree1_facet5_renamed(){check::<1,5>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet0(){check::<2,0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet0_renamed(){check::<2,0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet1(){check::<2,1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet1_renamed(){check::<2,1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet2(){check::<2,2>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet2_renamed(){check::<2,2>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet3(){check::<2,3>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet3_renamed(){check::<2,3>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet4(){check::<2,4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet4_renamed(){check::<2,4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet5(){check::<2,5>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn tree2_facet5_renamed(){check::<2,5>();}
