use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]struct Hash<'a>{q:&'a [u8;832],tree:usize,c:usize,answer:[u8;32],calls:&'a Cell<usize>}
impl Digest32 for Hash<'_>{fn digest(&self,p:&[&[u8]])->[u8;32]{
 assert_eq!(p.len(),3);assert_eq!(p[0].len(),2);assert_eq!(p[0][0],0x10);
 let (tag,start,len,salt)=if self.tree==0{(0x71,0,480,608)}else if self.tree==1{(0xf1,480,128,640)}else{(0x72,672,128,800)};
 assert_eq!(p[0][1],tag);assert_eq!(p[1].len(),len);assert_eq!(p[2].len(),32);
 assert_eq!(p[1][self.c%len],self.q[start+self.c%len]);assert_eq!(p[2][self.c%32],self.q[salt+self.c%32]);
 self.calls.set(self.calls.get()+1);self.answer
}}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_R_leaf(){
 let q:[u8;832]=kani::any();let tree:usize=kani::any();let c:usize=kani::any();
 kani::assume(tree<3 && c<480);let answer:[u8;32]=kani::any();let calls=Cell::new(0);
 let out=batch_leaf(Hash{q:&q,tree,c,answer,calls:&calls},tree,&q);
 assert_eq!(out[c%32],answer[c%32]);assert_eq!(calls.get(),1);
}
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_R_views(){
 let proof=[0u8;57607];let i:usize=kani::any();let s:usize=kani::any();kani::assume(i<22 && s<6);
 let q=opening(&proof,i);assert_eq!(q.len(),832);assert_eq!(q.as_ptr(),proof[10055+832*i..].as_ptr());
 let nodes=slot(&proof,s);assert_eq!(nodes.len(),32*SLOT_NODES[s]);
 assert_eq!(nodes.as_ptr(),proof[compact::slot_offset(s)..].as_ptr());
}

fn NBV_R_sort_step(mut keys:[u64;16],mut j:usize)->([u64;16],usize){
        if j > 0 && batch_key_at(&keys, j - 1) > batch_key_at(&keys, j) {
            keys.swap(j - 1, j);
            j -= 1;
        }
(keys,j)
}

#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_R_sort(){
 let keys:[u64;16]=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16 && k<16);
 let (out,next)=NBV_R_sort_step(keys,j);
 if j>0 && keys[j-1]>keys[j]{
 assert_eq!(next,j-1);assert_eq!(out[k],if k==j{keys[j-1]}else if k==j-1{keys[j]}else{keys[k]});
 }else{assert_eq!(next,j);assert_eq!(out[k],keys[k]);}
}

fn NBV_R_key_step(queries:&[u32;22],lo:usize,j:usize,tree:usize,keys:&mut [u64;16]){
        let u = queries[lo + j];
        let index = if tree == 2 { u / 4 } else { u };
        keys[j] = (u64::from(index) << 8) | j as u64;
}

#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_R_key(){
 let queries:[u32;22]=kani::any();let mut keys:[u64;16]=kani::any();let old=keys;
 let batch:usize=kani::any();let tree:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();
 kani::assume(batch<2 && tree<3 && k<16);let lo=if batch==0{0}else{10};let n=if batch==0{10}else{12};kani::assume(j<n);
 let u=queries[lo+j];kani::assume(u<262144);
 NBV_R_key_step(&queries,lo,j,tree,&mut keys);
 let index=if tree==2{u/4}else{u};let expected=u64::from(index)*256+j as u64;
 assert_eq!(keys[k],if k==j{expected}else{old[k]});assert_eq!(keys[j]>>8,u64::from(index));assert_eq!(keys[j]&255,j as u64);
}

fn NBV_R_offset_step(mut at:usize,mut i:usize)->(usize,usize){
        at += 32 * SLOT_NODES[i];
        i += 1;
(at,i)
}

#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
#[kani::proof] #[kani::unwind(34)]
fn NBV_R_offset(){
 let at:usize=kani::any();let i:usize=kani::any();kani::assume(at<=57607 && i<6);
 let (next,j)=NBV_R_offset_step(at,i);
 let cap=match i{0=>146,1=>146,2=>128,3=>172,4=>172,_=>150};
 assert_eq!(next,at+32*cap);assert_eq!(j,i+1);
}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_R_leaf_wrong(){
 let q:[u8;832]=kani::any();let tree:usize=kani::any();let c:usize=kani::any();
 kani::assume(tree<3 && c<480);let answer:[u8;32]=kani::any();let calls=Cell::new(0);
 let out=batch_leaf(Hash{q:&q,tree,c,answer,calls:&calls},tree,&q);
 assert_ne!(out[c%32],answer[c%32]);assert_eq!(calls.get(),1);
}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_R_key_wrong(){
 let queries:[u32;22]=kani::any();let mut keys:[u64;16]=kani::any();let old=keys;
 let batch:usize=kani::any();let tree:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();
 kani::assume(batch<2 && tree<3 && k<16);let lo=if batch==0{0}else{10};let n=if batch==0{10}else{12};kani::assume(j<n);
 let u=queries[lo+j];kani::assume(u<262144);
 NBV_R_key_step(&queries,lo,j,tree,&mut keys);
 let index=if tree==2{u/4}else{u};let expected=u64::from(index)*256+j as u64;
 assert_ne!(keys[k],if k==j{expected}else{old[k]});assert_eq!(keys[j]>>8,u64::from(index));assert_eq!(keys[j]&255,j as u64);
}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_R_sort_wrong(){
 let keys:[u64;16]=kani::any();let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16 && k<16);
 let (out,next)=NBV_R_sort_step(keys,j);
 if j>0 && keys[j-1]>keys[j]{
 assert_eq!(next,j-1);assert_ne!(out[k],if k==j{keys[j-1]}else if k==j-1{keys[j]}else{keys[k]});
 }else{assert_eq!(next,j);assert_ne!(out[k],keys[k]);}
}
