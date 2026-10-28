// Static recorder only. No SHA implementation and no function-pointer observer.
#[derive(Clone,Copy)]
struct Recorder{a:[u8;32],b:[u8;32],reply:[u8;32]}
impl Digest32 for Recorder{
 fn digest(&self,p:&[&[u8]])->[u8;32]{
  assert_eq!(p.len(),3);
  if cfg!(NDD_negative_digest){assert_ne!(p[0],&[BINARY_NODE_TAG]);}
  else{assert_eq!(p[0],&[BINARY_NODE_TAG]);}
  assert_eq!(p[1],&self.a);assert_eq!(p[2],&self.b);
  self.reply
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn occupied_grammar(){let v:[[u8;32];16]=kani::any();let i:usize=kani::any();kani::assume(i<15);let r:[u8;32]=kani::any();let h=Recorder{a:v[i],b:v[i+1],reply:r};assert_eq!(occupied_binary_parent(h,&v,i),r);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sibling_grammar(){let v:[[u8;32];16]=kani::any();let i:usize=kani::any();kani::assume(i<16);let s:[u8;32]=kani::any();let r:[u8;32]=kani::any();let left:bool=kani::any();let h=Recorder{a:if left{v[i]}else{s},b:if left{s}else{v[i]},reply:r};assert_eq!(sibling_binary_parent(h,&v,i,&s,left),r);}
