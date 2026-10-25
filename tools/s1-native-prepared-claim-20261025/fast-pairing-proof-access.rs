
        #[cfg(kani)] pub(super) fn proof_words(&self)->[u64;4]{self.sums}
        #[cfg(kani)] pub(super) fn proof_input(sums:[u64;4])->Self{Self{sums}}


#[cfg(kani)]
impl EbyKDot {
 pub(crate) fn proof_words(&self)->([u64;8],usize){
  let a=self.c0.proof_words();let b=self.c1.proof_words();
  ([a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]],self.count)
 }
 pub(crate) fn proof_input(w:[u64;8],count:usize)->Self{
  Self{c0:canonical::Dot::proof_input([w[0],w[1],w[2],w[3]]),
       c1:canonical::Dot::proof_input([w[4],w[5],w[6],w[7]]),count}
 }
}
