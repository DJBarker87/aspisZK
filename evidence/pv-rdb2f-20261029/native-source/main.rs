
fn pointer_guard_audit() {
  for seed in 0..256u32 {
    let mut words: [u32;8]=core::array::from_fn(|i|seed.wrapping_add(i as u32));
    let base=words.as_mut_ptr() as usize;
    for (step,word) in words.iter_mut().rev().enumerate() {
      assert_eq!(word as *mut u32 as usize,base+4*(7-step));
      *word=word.wrapping_add(100+step as u32);
    }
    for i in 0..8 { assert_eq!(words[i],seed+i as u32+107-i as u32); }
    let mut calls=0usize;
    let output:[u32;8]=core::array::from_fn(|i| {
      assert_eq!(i,calls);
      let current_base=words.as_mut_ptr() as usize;
      for (step,word) in words.iter_mut().rev().enumerate() {
        assert_eq!(word as *mut u32 as usize,current_base+4*(7-step));
        *word=word.wrapping_add(1);
      }
      calls+=1;
      words[0]
    });
    assert_eq!(calls,8);
    for i in 0..8 { assert_eq!(output[i],seed+108+i as u32);assert_eq!(words[i],seed+115); }
  }
  println!("RDB2F pointer_guard:256 cases;18432 actual pointer-address/current-allocation stores;2048 ordered FnMut captures;all pass (finite validation)");
}
mod consts;
mod soft;
mod x86;
mod sampler_original;
mod sampler_host;
use digest::{generic_array::GenericArray,typenum::{U32,U64},core_api::VariableOutputCore};
use block_buffer::{BlockBuffer,Eager};
use std::slice::from_ref;
type Buffer=BlockBuffer<U64,Eager>;
type Output=GenericArray<u8,U32>;

#[derive(Clone,Debug,PartialEq,Eq)]
struct Core {state:[u32;8],block_len:u64}
fn compress256(state:&mut[u32;8],blocks:&[GenericArray<u8,U64>]) {
    let p = blocks.as_ptr() as *const [u8; 64];
    let blocks = unsafe { core::slice::from_raw_parts(p, blocks.len()) };
    x86::compress(state, blocks)
}
impl Core {
 fn finalize(&mut self,buffer:&mut Buffer,out:&mut Output){
    let bs = 64u64;
    let bit_len = 8 * (buffer.get_pos() as u64 + bs * self.block_len);
    buffer.len64_padding_be(bit_len, |b| compress256(&mut self.state, from_ref(b)));

    for (chunk, v) in out.chunks_exact_mut(4).zip(self.state.iter()) {
        chunk.copy_from_slice(&v.to_be_bytes());
    }
 }
}
fn model(c:&mut Core,buffer:&mut[u8;64],pos:usize)->[u8;32]{
 let bits=8u64.wrapping_mul((pos as u64).wrapping_add(64u64.wrapping_mul(c.block_len)));
 buffer[pos]=128;for x in &mut buffer[pos+1..]{*x=0;}
 if pos>=56 {x86::compress(&mut c.state,from_ref(buffer));let mut last=[0;64];last[56..].copy_from_slice(&bits.to_be_bytes());x86::compress(&mut c.state,from_ref(&last));}
 else {buffer[56..].copy_from_slice(&bits.to_be_bytes());x86::compress(&mut c.state,from_ref(buffer));}
 let mut out=[0;32];for i in 0..8{out[4*i..4*i+4].copy_from_slice(&c.state[i].to_be_bytes());}out
}
fn next(r:&mut u64)->u32{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;*r as u32}
fn low_trace(block:&[u8;32])->([u32;8],u32,usize){
 let mut quotient:[u32;8]=core::array::from_fn(|i|u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap()));
 let mut refq=quotient;
 let base=quotient.as_mut_ptr() as usize;
 let mut visits=0;
 let digits=core::array::from_fn(|_| {
  let mut remainder=0u64;let mut rr=0u64;let mut j=8;
  for limb in quotient.iter_mut().rev(){
   j-=1;assert_eq!((limb as *mut u32 as usize)-base,4*j);
   let dividend=(remainder<<32)|u64::from(*limb);
   *limb=(dividend/u64::from(2147483647u32)) as u32;
   remainder=dividend%u64::from(2147483647u32);
   let rd=(rr<<32)|u64::from(refq[j]);refq[j]=(rd/u64::from(2147483647u32))as u32;rr=rd%u64::from(2147483647u32);
   assert_eq!(*limb,refq[j]);assert_eq!(remainder,rr);visits+=1;
  }
  assert_eq!(quotient,refq);remainder as u32
 });(digits,quotient[0],visits)
}
fn carry_trace(mut digits:[u32;8],mut addend:u32)->(bool,[u32;8]){
 let mut r=digits;let mut a=addend;let base=digits.as_mut_ptr()as usize;let mut i=0;
 for digit in &mut digits {
  assert_eq!((digit as *mut u32 as usize)-base,4*i);
  let sum=u64::from(*digit)+u64::from(addend);*digit=(sum%2147483647)as u32;addend=(sum/2147483647)as u32;
  let s=u64::from(r[i])+u64::from(a);r[i]=(s%2147483647)as u32;a=(s/2147483647)as u32;
  assert_eq!(*digit,r[i]);i+=1;
 }assert_eq!(digits,r);assert_eq!(addend,a);(addend!=0,digits)
}
fn main(){
 pointer_guard_audit();
 let mut rng=0x8e47a24532d8ab91;let mut sha=0;let mut sampler=0;let mut changed=0;
 for pos in 0..64 {for count in [0,1,u64::MAX/64,u64::MAX] {
  let buffer=core::array::from_fn(|_|next(&mut rng)as u8);let state=core::array::from_fn(|_|next(&mut rng));
  let initial=Core{state,block_len:count};let mut actual=initial.clone();let mut expected=initial;
  let mut b=Buffer::default();b.set(GenericArray::clone_from_slice(&buffer),pos);let mut out=Output::clone_from_slice(&[0xa5;32]);
  actual.finalize(&mut b,&mut out);let mut rb=buffer;let ro=model(&mut expected,&mut rb,pos);
  assert_eq!(actual,expected);assert_eq!(b.get_pos(),0);let mut expectedbuffer=Buffer::default();expectedbuffer.set(GenericArray::clone_from_slice(&rb),0);assert_eq!(format!("{b:?}"),format!("{expectedbuffer:?}"));assert_eq!(&out[..],&ro);sha+=1;
 }}
 for n in 0..1024 {let mut block=[0;32];for b in &mut block{*b=next(&mut rng)as u8;}if n==0{block=[0xff;32];}
  let (ds,h,visits)=low_trace(&block);assert_eq!((ds,h),sampler_original::low_for_audit(&block));assert_eq!((ds,h),sampler_host::low_for_audit(&block));assert_eq!(visits,64);
  assert_eq!(sampler_original::ordinary_sample(&block),sampler_host::ordinary_sample(&block));assert_eq!(sampler_original::gamma_sample(&block),sampler_host::gamma_sample(&block));
  assert_eq!(carry_trace(ds,h+1),sampler_original::add_for_audit(ds,h+1));sampler+=1;
  changed+=usize::from(ds.iter().any(|v|*v!=ds[0]));
 }
 assert!(changed>0);assert_eq!(carry_trace([2147483646;8],1),(true,[0;8]));assert_eq!(carry_trace([0;8],1),(false,[1,0,0,0,0,0,0,0]));
 let mut backend=0;for n in [0,1,2,3,17]{for _ in 0..64{let state=core::array::from_fn(|_|next(&mut rng));let blocks:Vec<[u8;64]>=(0..n).map(|_|core::array::from_fn(|_|next(&mut rng)as u8)).collect();let mut a=state;let mut b=state;x86::compress(&mut a,&blocks);soft::compress(&mut b,&blocks);assert_eq!(a,b);backend+=1;}}
 // Compare the public shipped trait at every padding boundary against its literal source body.
 for pos in 0..64 {let input=vec![0x47;pos];let mut c=sha2::Sha256VarCore::new(32).unwrap();let mut b=Buffer::default();let mut modelb=Buffer::default();let ga=GenericArray::clone_from_slice(&[0x47;64]);b.set(ga.clone(),pos);modelb.set(ga,pos);let mut out=Output::default();let mut copyout=Output::default();let mut copy=Core{state:consts::H256_256,block_len:0};c.finalize_variable_core(&mut b,&mut out);copy.finalize(&mut modelb,&mut copyout);assert_eq!(out,copyout);assert_eq!(b.get_pos(),modelb.get_pos());assert_eq!(format!("{b:?}"),format!("{modelb:?}"));assert_eq!(input.len(),pos);}
 println!("finite validation: SHA full mutable core/buffer/cursor/output cases={sha}; actual public trait padding cases=64; sampler original/indexed full pairs={sampler}; reverse mutable write visits={}; backend arbitrary-state/list cases={backend}; CPU sha={} sse2={} ssse3={} sse4.1={}",64*sampler,std::is_x86_feature_detected!("sha"),std::is_x86_feature_detected!("sse2"),std::is_x86_feature_detected!("ssse3"),std::is_x86_feature_detected!("sse4.1"));
}
