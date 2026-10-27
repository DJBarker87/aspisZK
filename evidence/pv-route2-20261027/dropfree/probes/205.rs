// Measurement only: concrete SHA-256; narrows the digest library generic quantifier.
#[derive(Clone,Copy)] pub struct Sha256 {pub state:[u32;8],pub blocks:u64,pub buffer:[u8;64],pub pos:usize}
pub const K32: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];


fn rr(x:u32,n:u32)->u32 {(x>>n)|(x<<(32u32-n))}
fn compress(state:&mut [u32;8],block:&[u8;64]){
 let mut w=[0u32;64];let mut i=0usize;
 while i<16 {w[i]=((block[4*i] as u32)<<24u32)|((block[4*i+1] as u32)<<16u32)|((block[4*i+2] as u32)<<8u32)|(block[4*i+3] as u32);i+=1;}
 while i<64 {let x=w[i-15];let y=w[i-2];let s0=rr(x,7)^rr(x,18)^(x>>3u32);let s1=rr(y,17)^rr(y,19)^(y>>10u32);w[i]=w[i-16].wrapping_add(s0).wrapping_add(w[i-7]).wrapping_add(s1);i+=1;}
 let mut a=state[0];let mut b=state[1];let mut c=state[2];let mut d=state[3];let mut e=state[4];let mut f=state[5];let mut g=state[6];let mut h=state[7];i=0;
 while i<64 {let s1=rr(e,6)^rr(e,11)^rr(e,25);let ch=(e&f)^(!e&g);let t1=h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K32[i]).wrapping_add(w[i]);let s0=rr(a,2)^rr(a,13)^rr(a,22);let maj=(a&b)^(a&c)^(b&c);let t2=s0.wrapping_add(maj);h=g;g=f;f=e;e=d.wrapping_add(t1);d=c;c=b;b=a;a=t1.wrapping_add(t2);i+=1;}
 state[0]=state[0].wrapping_add(a);state[1]=state[1].wrapping_add(b);state[2]=state[2].wrapping_add(c);state[3]=state[3].wrapping_add(d);state[4]=state[4].wrapping_add(e);state[5]=state[5].wrapping_add(f);state[6]=state[6].wrapping_add(g);state[7]=state[7].wrapping_add(h);
}
pub fn new()->Sha256 {Sha256{state:[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19],blocks:0,buffer:[0;64],pos:0}}
pub fn update(s:&mut Sha256,input:&[u8]){
 let start=s.pos;let rem=64-start;let n=input.len();let mut i=0usize;
 if n<rem {while i<n {s.buffer[start+i]=input[i];i+=1;}s.pos=start+n;return;}
 if start!=0 {while i<rem {s.buffer[start+i]=input[i];i+=1;}compress(&mut s.state,&s.buffer);s.blocks=s.blocks.wrapping_add(1);}
 while n-i>=64 {let mut block=[0u8;64];let mut j=0usize;while j<64 {block[j]=input[i+j];j+=1;}compress(&mut s.state,&block);s.blocks=s.blocks.wrapping_add(1);i+=64;}
 let tail=n-i;let mut j=0usize;while j<tail {s.buffer[j]=input[i+j];j+=1;}s.pos=tail;
}
pub fn finalize_variable_core(s:&mut Sha256)->[u8;32]{
 let bit_len=(s.pos as u64).wrapping_add(64u64.wrapping_mul(s.blocks)).wrapping_mul(8);
 let pos=s.pos;s.buffer[pos]=128;let mut j=pos+1;while j<64 {s.buffer[j]=0;j+=1;}
 if pos>55 {compress(&mut s.state,&s.buffer);let mut block=[0u8;64];let mut i=0usize;while i<8 {block[56+i]=(bit_len>>(8u32*(7-i as u32))) as u8;i+=1;}compress(&mut s.state,&block);}
 else {let mut i=0usize;while i<8 {s.buffer[56+i]=(bit_len>>(8u32*(7-i as u32))) as u8;i+=1;}compress(&mut s.state,&s.buffer);}
 s.pos=0;let mut out=[0u8;32];let mut i=0usize;while i<8 {let mut j=0usize;while j<4 {out[4*i+j]=(s.state[i]>>(8u32*(3-j as u32))) as u8;j+=1;}i+=1;}out
}

pub fn finalize_fixed_core(s:&mut Sha256,out:&mut [u8;32]){*out=finalize_variable_core(s);}
pub fn finalize_into(mut s:Sha256,out:&mut [u8;32]){finalize_fixed_core(&mut s,out);}
pub fn finalize(s:Sha256)->[u8;32]{let mut out=[0u8;32];finalize_into(s,&mut out);out}
