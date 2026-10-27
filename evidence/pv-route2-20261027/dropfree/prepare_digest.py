from pathlib import Path
import re
D=Path(__file__).resolve().parent
c=Path('/Users/dominic/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/sha2-0.10.9/src/consts.rs').read_text()
k=c[c.index('pub const K32:'):c.index('/// Constants necessary for SHA-256 family of digests.',c.index('pub const K32:'))]
s='''// Measurement only: concrete SHA-256; narrows the digest library generic quantifier.
#[derive(Clone,Copy)] pub struct Sha256 {pub state:[u32;8],pub blocks:u64,pub buffer:[u8;64],pub pos:usize}
'''+k+'''
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
'''
for op in [205,212,215,216,217,219]:(D/'probes'/f'{op}.rs').write_text(s)
(D/'probes/36.rs').write_text('''// Measurement: Copy elements and caller-owned fixed-capacity carrier; generic Vec<T> row remains open.
#[derive(Clone,Copy)] pub struct Buffer<T:Copy,const CAP:usize>{pub data:[T;CAP],pub len:usize}
pub fn array_try_from<T:Copy,const N:usize,const CAP:usize>(v:Buffer<T,CAP>,fill:T)->Result<[T;N],Buffer<T,CAP>>{
 if v.len!=N {return Err(v);}let mut out=[fill;N];let mut i=0usize;while i<N {out[i]=v.data[i];i+=1;}Ok(out)
}
''')
