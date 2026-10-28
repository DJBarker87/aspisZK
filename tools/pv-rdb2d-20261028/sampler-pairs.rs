mod sampler_original;
mod sampler_host;
fn block(words:[u32;8])->[u8;32]{let mut b=[0;32];for i in 0..8{b[4*i..4*i+4].copy_from_slice(&words[i].to_le_bytes())}b}
fn power_minus_one()->[u8;32]{let mut w=[0u32;8];w[0]=1;for _ in 0..8{let mut carry=0u64;for d in &mut w{let n=*d as u64*2147483647+carry;*d=n as u32;carry=n>>32;}assert_eq!(carry,0);}let mut borrow=1;for d in &mut w{let(n,b)=d.overflowing_sub(borrow);*d=n;borrow=b as u32;}block(w)}
fn check(b:[u8;32]){
 assert_eq!(sampler_original::low_for_audit(&b),sampler_host::low_for_audit(&b));
 assert_eq!(sampler_original::ordinary_sample(&b),sampler_host::ordinary_sample(&b));
 assert_eq!(sampler_original::gamma_sample(&b),sampler_host::gamma_sample(&b));
}
fn main(){let mut count=0;for b in [[0;32],[255;32],power_minus_one()]{check(b);count+=1;}
 for i in 0..8{for w in [0,1,2147483646,2147483647,2147483648,u32::MAX]{let mut words=[0;8];words[i]=w;check(block(words));count+=1;}}
 for bit in 0..256{let mut b=[0;32];b[bit/8]=1<<(bit%8);check(b);count+=1;}
 let mut rng=0x96145234abcdef01u64;for _ in 0..1024{let mut b=[0;32];for x in &mut b{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;*x=rng as u8;}check(b);count+=1;}
 for ds in [[0;8],[2147483646;8],[1,0,2,0,3,0,4,0]]{for n in [0,1,257]{assert_eq!(sampler_original::add_for_audit(ds,n),sampler_host::add_for_audit(ds,n));}}
 let b=power_minus_one();assert_eq!(sampler_host::low_for_audit(&b),([2147483646;8],0));
 let(wrapped,ds)=sampler_host::add_for_audit([2147483646;8],1);assert!(wrapped);assert_eq!(ds,[0;8]);let(wrapped_again,ds2)=sampler_host::add_for_audit(ds,1);assert!(!wrapped_again);assert_eq!(ds2,[1,0,0,0,0,0,0,0]);
 let(ds,_)=sampler_host::low_for_audit(&[255;32]);assert!(ds.iter().any(|x|*x!=ds[0]),"discarded quotient-write negative control must differ");
 println!("sampler complete low/digits/quotient+ordinary+gamma pairs={count}; carry pairs=9; optional second carry and dropped-write control passed");
}
