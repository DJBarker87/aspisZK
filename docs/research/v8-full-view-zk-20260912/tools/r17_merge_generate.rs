//! Optimized host generator; fixed public denominator spectra only.
extern crate aspis_core;
use aspis_core::field::{CM31,M31};
include!("r17_fast_g_tables.rs");
fn transform(a: &mut [CM31]) {
    let n=a.len(); let mut j=0;
    for i in 1..n {let mut bit=n>>1; while j&bit!=0 {j^=bit;bit>>=1;} j^=bit; if i<j {a.swap(i,j);}}
    let mut len=2;
    while len<=n {
        for start in (0..n).step_by(len) {for k in 0..len/2 {
            let u=a[start+k];let v=a[start+k+len/2].mul(ROOTS[k*2048/len]);
            a[start+k]=u.add(v);a[start+k+len/2]=u.sub(v);
        }}
        len*=2;
    }
}
fn main() {
    let mut offsets=[usize::MAX;16];let mut all=Vec::new();let mut nodes=0;
    for n in [64usize,128,256] {
        assert_eq!(ROOTS[2048/n].pow(n as u64),CM31::ONE);
        assert_ne!(ROOTS[2048/n].pow((n/2) as u64),CM31::ONE);
        for start in (0..271).step_by(n) {
            if start+n>271 {continue;}
            let node=512/n+start/n;offsets[node]=all.len();nodes+=1;
            for other in [node*2+1,node*2] {
                assert_eq!(DEN_LENGTHS[other],n/2+1);
                let mut data=vec![CM31::ZERO;n];
                for k in 0..DEN_LENGTHS[other] {data[k]=CM31::from_m31(DENOMINATORS[DEN_OFFSETS[other]+k]);}
                transform(&mut data);all.extend(data);
            }
        }
    }
    assert_eq!(nodes,7);assert_eq!(all.len(),1536);
    println!("static MERGE_OFFSETS: [usize;16] = [");
    for x in offsets {if x==usize::MAX {println!("usize::MAX,");} else {println!("{x},");}}
    println!("];");
    println!("static MERGE_SPECTRA: [CM31;1536] = [");
    for x in all {println!("CM31 {{ a: M31({}), b: M31({}) }},",x.a.0,x.b.0);}
    println!("];");
}
