//! Reorder existing fixed public spectra. No arithmetic or coin change.
extern crate aspis_core;
use aspis_core::field::{CM31,M31};
include!("r17_fast_g_tables.rs");
include!("r17_merge_spectra.rs");
fn reverse(i:usize,n:usize)->usize {i.reverse_bits()>>(usize::BITS-n.trailing_zeros())}
fn emit(name:&str,data:&[CM31]) {
    println!("static {name}: [CM31;{}] = [",data.len());
    for x in data {println!("CM31 {{a:M31({}),b:M31({})}},",x.a.0,x.b.0);}
    println!("];");
}
fn main() {
    let inverse:Vec<_>=(0..2048).map(|i|INVERSE_SPECTRUM[reverse(i,2048)]).collect();
    let mut merge=vec![CM31::ZERO;1536];let mut visited=vec![false;1536];
    for n in [64usize,128,256] {for start in (0..271).step_by(n) {
        if start+n>271 {continue;}
        let offset=MERGE_OFFSETS[512/n+start/n];
        for side in 0..2 {for i in 0..n {
            let at=offset+side*n+i;assert!(!visited[at]);visited[at]=true;
            merge[at]=MERGE_SPECTRA[offset+side*n+reverse(i,n)];
        }}
    }}
    assert!(visited.iter().all(|x|*x));
    emit("ALIGNED_INVERSE",&inverse);emit("ALIGNED_MERGE",&merge);
}
