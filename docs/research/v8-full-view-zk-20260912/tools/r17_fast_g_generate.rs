//! Optimized host generator. Emits fixed public constants, never runtime coins.
extern crate aspis_core;
use aspis_core::field::{CM31, M31};
fn fft(a: &mut [CM31], roots: &[CM31]) {
    let n=a.len(); let mut j=0;
    for i in 1..n { let mut bit=n>>1; while j&bit!=0 { j^=bit; bit>>=1; } j^=bit; if i<j {a.swap(i,j);} }
    let mut len=2;
    while len<=n { for start in (0..n).step_by(len) { for k in 0..len/2 {
        let u=a[start+k]; let v=a[start+k+len/2].mul(roots[k*n/len]);
        a[start+k]=u.add(v); a[start+k+len/2]=u.sub(v);
    }} len*=2; }
}
fn main() {
    let root=CM31::new(M31(2),M31(1268011823)).pow(1<<20);
    assert_eq!(root.pow(2048),CM31::ONE); assert_ne!(root.pow(1024),CM31::ONE);
    let mut roots=vec![CM31::ONE;2048];
    for i in 1..2048 { roots[i]=roots[i-1].mul(root); }
    let mut tree=vec![Vec::<M31>::new();1024];
    for i in 0..512 { tree[512+i]=if i<271 {vec![M31::ONE,M31((i+1) as u32).neg()]} else {vec![M31::ONE]}; }
    for i in (1..512).rev() {
        let mut d=vec![M31::ZERO;tree[2*i].len()+tree[2*i+1].len()-1];
        for (j,a) in tree[2*i].iter().enumerate() { for (k,b) in tree[2*i+1].iter().enumerate() {d[j+k]=d[j+k].add(a.mul(*b));} }
        tree[i]=d;
    }
    let mut inv=vec![M31::ZERO;1024]; inv[0]=M31::ONE;
    for j in 1..1024 { let mut sum=M31::ZERO; for k in 1..=core::cmp::min(j,271) {sum=sum.add(tree[1][k].mul(inv[j-k]));} inv[j]=sum.neg(); }
    let mut spectrum=vec![CM31::ZERO;2048];
    for i in 0..1024 {spectrum[i]=CM31::from_m31(inv[i]);} fft(&mut spectrum,&roots);
    let mut offsets=vec![0;1024]; let mut all=Vec::new();
    for i in 0..1024 {offsets[i]=all.len();all.extend_from_slice(&tree[i]);}
    println!("static DEN_OFFSETS: [usize;1024] = {:?};",offsets);
    println!("static DEN_LENGTHS: [usize;1024] = {:?};",tree.iter().map(Vec::len).collect::<Vec<_>>());
    println!("static DENOMINATORS: [M31;{}] = [",all.len());
    for x in all {println!("M31({}),",x.0);} println!("];");
    for (name,data) in [("ROOTS",roots),("INVERSE_SPECTRUM",spectrum)] {
        println!("static {}: [CM31;2048] = [",name);
        for x in data {println!("CM31 {{ a: M31({}), b: M31({}) }},",x.a.0,x.b.0);} println!("];");
    }
}
