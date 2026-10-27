// Source-expression checks, not extracted whole-function certificates.
const P:u32=0x7fff_ffff;
#[derive(Debug, PartialEq, Eq)]
struct Trace { branches:[bool;65], indices:[usize;65], nb:usize, ni:usize }
impl Trace {fn new()->Self {Self {branches:[false;65],indices:[0;65],nb:0,ni:0}}
fn index(&mut self,i:usize) {self.indices[self.ni]=i;self.ni+=1;}
fn branch(&mut self,b:bool) {self.branches[self.nb]=b;self.nb+=1;}
}
fn same(l:&Trace,r:&Trace) {
    assert_eq!(l.nb,r.nb);assert_eq!(l.ni,r.ni);
    for i in 0..32 {
        assert_eq!(l.branches[i],r.branches[i]);assert_eq!(l.indices[i],r.indices[i]);
        assert_eq!(l.branches[i+32],r.branches[i+32]);assert_eq!(l.indices[i+32],r.indices[i+32]);
    }
    assert_eq!(l.branches[64],r.branches[64]);assert_eq!(l.indices[64],r.indices[64]);
}
fn zero(bytes:&[u8;32],t:&mut Trace)->bool {
    for i in 0..32 {
        t.index(i);t.branch(bytes[i]==0);
        if bytes[i]!=0 {return false;}
    }
    true
}
fn seeds(a:&[u8;32],b:&[u8;32],t:&mut Trace)->bool {
    let left=!zero(a,t);t.branch(left);
    left && !zero(b,t)
}
#[kani::proof]
#[kani::unwind(33)]
fn L2Leaf_two_seed_erasure_and_two_run() {
    let a:[u8;32]=kani::any(); let b:[u8;32]=kani::any();
    let mut l=Trace::new(); let mut r=Trace::new();
    let x=seeds(&a,&b,&mut l);let y=seeds(&a,&b,&mut r);
    assert_eq!(x,a!=[0;32] && b!=[0;32]);
    assert_eq!(x,y); same(&l,&r);
}
fn reject(words:&[u32;16],t:&mut Trace)->Option<u32> {
    for i in 0..16 {
        t.index(i);
        let c=words[i]&0x7fff_ffff;
        t.branch(c<P);
        if c<P {return Some(c);}
    }
    None
}
#[kani::proof]
#[kani::unwind(33)]
fn L2Leaf_m31_word_schedule_two_run() {
    let words:[u32;16]=kani::any();
    let mut l=Trace::new();let mut r=Trace::new();
    assert_eq!(reject(&words,&mut l),reject(&words,&mut r));
    same(&l,&r);
    // Fixed common input proves determinism only, not its law or seed/hash
    // refinement. All rejected words are intentionally included.
}
fn scan_step(accepted:&[u32;22],len:usize,candidate:u32,t:&mut Trace)->bool {
    for i in 0..len {
        t.index(i);let found=accepted[i]==candidate;t.branch(found);
        if found {return true;}
    }
    false
}
#[kani::proof]
#[kani::unwind(33)]
fn L2Leaf_query_contains_erasure_and_two_run() {
    let a:[u32;22]=kani::any();let n:usize=kani::any();let c:u32=kani::any();
    kani::assume(n<=22);
    let mut l=Trace::new();let mut r=Trace::new();
    let x=scan_step(&a,n,c,&mut l);let y=scan_step(&a,n,c,&mut r);
    assert_eq!(x,a[..n].contains(&c));assert_eq!(x,y);same(&l,&r);
}
// Exact source qm31_div_pass loop, instrumented with each dividend.
fn division(mut rank:[u32;8])->([u32;8],u32,[u64;8]) {
    let mut dividends=[0;8];let mut remainder=0u64;let mut j=8;
    while j>0 {j-=1;let dividend=(remainder<<32)|u64::from(rank[j]);
        dividends[j]=dividend;rank[j]=(dividend/u64::from(P)) as u32;
        remainder=dividend%u64::from(P);}
    (rank,remainder as u32,dividends)
}
#[kani::proof]
#[kani::unwind(9)]
fn L2Leaf_division_trace_two_run() {
    let rank:[u32;8]=kani::any();
    let (q,r,t)=division(rank);let (qq,rr,tt)=division(rank);
    assert_eq!(r,rr);
    for i in 0..8 {assert_eq!(q[i],qq[i]);assert_eq!(t[i],tt[i]);assert!(q[i] as u64==t[i]/P as u64);}
    assert!(r<P);
}
