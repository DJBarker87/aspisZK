// Explicit wrapping operations need checks in addition to Kani's defaults.
trait R22Checked: Sized {
    fn r22_add(self, rhs: Self) -> Self;
    fn r22_sub(self, rhs: Self) -> Self;
}
macro_rules! checks {
    ($t:ty) => { impl R22Checked for $t {
        fn r22_add(self,rhs:Self)->Self {self.checked_add(rhs).expect("R22 wrapping add must not overflow")}
        fn r22_sub(self,rhs:Self)->Self {self.checked_sub(rhs).expect("R22 wrapping sub must not underflow")}
    }};
}
checks!(u32); checks!(u64);
#[cfg(kani)]
fn arbitrary_q()->Q {
    let a:[u32;4]=kani::any();
    for x in a {kani::assume(x<P);}
    Q(a)
}
#[cfg(kani)] #[kani::proof]
fn reduce_all_u64() { let x:u64=kani::any(); assert!(reduce(x)<P); }
#[cfg(kani)] #[kani::proof]
fn scalar_add_canonical() {
    let a:u32=kani::any();let b:u32=kani::any();
    kani::assume(a<P && b<P);assert!(add(a,b)<P);
}
#[cfg(kani)] #[kani::proof]
fn packed_add() {
    let a=arbitrary_q();let b=arbitrary_q();let c=a.add(b);
    for x in c.limbs() {assert!(x<P);}
}
#[cfg(kani)] #[kani::proof]
fn packed_sub() {
    let a=arbitrary_q();let b=arbitrary_q();let c=a.sub(b);
    for x in c.limbs() {assert!(x<P);}
}
#[cfg(kani)] #[kani::proof]
fn half_and_half_pow() {
    let a=arbitrary_q();let n:u8=kani::any();
    for x in a.half().limbs() {assert!(x<P);}
    if let Some(b)=a.half_pow(n) {for x in b.limbs() {assert!(x<P);}}
}
// Products from canonical limbs satisfy these caps. Independent products
// overapproximate their correlations: no solver assumption claims Q::mul total.
#[cfg(kani)] fn prod()->u64 {let x:u64=kani::any();kani::assume(x<=(u64::from(P)-1).pow(2));x}
#[cfg(kani)] fn partial_bound()->u64 {let x:u64=kani::any();kani::assume(x<=3*u64::from(P));x}
#[cfg(kani)] #[kani::proof]
fn widened_u32_product() {
    let a:u32=kani::any();let b:u32=kani::any();
    let product=u64::from(a)*u64::from(b);
    assert!(product<=u64::from(u32::MAX).pow(2));
}
#[cfg(kani)] #[kani::proof]
fn raw_partial_ranges() {
    const PP:u64=(P as u64)*(P as u64);
    let cg=prod();let dh=prod();let ch=prod();let dg=prod();
    let partial=|x:u64|(x&u64::from(P)).r22_add(x>>31);
    let u=partial(cg.r22_add(PP).r22_sub(dh));
    let v=partial(ch.r22_add(dg));
    assert!(u<=3*u64::from(P));assert!(v<=3*u64::from(P));
}
#[cfg(kani)] #[kani::proof]
fn raw_coordinate0() {
    const PP:u64=(P as u64)*(P as u64);
    let ae=prod();let bf=prod();let u=partial_bound();let v=partial_bound();
    let _x=ae.r22_add(PP).r22_sub(bf).r22_add(2*u).r22_add(3*u64::from(P)).r22_sub(v);
}
#[cfg(kani)] #[kani::proof]
fn raw_coordinate1() {
    let af=prod();let be=prod();let u=partial_bound();let v=partial_bound();
    let _x=af.r22_add(be).r22_add(u).r22_add(2*v);
}
#[cfg(kani)] #[kani::proof]
fn raw_coordinate2() {
    const PP:u64=(P as u64)*(P as u64);
    let ag=prod();let ce=prod();let bh=prod();let df=prod();
    let _x=ag.r22_add(ce).r22_add(2*PP).r22_sub(bh).r22_sub(df);
}
#[cfg(kani)] #[kani::proof]
fn raw_coordinate3() {
    let ah=prod();let bg=prod();let cf=prod();let de=prod();
    let _x=ah.r22_add(bg).r22_add(cf).r22_add(de);
}
#[cfg(kani)] #[kani::proof]
fn dot_prefix_step() {
    // Inductive phase: previous count <=4095, each previous partial <2^34.
    let count:usize=kani::any();let old:u64=kani::any();let raw:u64=kani::any();
    kani::assume(count<4096);kani::assume(old<=(count as u64)*((1u64<<34)-1));
    let folded=(raw&u64::from(P)).r22_add(raw>>31);
    assert!(folded<1u64<<34);
    let next=old.r22_add(folded);let next_count=count+1;
    assert!(next<=(next_count as u64)*((1u64<<34)-1));
    assert!(next<1u64<<46);
}
