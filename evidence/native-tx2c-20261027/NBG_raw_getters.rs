#[kani::proof]
fn NBG_raw_getters(){
 let w:[u32;8]=kani::any();let i:usize=kani::any();kani::assume(i<8);
 let x=super::WideExact{c0:q([w[0],w[1],w[2],w[3]]),c1:q([w[4],w[5],w[6],w[7]])};
 let a=x.c0();let b=x.c1();let observed=[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0,b.c0.a.0,b.c0.b.0,b.c1.a.0,b.c1.b.0];
 assert!(observed[i]==w[i]);assert!(x.to_limbs()[i]==w[i]);kani::cover!(w[0]==u32::MAX);
}
