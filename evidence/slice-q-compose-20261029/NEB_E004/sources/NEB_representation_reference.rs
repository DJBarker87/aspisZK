pub const P:u32=0x7fff_ffff;
pub struct C {pub a:u32,pub b:u32}
pub struct Q {pub c0:C,pub c1:C}
pub struct E {pub c0:Q,pub c1:Q}
pub fn words(x:E)->[u32;8] {[x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]}
pub fn canonical(x:Q)->Q {Q{c0:C{a:x.c0.a%P,b:x.c0.b%P},c1:C{a:x.c1.a%P,b:x.c1.b%P}}}
pub fn embed(x:Q)->E {E{c0:canonical(x),c1:Q{c0:C{a:0,b:0},c1:C{a:0,b:0}}}}
