pub fn sub_ref(x:u32,y:u32)->u32{if x>=y{x-y}else{x+2147483647-y}}
pub fn one_sub(a:[u32;4])->[u32;4]{[sub_ref(1,a[0]),sub_ref(0,a[1]),sub_ref(0,a[2]),sub_ref(0,a[3])]}
pub struct FactorPacket{pub left:[[u32;4];4],pub right:[[u32;4];4],pub row:[[u32;4];4]}
pub fn factor_ref(a:[u32;4],b:[u32;4],replies:[[u32;4];4])->FactorPacket{let aa=one_sub(a);let bb=one_sub(b);FactorPacket{left:[aa,a,aa,a],right:[bb,bb,b,b],row:replies}}
pub struct CirclePacket{pub row:[[u32;4];4],pub next:[u32;4]}
pub fn circle_ref(x:[u32;4],y:[u32;4],product:[u32;4],next:[u32;4])->CirclePacket{CirclePacket{row:[[1,0,0,0],x,y,product],next}}
pub struct All{pub factor:FactorPacket,pub circle:CirclePacket}
pub fn all_factors(a:[u32;4],b:[u32;4],replies:[[u32;4];4],next:[u32;4])->All{All{factor:factor_ref(a,b,replies),circle:circle_ref(a,b,replies[0],next)}}
