pub const P:u32=0x7fff_ffff;
pub fn add_word(x:u32,y:u32)->u32 {let s=x.wrapping_add(y);if s>=P {s.wrapping_sub(P)}else{s}}
pub fn sub_word(x:u32,y:u32)->u32 {let s=x.wrapping_add(P).wrapping_sub(y);if s>=P {s.wrapping_sub(P)}else{s}}
pub fn normalize_word(x:u32)->u32 {x%P}
pub fn add2(x:[u32;2],y:[u32;2])->[u32;2] {[add_word(x[0],y[0]),add_word(x[1],y[1])]}
pub fn add4(x:[u32;4],y:[u32;4])->[u32;4] {[add_word(x[0],y[0]),add_word(x[1],y[1]),add_word(x[2],y[2]),add_word(x[3],y[3])]}
pub fn add8(x:[u32;8],y:[u32;8])->[u32;8] {[add_word(x[0],y[0]),add_word(x[1],y[1]),add_word(x[2],y[2]),add_word(x[3],y[3]),add_word(x[4],y[4]),add_word(x[5],y[5]),add_word(x[6],y[6]),add_word(x[7],y[7])]}
pub fn sub2(x:[u32;2],y:[u32;2])->[u32;2] {[sub_word(x[0],y[0]),sub_word(x[1],y[1])]}
pub fn sub4(x:[u32;4],y:[u32;4])->[u32;4] {[sub_word(x[0],y[0]),sub_word(x[1],y[1]),sub_word(x[2],y[2]),sub_word(x[3],y[3])]}
pub fn sub8(x:[u32;8],y:[u32;8])->[u32;8] {[sub_word(x[0],y[0]),sub_word(x[1],y[1]),sub_word(x[2],y[2]),sub_word(x[3],y[3]),sub_word(x[4],y[4]),sub_word(x[5],y[5]),sub_word(x[6],y[6]),sub_word(x[7],y[7])]}
