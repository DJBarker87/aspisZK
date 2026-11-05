pub fn add_ref(x:u32,y:u32)->u32 {let s=x+y;if s>=2147483647{s-2147483647}else{s}}
pub fn sub_ref(x:u32,y:u32)->u32 {let s=x+2147483647-y;if s>=2147483647{s-2147483647}else{s}}
pub fn double_observed_ref(p0:[u32;4],p1:[u32;4])->[u32;4]{[sub_ref(add_ref(p0[0],p1[0]),1),sub_ref(add_ref(p0[1],p1[1]),0),sub_ref(add_ref(p0[2],p1[2]),0),sub_ref(add_ref(p0[3],p1[3]),0)]}
