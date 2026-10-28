#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
fn check(n:usize,cap:usize,size:usize,seed:usize) {
 let initial:Vec<u8>=(0..n).map(|j| j.wrapping_mul(31).wrapping_add(seed) as u8).collect();
 let bytes:Vec<u8>=(0..size).map(|j|j.wrapping_mul(53).wrapping_add(seed+7) as u8).collect();
 let mut out=Vec::with_capacity(cap);
 KMX_stubs::KMX_extend_from_slice(&mut out,&initial);
 assert_eq!(out.len(),n);assert_eq!(out.capacity(),cap);
 KMX_stubs::KMX_extend_from_slice(&mut out,&bytes);
 assert_eq!(out.len(),n+size);
 assert_eq!(out.capacity(),if n+size<=cap {cap} else {std::cmp::max(cap*2,n+size).max(8)});
 for j in 0..n+size {let expected=if j<n{initial[j]}else{bytes[j-n]};assert_eq!(out[j],expected);assert_ne!(out[j],expected^1);}
}
fn main() {
 let which=std::env::args().nth(1).unwrap();let mut count=0;
 match which.as_str() {
 "schedule" => {
check(0,1768,8,0+3);count+=1;
check(8,1768,8,8+3);count+=1;
check(16,1768,32,16+3);count+=1;
check(48,1768,32,48+3);count+=1;
check(80,1768,32,80+3);count+=1;
check(112,1768,32,112+3);count+=1;
check(144,1768,32,144+3);count+=1;
check(176,1768,32,176+3);count+=1;
check(208,1768,32,208+3);count+=1;
check(240,1768,32,240+3);count+=1;
check(272,1768,32,272+3);count+=1;
check(304,1768,16,304+3);count+=1;
check(320,1768,4,320+3);count+=1;
check(324,1768,4,324+3);count+=1;
check(328,1768,4,328+3);count+=1;
check(332,1768,4,332+3);count+=1;
check(336,1768,4,336+3);count+=1;
check(340,1768,4,340+3);count+=1;
check(344,1768,4,344+3);count+=1;
check(348,1768,4,348+3);count+=1;
check(352,1768,4,352+3);count+=1;
check(356,1768,4,356+3);count+=1;
check(360,1768,4,360+3);count+=1;
check(364,1768,4,364+3);count+=1;
check(368,1768,4,368+3);count+=1;
check(372,1768,4,372+3);count+=1;
check(376,1768,4,376+3);count+=1;
check(380,1768,4,380+3);count+=1;
check(384,1768,4,384+3);count+=1;
check(388,1768,4,388+3);count+=1;
check(392,1768,4,392+3);count+=1;
check(396,1768,4,396+3);count+=1;
check(400,1768,4,400+3);count+=1;
check(404,1768,4,404+3);count+=1;
check(408,1768,16,408+3);count+=1;
check(424,1768,16,424+3);count+=1;
check(440,1768,16,440+3);count+=1;
check(456,1768,16,456+3);count+=1;
check(472,1768,16,472+3);count+=1;
check(488,1768,16,488+3);count+=1;
check(504,1768,16,504+3);count+=1;
check(520,1768,16,520+3);count+=1;
check(536,1768,16,536+3);count+=1;
check(552,1768,16,552+3);count+=1;
check(568,1768,16,568+3);count+=1;
check(584,1768,16,584+3);count+=1;
check(600,1768,16,600+3);count+=1;
check(616,1768,16,616+3);count+=1;
check(632,1768,32,632+3);count+=1;
check(664,1768,32,664+3);count+=1;
check(696,1768,16,696+3);count+=1;
check(712,1768,16,712+3);count+=1;
check(728,1768,16,728+3);count+=1;
check(744,1768,16,744+3);count+=1;
check(760,1768,16,760+3);count+=1;
check(776,1768,16,776+3);count+=1;
check(792,1768,16,792+3);count+=1;
check(808,1768,16,808+3);count+=1;
check(824,1768,16,824+3);count+=1;
check(840,1768,16,840+3);count+=1;
check(856,1768,16,856+3);count+=1;
check(872,1768,16,872+3);count+=1;
check(888,1768,16,888+3);count+=1;
check(904,1768,16,904+3);count+=1;
check(920,1768,16,920+3);count+=1;
check(936,1768,16,936+3);count+=1;
check(952,1768,16,952+3);count+=1;
check(968,1768,16,968+3);count+=1;
check(984,1768,16,984+3);count+=1;
check(1000,1768,16,1000+3);count+=1;
check(1016,1768,16,1016+3);count+=1;
check(1032,1768,16,1032+3);count+=1;
check(1048,1768,16,1048+3);count+=1;
check(1064,1768,16,1064+3);count+=1;
check(1080,1768,16,1080+3);count+=1;
check(1096,1768,16,1096+3);count+=1;
check(1112,1768,16,1112+3);count+=1;
check(1128,1768,16,1128+3);count+=1;
check(1144,1768,16,1144+3);count+=1;
check(1160,1768,16,1160+3);count+=1;
check(1176,1768,16,1176+3);count+=1;
check(1192,1768,16,1192+3);count+=1;
check(1208,1768,16,1208+3);count+=1;
check(1224,1768,16,1224+3);count+=1;
check(1240,1768,16,1240+3);count+=1;
check(1256,1768,16,1256+3);count+=1;
check(1272,1768,16,1272+3);count+=1;
check(1288,1768,16,1288+3);count+=1;
check(1304,1768,16,1304+3);count+=1;
check(1320,1768,16,1320+3);count+=1;
check(1336,1768,16,1336+3);count+=1;
check(1352,1768,16,1352+3);count+=1;
check(1368,1768,16,1368+3);count+=1;
check(1384,1768,16,1384+3);count+=1;
check(1400,1768,16,1400+3);count+=1;
check(1416,1768,16,1416+3);count+=1;
check(1432,1768,16,1432+3);count+=1;
check(1448,1768,16,1448+3);count+=1;
check(1464,1768,16,1464+3);count+=1;
check(1480,1768,16,1480+3);count+=1;
check(1496,1768,16,1496+3);count+=1;
check(1512,1768,16,1512+3);count+=1;
check(1528,1768,16,1528+3);count+=1;
check(1544,1768,16,1544+3);count+=1;
check(1560,1768,16,1560+3);count+=1;
check(1576,1768,16,1576+3);count+=1;
check(1592,1768,16,1592+3);count+=1;
check(1608,1768,16,1608+3);count+=1;
check(1624,1768,16,1624+3);count+=1;
check(1640,1768,16,1640+3);count+=1;
check(1656,1768,16,1656+3);count+=1;
check(1672,1768,16,1672+3);count+=1;
check(1688,1768,16,1688+3);count+=1;
check(1704,1768,16,1704+3);count+=1;
check(1720,1768,16,1720+3);count+=1;
check(1736,1768,32,1736+3);count+=1;
},
 "queries" => {for i in 0..22 {check(64+4*i,if i==0{64}else if i<=16{128}else{256},4,i);count+=1;}},
 "checksum" => {for seed in 0..64 {check(1736,1736,32,seed);count+=1;}},
 "selected" => {for i in 0..64 {check(712+16*i,712+16*i,16,i);count+=1;}},
 "arbitrary_lengths" => {for size in [4,16,32] {for n in 0..=1736-size {check(n,n,size,n+size);count+=1;}}},
 _ => panic!("unknown case")
 }
 println!("PASS {} {} concrete transitions; XOR1 inequalities checked",which,count);
}
