use super::*;
fn NBR_src(row:usize)->usize{if row<=2{32+5*row}else if row<=14{64+5*row}else if row<=25{155+453*(row-15)}else if row==26{6546}else{7015}}
fn NBR_dst(row:usize)->usize{if row<=2{32+5*row}else if row<=14{64+5*row}else if row<=25{171+901*(row-15)}else if row==26{12898}else{13831}}
#[kani::proof]
fn NBR_semantic_geometry(){
 let row:u8=kani::any();kani::assume(row<27);
 let (tag,size)=crate::r1_wire::row_shape(row).unwrap();let r=row as usize;
 let expected=if r==2||r==14{32}else if (15..=24).contains(&r){896}else if r==25{3712}else if r==26{928}else{0};
 assert_eq!(size,expected);assert!(size<=3712);assert_eq!(size%32,0);
 assert_eq!(NBR_src(r+1),NBR_src(r)+5+if r>=14{size/2}else{size});
 assert_eq!(NBR_dst(r+1),NBR_dst(r)+5+size);
 assert!(NBR_src(r+1)<=7015);assert!(NBR_dst(r+1)<=13831);
 assert_eq!(tag,if r==2{1}else if r==14{3}else if (15..=24).contains(&r){2}else if r==25{4}else if r==26{5}else{0});
 assert_eq!(NBR_src(0),32);assert_eq!(NBR_dst(0),32);assert_eq!(NBR_src(27),7015);assert_eq!(NBR_dst(27),13831);
 kani::cover!(r==25,"largest compact semantic row fits the same carrier");
}
