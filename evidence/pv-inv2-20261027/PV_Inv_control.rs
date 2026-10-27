// Bounded control/index slices only. No field arithmetic, inverse, or stubs.
// Source anchors are in CONTROL-SLICES.md; not whole-function equivalence.
const PRIVATE_DIRECTIONS: usize = 24;
fn base_row(level: usize) -> Option<usize> {
    if level >= PRIVATE_DIRECTIONS { return None; }
    Some(912 + (level / 4) * 16 + [1,5,9,13][level % 4])
}
fn hash_block(level: usize) -> Option<usize> {
    if level >= PRIVATE_DIRECTIONS { None }
    else if level <= 20 { Some(4+level) } else { Some(33+level) }
}
fn translate(row:u16)->u16 { if usize::from(row)>=864 { row+48 } else {row} }
fn late(row:usize)->bool { (544..864).contains(&row) }

#[kani::proof]
fn path_base_bounds() {
 let level:usize=kani::any();
 match base_row(level) { None=>assert!(level>=24),Some(r)=>{assert!(level<24);assert!(r>=912&&r<1008);assert!(r%16==1||r%16==5||r%16==9||r%16==13);} }
}
#[kani::proof]
fn path_target_bounds() {
 let level:usize=kani::any();
 match hash_block(level) {None=>assert!(level>=24),Some(b)=>{assert!(level<24);assert!(b<57);assert!(b<34||b>=54);assert!(!late(b*16));}}
}
#[kani::proof]
fn aux_translation_bank() {
 let row:u16=kani::any();kani::assume(row<976);
 let r=translate(row);assert!(r<1024);
 if row>=864 {assert!(r>=912);assert!(!late(r as usize));} else {assert_eq!(r,row);}
 assert_eq!(late(row as usize),late(r as usize));
}
#[kani::proof]
fn tuple_cell_index() {
 let start:u8=kani::any();let count:u8=kani::any();let lane:u8=kani::any();
 kani::assume(count<=16);kani::assume(start<=16-count);kani::assume(lane<count);
 let column=start+lane;assert!(column<16);
 let tweak:bool=kani::any();let adjusted=tweak&&lane+1==count;
 if adjusted {assert_eq!(lane,count-1);}
}
#[kani::proof]
fn two_slot_position() {
 let weights:[u32;2]=kani::any();
 let selected=weights.iter().position(|value|*value==0);
 match selected {None=>assert!(weights[0]!=0&&weights[1]!=0),Some(i)=>{assert!(i<2);assert_eq!(weights[i],0);if i==1 {assert_ne!(weights[0],0);}}}
}
#[kani::proof]
fn masks_index() {
 let row:u16=kani::any();kani::assume(row<1024);
 let block=usize::from(row)>>4;let bit=usize::from(row)&15;
 assert!(block<64);assert!(bit<16);assert_eq!(16*block+bit,row as usize);
 let mask=1u16<<bit;assert_ne!(mask,0);
}
