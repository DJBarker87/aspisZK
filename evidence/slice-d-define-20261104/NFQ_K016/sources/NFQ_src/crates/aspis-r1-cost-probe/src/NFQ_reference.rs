// Safe scalar references: no Kani, unsafe, pointers, logs, or mutable statics.
pub fn row_shape_ref(row:u8)->Option<(u8,usize)>{
 match row {
  0|1|3..=13=>Some((0,0)),2=>Some((1,32)),14=>Some((3,32)),
  15..=24=>Some((2,896)),25=>Some((4,3712)),26=>Some((5,928)),_=>None,
 }
}
pub fn compact_row_ref(row:u8)->bool{row>=14}
pub fn folds_ref(v:u8)->usize{if v==0 {1}else{2}}
pub fn final_len_ref(v:u8)->usize{if v==0 {256}else{64}}
pub fn checkpoint_size_ref(v:u8)->usize{if v==0 {4840}else{1768}}
