//! Scalar projections of Slice D source control and exact call descriptors.
//! This is not a reference implementation of the whole prepare operation.
pub fn prepared_control_ref(query_error:bool,claim_error:bool)->(u8,u8,bool){
 if query_error{(1,6,false)}else if claim_error{(2,9,true)}else{(0,9,true)}
}
pub fn prepared_row_ref(index:u8)->Option<(u8,u32,bool)>{match index{
 0=>Some((27,928,true)),1=>Some((28,32,false)),2=>Some((29,224,false)),
 3=>Some((30,256,false)),4=>Some((31,2048,false)),5=>Some((32,0,false)),_=>None}}
pub fn scratch_size_ref()->usize{13831+29*32}
pub fn tx1_split_ref(k:usize)->bool{k==10}
pub fn tx2_split_ref(next:usize)->bool{next==10}
