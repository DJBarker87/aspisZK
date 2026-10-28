// Safe Rust value references; extracted with the pilot tool pins.
pub fn batch_key_at_ref(keys:&[u64;16],index:usize)->u64 { keys[index] }
pub fn same_batch_index_ref(values:&[u32;16],index:usize,expected:u32)->bool {values[index]==expected}
pub fn same_batch_leaf_ref(values:&[[u8;32];16],index:usize,leaf:[u8;32])->bool {values[index]==leaf}
pub fn opening_ref(proof:&[u8],i:usize)->&[u8] {let at=10055+i*832;&proof[at..at+832]}
pub fn validated_row_ref(row:u8)->u8 {row}
pub fn state_ref(state:[u8;32])->[u8;32] {state}
pub fn framed_ref(framed:&[u8])->&[u8] {framed}
pub fn record_ref<'a>(records:&[&'a [u8];27],row:u8)->Option<&'a [u8]> {if row>=27 {None} else {Some(records[row as usize])}}
pub fn raw_ref<const N:usize>(bytes:&[u8],at:usize)->([u8;N],usize) {
 let mut out=[0u8;N];let mut j=0;while j<N {out[j]=bytes[at+j];j+=1;}(out,at+N)
}
pub fn geometry_ref<'a,T>(rows:&'a [T],start:usize,index:usize)->&'a T {&rows[index-start]}
pub fn transcript_new_ref(reply:[u8;32])->([u8;32],u8,u8) {(reply,0,1)}
pub fn transcript_sample_ref(block:[u8;32],advanced:[u8;32],row:u8)->([u8;32],[u8;32],u8,u8) {(block,advanced,row+1,3)}
