// Safe Rust value references; extracted with the pilot tool pins.
pub fn batch_key_at_ref(keys:&[u64;16],index:usize)->u64 { keys[index] }
pub fn same_batch_index_ref(values:&[u32;16],index:usize,expected:u32)->bool {values[index]==expected}
pub fn same_batch_leaf_ref(values:&[[u8;32];16],index:usize,leaf:[u8;32])->bool {values[index]==leaf}
pub fn opening_ref(proof:&[u8],i:usize)->&[u8] {let at=10055+i*832;&proof[at..at+832]}
pub fn validated_row_ref(row:u8)->u8 {row}
pub fn state_ref(state:[u8;32])->[u8;32] {state}
pub fn framed_ref(framed:&[u8])->&[u8] {framed}
