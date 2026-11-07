pub fn word_step(word:u64,byte:u8)->u64{word*256+u64::from(byte)}
pub fn denominator(group:usize)->u64{match group{0=>562949953421312,1=>4398046511104,2=>34359738368,3=>268435456,4=>2097152,5=>16384,6=>128,_=>1}}
pub fn group(word:u64,group:usize)->u8{((word/denominator(group))%128)as u8}
