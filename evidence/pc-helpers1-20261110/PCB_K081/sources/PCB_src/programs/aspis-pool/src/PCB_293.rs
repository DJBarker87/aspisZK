use super::*;
// Exact one-iteration statements outlined from the frozen inner loops.
#[kani::requires(chunk<4 && byte<7 && (word as u128)<(1u128<<(8*byte)))]
#[cfg_attr(not(PCB_NEG_293_WORD),kani::ensures(|r| (r.0 as u128)==(word as u128)*256+(digest[7*chunk+byte] as u128) && r.1==byte+1))]
#[cfg_attr(PCB_NEG_293_WORD,kani::ensures(|r| (r.0 as u128)!=(word as u128)*256+(digest[7*chunk+byte] as u128)))]
fn read_step(digest:&[u8;32],chunk:usize,byte:usize,word:u64)->(u64,usize) {
 let word=(word<<8)|u64::from(digest[7*chunk+byte]);
 let byte=byte+1;
 (word,byte)
}
#[kani::proof_for_contract(read_step)]fn read_contract(){let digest:[u8;32]=kani::any();let chunk:usize=kani::any();let byte:usize=kani::any();let word:u64=kani::any();kani::assume(chunk<4&&byte<7&&(word as u128)<(1u128<<(8*byte)));let _=read_step(&digest,chunk,byte,word);}
#[kani::requires(group<8)]
#[cfg_attr(not(PCB_NEG_293_GROUP),kani::ensures(|r| *r==((word>>(49-7*group))&127) as u8))]
#[cfg_attr(PCB_NEG_293_GROUP,kani::ensures(|r| *r!=((word>>(49-7*group))&127) as u8))]
fn group_value(word:u64,group:usize)->u8 {((word>>(7*(7-group)))&0x7f)as u8}
#[kani::proof_for_contract(group_value)]fn group_contract(){let word:u64=kani::any();let group:usize=kani::any();kani::assume(group<8);let _=group_value(word,group);}
#[kani::requires(chunk<4&&group<8)]
#[cfg_attr(not(PCB_NEG_293_FRAME),kani::modifies(&mut seed[8*chunk+group]))]
#[cfg_attr(PCB_NEG_293_FRAME,kani::modifies(&mut seed[(8*chunk+group+1)%32]))]
#[kani::ensures(|_|seed[8*chunk+group]==((word>>(7*(7-group)))&0x7f)as u8)]
fn write_step(seed:&mut [u8;32],chunk:usize,group:usize,word:u64) {
 seed[8*chunk+group]=((word>>(7*(7-group)))&0x7f)as u8;
}
#[kani::proof_for_contract(write_step)]fn write_contract(){let mut seed:[u8;32]=kani::any();let chunk:usize=kani::any();let group:usize=kani::any();let word:u64=kani::any();kani::assume(chunk<4&&group<8);write_step(&mut seed,chunk,group,word);}
