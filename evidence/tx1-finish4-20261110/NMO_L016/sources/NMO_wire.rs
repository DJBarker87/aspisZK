use super::*;
pub fn hash<H:Digest32>(t:&SemanticTranscript<H>)->&H{&t.hash}
pub fn make<H:Digest32>(hash:H,state:[u8;32],next_row:u8)->SemanticTranscript<H>{SemanticTranscript{state,hash,next_row}}
pub fn prefix<'a>(c1_root:&'a[u8;32],records:[&'a[u8];27])->Prefix<'a>{Prefix{c1_root,records}}
pub fn record<'a>(p:&Prefix<'a>,row:usize)->&'a[u8]{p.records[row]}
pub fn into_parts<H:Digest32>(t:SemanticTranscript<H>)->([u8;32],H,u8){(t.state,t.hash,t.next_row)}
