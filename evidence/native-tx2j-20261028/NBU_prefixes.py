from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NBU_decode.rs.txt').read_text();attrs=s[s.index('#[kani::proof]'):s.index('fn NBU_decode_children')].replace('1881','34')
items={
'after_header':'''let mut output:[u8;48]=kani::any();let index:u64=kani::any();let root:[u8;32]=kani::any();
output[..4].copy_from_slice(&POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC);
output[4]=POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;
output[5]=super::super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION;
output[6]=POOL_V1_DIGEST_ENCODING_VERSION;output[7]=1;
output[8..16].copy_from_slice(&index.to_le_bytes());output[16..48].copy_from_slice(&root);
let j:usize=kani::any();kani::assume(j<48);assert_eq!(output[j],if j<4{b"ASJA"[j]}else if j<8{1}else if j<16{index.to_le_bytes()[j-8]}else{root[j-16]});''',
'live_header':'''use crate::pool_v1::pair_tree_profile::*;
let mut output:[u8;160]=[0;160];let pool:[u8;32]=kani::any();let domain:[u8;32]=kani::any();let sequence:u64=kani::any();let index:u64=kani::any();let root:[u8;32]=kani::any();
output[..8].copy_from_slice(&POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC);output[8]=POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION;
output[16..48].copy_from_slice(&POOL_V1_PAIR_TREE_FORMAT_BINDING);output[48..80].copy_from_slice(&pool);output[80..112].copy_from_slice(&domain);output[112..120].copy_from_slice(&sequence.to_le_bytes());output[120..128].copy_from_slice(&index.to_le_bytes());output[128..160].copy_from_slice(&root);
let j:usize=kani::any();kani::assume(j<160);assert_eq!(output[j],if j<8{POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC[j]}else if j==8{1}else if j<16{0}else if j<48{POOL_V1_PAIR_TREE_FORMAT_BINDING[j-16]}else if j<80{pool[j-48]}else if j<112{domain[j-80]}else if j<120{sequence.to_le_bytes()[j-112]}else if j<128{index.to_le_bytes()[j-120]}else{root[j-128]});'''
}
for name,body in items.items():
 for neg in ['', '_negative']:
  b=body.replace('assert_eq!','assert_ne!',1) if neg else body
  s+='\n'+attrs+'fn NBU_'+name+neg+'(){'+b+'}\n'
(E/'NBU_decode.rs.txt').write_text(s)
p=E/'NBU_more.rs.txt';s=p.read_text();attrs=s[s.index('#[kani::proof]'):s.index('fn NBU_validator_control')].replace('1881','34')
items={
'asf8_header':'''let mut output:[u8;8]=kani::any();let kind:u8=kani::any();let lane:u8=kani::any();output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC);output[4]=POOL_V1_PAIR_FOREST_TERMINAL_VERSION;output[5]=kind;output[6]=POOL_V1_DIGEST_ENCODING_VERSION;output[7]=lane;let j:usize=kani::any();kani::assume(j<8);assert_eq!(output[j],if j<4{b"ASF8"[j]}else if j==4||j==6{1}else if j==5{kind}else{lane});''',
'asf8_ranges':'''let mut out:[u8;1880]=kani::any();let ptr=out.as_mut_ptr();let field:usize=kani::any();kani::assume(field<7);let (start,len)=match field{0=>(MASTER_OFFSET,32),1=>(CHECKPOINT_ACCOUNT_OFFSET,32),2=>(SELECTED_LANE_ACCOUNT_OFFSET,32),3=>(CHECKPOINT_SEQUENCE_OFFSET,8),4=>(HISTORICAL_ANCHOR_OFFSET,32),5=>(LATE_STATEMENT_OFFSET,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES),_=>(PAYMENT_STATEMENT_OFFSET,POOL_V1_PAYMENT_STATEMENT_BYTES)};let expected_start=[8,40,72,104,112,144,1664][field];let expected_len=[32,32,32,8,32,1520,216][field];let view=&mut out[start..start+len];assert_eq!(view.len(),expected_len);assert_eq!(view.as_mut_ptr(),ptr.wrapping_add(expected_start));'''
}
for name,body in items.items():
 for neg in ['', '_negative']:
  b=body.replace('assert_eq!','assert_ne!',1) if neg else body
  s+='\n'+attrs+'fn NBU_'+name+neg+'(){'+b+'}\n'
p.write_text(s)
