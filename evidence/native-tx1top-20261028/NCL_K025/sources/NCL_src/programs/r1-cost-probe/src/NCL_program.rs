use super::*;
#[kani::proof]
fn NCL_route(){let bytes:[u8;8]=kani::any();let n:usize=kani::any();kani::assume(n<=8);let s=&bytes[..n];let expected=(n==2&&bytes[0]==3&&(bytes[1]==10||bytes[1]==11))||(n>=4&&bytes[0]==65&&bytes[1]==83&&bytes[2]==81&&bytes[3]==56);assert_eq!(pool_route::admitted(s),expected);}
#[kani::proof]
fn NCL_route_wrong(){assert!(!pool_route::admitted(&[3,10]));}
#[kani::proof]
fn NCL_entry_reject(){let tag:u8=kani::any();kani::assume(tag!=3);let p=Pubkey::new_from_array([0;32]);assert_eq!(process_r1_cost_probe_instruction(&p,&[],&[tag]),Err(ProgramError::InvalidInstructionData));}
#[kani::proof]
fn NCL_entry_reject_wrong(){let p=Pubkey::new_from_array([0;32]);assert_eq!(process_r1_cost_probe_instruction(&p,&[],&[1]),Ok(()));}
#[kani::proof]
fn NCL_checkpoint_size(){use aspis_r1_cost_probe::transport::Variant;let n:u8=kani::any();let v=match n%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D};let expected=if n%3==0{4840}else{1768};assert_eq!(verifier::checkpoint_size(v),expected);}
#[kani::proof]
fn NCL_checkpoint_size_wrong(){assert_eq!(verifier::checkpoint_size(aspis_r1_cost_probe::transport::Variant::S2),1769);}

#[kani::proof] fn NCL_route_tx1(){let a:u8=kani::any();let b:u8=kani::any();assert_eq!(pool_route::admitted(&[a,b]),a==3&&(b==10||b==11));}
#[kani::proof] fn NCL_route_tx1_wrong(){assert!(pool_route::admitted(&[3,12]));}
#[kani::proof] fn NCL_entry_stage1_count(){let p=Pubkey::new_from_array([0;32]);let k:u8=kani::any();kani::assume(k==10||k==11);assert!(matches!(process_r1_cost_probe_instruction(&p,&[],&[3,k]),Err(ProgramError::InvalidInstructionData)));}
#[kani::proof] fn NCL_entry_stage1_count_wrong(){let p=Pubkey::new_from_array([0;32]);assert!(process_r1_cost_probe_instruction(&p,&[],&[3,10]).is_ok());}
