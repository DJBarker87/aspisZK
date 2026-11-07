use super::*;
#[path="PCF_CountSliceReference.rs"]mod reference;
fn exact(result:&ProgramResult,tag:u8)->bool {
 match(result,tag){(Ok(()),0)=>true,(Err(ProgramError::NotEnoughAccountKeys),1)=>true,(Err(ProgramError::InvalidArgument),2)=>true,_=>false}
}
// A comparison/constructor observation at one VALID SDK slice extent.
// This is NOT the universal native slice-length certificate and earns no row credit.
#[kani::proof]
fn constructor_classes(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut lamports:u64=kani::any();let mut data=[];
 let info=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),kani::any());
 let accounts=[info];let expected:usize=kani::any();
 let result=require_exact_account_count(&accounts,expected);
 let tag=reference::count_reference(&accounts,expected);
 #[cfg(not(PCF_NEG_COUNT))]assert!(exact(&result,tag));
 #[cfg(PCF_NEG_COUNT)]assert!(!exact(&result,tag));
}
