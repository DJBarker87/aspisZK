#[cfg(kani)]
mod PoolN_cpi {
 use super::*;
 struct Inspect { clears:usize, calls:usize }
 impl PairForestVerifierRuntimeV1 for Inspect {
  fn clear_return_data(&mut self) { self.clears+=1; }
  fn invoke(&mut self,instruction:&Instruction,infos:&[AccountInfo<'_>])->ProgramResult {
   self.calls+=1;
   assert_eq!(self.clears,1); assert_eq!(instruction.accounts.len(),7); assert_eq!(infos.len(),8);
   for meta in &instruction.accounts { assert!(!meta.is_writable); assert!(!meta.is_signer); }
   assert_eq!(instruction.accounts[2].pubkey,*infos[2].key);
   assert_eq!(instruction.accounts[6].pubkey,*infos[6].key);
   Err(ProgramError::Custom(99))
  }
  fn get_return_data(&mut self)->Option<(Pubkey,Vec<u8>)> { panic!("no return read after failed CPI") }
 }
 #[kani::proof]
 #[kani::unwind(12)]
 fn PoolN_CPI_all_metas_readonly() {
  let keys:[Pubkey;8]=core::array::from_fn(|i|Pubkey::new_from_array([10+i as u8;32]));
  let mut balances=[1u64;8]; let mut data=[[0u8;0];8]; let loader=bpf_loader::id();
  let mut infos=Vec::new();
  for ((key,balance),bytes) in keys.iter().zip(balances.iter_mut()).zip(data.iter_mut()) {
   infos.push(AccountInfo::new(key,false,false,balance,bytes,&keys[7],false,0));
  }
  infos[7].executable=true; infos[7].owner=&loader;
  // Outer master/lane may be writable; CPI must still downgrade every meta.
  infos[1].is_writable=kani::any();infos[2].is_writable=kani::any();infos[3].is_writable=kani::any();
  let plan=PlannedPairForestDispatchV1{selected_verifier:keys[7],request_bytes:vec![]};
  let mut runtime=Inspect{clears:0,calls:0};
  let result=invoke_pair_forest_terminal_with_runtime_v1(plan,&infos[0],&infos[1],&infos[2],&infos[3],&infos[4..6],&infos[7],Some(&infos[6]),&mut runtime);
  assert!(matches!(result,Err(ProgramError::Custom(99))));
  assert_eq!(runtime.calls,1);kani::cover!(runtime.calls==1,"actual CPI reached");
 }
 #[kani::proof]
 #[kani::unwind(12)]
 fn PoolN_CPI_writable_checkpoint_rejected() {
  let keys:[Pubkey;3]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
  let mut balances=[1u64;3];let mut data=[[0u8;0];3];let id=Pubkey::new_from_array([30;32]);
  let mut infos=Vec::new();
  for ((key,balance),bytes) in keys.iter().zip(balances.iter_mut()).zip(data.iter_mut()) {
   infos.push(AccountInfo::new(key,false,false,balance,bytes,&keys[0],false,0));
  }
  infos[2].is_writable=true;
  let result=proof_transport_verifier(&infos[0],&infos[1],Some(&infos[2]));
  assert_eq!(result,Err(PoolV1ProgramError::InvalidVerifierProofAccount.into()));
 }
}
