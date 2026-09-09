// Default-off checkpoint setup extension. Receipt creation performs the FULL
// canonical lane/root/frontier validation. Finalization authenticates each
// receipt PDA and compares the entire lane image byte-for-byte. No digest
// collision assumption or persisted-write invariant substitutes for that check.
const CHECKPOINT_RECEIPT_SEED: &[u8] = b"aspis-v8-lane-validation";
const CHECKPOINT_RECEIPT_BYTES: usize = 40 + POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES;
const CHECKPOINT_RECEIPT_MAGIC: &[u8;8] = b"AS8V\x01\x08\x00\x00";

pub(crate) fn process_checkpoint_receipt_v1<'info, R: PoolCpiRuntimeV1>(
 program_id:&Pubkey, accounts:&[AccountInfo<'info>], data:&[u8], rent:&Rent, runtime:&mut R,
)->ProgramResult {
 if data.len()!=8 || &data[..4]!=b"AS8V" || data[4]!=1 || data[5]>=8 || data[6..]!=[0,0] {return Err(ProgramError::InvalidInstructionData);}
 require_exact_account_count(accounts,5)?; require_unique_accounts(accounts)?;
 let master=&accounts[0]; let lane=&accounts[1]; let receipt=&accounts[2]; let payer=&accounts[3]; let system=&accounts[4];
 decode_master_account(program_id,master,false)?;
 decode_lane_account(program_id,master.key,data[5],lane,false)?;
 require_payer_and_system_program(payer,system)?;
 let (address,bump)=Pubkey::find_program_address(&[CHECKPOINT_RECEIPT_SEED,lane.key.as_ref()],program_id);
 if receipt.key!=&address || receipt.is_signer || !receipt.is_writable || receipt.executable {return Err(ProgramError::InvalidAccountData);}
 if receipt.owner!=program_id {
  let preparation=plan_fresh_program_pda(receipt,program_id,&address,CHECKPOINT_RECEIPT_BYTES)?;
  if preparation!=FreshPdaPreparationV1::CreateOrAllocateSystemOwned {return Err(ProgramError::InvalidAccountData);}
  create_or_allocate_pda(runtime,payer,receipt,system,CHECKPOINT_RECEIPT_BYTES,program_id,&[CHECKPOINT_RECEIPT_SEED,lane.key.as_ref(),&[bump]])?;
  require_program_owned_zeroed(receipt,program_id,CHECKPOINT_RECEIPT_BYTES,rent)?;
 } else {
  require_program_account(receipt,program_id,true)?;
  let old=receipt.try_borrow_data()?;
  if old.len()!=CHECKPOINT_RECEIPT_BYTES || &old[..8]!=CHECKPOINT_RECEIPT_MAGIC || old[8..40]!=lane.key.to_bytes() || !rent.is_exempt(receipt.lamports(),old.len()) {return Err(ProgramError::InvalidAccountData);}
 }
 let image=lane.try_borrow_data()?;
 let mut out=receipt.try_borrow_mut_data()?;
 out[..8].copy_from_slice(CHECKPOINT_RECEIPT_MAGIC); out[8..40].copy_from_slice(lane.key.as_ref()); out[40..].copy_from_slice(&image);
 Ok(())
}

#[inline(never)]
fn decode_checkpoint_receipted_lanes_v1(program_id:&Pubkey,master:&Pubkey,lanes:&[AccountInfo<'_>],receipts:&[AccountInfo<'_>]) -> Result<Box<[PoolV1PairForestLaneStateV1;8]>,ProgramError> {
 if lanes.len()!=8 || receipts.len()!=8 {return Err(ProgramError::NotEnoughAccountKeys);}
 let mut states=Vec::with_capacity(8);
 for i in 0..8 {
  let receipt=&receipts[i]; let lane=&lanes[i];
  require_program_account(receipt,program_id,false)?;
  if receipt.is_signer || receipt.key!=&Pubkey::find_program_address(&[CHECKPOINT_RECEIPT_SEED,lane.key.as_ref()],program_id).0 {return Err(ProgramError::InvalidAccountData);}
  let r=receipt.try_borrow_data()?; let l=lane.try_borrow_data()?;
  if r.len()!=CHECKPOINT_RECEIPT_BYTES || &r[..8]!=CHECKPOINT_RECEIPT_MAGIC || r[8..40]!=lane.key.to_bytes() || r[40..]!=l[..] {return Err(ProgramError::InvalidAccountData);}
  // Root/frontier relation is established by the exact authenticated receipt,
  // not assumed from lane ownership. Recheck canonical structure and binding.
  states.push(decode_lane_account_from_program_invariant_v1(program_id,master,i as u8,lane,false)?);
 }
 states.into_boxed_slice().try_into().map_err(|_|ProgramError::InvalidAccountData)
}
