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

pub fn plan_receipted_checkpoint_v1(
    program_id: &Pubkey,
    master_account: &AccountInfo<'_>,
    lane_accounts: &[AccountInfo<'_>],
    receipts: &[AccountInfo<'_>],
    checkpoint_account: &AccountInfo<'_>,
) -> Result<PlannedPairForestCheckpointAccountsV1, ProgramError> {
    if lane_accounts.len() != POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(if lane_accounts.len() < POOL_V1_PAIR_FOREST_LANE_COUNT {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    require_alias_free(master_account, lane_accounts, checkpoint_account)?;
    let master = decode_checkpoint_master_box_v1(program_id, master_account)?;
    let lane_states =
        decode_checkpoint_receipted_lanes_v1(program_id, master_account.key, lane_accounts, receipts)?;
    let lane_roots = lane_states.each_ref().map(|lane| lane.tree.root);
    let global_root = pool_v1_pair_forest_global_root_v1(&lane_roots);
    let pure = plan_pool_v1_pair_forest_checkpoint_v1(&master, &lane_states, global_root)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let expected_checkpoint = pool_v1_pair_forest_checkpoint_address(
        program_id,
        master_account.key,
        pure.checkpoint.checkpoint_sequence,
    )
    .0;
    plan_fresh_program_pda(
        checkpoint_account,
        program_id,
        &expected_checkpoint,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    )?;
    let next_master_image = encode_pool_v1_pair_forest_master_v1(&pure.next_master)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let checkpoint_image = encode_pool_v1_pair_forest_checkpoint_v1(&pure.checkpoint)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    Ok(PlannedPairForestCheckpointAccountsV1 {
        master: *master_account.key,
        checkpoint: expected_checkpoint,
        lane_sequences: pure.checkpoint.lane_sequences,
        next_master_image,
        checkpoint_image,
    })
}
pub(crate) fn process_receipted_checkpoint_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    if instruction_data != b"AS8K\x01\x08\x01\x00" { return Err(ProgramError::InvalidInstructionData); }
    require_exact_account_count(accounts, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT + 8)?;
    require_unique_accounts(accounts)?;
    let master = &accounts[FOREST_MASTER_ACCOUNT_INDEX];
    let lanes = &accounts[FOREST_FIRST_LANE_ACCOUNT_INDEX
        ..FOREST_FIRST_LANE_ACCOUNT_INDEX + POOL_V1_PAIR_FOREST_LANE_COUNT];
    let checkpoint = &accounts[FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX];
    let payer = &accounts[FOREST_CHECKPOINT_PAYER_ACCOUNT_INDEX];
    let system_program_account = &accounts[FOREST_CHECKPOINT_SYSTEM_ACCOUNT_INDEX];
    require_payer_and_system_program(payer, system_program_account)?;

    let planned = plan_receipted_checkpoint_v1(program_id, master, lanes, &accounts[12..20], checkpoint)?;
    let preparation = plan_fresh_program_pda(
        checkpoint,
        program_id,
        &planned.checkpoint,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    )?;
    if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
        let sequence = decode_pool_v1_pair_forest_checkpoint_v1(&planned.checkpoint_image)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?
            .checkpoint_sequence;
        let sequence_bytes = sequence.to_le_bytes();
        let bump = pool_v1_pair_forest_checkpoint_address(program_id, master.key, sequence).1;
        let bump_bytes = [bump];
        let seeds: &[&[u8]] = &[
            POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
            master.key.as_ref(),
            &sequence_bytes,
            &bump_bytes,
        ];
        create_or_allocate_pda(
            runtime,
            payer,
            checkpoint,
            system_program_account,
            POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
            program_id,
            seeds,
        )?;
    }
    require_program_owned_zeroed(
        checkpoint,
        program_id,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
        rent,
    )?;

    let mut master_data = master.try_borrow_mut_data()?;
    let mut checkpoint_data = checkpoint.try_borrow_mut_data()?;
    checkpoint_data.copy_from_slice(&planned.checkpoint_image);
    master_data.copy_from_slice(&planned.next_master_image);
    Ok(())
}
