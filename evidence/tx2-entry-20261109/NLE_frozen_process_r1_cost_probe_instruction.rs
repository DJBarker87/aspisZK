pub fn process_r1_cost_probe_instruction(program_id:&Pubkey,accounts:&[AccountInfo],data:&[u8])->ProgramResult{
    #[cfg(feature="pool-adapter")]
    {
        // Reject before inspecting or borrowing any account. Lifecycle loaders
        // are not part of the release instruction surface.
        if !pool_route::admitted(data) {
            return Err(ProgramError::InvalidInstructionData);
        }
        return r1_pool_adapter::process(program_id,accounts,data);
    }

    #[cfg(not(feature="pool-adapter"))]
    {
    if accounts.len()!=3||!matches!(data,[1,0..=22]|[2]) {return Err(ProgramError::InvalidInstructionData);}
    for (i,a) in accounts.iter().enumerate(){if a.owner!=program_id||a.executable||a.is_writable!=(i==2){return Err(ProgramError::InvalidAccountData);}}
    let proof=accounts[0].try_borrow_data()?;let public=accounts[1].try_borrow_data()?;let mut checkpoint=accounts[2].try_borrow_mut_data()?;
    msg!("UNPROVED R1 COST PROBE");msg!("r1:begin");sol_log_compute_units();
    if data[0]==1 {
        if checkpoint.iter().any(|&b|b!=0){return Err(ProgramError::AccountAlreadyInitialized);}
        let bytes=first(&public,&proof,data[1]as usize)?;
        if checkpoint.len()!=bytes.len(){return Err(ProgramError::InvalidAccountData);}
        checkpoint.copy_from_slice(&bytes);
    } else {
        verifier::tx2(&public,&proof,&checkpoint,SolanaDigest,observer()).map_err(error)?;
        checkpoint[10]=2;let end=checkpoint.len()-32;let sum=hashv(&[b"UNPROVED:R1:checkpoint",&checkpoint[..end]]).to_bytes();checkpoint[end..].copy_from_slice(&sum);
    }
    msg!("r1:account-write");sol_log_compute_units();
    #[cfg(target_os="solana")]
    unsafe {
        let cursor=*(solana_program::entrypoint::HEAP_START_ADDRESS as *const usize);
        msg!("r1:heap-high-water");solana_program::log::sol_log_64((solana_program::entrypoint::HEAP_START_ADDRESS as usize+256*1024-cursor+core::mem::size_of::<usize>())as u64,0,0,0,0);
    }
    Ok(())
    }
}
