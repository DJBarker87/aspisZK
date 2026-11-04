pub fn process_ref<'info>(
    program_id:&solana_program::pubkey::Pubkey,
    accounts:&[solana_program::account_info::AccountInfo<'info>],
    instruction_data:&[u8],
)->solana_program::entrypoint::ProgramResult{
    aspis_pool::process_instruction(program_id,accounts,instruction_data)
}
