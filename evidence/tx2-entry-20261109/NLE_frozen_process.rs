pub(super) fn process(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    data: &[u8],
) -> ProgramResult {
    match data.first().copied() {
        Some(4) => lifecycle_init(program_id, accounts, data),
        Some(5) => lifecycle_write(program_id, accounts, data),
        Some(6) => lifecycle_finalize(program_id, accounts, data),
        _ if data == &[3, 10] || data == &[3, 11] => stage1(program_id, accounts, data),
        _ => stage2(program_id, accounts, data),
    }
}
