use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult};
#[inline(always)]
pub(crate) fn write_zero_data(account: &AccountInfo<'_>) -> ProgramResult {
    let mut data = match account.try_borrow_mut_data() { Ok(data) => data, Err(err) => return Err(err) };
    data[..8].fill(0);
    Ok(())
}
