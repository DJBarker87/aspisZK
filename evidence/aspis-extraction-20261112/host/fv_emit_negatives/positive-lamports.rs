use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult};
pub(crate) fn set_lamports_v1<'a>(account: &AccountInfo<'a>, amount: u64) -> ProgramResult {
    let mut lamports = match account.try_borrow_mut_lamports() {
        Ok(lamports) => lamports,
        Err(err) => return Err(err),
    };
    **lamports = amount;
    Ok(())
}
