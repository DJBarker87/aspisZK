//! Account write boundary (X2c). The only place in the Pool program that takes a mutable handle on account data.
//!
//! Every account-data write of the four deployed handlers goes through the function below. Its callers decide
//! everything (the account, the byte range and the bytes) in plain-value code; this function only borrows the data
//! and copies. The Charon and Aeneas tools cannot express a write through the SDK's `RefMut<&mut [u8]>`, so this
//! function is made opaque by name in the emission and is reported as an account write boundary item.
//!
//! Contract on bytes: after `write_account_data_v1(account, start, end, bytes)` returns `Ok(())`, the account's data
//! equals its old data with `bytes` at `start..end`; every other field of the account and every other account are
//! unchanged. If the borrow fails, the borrow error is returned unchanged and nothing is changed. The caller
//! guarantees `start <= end`, `end - start == bytes.len()` and `end <= account.data_len()` (otherwise the slice
//! index or the copy panics, as the frozen writes did).
//!
//! The Pool moves lamports only through System and Token program invocations; it has no direct lamports write.

use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult};

#[inline(always)]
pub(crate) fn write_account_data_v1(account: &AccountInfo<'_>, start: usize, end: usize, bytes: &[u8]) -> ProgramResult {
    let mut data = match account.try_borrow_mut_data() {
        Ok(data) => data,
        Err(err) => return Err(err),
    };
    data[start..start + bytes.len()].copy_from_slice(bytes);
    Ok(())
}
