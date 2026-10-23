//! The optional historical metadata-injection suite needs a patched LiteSVM.
//! This replay uses unpatched, pinned LiteSVM; the native differential suite
//! covers malformed metadata. Ordinary fixture replay never calls these hooks.
use super::*;
pub(super) fn run(_: &LiteSVM, _: Pubkey, _: &[Address], _: &[Address;7], _: &[u8], _: &[u8], _: &Keypair, _: &Path)->Result<()> { Err(anyhow!("metadata injection unavailable in pinned LiteSVM")) }
pub(super) fn run_stage1(_: &LiteSVM, _: Pubkey, _: &[Address], _: &[Address;3], _: &[Account], _: &Keypair, _: &Path)->Result<()> { Err(anyhow!("metadata injection unavailable in pinned LiteSVM")) }
