#[derive(Clone,Copy)]
pub struct PoolV1PairForestTerminalBumpHintsV1 {pub current_page:u8,pub next_page:u8,pub vault_authority:u8,pub vault_token_account:u8}
#[derive(Clone,Copy)]
pub struct VaultBumpHintsV1 {pub vault_authority:u8,pub vault_token_account:u8}
pub fn reference(h:PoolV1PairForestTerminalBumpHintsV1)->VaultBumpHintsV1 {
 VaultBumpHintsV1 {vault_authority:h.vault_authority,vault_token_account:h.vault_token_account}
}
