use super::*;
pub(super) fn reference(h:PoolV1PairForestTerminalBumpHintsV1)->VaultBumpHintsV1 { VaultBumpHintsV1 {vault_authority:h.vault_authority,vault_token_account:h.vault_token_account} }
#[cfg(kani)]
#[kani::proof_for_contract(PoolV1PairForestTerminalBumpHintsV1::vault)]
fn small_contract(){let p:PoolV1PairForestTerminalBumpHintsV1=kani::any();let _=p.vault();}
