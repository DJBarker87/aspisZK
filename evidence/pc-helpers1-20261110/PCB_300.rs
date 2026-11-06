use super::*;
pub(super) fn reference(h:PoolV1PairForestTerminalBumpHintsV1)->VaultBumpHintsV1 { VaultBumpHintsV1 {vault_authority:h.vault_authority,vault_token_account:h.vault_token_account} }
#[cfg(kani)]
#[kani::proof_for_contract(PoolV1PairForestTerminalBumpHintsV1::vault)]
fn small_contract(){let p:PoolV1PairForestTerminalBumpHintsV1=kani::any();let _=p.vault();}

#[cfg(kani)] #[kani::ensures(|r| r.vault_authority==x)]
fn record_weak(x:u8,y:u8)->VaultBumpHintsV1 {VaultBumpHintsV1 {vault_authority:x,vault_token_account:y}}
#[cfg(kani)] #[kani::proof_for_contract(record_weak)]
fn record_weak_contract(){let _=record_weak(kani::any(),kani::any());}
#[cfg(kani)] #[kani::proof]
fn record_real(){let x:u8=kani::any();let y:u8=kani::any();assert_eq!(record_weak(x,y).vault_token_account,y);}
#[cfg(kani)] #[kani::proof] #[kani::stub_verified(record_weak)]
fn record_unimplied(){let x:u8=kani::any();let y:u8=kani::any();assert_eq!(record_weak(x,y).vault_token_account,y);}
#[cfg(kani)] #[kani::modifies(&mut x[0])] #[kani::ensures(|_| true)]
fn record_bad_frame(x:&mut [u8;2])->VaultBumpHintsV1 {x[1]=x[1].wrapping_add(1);VaultBumpHintsV1 {vault_authority:0,vault_token_account:0}}
#[cfg(kani)] #[kani::proof_for_contract(record_bad_frame)]
fn record_frame(){let mut x:[u8;2]=kani::any();let _=record_bad_frame(&mut x);}
