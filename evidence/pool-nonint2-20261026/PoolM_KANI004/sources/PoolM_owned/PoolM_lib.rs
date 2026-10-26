// P6 owned metadata reference. Key/owner equalities are evaluated at the SDK cut.
// Errors use exact ProgramError/PoolV1ProgramError discriminants in the leaf bridge.
#[derive(Clone, Copy)]
pub struct Account {
 pub owner_matches: bool, pub system_owned: bool, pub executable: bool,
 pub signer: bool, pub writable: bool, pub len: usize,
}
pub fn prepared(a: Account, exact: usize) -> u32 {
 if !a.owner_matches || a.executable || a.signer || !a.writable || a.len != exact { 1 } else { 0 }
}
pub fn authority(a: Account) -> u32 {
 if !a.signer || !a.writable || a.executable || !a.system_owned { 2 } else { 0 }
}
pub fn cancel_roles(authority_account: Account, core: Account, shard: Account, has_shard: bool) -> u32 {
 let e=authority(authority_account);
 if e != 0 {return e;}
 let e=prepared(core,10000);
 if e != 0 {return e;}
 if has_shard {
  let e=prepared(shard,8504);
  if e != 0 {return e;}
 }
 0
}
