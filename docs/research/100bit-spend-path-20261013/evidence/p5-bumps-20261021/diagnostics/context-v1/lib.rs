#![allow(dead_code, unused_variables, static_mut_refs)]
// SDK boundary: a memoised symbolic function on full seed tuples + program ID.
// Each selected guard makes at most one distinct query. A second identical
// query returns the saved result; a second distinct query fails this harness.
// Thus all possible one-query functions are represented, including failure,
// collisions, and noncanonical addresses. No injectivity/canonicality assumed.
#[derive(Clone,Copy,Debug,PartialEq,Eq,kani::Arbitrary)]
struct Pubkey([u8;32]);
impl AsRef<[u8]> for Pubkey {fn as_ref(&self)->&[u8]{&self.0}}
impl Pubkey {
 fn new_from_array(v:[u8;32])->Self{Self(v)}
 fn to_bytes(&self)->[u8;32]{self.0}
 fn create_program_address(s:&[&[u8]],p:&Self)->Result<Self,ProgramError>{derive(query(s,p)).ok_or(ProgramError::InvalidSeeds)}
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Query{program:Pubkey,bytes:[u8;192],ends:[usize;8],count:usize,len:usize}
fn query(seeds:&[&[u8]],p:&Pubkey)->Query {
 let mut q=Query{program:*p,bytes:[0;192],ends:[0;8],count:seeds.len(),len:0};
 for (i,s) in seeds.iter().enumerate(){for &b in *s{q.bytes[q.len]=b;q.len+=1;}q.ends[i]=q.len;}q
}
#[derive(Clone,Copy,Debug)]struct Memo{query:Query,answer:Option<Pubkey>}
static mut MEMO:Option<Memo>=None;
fn reset(){unsafe{MEMO=None;}}
fn memo()->Memo{unsafe{MEMO.expect("acceptance must call derivation")}}
fn derive(q:Query)->Option<Pubkey>{unsafe{if let Some(m)=MEMO{assert_eq!(m.query,q);m.answer}else{let answer:Option<Pubkey>=kani::any();MEMO=Some(Memo{query:q,answer});answer}}}
fn any_key()->Pubkey{kani::any()}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum ProgramError{InvalidSeeds,InvalidAccountData,InvalidInstructionData,IncorrectProgramId}
type PoolV1ProgramError=Errors;
type RegistryProgramErrorV1=Errors;
#[derive(Clone,Copy)]enum Errors{InvalidRootPageAddress,StateHistoryMismatch,InvalidVaultAuthority,InvalidVaultTokenAddress,InvalidNullifierMarkerAddress,InvalidFreshAccount}
impl From<Errors> for ProgramError{fn from(_:Errors)->Self{Self::InvalidAccountData}}
#[derive(Clone,Copy)]struct AccountInfo<'a>{key:&'a Pubkey,owner:&'a Pubkey,executable:bool,is_signer:bool,is_writable:bool,data:[u8;16],len:usize}
impl AccountInfo<'_>{fn data_is_empty(&self)->bool{self.len==0}fn try_borrow_data(&self)->Result<&[u8],ProgramError>{Ok(&self.data[..self.len])}}
static SYSTEM:Pubkey=Pubkey([0;32]);
static mut OWNER:Pubkey=Pubkey([0;32]);
mod system_program{use super::*;pub fn id()->Pubkey{SYSTEM}}
// Metadata, bytes and length are symbolic, with the memory validity invariant
// enforced by AccountInfo itself represented as len <= allocated buffer.
fn account(key:&Pubkey)->AccountInfo<'_>{let len:usize=kani::any();kani::assume(len<=16);AccountInfo{key,owner:unsafe{OWNER=any_key();&OWNER},executable:kani::any(),is_signer:kani::any(),is_writable:kani::any(),data:kani::any(),len}}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Identity{pool:[u8;32],asset_mint:[u8;32],deployment_domain:[u8;32]}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Policy{registry_authority:[u8;32],policy_binding:[u8;32]}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Master{identity:Identity,bump:u8,initialized_lane_mask:u8,verifier_policy:Policy}
type PoolV1PairForestMasterV1=Master;
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Checkpoint{master:[u8;32],bump:u8,checkpoint_sequence:u64,deployment_domain:[u8;32]}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Lane{master:[u8;32],bump:u8,lane_id:u8}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Registry{bump:u8,programdata_bump:u8,pool:[u8;32],authority:[u8;32],policy_binding:[u8;32],registry_program:[u8;32],loader_program:[u8;32],programdata_address:[u8;32],verifier_program:[u8;32],profile_binding:[u8;32],release_binding:[u8;32],statement_version:u8,expected_upgrade_authority:[u8;32],immutable:bool,paused:bool,active:bool}
impl Registry{fn is_immutable(&self)->bool{self.immutable}fn is_paused(&self)->bool{self.paused}fn is_active_at(&self,_:u64)->bool{self.active}}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct VaultBumpHintsV1{vault_authority:u8,vault_token_account:u8}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Marker{pool:[u8;32],nullifier:[u8;32]}
impl Marker{fn canonical_nullifier_encoding(&self)->[u8;32]{self.nullifier}}
fn pool_v1_pair_forest_nullifier_marker_address(p:&Pubkey,pool:&Pubkey,n:&[u8;32])->Result<(Pubkey,[u8;32]),ProgramError>{Ok((derive(query(&[pool.as_ref(),n],p)).ok_or(ProgramError::InvalidSeeds)?,[0;32]))}
// The unhinted vault branch is unreachable in the selected Some(hints) harness.
fn pool_v1_vault_token_account_address(_: &Pubkey,_:&Pubkey)->(Pubkey,u8){panic!("unhinted branch")}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]enum FreshPdaPreparationV1{ProgramOwnedZeroed,CreateOrAllocateSystemOwned}
const POOL_V1_PAIR_FOREST_LANE_COUNT:usize=8;
const POOL_V1_PAIR_FOREST_ALL_LANES_MASK:u8=255;
const POOL_V1_PAIR_FOREST_TERMINAL_VERSION:u8=1;
const PROFILE_BINDING:[u8;32]=[1;32];const RELEASE_BINDING:[u8;32]=[2;32];const AUDIT_POLICY_BINDING:[u8;32]=[3;32];
const POOL_V1_PAIR_FOREST_MASTER_SEED:&[u8]=b"aspis-pair-forest-master-v1";
const POOL_V1_PAIR_FOREST_LANE_SEED:&[u8]=b"aspis-pair-forest-lane-v1";
const POOL_V1_PAIR_FOREST_CHECKPOINT_SEED:&[u8]=b"aspis-pair-forest-checkpoint-v1";
const PAIR_FOREST_MASTER_SEED:&[u8]=POOL_V1_PAIR_FOREST_MASTER_SEED;
const PAIR_FOREST_LANE_SEED:&[u8]=POOL_V1_PAIR_FOREST_LANE_SEED;
const PAIR_FOREST_CHECKPOINT_SEED:&[u8]=POOL_V1_PAIR_FOREST_CHECKPOINT_SEED;
const POOL_V1_ROOT_HISTORY_PAGE_SEED:&[u8]=b"aspis-root-page-v1";
const VERIFIER_REGISTRY_SEED:&[u8]=b"aspis-verifier-registry-v1";
const VERIFIER_REGISTRY_V2_SEED:&[u8]=b"aspis-verifier-registry-v2";
const VERIFIER_ENTRY_SEED:&[u8]=b"aspis-verifier-entry-v1";
const VERIFIER_ENTRY_V2_SEED:&[u8]=b"aspis-verifier-entry-v2";
const POOL_V1_VAULT_AUTHORITY_SEED:&[u8]=b"aspis-pool-vault-authority-v1";
const POOL_V1_VAULT_TOKEN_ACCOUNT_SEED:&[u8]=b"aspis-pool-vault-token-v1";

mod registry { use super::*;
pub(crate) fn stored_bump_address_matches(
    seeds_with_bump: &[&[u8]],
    program_id: &Pubkey,
    key: &Pubkey,
) -> bool {
    Pubkey::create_program_address(seeds_with_bump, program_id).is_ok_and(|address| &address == key)
}
}

mod pool_master { use super::*;
fn master_address_matches(
    program_id: &Pubkey,
    master: &PoolV1PairForestMasterV1,
    key: &Pubkey,
) -> bool {
    crate::registry::stored_bump_address_matches(
        &[
            POOL_V1_PAIR_FOREST_MASTER_SEED,
            &master.identity.asset_mint,
            &[master.bump],
        ],
        program_id,
        key,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn pool_master(){reset();let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any(); let master: Master=kani::any(); let lane:u8=kani::any(); let accepted=master_address_matches(&program_id,&master,&target); if accepted {assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&[POOL_V1_PAIR_FOREST_MASTER_SEED,&master.identity.asset_mint,&[master.bump]],&program_id));}}
}

mod pool_lane { use super::*;
fn lane_address_matches(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
    bump: u8,
    key: &Pubkey,
) -> Result<bool, ProgramError> {
    if usize::from(lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok(crate::registry::stored_bump_address_matches(
        &[
            POOL_V1_PAIR_FOREST_LANE_SEED,
            master.as_ref(),
            &[lane_id],
            &[bump],
        ],
        program_id,
        key,
    ))
}
#[kani::proof]
#[kani::unwind(200)]
fn pool_lane(){reset();let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any(); let master: Master=kani::any(); let lane:u8=kani::any(); let accepted=lane_address_matches(&program_id,&pool,lane,bump,&target).unwrap_or(false); if accepted {assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&[POOL_V1_PAIR_FOREST_LANE_SEED,pool.as_ref(),&[lane],&[bump]],&program_id));}}
}

mod page_genesis {use super::*;
pub(crate) fn require_root_page_address_with_bump(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
    bump: u8,
    account: &AccountInfo,
) -> Result<(), ProgramError> {
    let page_number_bytes = page_number.to_le_bytes();
    if !crate::registry::stored_bump_address_matches(
        &[
            POOL_V1_ROOT_HISTORY_PAGE_SEED,
            pool.as_ref(),
            &page_number_bytes,
            &[bump],
        ],
        program_id,
        account.key,
    ) {
        return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
    }
    Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn page_genesis(){reset();let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any();let page:u64=kani::any(); let accepted=require_root_page_address_with_bump(&program_id,&pool,page,bump,&account).is_ok(); if accepted {assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&[POOL_V1_ROOT_HISTORY_PAGE_SEED,pool.as_ref(),&page.to_le_bytes(),&[bump]],&program_id));}}
}

mod page_current {use super::*;
pub(crate) fn require_root_page_address_with_bump(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
    bump: u8,
    account: &AccountInfo,
) -> Result<(), ProgramError> {
    let page_number_bytes = page_number.to_le_bytes();
    if !crate::registry::stored_bump_address_matches(
        &[
            POOL_V1_ROOT_HISTORY_PAGE_SEED,
            pool.as_ref(),
            &page_number_bytes,
            &[bump],
        ],
        program_id,
        account.key,
    ) {
        return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
    }
    Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn page_current(){reset();let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any();let page:u64=kani::any(); let accepted=require_root_page_address_with_bump(&program_id,&pool,page,bump,&account).is_ok(); if accepted {assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&[POOL_V1_ROOT_HISTORY_PAGE_SEED,pool.as_ref(),&page.to_le_bytes(),&[bump]],&program_id));}}
}

mod page_rollover {use super::*;
pub(crate) fn require_root_page_address_with_bump(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
    bump: u8,
    account: &AccountInfo,
) -> Result<(), ProgramError> {
    let page_number_bytes = page_number.to_le_bytes();
    if !crate::registry::stored_bump_address_matches(
        &[
            POOL_V1_ROOT_HISTORY_PAGE_SEED,
            pool.as_ref(),
            &page_number_bytes,
            &[bump],
        ],
        program_id,
        account.key,
    ) {
        return Err(PoolV1ProgramError::InvalidRootPageAddress.into());
    }
    Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn page_rollover(){reset();let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any();let page:u64=kani::any(); let accepted=require_root_page_address_with_bump(&program_id,&pool,page,bump,&account).is_ok(); if accepted {assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&[POOL_V1_ROOT_HISTORY_PAGE_SEED,pool.as_ref(),&page.to_le_bytes(),&[bump]],&program_id));}}
}

mod pool_checkpoint {
use super::*;
fn check(program_id: &Pubkey, expected_master: &Pubkey, account: &AccountInfo, checkpoint: &Checkpoint) -> Result<(),ProgramError> {
    if checkpoint.master != expected_master.to_bytes()
        || !crate::registry::stored_bump_address_matches(
            &[
                POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
                expected_master.as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
                &[checkpoint.bump],
            ],
            program_id,
            account.key,
        )
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn pool_checkpoint() { reset();
let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any();let expected_master=&pool;let program_id=&program_id;let account=&account;let checkpoint:&Checkpoint=&kani::any();
let accepted = check(program_id,expected_master,account,checkpoint).is_ok();
if accepted { let target = *account.key; assert_eq!(memo().query, query(&[POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,expected_master.as_ref(),&checkpoint.checkpoint_sequence.to_le_bytes(),&[checkpoint.bump]], &*program_id)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_master {
use super::*;
fn check(pool_program: &Pubkey, master_account: &AccountInfo, checkpoint_account: &AccountInfo, lane_account: &AccountInfo, master: &Master, checkpoint: &Checkpoint, selected_lane: &Lane, output_lane: u8) -> Result<(),ProgramError> {
    if master.identity.pool != master_account.key.to_bytes()
        || master.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_MASTER_SEED,
                Pubkey::new_from_array(master.identity.asset_mint).as_ref(),
                &[master.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *master_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_master() { reset();
let pp=any_key();let pool_program=&pp;let mk=any_key();let ck=any_key();let lk=any_key();let ma=account(&mk);let ca=account(&ck);let la=account(&lk);let master_account=&ma;let checkpoint_account=&ca;let lane_account=&la;let master:&Master=&kani::any();let checkpoint:&Checkpoint=&kani::any();let selected_lane:&Lane=&kani::any();let output_lane:u8=kani::any();
let accepted = check(pool_program,master_account,checkpoint_account,lane_account,master,checkpoint,selected_lane,output_lane).is_ok();
if accepted { let target = *master_account.key; assert_eq!(memo().query, query(&[PAIR_FOREST_MASTER_SEED,&master.identity.asset_mint,&[master.bump]], &*pool_program)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_checkpoint {
use super::*;
fn check(pool_program: &Pubkey, master_account: &AccountInfo, checkpoint_account: &AccountInfo, lane_account: &AccountInfo, master: &Master, checkpoint: &Checkpoint, selected_lane: &Lane, output_lane: u8) -> Result<(),ProgramError> {
    if checkpoint.master != master_account.key.to_bytes()
        || checkpoint.deployment_domain != master.identity.deployment_domain
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_account.key.as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
                &[checkpoint.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *checkpoint_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_checkpoint() { reset();
let pp=any_key();let pool_program=&pp;let mk=any_key();let ck=any_key();let lk=any_key();let ma=account(&mk);let ca=account(&ck);let la=account(&lk);let master_account=&ma;let checkpoint_account=&ca;let lane_account=&la;let master:&Master=&kani::any();let checkpoint:&Checkpoint=&kani::any();let selected_lane:&Lane=&kani::any();let output_lane:u8=kani::any();
let accepted = check(pool_program,master_account,checkpoint_account,lane_account,master,checkpoint,selected_lane,output_lane).is_ok();
if accepted { let target = *checkpoint_account.key; assert_eq!(memo().query, query(&[PAIR_FOREST_CHECKPOINT_SEED,master_account.key.as_ref(),&checkpoint.checkpoint_sequence.to_le_bytes(),&[checkpoint.bump]], &*pool_program)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_lane {
use super::*;
fn check(pool_program: &Pubkey, master_account: &AccountInfo, checkpoint_account: &AccountInfo, lane_account: &AccountInfo, master: &Master, checkpoint: &Checkpoint, selected_lane: &Lane, output_lane: u8) -> Result<(),ProgramError> {
    if selected_lane.master != master_account.key.to_bytes()
        || selected_lane.lane_id != output_lane
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master_account.key.as_ref(),
                &[output_lane],
                &[selected_lane.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *lane_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_lane() { reset();
let pp=any_key();let pool_program=&pp;let mk=any_key();let ck=any_key();let lk=any_key();let ma=account(&mk);let ca=account(&ck);let la=account(&lk);let master_account=&ma;let checkpoint_account=&ca;let lane_account=&la;let master:&Master=&kani::any();let checkpoint:&Checkpoint=&kani::any();let selected_lane:&Lane=&kani::any();let output_lane:u8=kani::any();
let accepted = check(pool_program,master_account,checkpoint_account,lane_account,master,checkpoint,selected_lane,output_lane).is_ok();
if accepted { let target = *lane_account.key; assert_eq!(memo().query, query(&[PAIR_FOREST_LANE_SEED,master_account.key.as_ref(),&[output_lane],&[selected_lane.bump]], &*pool_program)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_registry_v1 {
use super::*;
fn check(registry_program: Pubkey, master_account: &AccountInfo, registry_account: &AccountInfo, entry_account: &AccountInfo, registry: &Registry, entry: &Registry) -> Result<(),ProgramError> {
let expected_registry = Pubkey::create_program_address(
        &[
            VERIFIER_REGISTRY_SEED,
            master_account.key.as_ref(),
            &[registry.bump],
        ],
        &registry_program,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if registry_account.key != &expected_registry {
        return Err(ProgramError::InvalidAccountData);
    }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_registry_v1() { reset();
let registry_program=any_key();let mk=any_key();let rk=any_key();let ek=any_key();let ma=account(&mk);let ra=account(&rk);let ea=account(&ek);let master_account=&ma;let registry_account=&ra;let entry_account=&ea;let registry:&Registry=&kani::any();let entry:&Registry=&kani::any();
let accepted = check(registry_program,master_account,registry_account,entry_account,registry,entry).is_ok();
if accepted { let target = *registry_account.key; assert_eq!(memo().query, query(&[VERIFIER_REGISTRY_SEED,master_account.key.as_ref(),&[registry.bump]], &registry_program)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_entry_v1 {
use super::*;
fn check(registry_program: Pubkey, master_account: &AccountInfo, registry_account: &AccountInfo, entry_account: &AccountInfo, registry: &Registry, entry: &Registry) -> Result<(),ProgramError> {
let expected_entry = Pubkey::create_program_address(
        &[
            VERIFIER_ENTRY_SEED,
            master_account.key.as_ref(),
            &PROFILE_BINDING,
            &RELEASE_BINDING,
            &[entry.bump],
        ],
        &registry_program,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if entry_account.key != &expected_entry {
        return Err(ProgramError::InvalidAccountData);
    }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_entry_v1() { reset();
let registry_program=any_key();let mk=any_key();let rk=any_key();let ek=any_key();let ma=account(&mk);let ra=account(&rk);let ea=account(&ek);let master_account=&ma;let registry_account=&ra;let entry_account=&ea;let registry:&Registry=&kani::any();let entry:&Registry=&kani::any();
let accepted = check(registry_program,master_account,registry_account,entry_account,registry,entry).is_ok();
if accepted { let target = *entry_account.key; assert_eq!(memo().query, query(&[VERIFIER_ENTRY_SEED,master_account.key.as_ref(),&PROFILE_BINDING,&RELEASE_BINDING,&[entry.bump]], &registry_program)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_registry_v2 {
use super::*;
fn check(registry_program: Pubkey, master_account: &AccountInfo, registry_account: &AccountInfo, entry_account: &AccountInfo, registry: &Registry, entry: &Registry) -> Result<(),ProgramError> {
let expected_registry = Pubkey::create_program_address(
            &[
                VERIFIER_REGISTRY_V2_SEED,
                master_account.key.as_ref(),
                &[registry.bump],
            ],
            &registry_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if registry_account.key != &expected_registry {
            return Err(ProgramError::InvalidAccountData);
        }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_registry_v2() { reset();
let registry_program=any_key();let mk=any_key();let rk=any_key();let ek=any_key();let ma=account(&mk);let ra=account(&rk);let ea=account(&ek);let master_account=&ma;let registry_account=&ra;let entry_account=&ea;let registry:&Registry=&kani::any();let entry:&Registry=&kani::any();
let accepted = check(registry_program,master_account,registry_account,entry_account,registry,entry).is_ok();
if accepted { let target = *registry_account.key; assert_eq!(memo().query, query(&[VERIFIER_REGISTRY_V2_SEED,master_account.key.as_ref(),&[registry.bump]], &registry_program)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_entry_v2 {
use super::*;
fn check(registry_program: Pubkey, master_account: &AccountInfo, registry_account: &AccountInfo, entry_account: &AccountInfo, registry: &Registry, entry: &Registry) -> Result<(),ProgramError> {
let expected_entry = Pubkey::create_program_address(
            &[
                VERIFIER_ENTRY_V2_SEED,
                master_account.key.as_ref(),
                &PROFILE_BINDING,
                &RELEASE_BINDING,
                &[entry.bump],
            ],
            &registry_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if entry_account.key != &expected_entry {
            return Err(ProgramError::InvalidAccountData);
        }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_entry_v2() { reset();
let registry_program=any_key();let mk=any_key();let rk=any_key();let ek=any_key();let ma=account(&mk);let ra=account(&rk);let ea=account(&ek);let master_account=&ma;let registry_account=&ra;let entry_account=&ea;let registry:&Registry=&kani::any();let entry:&Registry=&kani::any();
let accepted = check(registry_program,master_account,registry_account,entry_account,registry,entry).is_ok();
if accepted { let target = *entry_account.key; assert_eq!(memo().query, query(&[VERIFIER_ENTRY_V2_SEED,master_account.key.as_ref(),&PROFILE_BINDING,&RELEASE_BINDING,&[entry.bump]], &registry_program)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_registry_programdata {
use super::*;
fn check(registry_program: Pubkey, verifier_program: &Pubkey, loader: Pubkey, master_account: &AccountInfo, master: &Master, registry: &Registry, entry: &Registry, current_slot: u64) -> Result<(),ProgramError> {
let registry_programdata = Pubkey::create_program_address(
            &[registry_program.as_ref(), &[registry.programdata_bump]],
            &loader,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if registry.pool != master_account.key.to_bytes()
            || registry.authority != master.verifier_policy.registry_authority
            || registry.policy_binding != master.verifier_policy.policy_binding
            || registry.registry_program != registry_program.to_bytes()
            || registry.loader_program != loader.to_bytes()
            || registry.programdata_address != registry_programdata.to_bytes()
            || !registry.is_immutable()
            || registry.is_paused()
        {
            return Err(ProgramError::InvalidAccountData);
        }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_registry_programdata() { reset();
let registry_program=any_key();let vp=any_key();let verifier_program=&vp;let loader=any_key();let mk=any_key();let ma=account(&mk);let master_account=&ma;let master:&Master=&kani::any();let registry:&Registry=&kani::any();let entry:&Registry=&kani::any();let current_slot:u64=kani::any();
let accepted = check(registry_program,verifier_program,loader,master_account,master,registry,entry,current_slot).is_ok();
if accepted { let target = Pubkey::new_from_array(registry.programdata_address); assert_eq!(memo().query, query(&[registry_program.as_ref(),&[registry.programdata_bump]], &loader)); assert_eq!(memo().answer,Some(target)); }
}
}

mod verifier_entry_programdata {
use super::*;
fn check(registry_program: Pubkey, verifier_program: &Pubkey, loader: Pubkey, master_account: &AccountInfo, master: &Master, registry: &Registry, entry: &Registry, current_slot: u64) -> Result<(),ProgramError> {
let verifier_programdata = Pubkey::create_program_address(
            &[verifier_program.as_ref(), &[entry.programdata_bump]],
            &loader,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if entry.pool != master_account.key.to_bytes()
            || entry.policy_binding != AUDIT_POLICY_BINDING
            || entry.verifier_program != verifier_program.to_bytes()
            || entry.profile_binding != PROFILE_BINDING
            || entry.release_binding != RELEASE_BINDING
            || entry.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
            || entry.loader_program != loader.to_bytes()
            || entry.programdata_address != verifier_programdata.to_bytes()
            || entry.expected_upgrade_authority != [0u8; 32]
            || !entry.is_active_at(current_slot)
        {
            return Err(ProgramError::InvalidAccountData);
        }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_entry_programdata() { reset();
let registry_program=any_key();let vp=any_key();let verifier_program=&vp;let loader=any_key();let mk=any_key();let ma=account(&mk);let master_account=&ma;let master:&Master=&kani::any();let registry:&Registry=&kani::any();let entry:&Registry=&kani::any();let current_slot:u64=kani::any();
let accepted = check(registry_program,verifier_program,loader,master_account,master,registry,entry,current_slot).is_ok();
if accepted { let target = Pubkey::new_from_array(entry.programdata_address); assert_eq!(memo().query, query(&[verifier_program.as_ref(),&[entry.programdata_bump]], &loader)); assert_eq!(memo().answer,Some(target)); }
}
}

mod vault_authority {use super::*; fn check(program_id:&Pubkey,pool:&Pubkey,hints:VaultBumpHintsV1,vault_authority:&AccountInfo)->Result<(),ProgramError>{let _authority=if crate::registry::stored_bump_address_matches(
                &[
                    POOL_V1_VAULT_AUTHORITY_SEED,
                    pool.as_ref(),
                    &[hints.vault_authority],
                ],
                program_id,
                vault_authority.key,
            ) {
                *vault_authority.key
            } else {
                return Err(PoolV1ProgramError::InvalidVaultAuthority.into());
            };Ok(())}
#[kani::proof]
#[kani::unwind(200)]
fn vault_authority(){reset();let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any();let hints:VaultBumpHintsV1=kani::any();let accepted=check(&program_id,&pool,hints,&account).is_ok();if accepted{assert_eq!(memo().answer,Some(target));assert_eq!(memo().query,query(&[POOL_V1_VAULT_AUTHORITY_SEED,pool.as_ref(),&[hints.vault_authority]],&program_id));}}}

mod vault_token {
use super::*;
fn check(program_id: &Pubkey, pool: &Pubkey, bump_hints: Option<VaultBumpHintsV1>, vault_account: &AccountInfo) -> Result<(),ProgramError> {
let vault_address_ok = match bump_hints {
        Some(hints) => crate::registry::stored_bump_address_matches(
            &[
                POOL_V1_VAULT_TOKEN_ACCOUNT_SEED,
                pool.as_ref(),
                &[hints.vault_token_account],
            ],
            program_id,
            vault_account.key,
        ),
        None => vault_account.key == &pool_v1_vault_token_account_address(program_id, pool).0,
    };
    if !vault_address_ok {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn vault_token() { reset();
let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any();let hints:VaultBumpHintsV1=kani::any();let program_id=&program_id;let pool=&pool;let bump_hints=Some(hints);let vault_account=&account;
let accepted = check(program_id,pool,bump_hints,vault_account).is_ok();
if accepted { let target = *vault_account.key; assert_eq!(memo().query, query(&[POOL_V1_VAULT_TOKEN_ACCOUNT_SEED,pool.as_ref(),&[bump_hints.unwrap().vault_token_account]], &*program_id)); assert_eq!(memo().answer,Some(target)); }
}
}

mod marker_b1 {
use super::*;
fn check(program_id: &Pubkey, marker_account: &AccountInfo, marker: Marker) -> Result<(),ProgramError> {
let pool = Pubkey::new_from_array(marker.pool);
    let (expected_address, seed) = pool_v1_pair_forest_nullifier_marker_address(
        program_id,
        &pool,
        &marker.canonical_nullifier_encoding(),
    )?;
    if marker_account.key != &expected_address || marker_account.key == &pool {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into());
    }
Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn marker_b1() { reset();
let program_id=any_key(); let pool=any_key(); let target=any_key(); let account=account(&target); let bump:u8=kani::any();let program_id=&program_id;let marker_account=&account;let marker:Marker=kani::any();
let accepted = check(program_id,marker_account,marker).is_ok();
if accepted { let target = *marker_account.key; assert_eq!(memo().query, query(&[&marker.pool,&marker.canonical_nullifier_encoding()], &*program_id)); assert_eq!(memo().answer,Some(target)); }
}
}

mod pool_fresh {use super::*;pub(crate) fn plan_fresh_program_pda(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    expected_address: &Pubkey,
    exact_bytes: usize,
) -> Result<FreshPdaPreparationV1, ProgramError> {
    if account.key != expected_address
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    if account.owner == program_id {
        let data = account.try_borrow_data()?;
        if data.len() != exact_bytes || data.iter().any(|byte| *byte != 0) {
            return Err(PoolV1ProgramError::InvalidFreshAccount.into());
        }
        Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)
    } else if account.owner == &system_program::id() && account.data_is_empty() {
        Ok(FreshPdaPreparationV1::CreateOrAllocateSystemOwned)
    } else {
        Err(PoolV1ProgramError::InvalidFreshAccount.into())
    }
}
#[kani::proof]
#[kani::unwind(200)]
fn pool_fresh(){let program_id=any_key();let expected=any_key();let key=any_key();let account=account(&key);let size:usize=kani::any();let accepted=plan_fresh_program_pda(&account,&program_id,&expected,size).is_ok();if accepted{assert_eq!(key,expected);assert!(!account.executable&&!account.is_signer&&account.is_writable);assert!(account.owner==&program_id||(account.owner==&system_program::id()&&account.data_is_empty()));}}}

mod registry_fresh {use super::*;fn plan_fresh_program_pda(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    expected_address: &Pubkey,
    exact_bytes: usize,
) -> Result<FreshPdaPreparationV1, ProgramError> {
    if account.key != expected_address
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(RegistryProgramErrorV1::InvalidFreshAccount.into());
    }
    if account.owner == program_id {
        let data = account.try_borrow_data()?;
        if data.len() != exact_bytes || data.iter().any(|byte| *byte != 0) {
            return Err(RegistryProgramErrorV1::InvalidFreshAccount.into());
        }
        Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)
    } else if account.owner == &system_program::id() && account.data_is_empty() {
        Ok(FreshPdaPreparationV1::CreateOrAllocateSystemOwned)
    } else {
        Err(RegistryProgramErrorV1::InvalidFreshAccount.into())
    }
}
#[kani::proof]
#[kani::unwind(200)]
fn registry_fresh(){let program_id=any_key();let expected=any_key();let key=any_key();let account=account(&key);let size:usize=kani::any();let accepted=plan_fresh_program_pda(&account,&program_id,&expected,size).is_ok();if accepted{assert_eq!(key,expected);assert!(!account.executable&&!account.is_signer&&account.is_writable);assert!(account.owner==&program_id||(account.owner==&system_program::id()&&account.data_is_empty()));}}}
