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
 fn create_with_seed(base:&Pubkey,seed:&str,owner:&Pubkey)->Result<Self,ProgramError>{derive(query(&[base.as_ref(),seed.as_bytes()],owner)).ok_or(ProgramError::InvalidSeeds)}
 fn new_from_array(v:[u8;32])->Self{Self(v)}
 fn to_bytes(&self)->[u8;32]{self.0}
 fn find_program_address(s:&[&[u8]],p:&Self)->(Self,u8){let key=derive(query(s,p));kani::assume(key.is_some());let b:u8=kani::any();kani::assume(b>0);unsafe{CANON_BUMP=b;}(key.unwrap(),b)}
 fn create_program_address(s:&[&[u8]],p:&Self)->Result<Self,ProgramError>{derive(query(s,p)).ok_or(ProgramError::InvalidSeeds)}
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Query{program:Pubkey,bytes:[u8;192],ends:[usize;8],count:usize,len:usize}
fn query(seeds:&[&[u8]],p:&Pubkey)->Query {
 let mut q=Query{program:*p,bytes:[0;192],ends:[0;8],count:seeds.len(),len:0};
 for (i,s) in seeds.iter().enumerate(){for &b in *s{q.bytes[q.len]=b;q.len+=1;}q.ends[i]=q.len;}q
}
#[derive(Clone,Copy,Debug)]struct Memo{query:Query,answer:Option<Pubkey>}
static mut CANON_BUMP:u8=1;
static mut MEMO:Option<Memo>=None;
fn reset(){unsafe{MEMO=None;}}
fn memo()->Memo{unsafe{MEMO.expect("acceptance must call derivation")}}
fn derive(q:Query)->Option<Pubkey>{unsafe{if let Some(m)=MEMO{assert_eq!(m.query,q);m.answer}else{let answer:Option<Pubkey>=kani::any();MEMO=Some(Memo{query:q,answer});answer}}}
fn any_key()->Pubkey{kani::any()}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum ProgramError{InvalidSeeds,InvalidAccountData,InvalidInstructionData,IncorrectProgramId}
type PoolV1ProgramError=Errors;
type RegistryProgramErrorV1=Errors;
#[derive(Clone,Copy)]enum Errors{InvalidRootPageAddress,StateHistoryMismatch,InvalidVaultAuthority,InvalidVaultTokenAddress,InvalidNullifierMarkerAddress,InvalidFreshAccount,GenerationOverflow,InvalidNullifierMarkerAccount,InvalidProgramData,InvalidVerifierRegistry,VerifierSelectionMismatch}
impl From<Errors> for ProgramError{fn from(_:Errors)->Self{Self::InvalidAccountData}}
#[derive(Clone,Copy)]struct AccountInfo<'a>{key:&'a Pubkey,owner:&'a Pubkey,executable:bool,is_signer:bool,is_writable:bool,data:[u8;16],len:usize}
impl AccountInfo<'_>{fn data_is_empty(&self)->bool{self.len==0}fn try_borrow_data(&self)->Result<&[u8],ProgramError>{Ok(&self.data[..self.len])}}
static SYSTEM:Pubkey=Pubkey([0;32]);
static mut OWNER:Pubkey=Pubkey([0;32]);
mod system_program{use super::*;pub fn id()->Pubkey{SYSTEM}}
// Metadata, bytes and length are symbolic, with the memory validity invariant
// enforced by AccountInfo itself represented as len <= allocated buffer.
fn account(key:&Pubkey)->AccountInfo<'_>{let len:usize=kani::any();kani::assume(len<=16);AccountInfo{key,owner:unsafe{OWNER=any_key();&OWNER},executable:kani::any(),is_signer:kani::any(),is_writable:kani::any(),data:kani::any(),len}}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Identity{pool:[u8;32],asset_mint:[u8;32],token_program:[u8;32],asset_id:[u8;32],deployment_domain:[u8;32]}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Policy{registry_program:[u8;32],registry_authority:[u8;32],policy_binding:[u8;32]}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Master{identity:Identity,bump:u8,initialized_lane_mask:u8,verifier_policy:Policy,has_checkpoint:bool,next_checkpoint_sequence:u64,last_checkpoint_lane_sequences:[u64;8]}
type PoolV1PairForestMasterV1=Master;
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Checkpoint{master:[u8;32],bump:u8,checkpoint_sequence:u64,deployment_domain:[u8;32],global_root:[u32;8],lane_sequences:[u64;8]}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Lane{master:[u8;32],bump:u8,lane_id:u8,tree:IncrementalMerkleTreeV1}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Registry{generation:u64,bump:u8,programdata_bump:u8,pool:[u8;32],authority:[u8;32],policy_binding:[u8;32],registry_program:[u8;32],loader_program:[u8;32],programdata_address:[u8;32],verifier_program:[u8;32],profile_binding:[u8;32],release_binding:[u8;32],statement_version:u8,expected_upgrade_authority:[u8;32],immutable:bool,paused:bool,active:bool}
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

const POOL_V1_PAIR_FOREST_MASTER_SEED:&[u8]=b"aspis-pair-forest-master-v1";
const POOL_V1_PAIR_FOREST_LANE_SEED:&[u8]=b"aspis-pair-forest-lane-v1";
const POOL_V1_PAIR_FOREST_CHECKPOINT_SEED:&[u8]=b"aspis-pair-forest-checkpoint-v1";
const PAIR_FOREST_MASTER_SEED:&[u8]=POOL_V1_PAIR_FOREST_MASTER_SEED;
const PAIR_FOREST_LANE_SEED:&[u8]=POOL_V1_PAIR_FOREST_LANE_SEED;
const PAIR_FOREST_CHECKPOINT_SEED:&[u8]=POOL_V1_PAIR_FOREST_CHECKPOINT_SEED;

const VERIFIER_REGISTRY_SEED:&[u8]=b"aspis-verifier-registry-v1";
const VERIFIER_REGISTRY_V2_SEED:&[u8]=b"aspis-verifier-registry-v2";
const VERIFIER_ENTRY_SEED:&[u8]=b"aspis-verifier-entry-v1";
const VERIFIER_ENTRY_V2_SEED:&[u8]=b"aspis-verifier-entry-v2";
const POOL_V1_VAULT_AUTHORITY_SEED:&[u8]=b"aspis-pool-vault-authority-v1";
const POOL_V1_VAULT_TOKEN_ACCOUNT_SEED:&[u8]=b"aspis-pool-vault-token-v1";

type VerifierRegistryV1=Registry;type VerifierRegistryV2=Registry;
type PoolV1PairForestLaneStateV1=Lane;
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct IncrementalMerkleTreeV1{next_leaf_index:u64,root:[u32;8],frontier:[[u32;8];20]}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Afterstate{next_pair_index:u64,next_root:[u32;8],next_frontier:[[u32;8];20]}
const POOL_V1_VERIFIER_REGISTRY_SEED:&[u8]=VERIFIER_REGISTRY_SEED;
const POOL_V1_VERIFIER_REGISTRY_V2_SEED:&[u8]=VERIFIER_REGISTRY_V2_SEED;
const POOL_V1_VERIFIER_ENTRY_SEED:&[u8]=VERIFIER_ENTRY_SEED;
const POOL_V1_VERIFIER_ENTRY_V2_SEED:&[u8]=VERIFIER_ENTRY_V2_SEED;
const POOL_V1_PREPARED_SETTLEMENT_SEED:&[u8]=b"aspis-settle-plan-v1";
const POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED:&[u8]=b"aspis-settle-roll-v1";

type PoolIdentityV1=Identity;type PoolV1PairForestCheckpointV1=Checkpoint;
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct PoolInitializationV1{asset_mint:[u8;32],token_program:[u8;32],asset_id:[u8;32],deployment_domain:[u8;32],verifier_policy:Policy}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Deployment{programdata_address:[u8;32],programdata_bump:u8,executable_hash:[u8;32]}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]enum VerifierEntryStatusV1{Pending,Active,Retired}
const POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT:u64=u64::MAX;
const POOL_V1_PAIR_TREE_DEPTH:usize=20;
const POOL_V1_PAIR_EMPTY_ROOTS:[[u32;8];21]=[[0;8];21];
mod aspis_statement{pub mod pool_v1{pub const POOL_V1_PAIR_FOREST_ALL_LANES_MASK:u8=255;}}
mod bpf_loader_upgradeable{use super::*;pub fn id()->Pubkey{Pubkey([4;32])}}

type ProgramResult=Result<(),ProgramError>;

#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct Selection{profile_binding:[u8;32],release_binding:[u8;32],verifier_program:[u8;32],statement_version:u8}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct TerminalHints{current_page:u8,next_page:u8,vault_authority:u8,vault_token_account:u8}

#[derive(Clone,Copy,Debug)]enum PreparedSettlementFormatErrorV1{InvalidPda,WrongShard}
#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct PlanFields{program_id:[u8;32],pool:[u8;32],plan_authority:[u8;32],statement_digest:[u8;32],source_sequence:u64,pda_bump:u8}
#[derive(Clone,Copy)]struct PreparedAccount<'a>{owner:&'a Pubkey,address:&'a Pubkey}
const POOL_V1_PREPARED_SETTLEMENT_HEADER_BYTES:usize=16;

const PROFILE_BINDING: [u8; 32] = [
    0x78, 0x17, 0x1b, 0x56, 0x9e, 0xa7, 0xbc, 0xe5, 0x97, 0x63, 0xa2, 0xb5, 0x78, 0x81, 0x06, 0xa7,
    0x49, 0xbe, 0xd7, 0x47, 0x75, 0x6c, 0xf2, 0xd2, 0x00, 0x69, 0x99, 0x37, 0x92, 0x19, 0x13, 0xe9,
];
const RELEASE_BINDING: [u8; 32] = [
    0x45, 0x90, 0xcd, 0x06, 0x35, 0x37, 0xb3, 0xb0, 0x2f, 0xae, 0xb1, 0x0d, 0x9a, 0x7f, 0x39, 0x99,
    0x3f, 0xbe, 0x4b, 0xb6, 0x20, 0x30, 0x53, 0x32, 0x8d, 0x60, 0x0d, 0xbd, 0x48, 0x1c, 0xe0, 0x34,
];
const AUDIT_POLICY_BINDING: [u8; 32] = [7; 32];
const POOL_V1_ROOT_HISTORY_PAGE_SEED: &[u8] = b"aspis-pool-root-page-v1";
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

mod search_master {use super::*;
pub fn pool_v1_pair_forest_master_address(
    program_id: &Pubkey,
    asset_mint: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_PAIR_FOREST_MASTER_SEED, asset_mint.as_ref()],
        program_id,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_master(){reset();
let program_id=any_key();let mint=any_key();let (key,bump)=pool_v1_pair_forest_master_address(&program_id,&mint);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PAIR_FOREST_MASTER_SEED,mint.as_ref()],&program_id));
}
}

mod search_checkpoint {use super::*;
pub fn pool_v1_pair_forest_checkpoint_address(
    program_id: &Pubkey,
    master: &Pubkey,
    checkpoint_sequence: u64,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
            master.as_ref(),
            &checkpoint_sequence.to_le_bytes(),
        ],
        program_id,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_checkpoint(){reset();
let program_id=any_key();let pool=any_key();let sequence:u64=kani::any();let (key,bump)=pool_v1_pair_forest_checkpoint_address(&program_id,&pool,sequence);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,pool.as_ref(),&sequence.to_le_bytes()],&program_id));
}
}

mod search_vault_authority {use super::*;
pub fn pool_v1_vault_authority_address(program_id: &Pubkey, pool: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[POOL_V1_VAULT_AUTHORITY_SEED, pool.as_ref()], program_id)
}
#[kani::proof]
#[kani::unwind(200)]
fn search_vault_authority(){reset();
let program_id=any_key();let pool=any_key();let (key,bump)=pool_v1_vault_authority_address(&program_id,&pool);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_VAULT_AUTHORITY_SEED,pool.as_ref()],&program_id));
}
}

mod search_vault_token {use super::*;
pub fn pool_v1_vault_token_account_address(program_id: &Pubkey, pool: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_VAULT_TOKEN_ACCOUNT_SEED, pool.as_ref()],
        program_id,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_vault_token(){reset();
let program_id=any_key();let pool=any_key();let (key,bump)=pool_v1_vault_token_account_address(&program_id,&pool);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_VAULT_TOKEN_ACCOUNT_SEED,pool.as_ref()],&program_id));
}
}

mod search_page {use super::*;
pub fn pool_v1_root_page_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    page_number: u64,
) -> (Pubkey, u8) {
    let page_number_bytes = page_number.to_le_bytes();
    Pubkey::find_program_address(
        &[
            POOL_V1_ROOT_HISTORY_PAGE_SEED,
            pool.as_ref(),
            &page_number_bytes,
        ],
        program_id,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_page(){reset();
let program_id=any_key();let pool=any_key();let sequence:u64=kani::any();let (key,bump)=pool_v1_root_page_address(&program_id,&pool,sequence);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_ROOT_HISTORY_PAGE_SEED,pool.as_ref(),&sequence.to_le_bytes()],&program_id));
}
}

mod search_registry {use super::*;
pub fn pool_v1_verifier_registry_address(registry_program: &Pubkey, pool: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_VERIFIER_REGISTRY_SEED, pool.as_ref()],
        registry_program,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_registry(){reset();
let program_id=any_key();let pool=any_key();let (key,bump)=pool_v1_verifier_registry_address(&program_id,&pool);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_VERIFIER_REGISTRY_SEED,pool.as_ref()],&program_id));
}
}

mod search_entry {use super::*;
pub fn pool_v1_verifier_entry_address(
    registry_program: &Pubkey,
    pool: &Pubkey,
    profile_binding: &[u8; 32],
    release_binding: &[u8; 32],
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_VERIFIER_ENTRY_SEED,
            pool.as_ref(),
            profile_binding,
            release_binding,
        ],
        registry_program,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_entry(){reset();
let program_id=any_key();let pool=any_key();let profile:[u8;32]=kani::any();let release:[u8;32]=kani::any();let (key,bump)=pool_v1_verifier_entry_address(&program_id,&pool,&profile,&release);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_VERIFIER_ENTRY_SEED,pool.as_ref(),&profile,&release],&program_id));
}
}

mod search_registry_v2 {use super::*;
pub fn pool_v1_verifier_registry_v2_address(
    registry_program: &Pubkey,
    pool: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_VERIFIER_REGISTRY_V2_SEED, pool.as_ref()],
        registry_program,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_registry_v2(){reset();
let program_id=any_key();let pool=any_key();let (key,bump)=pool_v1_verifier_registry_v2_address(&program_id,&pool);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_VERIFIER_REGISTRY_V2_SEED,pool.as_ref()],&program_id));
}
}

mod search_entry_v2 {use super::*;
pub fn pool_v1_verifier_entry_v2_address(
    registry_program: &Pubkey,
    pool: &Pubkey,
    profile_binding: &[u8; 32],
    release_binding: &[u8; 32],
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_VERIFIER_ENTRY_V2_SEED,
            pool.as_ref(),
            profile_binding,
            release_binding,
        ],
        registry_program,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_entry_v2(){reset();
let program_id=any_key();let pool=any_key();let profile:[u8;32]=kani::any();let release:[u8;32]=kani::any();let (key,bump)=pool_v1_verifier_entry_v2_address(&program_id,&pool,&profile,&release);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_VERIFIER_ENTRY_V2_SEED,pool.as_ref(),&profile,&release],&program_id));
}
}

mod search_prepared_core {use super::*;
pub fn pool_v1_prepared_settlement_plan_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    statement_digest: &[u8; 32],
    source_sequence: u64,
    plan_authority: &Pubkey,
) -> (Pubkey, u8) {
    let source_sequence = source_sequence.to_le_bytes();
    Pubkey::find_program_address(
        &[
            POOL_V1_PREPARED_SETTLEMENT_SEED,
            pool.as_ref(),
            statement_digest,
            &source_sequence,
            plan_authority.as_ref(),
        ],
        program_id,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_prepared_core(){reset();
let program_id=any_key();let pool=any_key();let digest:[u8;32]=kani::any();let sequence:u64=kani::any();let authority=any_key();let (key,bump)=pool_v1_prepared_settlement_plan_address(&program_id,&pool,&digest,sequence,&authority);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PREPARED_SETTLEMENT_SEED,pool.as_ref(),&digest,&sequence.to_le_bytes(),authority.as_ref()],&program_id));
}
}

mod search_prepared_rollover {use super::*;
pub fn pool_v1_prepared_settlement_rollover_address(
    program_id: &Pubkey,
    core_plan_address: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED,
            core_plan_address.as_ref(),
        ],
        program_id,
    )
}
#[kani::proof]
#[kani::unwind(200)]
fn search_prepared_rollover(){reset();
let program_id=any_key();let pool=any_key();let (key,bump)=pool_v1_prepared_settlement_rollover_address(&program_id,&pool);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED,pool.as_ref()],&program_id));
}
}

mod search_lane {use super::*;
pub fn pool_v1_pair_forest_lane_address(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
) -> Result<(Pubkey, u8), ProgramError> {
    if usize::from(lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok(Pubkey::find_program_address(
        &[POOL_V1_PAIR_FOREST_LANE_SEED, master.as_ref(), &[lane_id]],
        program_id,
    ))
}
#[kani::proof]
#[kani::unwind(200)]
fn search_lane(){reset();
let program_id=any_key();let pool=any_key();let lane:u8=kani::any();let result=pool_v1_pair_forest_lane_address(&program_id,&pool,lane);if let Ok((key,bump))=result{assert!(lane<8);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PAIR_FOREST_LANE_SEED,pool.as_ref(),&[lane]],&program_id));}else{assert!(lane>=8);}
}
}

mod preserve_registry {use super::*;
fn incremented_registry(registry: VerifierRegistryV1) -> Result<VerifierRegistryV1, ProgramError> {
    let generation = registry
        .generation
        .checked_add(1)
        .ok_or(RegistryProgramErrorV1::GenerationOverflow)?;
    Ok(VerifierRegistryV1 {
        generation,
        ..registry
    })
}
#[kani::proof]
#[kani::unwind(200)]
fn preserve_registry(){reset();
let registry:Registry=kani::any();if let Ok(next)=incremented_registry(registry){assert_eq!(next.bump,registry.bump);assert_eq!(next.programdata_bump,registry.programdata_bump);assert_eq!(next.pool,registry.pool);assert_eq!(next.programdata_address,registry.programdata_address);}
}
}

mod preserve_registry_v2 {use super::*;
fn incremented_registry_v2(
    registry: VerifierRegistryV2,
) -> Result<VerifierRegistryV2, ProgramError> {
    let generation = registry
        .generation
        .checked_add(1)
        .ok_or(RegistryProgramErrorV1::GenerationOverflow)?;
    Ok(VerifierRegistryV2 {
        generation,
        ..registry
    })
}
#[kani::proof]
#[kani::unwind(200)]
fn preserve_registry_v2(){reset();
let registry:Registry=kani::any();if let Ok(next)=incremented_registry_v2(registry){assert_eq!(next.bump,registry.bump);assert_eq!(next.programdata_bump,registry.programdata_bump);assert_eq!(next.pool,registry.pool);assert_eq!(next.programdata_address,registry.programdata_address);}
}
}

mod preserve_master {use super::*;
fn check(master:&Master,next_sequence:u64,lane_sequences:[u64;8])->Master{let next_master = PoolV1PairForestMasterV1 {
        has_checkpoint: true,
        next_checkpoint_sequence: next_sequence,
        last_checkpoint_lane_sequences: lane_sequences,
        ..*master
    };
next_master}
#[kani::proof]
#[kani::unwind(200)]
fn preserve_master(){reset();
let master:Master=kani::any();let next=check(&master,kani::any(),kani::any());assert_eq!(next.bump,master.bump);assert_eq!(next.identity.pool,master.identity.pool);assert_eq!(next.identity.asset_mint,master.identity.asset_mint);
}
}

mod preserve_lane {use super::*;
fn check(lane:&Lane,afterstate:Afterstate)->Result<Lane,ProgramError>{Ok(PoolV1PairForestLaneStateV1 {
        master: lane.master,
        bump: lane.bump,
        lane_id: lane.lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: afterstate.next_pair_index,
            root: afterstate.next_root,
            frontier: afterstate.next_frontier,
        },
    })}
#[kani::proof]
#[kani::unwind(200)]
fn preserve_lane(){reset();
let lane:Lane=kani::any();let next=check(&lane,kani::any()).unwrap();assert_eq!(next.bump,lane.bump);assert_eq!(next.master,lane.master);assert_eq!(next.lane_id,lane.lane_id);
}
}

mod initialize_master {use super::*;
pub fn pool_v1_pair_forest_master_address(
    program_id: &Pubkey,
    asset_mint: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_PAIR_FOREST_MASTER_SEED, asset_mint.as_ref()],
        program_id,
    )
}
fn image(expected_master:&Pubkey,initialization:&PoolInitializationV1,master_bump:u8)->u8{let master_state = Box::new(PoolV1PairForestMasterV1 {
        bump: master_bump,
        identity: PoolIdentityV1 {
            pool: expected_master.to_bytes(),
            asset_mint: initialization.asset_mint,
            token_program: initialization.token_program,
            asset_id: initialization.asset_id,
            deployment_domain: initialization.deployment_domain,
        },
        verifier_policy: initialization.verifier_policy,
        initialized_lane_mask: aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        has_checkpoint: false,
        next_checkpoint_sequence: 0,
        last_checkpoint_lane_sequences: [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
    });let master=&*master_state;let mut output=[0u8;8];output[7] = master.bump;output[7]}
#[kani::proof]
#[kani::unwind(200)]
fn initialize_master(){reset();
let program_id=any_key();let init:PoolInitializationV1=kani::any();let (key,bump)=pool_v1_pair_forest_master_address(&program_id,&Pubkey::new_from_array(init.asset_mint));let stored=image(&key,&init,bump);assert_eq!(stored,unsafe{CANON_BUMP});
}
}

mod initialize_lane {use super::*;
fn genesis_lane_state(master: &Pubkey, lane_id: u8, bump: u8) -> PoolV1PairForestLaneStateV1 {
    PoolV1PairForestLaneStateV1 {
        bump,
        master: master.to_bytes(),
        lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
            frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
        },
    }
}
pub fn pool_v1_pair_forest_lane_address(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
) -> Result<(Pubkey, u8), ProgramError> {
    if usize::from(lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok(Pubkey::find_program_address(
        &[POOL_V1_PAIR_FOREST_LANE_SEED, master.as_ref(), &[lane_id]],
        program_id,
    ))
}
#[kani::proof]
#[kani::unwind(200)]
fn initialize_lane(){reset();
let program_id=any_key();let master=any_key();let lane_id:u8=kani::any();if let Ok((key,bump))=pool_v1_pair_forest_lane_address(&program_id,&master,lane_id){let lane=genesis_lane_state(&master,lane_id,bump);let mut output=[0u8;73];output[72] = lane.bump;assert_eq!(output[72],unsafe{CANON_BUMP});assert_eq!(lane.master,master.to_bytes());assert_eq!(lane.lane_id,lane_id);}
}
}

mod initialize_checkpoint {use super::*;
pub fn pool_v1_pair_forest_checkpoint_address(
    program_id: &Pubkey,
    master: &Pubkey,
    checkpoint_sequence: u64,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
            master.as_ref(),
            &checkpoint_sequence.to_le_bytes(),
        ],
        program_id,
    )
}
fn image(master:&Master,global_root:[u32;8],lane_sequences:[u64;8],checkpoint_bump:u8)->u8{let checkpoint = PoolV1PairForestCheckpointV1 {
        bump: checkpoint_bump,
        master: master.identity.pool,
        deployment_domain: master.identity.deployment_domain,
        checkpoint_sequence: master.next_checkpoint_sequence,
        global_root,
        lane_sequences,
    };let mut output=[0u8;8];output[7] = checkpoint.bump;output[7]}
#[kani::proof]
#[kani::unwind(200)]
fn initialize_checkpoint(){reset();
let program_id=any_key();let master:Master=kani::any();let (key,bump)=pool_v1_pair_forest_checkpoint_address(&program_id,&Pubkey::new_from_array(master.identity.pool),master.next_checkpoint_sequence);let stored=image(&master,kani::any(),kani::any(),bump);assert_eq!(stored,unsafe{CANON_BUMP});
}
}

mod initialize_registry {use super::*;
pub struct VerifierRegistryV1 {
    pub flags: u8,
    /// Canonical registry PDA bump established by initialization.
    pub bump: u8,
    pub pool: [u8; 32],
    pub authority: [u8; 32],
    pub policy_binding: [u8; 32],
    pub generation: u64,
    pub minimum_activation_delay_slots: u64,
}
pub fn pool_v1_verifier_registry_address(registry_program: &Pubkey, pool: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_VERIFIER_REGISTRY_SEED, pool.as_ref()],
        registry_program,
    )
}

#[kani::proof]
#[kani::unwind(200)]
fn initialize_registry(){reset();
let program_id=any_key();let pool:[u8;32]=kani::any();let pool_key=Pubkey::new_from_array(pool);let profile_binding:[u8;32]=kani::any();let release_binding:[u8;32]=kani::any();let verifier_program:[u8;32]=kani::any();let policy_binding:[u8;32]=kani::any();let minimum_activation_delay_slots:u64=kani::any();let statement_version:u8=kani::any();let activation_slot:u64=kani::any();let authority_key=any_key();let authority=account(&authority_key);let registry:Registry=kani::any();let deployment:Deployment=kani::any();let (expected_address,bump)=pool_v1_verifier_registry_address(&program_id,&pool_key);let program_id=&program_id;let registry = VerifierRegistryV1 {
        flags: 0,
        bump,
        pool,
        authority: authority.key.to_bytes(),
        policy_binding,
        generation: 0,
        minimum_activation_delay_slots,
    };let mut output=[0u8;320];output[6] = registry.bump;assert_eq!(output[6],unsafe{CANON_BUMP});
}
}

mod initialize_entry {use super::*;
pub struct VerifierRegistryEntryV1 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    /// Canonical entry PDA bump established by scheduling.
    pub bump: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}
pub fn pool_v1_verifier_entry_address(
    registry_program: &Pubkey,
    pool: &Pubkey,
    profile_binding: &[u8; 32],
    release_binding: &[u8; 32],
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_VERIFIER_ENTRY_SEED,
            pool.as_ref(),
            profile_binding,
            release_binding,
        ],
        registry_program,
    )
}

#[kani::proof]
#[kani::unwind(200)]
fn initialize_entry(){reset();
let program_id=any_key();let pool:[u8;32]=kani::any();let pool_key=Pubkey::new_from_array(pool);let profile_binding:[u8;32]=kani::any();let release_binding:[u8;32]=kani::any();let verifier_program:[u8;32]=kani::any();let policy_binding:[u8;32]=kani::any();let minimum_activation_delay_slots:u64=kani::any();let statement_version:u8=kani::any();let activation_slot:u64=kani::any();let authority_key=any_key();let authority=account(&authority_key);let registry:Registry=kani::any();let deployment:Deployment=kani::any();let (expected_address,bump)=pool_v1_verifier_entry_address(&program_id,&pool_key,&profile_binding,&release_binding);let program_id=&program_id;let entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Pending,
        statement_version,
        bump,
        pool: registry.pool,
        verifier_program,
        profile_binding,
        release_binding,
        activation_slot,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: registry.policy_binding,
    };let mut output=[0u8;320];output[7] = entry.bump;assert_eq!(output[7],unsafe{CANON_BUMP});
}
}

mod initialize_registry_v2 {use super::*;
pub struct VerifierRegistryV2 {
    pub flags: u8,
    /// Canonical registry PDA bump established by initialization.
    pub bump: u8,
    pub pool: [u8; 32],
    pub authority: [u8; 32],
    pub policy_binding: [u8; 32],
    pub generation: u64,
    pub minimum_activation_delay_slots: u64,
    pub registry_program: [u8; 32],
    pub loader_program: [u8; 32],
    pub programdata_address: [u8; 32],
    /// Canonical loader-v3 ProgramData bump established by deployment authentication.
    pub programdata_bump: u8,
    pub executable_hash: [u8; 32],
}
pub fn pool_v1_verifier_registry_v2_address(
    registry_program: &Pubkey,
    pool: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_VERIFIER_REGISTRY_V2_SEED, pool.as_ref()],
        registry_program,
    )
}

#[kani::proof]
#[kani::unwind(200)]
fn initialize_registry_v2(){reset();
let program_id=any_key();let pool:[u8;32]=kani::any();let pool_key=Pubkey::new_from_array(pool);let profile_binding:[u8;32]=kani::any();let release_binding:[u8;32]=kani::any();let verifier_program:[u8;32]=kani::any();let policy_binding:[u8;32]=kani::any();let minimum_activation_delay_slots:u64=kani::any();let statement_version:u8=kani::any();let activation_slot:u64=kani::any();let authority_key=any_key();let authority=account(&authority_key);let registry:Registry=kani::any();let deployment:Deployment=kani::any();let (expected_address,bump)=pool_v1_verifier_registry_v2_address(&program_id,&pool_key);let program_id=&program_id;let registry = VerifierRegistryV2 {
        flags: 0,
        bump,
        pool,
        authority: authority.key.to_bytes(),
        policy_binding,
        generation: 0,
        minimum_activation_delay_slots,
        registry_program: program_id.to_bytes(),
        loader_program: bpf_loader_upgradeable::id().to_bytes(),
        programdata_address: deployment.programdata_address,
        programdata_bump: deployment.programdata_bump,
        executable_hash: deployment.executable_hash,
    };let mut output=[0u8;320];output[7] = registry.bump;output[248] = registry.programdata_bump;assert_eq!(output[7],unsafe{CANON_BUMP});assert_eq!(output[248],deployment.programdata_bump);
}
}

mod initialize_entry_v2 {use super::*;
pub struct VerifierRegistryEntryV2 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    /// Canonical entry PDA bump established by scheduling.
    pub bump: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub loader_program: [u8; 32],
    pub programdata_address: [u8; 32],
    /// Canonical loader-v3 ProgramData bump established by deployment authentication.
    pub programdata_bump: u8,
    pub executable_hash: [u8; 32],
    /// Production V2 requires this to be all zero, denoting `None`.
    pub expected_upgrade_authority: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}
pub fn pool_v1_verifier_entry_v2_address(
    registry_program: &Pubkey,
    pool: &Pubkey,
    profile_binding: &[u8; 32],
    release_binding: &[u8; 32],
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_VERIFIER_ENTRY_V2_SEED,
            pool.as_ref(),
            profile_binding,
            release_binding,
        ],
        registry_program,
    )
}

#[kani::proof]
#[kani::unwind(200)]
fn initialize_entry_v2(){reset();
let program_id=any_key();let pool:[u8;32]=kani::any();let pool_key=Pubkey::new_from_array(pool);let profile_binding:[u8;32]=kani::any();let release_binding:[u8;32]=kani::any();let verifier_program:[u8;32]=kani::any();let policy_binding:[u8;32]=kani::any();let minimum_activation_delay_slots:u64=kani::any();let statement_version:u8=kani::any();let activation_slot:u64=kani::any();let authority_key=any_key();let authority=account(&authority_key);let registry:Registry=kani::any();let deployment:Deployment=kani::any();let (expected_address,bump)=pool_v1_verifier_entry_v2_address(&program_id,&pool_key,&profile_binding,&release_binding);let program_id=&program_id;let entry = VerifierRegistryEntryV2 {
        status: VerifierEntryStatusV1::Pending,
        statement_version,
        bump,
        pool: registry.pool,
        verifier_program,
        profile_binding,
        release_binding,
        loader_program: bpf_loader_upgradeable::id().to_bytes(),
        programdata_address: deployment.programdata_address,
        programdata_bump: deployment.programdata_bump,
        executable_hash: deployment.executable_hash,
        expected_upgrade_authority: [0u8; 32],
        activation_slot,
        retirement_slot: POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT,
        policy_binding: registry.policy_binding,
    };let mut output=[0u8;320];output[312] = entry.bump;output[313] = entry.programdata_bump;assert_eq!(output[312],unsafe{CANON_BUMP});assert_eq!(output[313],deployment.programdata_bump);
}
}

mod pool_owner_guard {use super::*;
pub(crate) fn require_program_account(
    account: &AccountInfo,
    program_id: &Pubkey,
    writable: bool,
) -> Result<(), ProgramError> {
    if account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if account.executable || account.is_writable != writable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
#[kani::proof]
#[kani::unwind(200)]
fn pool_owner_guard(){reset();
let program_id=any_key();let key=any_key();let account=account(&key);let writable:bool=kani::any();if require_program_account(&account,&program_id,writable).is_ok(){assert_eq!(*account.owner,program_id);assert!(!account.executable);assert_eq!(account.is_writable,writable);}
}
}

mod verifier_owner_guard {use super::*;
fn readonly_meta_ok(
    owner: &Pubkey,
    expected: &Pubkey,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
) -> ProgramResult {
    if owner != expected || is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_readonly_account(account: &AccountInfo<'_>, owner: &Pubkey) -> ProgramResult {
    readonly_meta_ok(account.owner, owner, account.is_signer, account.is_writable, account.executable)
}
#[kani::proof]
#[kani::unwind(200)]
fn verifier_owner_guard(){reset();
let program_id=any_key();let key=any_key();let account=account(&key);if require_readonly_account(&account,&program_id).is_ok(){assert_eq!(*account.owner,program_id);assert!(!account.executable&&!account.is_signer&&!account.is_writable);}
}
}

mod marker_create_with_seed {use super::*;
fn decode_digest_canonical(_: &[u8;32])->Result<(),ProgramError>{if kani::any(){Ok(())}else{Err(ProgramError::InvalidAccountData)}}
fn pool_v1_pair_forest_marker_seed_v1(_:&Pubkey,_:&[u8;32])->[u8;32]{let mut s:[u8;32]=kani::any();for x in &mut s{*x &=127;}s}
pub fn pool_v1_pair_forest_marker_seed_str_v1(seed: &[u8; 32]) -> Result<&str, ProgramError> {
    core::str::from_utf8(seed).map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAddress.into())
}
pub fn pool_v1_pair_forest_nullifier_marker_address(
    program_id: &Pubkey,
    master: &Pubkey,
    canonical_nullifier_encoding: &[u8; 32],
) -> Result<(Pubkey, [u8; 32]), ProgramError> {
    decode_digest_canonical(canonical_nullifier_encoding)
        .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAccount)?;
    let seed = pool_v1_pair_forest_marker_seed_v1(master, canonical_nullifier_encoding);
    let address = Pubkey::create_with_seed(
        master,
        pool_v1_pair_forest_marker_seed_str_v1(&seed)?,
        program_id,
    )
    .map_err(|_| PoolV1ProgramError::InvalidNullifierMarkerAddress)?;
    Ok((address, seed))
}
#[kani::proof]
#[kani::unwind(34)]
fn marker_create_with_seed(){reset();
let program_id=any_key();let master=any_key();let n:[u8;32]=kani::any();if let Ok((key,seed))=pool_v1_pair_forest_nullifier_marker_address(&program_id,&master,&n){assert_eq!(memo().answer,Some(key));assert_eq!(memo().query,query(&[master.as_ref(),&seed],&program_id));}
}
}

mod initialize_programdata {use super::*;
fn check(expected_program:&Pubkey,loader:Pubkey,linked_programdata:[u8;32],programdata_account:&AccountInfo)->Result<u8,ProgramError>{let (derived_programdata, programdata_bump) =
        Pubkey::find_program_address(&[expected_program.as_ref()], &loader);
    if linked_programdata != programdata_account.key.to_bytes()
        || linked_programdata != derived_programdata.to_bytes()
    {
        return Err(RegistryProgramErrorV1::InvalidProgramData.into());
    }
Ok(programdata_bump)}
#[kani::proof]
#[kani::unwind(200)]
fn initialize_programdata(){reset();
let program=any_key();let loader=any_key();let linked:[u8;32]=kani::any();let key=any_key();let account=account(&key);if let Ok(bump)=check(&program,loader,linked,&account){assert_eq!(linked,key.to_bytes());assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[program.as_ref()],&loader));}
}
}

mod pool_registry_v2_call {use super::*;
use crate::registry::stored_bump_address_matches;
#[kani::proof]
#[kani::unwind(200)]
fn pool_registry_v2_call(){reset();
let pp=any_key();let pool=&pp;let registry_program=any_key();let rk=any_key();let ek=any_key();let ra=account(&rk);let ea=account(&ek);let registry_account=&ra;let entry_account=&ea;let registry:Registry=kani::any();let entry:Registry=kani::any();let selection:Selection=kani::any();let accepted=stored_bump_address_matches(
            &[
                POOL_V1_VERIFIER_REGISTRY_V2_SEED,
                pool.as_ref(),
                &[registry.bump],
            ],
            &registry_program,
            registry_account.key,
        );if accepted{assert_eq!(memo().answer,Some(*registry_account.key));assert_eq!(memo().query,query(&[POOL_V1_VERIFIER_REGISTRY_V2_SEED,pool.as_ref(),&[registry.bump]],&registry_program));}
}
}

mod pool_entry_v2_call {use super::*;
use crate::registry::stored_bump_address_matches;
#[kani::proof]
#[kani::unwind(200)]
fn pool_entry_v2_call(){reset();
let pp=any_key();let pool=&pp;let registry_program=any_key();let rk=any_key();let ek=any_key();let ra=account(&rk);let ea=account(&ek);let registry_account=&ra;let entry_account=&ea;let registry:Registry=kani::any();let entry:Registry=kani::any();let selection:Selection=kani::any();let accepted=stored_bump_address_matches(
            &[
                POOL_V1_VERIFIER_ENTRY_V2_SEED,
                pool.as_ref(),
                &selection.profile_binding,
                &selection.release_binding,
                &[entry.bump],
            ],
            &registry_program,
            entry_account.key,
        );if accepted{assert_eq!(memo().answer,Some(*entry_account.key));assert_eq!(memo().query,query(&[POOL_V1_VERIFIER_ENTRY_V2_SEED,pool.as_ref(),&selection.profile_binding,&selection.release_binding,&[entry.bump]],&registry_program));}
}
}

mod pool_registry_programdata {use super::*;
fn check(pool:Pubkey,registry_program:Pubkey,selected_program:Pubkey,loader:Pubkey,registry:Registry,entry:Registry,selection:Selection,policy:Policy,registry_address_matches:bool)->ProgramResult{let expected_registry_programdata = Pubkey::create_program_address(
        &[registry_program.as_ref(), &[registry.programdata_bump]],
        &loader,
    )
    .map_err(|_| PoolV1ProgramError::InvalidVerifierRegistry)?;
    if !registry_address_matches
        || registry.pool != pool.to_bytes()
        || registry.authority != policy.registry_authority
        || registry.policy_binding != policy.policy_binding
        || !registry.is_immutable()
        || registry.registry_program != policy.registry_program
        || registry.loader_program != loader.to_bytes()
        || registry.programdata_address != expected_registry_programdata.to_bytes()
    {
        return Err(PoolV1ProgramError::InvalidVerifierRegistry.into());
    }
Ok(())}
#[kani::proof]
#[kani::unwind(200)]
fn pool_registry_programdata(){reset();
let pool=any_key();let registry_program=any_key();let selected_program=any_key();let loader=any_key();let registry:Registry=kani::any();let entry:Registry=kani::any();let selection:Selection=kani::any();let policy:Policy=kani::any();let registry_address_matches:bool=kani::any();if check(pool,registry_program,selected_program,loader,registry,entry,selection,policy,registry_address_matches).is_ok(){assert_eq!(memo().answer,Some(Pubkey::new_from_array(registry.programdata_address)));assert_eq!(memo().query,query(&[registry_program.as_ref(),&[registry.programdata_bump]],&loader));}
}
}

mod pool_entry_programdata {use super::*;
fn check(pool:Pubkey,registry_program:Pubkey,selected_program:Pubkey,loader:Pubkey,registry:Registry,entry:Registry,selection:Selection,policy:Policy,registry_address_matches:bool)->ProgramResult{let expected_verifier_programdata = Pubkey::create_program_address(
        &[selected_program.as_ref(), &[entry.programdata_bump]],
        &loader,
    )
    .map_err(|_| PoolV1ProgramError::VerifierSelectionMismatch)?;
    if entry.pool != pool.to_bytes()
        || entry.policy_binding != policy.policy_binding
        || entry.verifier_program != selection.verifier_program
        || entry.profile_binding != selection.profile_binding
        || entry.release_binding != selection.release_binding
        || entry.statement_version != selection.statement_version
        || entry.loader_program != loader.to_bytes()
        || entry.programdata_address != expected_verifier_programdata.to_bytes()
        || entry.expected_upgrade_authority != [0u8; 32]
    {
        return Err(PoolV1ProgramError::VerifierSelectionMismatch.into());
    }
Ok(())}
#[kani::proof]
#[kani::unwind(200)]
fn pool_entry_programdata(){reset();
let pool=any_key();let registry_program=any_key();let selected_program=any_key();let loader=any_key();let registry:Registry=kani::any();let entry:Registry=kani::any();let selection:Selection=kani::any();let policy:Policy=kani::any();let registry_address_matches:bool=kani::any();if check(pool,registry_program,selected_program,loader,registry,entry,selection,policy,registry_address_matches).is_ok(){assert_eq!(memo().answer,Some(Pubkey::new_from_array(entry.programdata_address)));assert_eq!(memo().query,query(&[selected_program.as_ref(),&[entry.programdata_bump]],&loader));}
}
}

mod preserve_entry_activate {use super::*;
#[derive(Clone,Copy,kani::Arbitrary)]
pub struct VerifierRegistryEntryV1 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    /// Canonical entry PDA bump established by scheduling.
    pub bump: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}
#[kani::proof]
#[kani::unwind(200)]
fn preserve_entry_activate(){reset();
let entry:VerifierRegistryEntryV1=kani::any();let current_slot:u64=kani::any();let next_entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Active,
        ..entry
    };assert_eq!(next_entry.bump,entry.bump);assert_eq!(next_entry.pool,entry.pool);assert_eq!(next_entry.profile_binding,entry.profile_binding);assert_eq!(next_entry.release_binding,entry.release_binding);
}
}

mod preserve_entry_retire {use super::*;
#[derive(Clone,Copy,kani::Arbitrary)]
pub struct VerifierRegistryEntryV1 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    /// Canonical entry PDA bump established by scheduling.
    pub bump: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}
#[kani::proof]
#[kani::unwind(200)]
fn preserve_entry_retire(){reset();
let retiring:VerifierRegistryEntryV1=kani::any();let current_slot:u64=kani::any();let next_entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::Retired,
        retirement_slot: current_slot,
        ..retiring
    };assert_eq!(next_entry.bump,retiring.bump);assert_eq!(next_entry.pool,retiring.pool);assert_eq!(next_entry.profile_binding,retiring.profile_binding);assert_eq!(next_entry.release_binding,retiring.release_binding);
}
}

mod preserve_entry_activate_v2 {use super::*;
#[derive(Clone,Copy,kani::Arbitrary)]
pub struct VerifierRegistryEntryV2 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    /// Canonical entry PDA bump established by scheduling.
    pub bump: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub loader_program: [u8; 32],
    pub programdata_address: [u8; 32],
    /// Canonical loader-v3 ProgramData bump established by deployment authentication.
    pub programdata_bump: u8,
    pub executable_hash: [u8; 32],
    /// Production V2 requires this to be all zero, denoting `None`.
    pub expected_upgrade_authority: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}
#[kani::proof]
#[kani::unwind(200)]
fn preserve_entry_activate_v2(){reset();
let entry:VerifierRegistryEntryV2=kani::any();let current_slot:u64=kani::any();let next_entry = VerifierRegistryEntryV2 {
        status: VerifierEntryStatusV1::Active,
        ..entry
    };assert_eq!(next_entry.bump,entry.bump);assert_eq!(next_entry.pool,entry.pool);assert_eq!(next_entry.profile_binding,entry.profile_binding);assert_eq!(next_entry.release_binding,entry.release_binding);assert_eq!(next_entry.programdata_bump,entry.programdata_bump);assert_eq!(next_entry.programdata_address,entry.programdata_address);
}
}

mod preserve_entry_retire_v2 {use super::*;
#[derive(Clone,Copy,kani::Arbitrary)]
pub struct VerifierRegistryEntryV2 {
    pub status: VerifierEntryStatusV1,
    pub statement_version: u8,
    /// Canonical entry PDA bump established by scheduling.
    pub bump: u8,
    pub pool: [u8; 32],
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub loader_program: [u8; 32],
    pub programdata_address: [u8; 32],
    /// Canonical loader-v3 ProgramData bump established by deployment authentication.
    pub programdata_bump: u8,
    pub executable_hash: [u8; 32],
    /// Production V2 requires this to be all zero, denoting `None`.
    pub expected_upgrade_authority: [u8; 32],
    pub activation_slot: u64,
    pub retirement_slot: u64,
    pub policy_binding: [u8; 32],
}
#[kani::proof]
#[kani::unwind(200)]
fn preserve_entry_retire_v2(){reset();
let retiring:VerifierRegistryEntryV2=kani::any();let current_slot:u64=kani::any();let next_entry = VerifierRegistryEntryV2 {
        status: VerifierEntryStatusV1::Retired,
        retirement_slot: current_slot,
        ..retiring
    };assert_eq!(next_entry.bump,retiring.bump);assert_eq!(next_entry.pool,retiring.pool);assert_eq!(next_entry.profile_binding,retiring.profile_binding);assert_eq!(next_entry.release_binding,retiring.release_binding);assert_eq!(next_entry.programdata_bump,retiring.programdata_bump);assert_eq!(next_entry.programdata_address,retiring.programdata_address);
}
}

mod unused_next_hint {use super::*;
fn check(cursor:usize,withdrawal:bool,hints:TerminalHints)->ProgramResult{if cursor == 4 && hints.next_page != 0 {
        // Canonical encoding: an unused hint byte is zero.
        return Err(ProgramError::InvalidInstructionData);
    }
Ok(())}
#[kani::proof]
#[kani::unwind(200)]
fn unused_next_hint(){reset();
let cursor:usize=kani::any();let withdrawal:bool=kani::any();let hints:TerminalHints=kani::any();let accepted=check(cursor,withdrawal,hints).is_ok();if accepted&&cursor==4{assert_eq!(hints.next_page,0);}
}
}

mod unused_vault_hints {use super::*;
fn check(cursor:usize,withdrawal:bool,hints:TerminalHints)->ProgramResult{if !withdrawal && (hints.vault_authority != 0 || hints.vault_token_account != 0) {
        // Canonical encoding: a transfer carries no custody hints.
        return Err(ProgramError::InvalidInstructionData);
    }
Ok(())}
#[kani::proof]
#[kani::unwind(200)]
fn unused_vault_hints(){reset();
let cursor:usize=kani::any();let withdrawal:bool=kani::any();let hints:TerminalHints=kani::any();let accepted=check(cursor,withdrawal,hints).is_ok();if accepted&&!withdrawal{assert_eq!(hints.vault_authority,0);assert_eq!(hints.vault_token_account,0);}
}
}

mod prepared_core_decode {use super::*;
pub fn pool_v1_prepared_settlement_plan_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    statement_digest: &[u8; 32],
    source_sequence: u64,
    plan_authority: &Pubkey,
) -> (Pubkey, u8) {
    let source_sequence = source_sequence.to_le_bytes();
    Pubkey::find_program_address(
        &[
            POOL_V1_PREPARED_SETTLEMENT_SEED,
            pool.as_ref(),
            statement_digest,
            &source_sequence,
            plan_authority.as_ref(),
        ],
        program_id,
    )
}
fn check(program_id:[u8;32],pool:[u8;32],plan_authority:[u8;32],statement_digest:[u8;32],source_sequence:u64,core_address:&Pubkey,bytes:&[u8;10])->Result<(),PreparedSettlementFormatErrorV1>{let (expected_core_address, expected_core_bump) = pool_v1_prepared_settlement_plan_address(
        &Pubkey::new_from_array(program_id),
        &Pubkey::new_from_array(pool),
        &statement_digest,
        source_sequence,
        &Pubkey::new_from_array(plan_authority),
    );
    if *core_address != expected_core_address || bytes[9] != expected_core_bump {
        return Err(PreparedSettlementFormatErrorV1::InvalidPda);
    }
Ok(())}
#[kani::proof]
#[kani::unwind(200)]
fn prepared_core_decode(){reset();
let program_id:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let authority:[u8;32]=kani::any();let digest:[u8;32]=kani::any();let seq:u64=kani::any();let key=any_key();let bytes:[u8;10]=kani::any();if check(program_id,pool,authority,digest,seq,&key,&bytes).is_ok(){assert_eq!(memo().answer,Some(key));assert_eq!(bytes[9],unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PREPARED_SETTLEMENT_SEED,&pool,&digest,&seq.to_le_bytes(),&authority],&Pubkey(program_id)));}
}
}

mod prepared_core_initialize {use super::*;
pub fn pool_v1_prepared_settlement_plan_address(
    program_id: &Pubkey,
    pool: &Pubkey,
    statement_digest: &[u8; 32],
    source_sequence: u64,
    plan_authority: &Pubkey,
) -> (Pubkey, u8) {
    let source_sequence = source_sequence.to_le_bytes();
    Pubkey::find_program_address(
        &[
            POOL_V1_PREPARED_SETTLEMENT_SEED,
            pool.as_ref(),
            statement_digest,
            &source_sequence,
            plan_authority.as_ref(),
        ],
        program_id,
    )
}
fn image(fields:PlanFields)->Result<u8,PreparedSettlementFormatErrorV1>{let program_id = Pubkey::new_from_array(fields.program_id);
    let pool = Pubkey::new_from_array(fields.pool);
    let plan_authority = Pubkey::new_from_array(fields.plan_authority);
    let (core_address, core_bump) = pool_v1_prepared_settlement_plan_address(
        &program_id,
        &pool,
        &fields.statement_digest,
        fields.source_sequence,
        &plan_authority,
    );
    if fields.pda_bump != core_bump {
        return Err(PreparedSettlementFormatErrorV1::InvalidPda);
    }
let mut output=[0u8;10];output[9] = fields.pda_bump;Ok(output[9])}
#[kani::proof]
#[kani::unwind(200)]
fn prepared_core_initialize(){reset();
let fields:PlanFields=kani::any();if let Ok(bump)=image(fields){assert_eq!(bump,unsafe{CANON_BUMP});}
}
}

mod prepared_shard_decode {use super::*;
pub fn pool_v1_prepared_settlement_rollover_address(
    program_id: &Pubkey,
    core_plan_address: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED,
            core_plan_address.as_ref(),
        ],
        program_id,
    )
}
const SHARD_CORE_ADDRESS_OFFSET: usize = POOL_V1_PREPARED_SETTLEMENT_HEADER_BYTES;
const SHARD_PROGRAM_OFFSET: usize = SHARD_CORE_ADDRESS_OFFSET + 32;
const SHARD_POOL_OFFSET: usize = SHARD_PROGRAM_OFFSET + 32;
const SHARD_STATEMENT_DIGEST_OFFSET: usize = SHARD_POOL_OFFSET + 32;
const SHARD_SOURCE_SEQUENCE_OFFSET: usize = SHARD_STATEMENT_DIGEST_OFFSET + 32;
const SHARD_PLAN_AUTHORITY_OFFSET: usize = SHARD_SOURCE_SEQUENCE_OFFSET + 8;
const SHARD_NEXT_PAGE_ADDRESS_OFFSET: usize = SHARD_PLAN_AUTHORITY_OFFSET + 32;
const SHARD_NEXT_PAGE_IMAGE_OFFSET: usize = SHARD_NEXT_PAGE_ADDRESS_OFFSET + 32;

#[inline(never)]
fn check(expected_program:[u8;32],core_address:&Pubkey,account:PreparedAccount,bytes:&[u8;248],expected_shard_address:[u8;32],expected_pool:[u8;32],expected_statement_digest:[u8;32],expected_source_sequence:u64,expected_plan_authority:[u8;32],expected_next_page_address:[u8;32])->Result<(),PreparedSettlementFormatErrorV1>{let program_id = Pubkey::new_from_array(expected_program);
    let (expected_address, expected_bump) =
        pool_v1_prepared_settlement_rollover_address(&program_id, core_address);
    if account.owner != &program_id
        || account.address != &expected_address
        || account.address.to_bytes() != expected_shard_address
        || bytes[6] != expected_bump
        || bytes[SHARD_CORE_ADDRESS_OFFSET..SHARD_PROGRAM_OFFSET] != core_address.to_bytes()
        || bytes[SHARD_PROGRAM_OFFSET..SHARD_POOL_OFFSET] != expected_program
        || bytes[SHARD_POOL_OFFSET..SHARD_STATEMENT_DIGEST_OFFSET] != expected_pool
        || bytes[SHARD_STATEMENT_DIGEST_OFFSET..SHARD_SOURCE_SEQUENCE_OFFSET]
            != expected_statement_digest
        || bytes[SHARD_SOURCE_SEQUENCE_OFFSET..SHARD_PLAN_AUTHORITY_OFFSET]
            != expected_source_sequence.to_le_bytes()
        || bytes[SHARD_PLAN_AUTHORITY_OFFSET..SHARD_NEXT_PAGE_ADDRESS_OFFSET]
            != expected_plan_authority
        || bytes[SHARD_NEXT_PAGE_ADDRESS_OFFSET..SHARD_NEXT_PAGE_IMAGE_OFFSET]
            != expected_next_page_address
    {
        return Err(PreparedSettlementFormatErrorV1::WrongShard);
    }
Ok(())}
#[kani::proof]
#[kani::unwind(200)]
fn prepared_shard_decode(){reset();
let shard_addr:[u8;32]=kani::any();let expected_pool:[u8;32]=kani::any();let digest:[u8;32]=kani::any();let seq:u64=kani::any();let authority:[u8;32]=kani::any();let next_page:[u8;32]=kani::any();let program:[u8;32]=kani::any();let core=any_key();let key=any_key();let owner=any_key();let account=PreparedAccount{owner:&owner,address:&key};let bytes:[u8;248]=kani::any();if check(program,&core,account,&bytes,shard_addr,expected_pool,digest,seq,authority,next_page).is_ok(){assert_eq!(owner.to_bytes(),program);assert_eq!(memo().answer,Some(key));assert_eq!(bytes[6],unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED,core.as_ref()],&Pubkey(program)));}
}
}
