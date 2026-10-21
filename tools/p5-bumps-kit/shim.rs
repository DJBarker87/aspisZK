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

#[derive(Clone,Copy,Debug,kani::Arbitrary)]struct PlanFields{program_id:[u8;32],pool:[u8;32],plan_authority:[u8;32],statement_digest:[u8;32],source_sequence:u64,pda_bump:u8}
#[derive(Clone,Copy)]struct PreparedAccount<'a>{owner:&'a Pubkey,address:&'a Pubkey}
const POOL_V1_PREPARED_SETTLEMENT_HEADER_BYTES:usize=16;

const POOL_V1_PAIR_FOREST_MARKER_SEED_BYTES:usize=32;
