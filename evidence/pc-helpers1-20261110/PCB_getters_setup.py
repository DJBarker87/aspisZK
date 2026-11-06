from pathlib import Path
import subprocess,json,difflib
E=Path(__file__).resolve().parent;R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';P='b936275465600469312d1f058cdc91ea2a11f3dc'
mods=[('crates/aspis-statement/src/pool_v1/incremental_merkle.rs','178'),('programs/aspis-pool/src/nullifier.rs','291'),('programs/aspis-pool/src/pair_forest_dispatch.rs','343'),('programs/aspis-pool/src/pair_state.rs','355')];files={};patch=''
for path,id in mods:
 orig=subprocess.check_output(['git','show',(P if path.startswith('programs/') else R)+':'+path],text=True);name='PCB_'+Path(path).stem+'.rs.txt';s=(E/name).read_text() if (E/name).exists() else orig
 s+=f'\n#[cfg(kani)]\n#[path="PCB_{id}.rs"]\nmod PCB_{id};\n';(E/name).write_text(s);files['PCB_src/'+path]=name
 patch+=''.join(difflib.unified_diff(orig.splitlines(True),s.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
(E/'PCB_GETTERS.patch').write_text(patch)
(E/'PCB_178.rs').write_text('''use super::*;
const WRONG_TREE:IncrementalMerkleTreeV1=IncrementalMerkleTreeV1 {next_leaf_index:0,root:[M31::ZERO;8],frontier:[[M31::ZERO;8];POOL_V1_TREE_DEPTH]};
fn correct<'a,'b>(x:&'a ValidatedIncrementalMerkleTreeV1<'b>)->&'a IncrementalMerkleTreeV1 {&x.inner}
fn wrong<'a,'b>(_:&'a ValidatedIncrementalMerkleTreeV1<'b>)->&'a IncrementalMerkleTreeV1 {&WRONG_TREE}
#[kani::proof] #[kani::stub(ValidatedIncrementalMerkleTreeV1::as_tree,correct)]
fn tree_correct(){let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];let mut inner=WRONG_TREE;inner.next_leaf_index=kani::any();let x=ValidatedIncrementalMerkleTreeV1 {inner,empty:&empty};assert!(core::ptr::eq(x.as_tree(),&x.inner));}
#[kani::proof] #[kani::stub(ValidatedIncrementalMerkleTreeV1::as_tree,wrong)]
fn tree_wrong(){let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];let mut inner=WRONG_TREE;inner.next_leaf_index=kani::any();let x=ValidatedIncrementalMerkleTreeV1 {inner,empty:&empty};assert!(core::ptr::eq(x.as_tree(),&x.inner));}
#[kani::proof] #[kani::stub(ValidatedIncrementalMerkleTreeV1::as_tree,correct)]
fn deref_correct(){let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];let mut inner=WRONG_TREE;inner.next_leaf_index=kani::any();let x=ValidatedIncrementalMerkleTreeV1 {inner,empty:&empty};assert!(core::ptr::eq(core::ops::Deref::deref(&x),&x.inner));}
#[kani::proof] #[kani::stub(ValidatedIncrementalMerkleTreeV1::as_tree,wrong)]
fn deref_wrong(){let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];let mut inner=WRONG_TREE;inner.next_leaf_index=kani::any();let x=ValidatedIncrementalMerkleTreeV1 {inner,empty:&empty};assert!(core::ptr::eq(core::ops::Deref::deref(&x),&x.inner));}
''')
(E/'PCB_291.rs').write_text('''use super::*;
const WRONG:[u8;32]=[0;32];
fn correct(x:&PlannedPairForestNullifierMarkerV1)->&[u8;32] {&x.seed}
fn wrong(_:&PlannedPairForestNullifierMarkerV1)->&[u8;32] {&WRONG}
#[kani::proof] #[kani::stub(PlannedPairForestNullifierMarkerV1::seed,correct)]
fn seed_correct(){let x=PlannedPairForestNullifierMarkerV1 {preparation:NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed,seed:kani::any(),encoded_marker:[0;POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES]};assert!(core::ptr::eq(x.seed(),&x.seed));}
#[kani::proof] #[kani::stub(PlannedPairForestNullifierMarkerV1::seed,wrong)]
fn seed_wrong(){let x=PlannedPairForestNullifierMarkerV1 {preparation:NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed,seed:kani::any(),encoded_marker:[0;POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES]};assert!(core::ptr::eq(x.seed(),&x.seed));}
''')
(E/'PCB_343.rs').write_text('''use super::*;
fn fixture()->PoolV1PairForestTerminalResultV1 {PoolV1PairForestTerminalResultV1 {
 transition_kind:aspis_statement::pool_v1::PoolV1TransitionKind::PrivateTransfer,master_account:[0;32],selected_lane_account:[0;32],output_lane:0,nullifier:[aspis_core::field::M31::ZERO;8],verified_afterstate:aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1 {next_pair_index:kani::any(),next_root:[aspis_core::field::M31::ZERO;8],next_frontier:[[aspis_core::field::M31::ZERO;8];aspis_statement::pool_v1::POOL_V1_PAIR_TREE_DEPTH]}}}
fn correct(x:&AuthenticatedPairForestResultV1)->&PoolV1PairForestTerminalResultV1 {&x.value}
fn wrong(_:&AuthenticatedPairForestResultV1)->&PoolV1PairForestTerminalResultV1 {Box::leak(Box::new(fixture()))}
#[kani::proof] #[kani::stub(AuthenticatedPairForestResultV1::value,correct)]
fn value_correct(){let x=AuthenticatedPairForestResultV1 {value:Box::new(fixture()),exact_bytes:alloc::vec::Vec::<u8>::new().into_boxed_slice()};assert!(core::ptr::eq(x.value(),&*x.value));}
#[kani::proof] #[kani::stub(AuthenticatedPairForestResultV1::value,wrong)]
fn value_wrong(){let x=AuthenticatedPairForestResultV1 {value:Box::new(fixture()),exact_bytes:alloc::vec::Vec::<u8>::new().into_boxed_slice()};assert!(core::ptr::eq(x.value(),&*x.value));}
''')
(E/'PCB_355.rs').write_text('''use super::*;
fn fixture()->PairPoolStateV1 {PairPoolStateV1 {
 identity:aspis_statement::pool_v1::PoolIdentityV1 {pool:[0;32],asset_mint:[0;32],token_program:[0;32],asset_id:aspis_core::field::M31::ZERO,deployment_domain:[0;32]},verifier_policy:aspis_statement::pool_v1::VerifierPolicyV1 {flags:0,registry_program:[0;32],registry_authority:[0;32],policy_binding:[0;32]},tree:aspis_statement::pool_v1::IncrementalMerkleTreeV1 {next_leaf_index:kani::any(),root:[aspis_core::field::M31::ZERO;8],frontier:[[aspis_core::field::M31::ZERO;8];aspis_statement::pool_v1::POOL_V1_TREE_DEPTH]}}}
fn correct(x:&CanonicalPairPoolStateV1)->&PairPoolStateV1 {&x.state}
fn wrong(_:&CanonicalPairPoolStateV1)->&PairPoolStateV1 {Box::leak(Box::new(fixture()))}
#[kani::proof] #[kani::stub(<CanonicalPairPoolStateV1 as core::ops::Deref>::deref,correct)]
fn state_correct(){let x=CanonicalPairPoolStateV1 {program_id:Pubkey::new_from_array([0;32]),pool:Pubkey::new_from_array([0;32]),state:Box::new(fixture())};assert!(core::ptr::eq(core::ops::Deref::deref(&x),&*x.state));}
#[kani::proof] #[kani::stub(<CanonicalPairPoolStateV1 as core::ops::Deref>::deref,wrong)]
fn state_wrong(){let x=CanonicalPairPoolStateV1 {program_id:Pubkey::new_from_array([0;32]),pool:Pubkey::new_from_array([0;32]),state:Box::new(fixture())};assert!(core::ptr::eq(core::ops::Deref::deref(&x),&*x.state));}
''')
for path,id in mods:files['PCB_src/'+str(Path(path).parent/f'PCB_{id}.rs')]='PCB_'+id+'.rs'
t=json.loads((E/'PCB_TASKS.json').read_text());entries=[('178','pool_v1::incremental_merkle::PCB_178::tree_correct',False),('178','pool_v1::incremental_merkle::PCB_178::tree_wrong',True),('176','pool_v1::incremental_merkle::PCB_178::deref_correct',False),('176','pool_v1::incremental_merkle::PCB_178::deref_wrong',True),('291','nullifier::PCB_291::seed_correct',False),('291','nullifier::PCB_291::seed_wrong',True),('343','pair_forest_dispatch::PCB_343::value_correct',False),('343','pair_forest_dispatch::PCB_343::value_wrong',True),('355','pair_state::PCB_355::state_correct',False),('355','pair_state::PCB_355::state_wrong',True)]
for i,(id,h,neg) in enumerate(entries):
 a=f'PCB_K{57+i:03}';base='PCB_K027' if id in ['178','176'] else 'PCB_K055';x=json.loads(json.dumps(t[base]));x['files'].update(files);x['command']=['python3','PCB_gate.py',a+'.json'];x['collect']=[n.replace(base,a) for n in x['collect']];x['target']='y-prime borrowed place '+id+(' wrong-place control' if neg else ' correct-place caller');x['native_command'][x['native_command'].index('--harness')+1]=h;t[a]=x
(E/'PCB_TASKS.json').write_text(json.dumps(t,indent=1)+'\n')
print('PCB five borrowed-place packets prepared with local or immutable oracle state')
