"""Source association of the selected planner's field-origin cut.
No whole planner trace/observation refinement is asserted by this inventory.
"""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-l2c-20261028/resume-d371'
def compact(s):return re.sub(r'\s+','',s)
def body(s,marker):
 a=s.index(marker);a=s.index('{',a);b=a+1;depth=1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
plan=(R/'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs').read_text()
spend=(R/'crates/aspis-statement/src/spend.rs').read_text()
fmt=(R/'crates/aspis-statement/src/pool_v1/format.rs').read_text()
client=(R/'crates/aspis-r1-cost-probe/src/RealR1_client.rs').read_text()
assert compact(body(spend,'pub fn derive_owner_key('))=='derive_owner_key_with(nullifier_key,&muthash_fields)'
assert compact(body(spend,'fn derive_owner_key_with<H>('))=='hash(DOMAIN_OWNER_KEY,nullifier_key)'
assert 'pub(crate) const DOMAIN_OWNER_KEY: M31 = M31(0x4153_0001);' in spend
assert int('41530001',16)==1095958529
for marker,expected in [('pub fn pool_v1_note_commitment(', 'note_commitment(owner_key,value,asset_id,salt)'),('pub fn pool_v1_nullifier(', 'derive_nullifier(nullifier_key,salt)'),('pub fn pool_v1_tree_parent(', 'merkle_node_compress_v3(left,right)')]:
 assert compact(body(fmt,marker))==expected
checks=[
 'let n=q["note"].as_u64().unwrap() as u32;let(k,salt,cm)=note(n);let nf=pool_v1_nullifier(&k,&salt);',
 'let change=PoolV1OutputNoteWitnessV1{owner_key:derive_owner_key(&digest(500+n)),salt:digest(600+n),value:if withdrawal{750}else{400}};',
 'let recipient=PoolV1OutputNoteWitnessV1{owner_key:derive_owner_key(&digest(300)),salt:digest(400),value:600};',
 'let lane=decode_pool_v1_pair_forest_lane_state_v1(&bytes(q,"lane_bytes"),&POOL_V1_PAIR_EMPTY_ROOTS).map_err(err)?;',
 'let cp=decode_pool_v1_pair_forest_checkpoint_v1(&bytes(q,"checkpoint_bytes")).map_err(err)?;',
 'let live=PoolV1PairLiveSnapshotV1{pool:master.to_bytes(),deployment_domain:[5;32],sequence:lane.tree.next_leaf_index,next_pair_index:lane.tree.next_leaf_index,current_root:lane.tree.root,frontier:lane.tree.frontier};',
 'let result=RealR1_client::prove_for_proof_accounts(statement.semantic_public(),&compiled,HOST_HASH,&mut store,|k| accounts.nonce(k)).map_err(err)?;']
for expected in checks:assert compact(expected) in compact(plan),expected
# Inventory *all* raw M31 tuple constructors in the executable planner.
# Parenthesized generator separately checked; every remaining constructor is literal 77.
without_generator=plan.replace('M31((seed+17*i as u32+1)%P)','GENERATOR_CANONICAL_REMAINDER')
remaining=re.findall(r'\bM31\(([^)]*)\)',without_generator)
assert remaining and set(remaining)=={'77'},remaining
assert compact(body(plan,'fn digest('))=='core::array::from_fn(|i|M31((seed+17*iasu32+1)%P))'
prove=body(plan,'fn prove(q:&Value')
reads=sorted(set(re.findall(r'q\["([^"]+)"\]',prove)))
assert reads==['note','proof_dir','withdrawal'],reads
# Other JSON access occurs only through byte/account-address helpers; none supplies note limbs.
assert 'q["recipient' not in plan and 'q["owner_key' not in plan and 'q["salt' not in plan
assert compact(body(client,'pub fn prove_for_proof_accounts('))==compact('''prover::prove_masked_retrying_with(public, compiled, Variant::S2, hash, nonce_store, |k| {
StateOnlyAttemptSecrets::generate_for_mask_nonce(proof_account(k)).map_err(|_| Error::Entropy)
})''')
paths=['tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','crates/aspis-statement/src/spend.rs','crates/aspis-statement/src/pool_v1/format.rs','crates/aspis-r1-cost-probe/src/RealR1_client.rs']
pins={}
for p in paths:
 data=(R/p).read_bytes(); assert data==subprocess.check_output(['git','show','3197fab0eb:'+p],cwd=R)
 pins[p]=hashlib.sha256(data).hexdigest()
out={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'evidence_class':'structural (K-1 substitute), generated/decoded field-origin cut; full route association incomplete',
 'pins':pins,'direct_prove_json_reads':reads,'remaining_M31_constructors':remaining,
 'checked_selected_statements':checks,
 'complete_result_laws':['PV_L2C_GeneratedRange.remainder_result','PV_L2C_PlannerOutputs.owner_total','PV_L2C_PlannerOutputs.outputs','PV_L2C_DigestRange.digest_success'],
 'composition':['decoder-source-check.json','hash-source-check.json','account-source-check.json'],
 'finite_validation':['decoder-probe1/receipt.json','decoder-probe2/receipt.json','account-probe4/receipt.json'],
 'differences':[
 'Lean names the planner generator as eight U32 wrapping operations followed by final remainder. Debug overflow rejects before compilation; release wrapping is covered by arbitrary U32 seed/prior bounds.',
 'Native derive_owner_key wrapper is unfolded into domain 1095958529 and exactly eight input words; no error or branch is removed by unfolding these infallible wrappers.',
 'The planner constructs a snapshot directly from lane decoding; it does not call the different 800-byte snapshot decoder. Its bridge to the canonical-preparation carrier still requires a codec encoding/roundtrip association.',
 'RealR1_client is a generic compiled-column API. This cut proves no canonicality for arbitrary direct Rust callers; D370 remains admitted there.'],
 'result':'No unchecked raw-limb source found in selected JSON planner. Domain/record/compiler/mask transport must be completed before universal N3 credit.'}
(E/'planner-source-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('Checked selected planner output origins, all raw constructors, JSON reads, owner/hash wrappers and RealR1_client forwarding')
