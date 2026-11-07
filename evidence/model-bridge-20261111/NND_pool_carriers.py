from pathlib import Path
E=Path(__file__).resolve().parent
items=[
 ('PoolIdentity','aspis_statement.pool_v1.format.PoolIdentityV1','PoolIdentity',[('pool','key'),('asset_mint','key'),('token_program','key'),('asset_id','word'),('deployment_domain','key')]),
 ('Policy','aspis_statement.pool_v1.format.VerifierPolicyV1','VerifierPolicy',[('flags','byte'),('registry_program','key'),('registry_authority','key'),('policy_binding','key')]),
 ('Master','aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1','Master',[('bump','byte'),('identity','poolIdentity'),('verifier_policy','policy'),('initialized_lane_mask','byte'),('has_checkpoint','id'),('next_checkpoint_sequence','slot'),('last_checkpoint_lane_sequences','slots')]),
 ('Checkpoint','aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1','Checkpoint',[('bump','byte'),('master','key'),('deployment_domain','key'),('checkpoint_sequence','slot'),('global_root','digest'),('lane_sequences','slots')]),
 ('Tree','aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1','Tree',[('next_leaf_index','slot'),('root','digest'),('frontier','frontier')]),
 ('Lane','aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1','LaneState',[('bump','byte'),('master','key'),('lane_id','byte'),('tree','tree')]),
 ('Live','aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1','LiveSnapshot',[('pool','key'),('deployment_domain','key'),('sequence','slot'),('next_pair_index','slot'),('current_root','digest'),('frontier','frontier')]),
 ('Auth','r1_pool_adapter.AuthenticatedAsq8Accounts','Authenticated',[('master_account','key'),('checkpoint_account','key'),('selected_lane_account','key'),('master','master'),('checkpoint','checkpoint'),('selected_lane','lane'),('live_snapshot','live')])]
prev='NND_CarrierInjective'
for name,typ,target,fields in items:
 fn=name[0].lower()+name[1:];mod='NND_'+name+'Carrier'
 native='AdapterRw.'+typ
 s='import '+prev+'\nset_option autoImplicit false\nnamespace NND_Carrier\n'
 s+='def '+fn+' (x : '+native+') : RSL.'+target+' :=\n { '+',\n   '.join(f+' := '+c+' x.'+f for f,c in fields)+' }\n'
 s+='theorem '+fn+'_injective : Function.Injective '+fn+' := by\n intro x y h\n cases x\n cases y\n simp only ['+fn+',RSL.'+target+'.mk.injEq'
 for c in sorted({c for _,c in fields} - {'id'}):s+=','+c+'_eq_iff'
 s+='] at h\n exact '+native+'.mk.injEq.mpr h\n'
 s+='@[simp] theorem '+fn+'_eq_iff (x y : '+native+') : '+fn+' x = '+fn+' y ↔ x = y :=\n ⟨fun h => '+fn+'_injective h,congrArg '+fn+'⟩\n'
 s+='#print axioms '+fn+'_injective\n#print axioms '+fn+'_eq_iff\nend NND_Carrier\n'
 (E/(mod+'.lean')).write_text(s);prev=mod
