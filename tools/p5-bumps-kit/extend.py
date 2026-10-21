"""Canonical-search call sites and source-preserving record updates."""
def extend(ns):
    fn=ns['fn'];record=ns['record'];modules=ns['modules'];harnesses=ns['harnesses'];blob=ns['blob']
    def add(name,code,test):
        modules.append('mod '+name+' {use super::*;\n'+code+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn '+name+'(){reset();\n'+test+'\n}\n}\n');harnesses.append(name+'::'+name)
    F=ns['F'];G=ns['G']
    # Complete canonical derivation declarations. The SDK search contract is
    # external, while the exact selected seed tuple and return-value flow are checked.
    specs=[
      ('search_master',F,'pool_v1_pair_forest_master_address','let mint=any_key();','&program_id,&mint','[POOL_V1_PAIR_FOREST_MASTER_SEED,mint.as_ref()]'),
      ('search_checkpoint',F,'pool_v1_pair_forest_checkpoint_address','let pool=any_key();let sequence:u64=kani::any();','&program_id,&pool,sequence','[POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,pool.as_ref(),&sequence.to_le_bytes()]'),
      ('search_vault_authority','programs/aspis-pool/src/vault.rs','pool_v1_vault_authority_address','let pool=any_key();','&program_id,&pool','[POOL_V1_VAULT_AUTHORITY_SEED,pool.as_ref()]'),
      ('search_vault_token','programs/aspis-pool/src/vault.rs','pool_v1_vault_token_account_address','let pool=any_key();','&program_id,&pool','[POOL_V1_VAULT_TOKEN_ACCOUNT_SEED,pool.as_ref()]'),
      ('search_page','programs/aspis-pool/src/history.rs','pool_v1_root_page_address','let pool=any_key();let sequence:u64=kani::any();','&program_id,&pool,sequence','[POOL_V1_ROOT_HISTORY_PAGE_SEED,pool.as_ref(),&sequence.to_le_bytes()]'),
    ]
    for version in ['','_v2']:
        specs += [
         ('search_registry'+version,G,'pool_v1_verifier_registry'+version+'_address','let pool=any_key();','&program_id,&pool','[POOL_V1_VERIFIER_REGISTRY'+version.upper()+'_SEED,pool.as_ref()]'),
         ('search_entry'+version,G,'pool_v1_verifier_entry'+version+'_address','let pool=any_key();let profile:[u8;32]=kani::any();let release:[u8;32]=kani::any();','&program_id,&pool,&profile,&release','[POOL_V1_VERIFIER_ENTRY'+version.upper()+'_SEED,pool.as_ref(),&profile,&release]')]
    specs += [
     ('search_prepared_core','programs/aspis-pool/src/prepared_settlement_format.rs','pool_v1_prepared_settlement_plan_address','let pool=any_key();let digest:[u8;32]=kani::any();let sequence:u64=kani::any();let authority=any_key();','&program_id,&pool,&digest,sequence,&authority','[POOL_V1_PREPARED_SETTLEMENT_SEED,pool.as_ref(),&digest,&sequence.to_le_bytes(),authority.as_ref()]'),
     ('search_prepared_rollover','programs/aspis-pool/src/prepared_settlement_format.rs','pool_v1_prepared_settlement_rollover_address','let pool=any_key();','&program_id,&pool','[POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED,pool.as_ref()]')]
    for name,path,owner,setup,args,seeds in specs:
        s,_=fn(path,owner);record(path,owner,s,'complete canonical-search declaration')
        add(name,s,'let program_id=any_key();'+setup+'let (key,bump)='+owner+'('+args+');assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&'+seeds+',&program_id));')
    s,_=fn(F,'pool_v1_pair_forest_lane_address');record(F,'pool_v1_pair_forest_lane_address',s,'complete canonical-search declaration')
    add('search_lane',s,'let program_id=any_key();let pool=any_key();let lane:u8=kani::any();let result=pool_v1_pair_forest_lane_address(&program_id,&pool,lane);if let Ok((key,bump))=result{assert!(lane<8);assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PAIR_FOREST_LANE_SEED,pool.as_ref(),&[lane]],&program_id));}else{assert!(lane>=8);}')
    # Complete registry generation updaters preserve both bump fields.
    for suffix in ['','_v2']:
        owner='incremented_registry'+suffix;s,_=fn(G,owner);record(G,owner,s,'complete state-update declaration')
        add('preserve_registry'+suffix,s,'let registry:Registry=kani::any();if let Ok(next)='+owner+'(registry){assert_eq!(next.bump,registry.bump);assert_eq!(next.programdata_bump,registry.programdata_bump);assert_eq!(next.pool,registry.pool);assert_eq!(next.programdata_address,registry.programdata_address);}')
    # A source-exact struct update at checkpoint creation retains all master
    # identity fields, independent of arbitrary chronology/payload values.
    p='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs';o='plan_pool_v1_pair_forest_checkpoint_v1';whole,_=fn(p,o)
    i=whole.index('let next_master =');j=whole.index('\n    validate_master(&next_master)',i);s=whole[i:j].rstrip();record(p,o,s,'master update constructor slice')
    add('preserve_master','fn check(master:&Master,next_sequence:u64,lane_sequences:[u64;8])->Master{'+s+'\nnext_master}', 'let master:Master=kani::any();let next=check(&master,kani::any(),kani::any());assert_eq!(next.bump,master.bump);assert_eq!(next.identity.pool,master.identity.pool);assert_eq!(next.identity.asset_mint,master.identity.asset_mint);')
    # Exact lane update constructor; unrelated tree data is abstracted by type.
    o='next_pair_forest_lane_v1';whole,_=fn(F,o);i=whole.index('Ok(PoolV1PairForestLaneStateV1');s=whole[i:whole.rfind('}')].rstrip();record(F,o,s,'lane update constructor slice')
    add('preserve_lane','fn check(lane:&Lane,afterstate:Afterstate)->Result<Lane,ProgramError>{'+s+'}', 'let lane:Lane=kani::any();let next=check(&lane,kani::any()).unwrap();assert_eq!(next.bump,lane.bump);assert_eq!(next.master,lane.master);assert_eq!(next.lane_id,lane.lane_id);')
