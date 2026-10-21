"""Source-exact initializer records and their exact wire bump writes.
Composition follows the frozen callers; unrelated codec/state checks are not
asserted by these component harnesses.
"""
def extend(ns):
    fn=ns['fn'];record=ns['record'];modules=ns['modules'];harnesses=ns['harnesses'];blob=ns['blob'];F=ns['F'];G=ns['G']
    def add(name,code,test):
        modules.append('mod '+name+' {use super::*;\n'+code+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn '+name+'(){reset();\n'+test+'\n}\n}\n');harnesses.append(name+'::'+name)
    def pick(path,owner,start,end):
        w,_=fn(path,owner);i=w.index(start);j=w.index(end,i);s=w[i:j].rstrip();record(path,owner,s,'initializer record slice');return s
    def wire(path,owner,text):
        w,_=fn(path,owner);assert text in w;record(path,owner,text,'exact wire bump assignment');return text
    A='crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs'
    # Pool master initialization: selected record literal + wire assignment.
    s=pick(F,'forest_master_image_box_v1','let master_state =','    Ok(Box::new(')
    w=wire(A,'encode_pool_v1_pair_forest_master_v1','output[7] = master.bump;')
    search,_=fn(F,'pool_v1_pair_forest_master_address');record(F,'pool_v1_pair_forest_master_address',search,'complete declaration reused for initializer')
    add('initialize_master',search+'\nfn image(expected_master:&Pubkey,initialization:&PoolInitializationV1,master_bump:u8)->u8{'+s+'let master=&*master_state;let mut output=[0u8;8];'+w+'output[7]}','let program_id=any_key();let init:PoolInitializationV1=kani::any();let (key,bump)=pool_v1_pair_forest_master_address(&program_id,&Pubkey::new_from_array(init.asset_mint));let stored=image(&key,&init,bump);assert_eq!(stored,unsafe{CANON_BUMP});')
    # Pool lane initializer is a complete declaration; EMPTY_ROOTS is an
    # opaque payload constant. It has no influence on seeds, key or bump.
    s,_=fn(F,'genesis_lane_state');record(F,'genesis_lane_state',s,'complete initializer declaration')
    w=wire(A,'encode_pool_v1_pair_forest_lane_state_v1','output[72] = lane.bump;')
    search,_=fn(F,'pool_v1_pair_forest_lane_address');record(F,'pool_v1_pair_forest_lane_address',search,'complete declaration reused for initializer')
    add('initialize_lane',s+'\n'+search,'let program_id=any_key();let master=any_key();let lane_id:u8=kani::any();if let Ok((key,bump))=pool_v1_pair_forest_lane_address(&program_id,&master,lane_id){let lane=genesis_lane_state(&master,lane_id,bump);let mut output=[0u8;73];'+w+'assert_eq!(output[72],unsafe{CANON_BUMP});assert_eq!(lane.master,master.to_bytes());assert_eq!(lane.lane_id,lane_id);}')
    # Immutable checkpoint literal + wire byte.
    s=pick(A,'plan_pool_v1_pair_forest_checkpoint_v1','let checkpoint =','    let next_master =')
    w=wire(A,'encode_pool_v1_pair_forest_checkpoint_v1','output[7] = checkpoint.bump;')
    search,_=fn(F,'pool_v1_pair_forest_checkpoint_address');record(F,'pool_v1_pair_forest_checkpoint_address',search,'complete declaration reused for initializer')
    add('initialize_checkpoint',search+'\nfn image(master:&Master,global_root:[u32;8],lane_sequences:[u64;8],checkpoint_bump:u8)->u8{'+s+'let mut output=[0u8;8];'+w+'output[7]}','let program_id=any_key();let master:Master=kani::any();let (key,bump)=pool_v1_pair_forest_checkpoint_address(&program_id,&Pubkey::new_from_array(master.identity.pool),master.next_checkpoint_sequence);let stored=image(&master,kani::any(),kani::any(),bump);assert_eq!(stored,unsafe{CANON_BUMP});')
    # Both registry versions and both entry versions. Input authority/policy/
    # timing values are symbolic. The actual caller's authenticated deployment
    # supplies the programdata bump; its canonical derivation is a separate gate.
    V='crates/aspis-statement/src/pool_v1/verifier_registry.rs'
    for suffix in ['','_v2']:
      version='V2' if suffix else 'V1'
      for field in ['registry','entry']:
        owner=('process_initialize' if field=='registry' else 'process_schedule')+suffix
        whole,_=fn(G,owner);start='let '+field+' = VerifierRegistry'+('Entry' if field=='entry' else '')+version+' {'
        i=whole.index(start);j=whole.index('\n    };',i)+len('\n    };');s=whole[i:j];record(G,owner,s,'initializer record slice')
        codec='encode_verifier_registry'+('_entry' if field=='entry' else '')+suffix.replace('_v2','_v2')
        # Actual names use v1 suffix for the V1 codec.
        codec='encode_verifier_registry'+('_entry' if field=='entry' else '')+('_v2' if suffix else '_v1')
        offset=7 if field=='registry' and suffix else 6 if field=='registry' else 312 if suffix else 7
        rhs=field+'.bump';w=wire(V,codec,f'output[{offset}] = {rhs};')
        pw='';offset2=248 if field=='registry' else 313
        if suffix:pw=wire(V,codec,f'output[{offset2}] = {field}.programdata_bump;')
        search_owner='pool_v1_verifier_'+field+suffix+'_address';search,_=fn(G,search_owner);record(G,search_owner,search,'complete declaration reused for initializer')
        setup='let program_id=any_key();let pool:[u8;32]=kani::any();let pool_key=Pubkey::new_from_array(pool);let profile_binding:[u8;32]=kani::any();let release_binding:[u8;32]=kani::any();let verifier_program:[u8;32]=kani::any();let policy_binding:[u8;32]=kani::any();let minimum_activation_delay_slots:u64=kani::any();let statement_version:u8=kani::any();let activation_slot:u64=kani::any();let authority_key=any_key();let authority=account(&authority_key);let registry:Registry=kani::any();let deployment:Deployment=kani::any();'
        args='&program_id,&pool_key' if field=='registry' else '&program_id,&pool_key,&profile_binding,&release_binding'
        structname='VerifierRegistry'+('Entry' if field=='entry' else '')+version
        vsrc=blob(V);si=vsrc.index('pub struct '+structname+' {');sj=vsrc.index('\n}',si)+2
        struct=vsrc[si:sj];record(V,structname,struct,'exact initializer record type')
        code=struct+'\n'+search+'\n'
        # In the source initializer program_id is already a reference.
        test=setup+'let (expected_address,bump)='+search_owner+'('+args+');let program_id=&program_id;'+s+'let mut output=[0u8;320];'+w+pw+f'assert_eq!(output[{offset}],unsafe{{CANON_BUMP}});'
        if suffix:test+=f'assert_eq!(output[{offset2}],deployment.programdata_bump);'
        add('initialize_'+field+suffix,code,test)
