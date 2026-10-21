def extend(ns):
    fn=ns['fn'];record=ns['record'];modules=ns['modules'];harnesses=ns['harnesses']
    def add(name,code,test):
        modules.append('mod '+name+' {use super::*;\n'+code+'\n#[kani::proof]\n#[kani::unwind('+'200'+')]\nfn '+name+'(){reset();\n'+test+'\n}\n}\n');harnesses.append(name+'::'+name)
    p='programs/aspis-pool/src/history.rs';s,_=fn(p,'require_program_account');record(p,'require_program_account',s,'complete ownership guard')
    add('pool_owner_guard',s,'let program_id=any_key();let key=any_key();let account=account(&key);let writable:bool=kani::any();if require_program_account(&account,&program_id,writable).is_ok(){assert_eq!(*account.owner,program_id);assert!(!account.executable);assert_eq!(account.is_writable,writable);}')
    p=ns['R'];s,_=fn(p,'require_readonly_account');record(p,'require_readonly_account',s,'complete ownership guard')
    helper,_=fn(p,'readonly_meta_ok');record(p,'readonly_meta_ok',helper,'complete ownership predicate')
    add('verifier_owner_guard',helper+'\n'+s,'let program_id=any_key();let key=any_key();let account=account(&key);if require_readonly_account(&account,&program_id).is_ok(){assert_eq!(*account.owner,program_id);assert!(!account.executable&&!account.is_signer&&!account.is_writable);}')
    # Link the actual B1 address helper to create_with_seed, independently of
    # the planner's already-proved derive-and-compare property.
    p='programs/aspis-pool/src/nullifier.rs';s,_=fn(p,'pool_v1_pair_forest_nullifier_marker_address');record(p,'pool_v1_pair_forest_nullifier_marker_address',s,'complete create_with_seed helper')
    # Only hash/packing and canonical scalar decoder are opaque here. The seed
    # is an arbitrary ASCII32 word, the exact output type of the hash packing.
    stubs='fn decode_digest_canonical(_: &[u8;32])->Result<(),ProgramError>{if kani::any(){Ok(())}else{Err(ProgramError::InvalidAccountData)}}\nfn pool_v1_pair_forest_marker_seed_v1(_:&Pubkey,_:&[u8;32])->[u8;32]{let mut s:[u8;32]=kani::any();for x in &mut s{*x &=127;}s}\n'
    st,_=fn(p,'pool_v1_pair_forest_marker_seed_str_v1');record(p,'pool_v1_pair_forest_marker_seed_str_v1',st,'UTF8 boundary target: original retained; compiled shim below asserts ASCII and preserves bytes')
    st='fn pool_v1_pair_forest_marker_seed_str_v1(seed:&[u8;32])->Result<&str,ProgramError>{for b in seed{assert!(*b<128);}Ok(unsafe{core::str::from_utf8_unchecked(seed)})}'
    pack,_=fn(p,'pack_pool_v1_pair_forest_marker_seed_v1');record(p,'pack_pool_v1_pair_forest_marker_seed_v1',pack,'complete seed packing declaration')
    add('marker_seed_ascii',pack,'let digest:[u8;32]=kani::any();let seed=pack_pool_v1_pair_forest_marker_seed_v1(&digest);for b in seed{assert!(b<128);}')
    add('marker_create_with_seed',stubs+st+'\n'+s,'let program_id=any_key();let master=any_key();let n:[u8;32]=kani::any();if let Ok((key,seed))=pool_v1_pair_forest_nullifier_marker_address(&program_id,&master,&n){assert_eq!(memo().answer,Some(key));assert_eq!(memo().query,query(&[master.as_ref(),&seed],&program_id));}')
    # Exact highest-bump / ProgramData linkage guard from the Registry's
    # deployment authenticator, including its canonical search call.
    p=ns['G'];o='authenticate_immutable_loader_v3_deployment_v2';w,_=fn(p,o);i=w.index('let (derived_programdata, programdata_bump) =');j=w.index('\n    let executable_hash =',i);s=w[i:j].rstrip();record(p,o,s,'canonical ProgramData linkage guard slice')
    add('initialize_programdata','fn check(expected_program:&Pubkey,loader:Pubkey,linked_programdata:[u8;32],programdata_account:&AccountInfo)->Result<u8,ProgramError>{'+s+'\nOk(programdata_bump)}','let program=any_key();let loader=any_key();let linked:[u8;32]=kani::any();let key=any_key();let account=account(&key);if let Ok(bump)=check(&program,loader,linked,&account){assert_eq!(linked,key.to_bytes());assert_eq!(memo().answer,Some(key));assert_eq!(bump,unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[program.as_ref()],&loader));}')
    # Prepared-plan decoders perform canonical search themselves, so these
    # stronger guards do not need initializer provenance for bump canonicality.
    p='programs/aspis-pool/src/prepared_settlement_format.rs'
    for name,o,anchor in [('prepared_core_guard','decode_prepared_settlement_plan_v1','if *core_address !='),('prepared_shard_guard','decode_rollover_shard_v1','if *rollover_address !=')]:
        w,_=fn(p,o)
        # Retain this as a recorded source gate; full opaque format helpers and
        # ownership capabilities are outside the one-query address proof kit.
        if anchor in w:
            i=w.index(anchor);j=w.index('\n    }',i)+len('\n    }');record(p,o,w[i:j],'canonical decoder guard (source audit; not separate Kani harness)')
