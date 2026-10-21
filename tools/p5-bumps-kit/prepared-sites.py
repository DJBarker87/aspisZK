def extend(ns):
 fn=ns['fn'];record=ns['record'];modules=ns['modules'];harnesses=ns['harnesses'];blob=ns['blob']
 p='programs/aspis-pool/src/prepared_settlement_format.rs'
 def add(name,code,test):
  modules.append('mod '+name+' {use super::*;\n'+code+'\n#[kani::proof]\n#[kani::unwind(200)]\nfn '+name+'(){reset();\n'+test+'\n}\n}\n');harnesses.append(name+'::'+name)
 def slice(owner,start,end):
  w,_=fn(p,owner);i=w.index(start);j=w.index(end,i);s=w[i:j].rstrip();record(p,owner,s,'canonical address/bump gate slice');return s
 search,_=fn(p,'pool_v1_prepared_settlement_plan_address');record(p,'pool_v1_prepared_settlement_plan_address',search,'complete helper reused for core gate')
 s=slice('decode_prepared_settlement_plan_v1','let (expected_core_address, expected_core_bump) =','    let next_page_raw =')
 add('prepared_core_decode',search+'\nfn check(program_id:[u8;32],pool:[u8;32],plan_authority:[u8;32],statement_digest:[u8;32],source_sequence:u64,core_address:&Pubkey,bytes:&[u8;10])->Result<(),PreparedSettlementFormatErrorV1>{'+s+'\nOk(())}', 'let program_id:[u8;32]=kani::any();let pool:[u8;32]=kani::any();let authority:[u8;32]=kani::any();let digest:[u8;32]=kani::any();let seq:u64=kani::any();let key=any_key();let bytes:[u8;10]=kani::any();if check(program_id,pool,authority,digest,seq,&key,&bytes).is_ok(){assert_eq!(memo().answer,Some(key));assert_eq!(bytes[9],unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PREPARED_SETTLEMENT_SEED,&pool,&digest,&seq.to_le_bytes(),&authority],&Pubkey(program_id)));}')
 s=slice('encode_prepared_settlement_plan_v1','let program_id = Pubkey::new_from_array(fields.program_id);','    // Allocate the core first')
 w='output[9] = fields.pda_bump;';record(p,'encode_prepared_settlement_plan_v1',w,'exact wire bump assignment')
 add('prepared_core_initialize',search+'\nfn image(fields:PlanFields)->Result<u8,PreparedSettlementFormatErrorV1>{'+s+'\nlet mut output=[0u8;10];'+w+'Ok(output[9])}', 'let fields:PlanFields=kani::any();if let Ok(bump)=image(fields){assert_eq!(bump,unsafe{CANON_BUMP});}')
 search,_=fn(p,'pool_v1_prepared_settlement_rollover_address');record(p,'pool_v1_prepared_settlement_rollover_address',search,'complete helper reused for shard gate')
 w,_=fn(p,'decode_rollover_shard_v1');i=w.index('let program_id = Pubkey::new_from_array(expected_program);');j=w.index('\n    exact_ref(',i);full=w[i:j].rstrip();record(p,'decode_rollover_shard_v1',full,'complete canonical shard guard; final proof preserves complete frozen error enum')
 prefix_end=full.index('        || bytes[SHARD_CORE_ADDRESS_OFFSET')
 prefix=full[:prefix_end];record(p,'decode_rollover_shard_v1',prefix,'canonical shard guard prefix retained for diagnostic weakening only')
 s=full
 text=blob(p);i=text.index('const SHARD_CORE_ADDRESS_OFFSET:');j=text.index('const SHARD_DIGEST_OFFSET:',i);consts=text[i:j];record(p,'shard_offsets',consts,'exact fixed header offsets')
 code=search+'\n'+consts+'\n#[inline(never)]\nfn check(expected_program:[u8;32],core_address:&Pubkey,account:PreparedAccount,bytes:&[u8;248],expected_shard_address:[u8;32],expected_pool:[u8;32],expected_statement_digest:[u8;32],expected_source_sequence:u64,expected_plan_authority:[u8;32],expected_next_page_address:[u8;32])->Result<(),PreparedSettlementFormatErrorV1>{'+s+'\nOk(())}'
 test='let shard_addr:[u8;32]=kani::any();let expected_pool:[u8;32]=kani::any();let digest:[u8;32]=kani::any();let seq:u64=kani::any();let authority:[u8;32]=kani::any();let next_page:[u8;32]=kani::any();let program:[u8;32]=kani::any();let core=any_key();let key=any_key();let owner=any_key();let account=PreparedAccount{owner:&owner,address:&key};let bytes:[u8;248]=kani::any();if check(program,&core,account,&bytes,shard_addr,expected_pool,digest,seq,authority,next_page).is_ok(){assert_eq!(owner.to_bytes(),program);assert_eq!(memo().answer,Some(key));assert_eq!(bytes[6],unsafe{CANON_BUMP});assert_eq!(memo().query,query(&[POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_SEED,core.as_ref()],&Pubkey(program)));}'
 add('prepared_shard_decode',code,test)
