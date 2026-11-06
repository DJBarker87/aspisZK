from NLA_lane import *

def shape(part,mode):
 if part=='length':
  start=FROZEN.index('    if bytes.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES',FROZEN.index('fn decode_lane_from_pool_release'))
  end=FROZEN.index('    let master:',start);segment=FROZEN[start:end]
  actual=segment.replace('bytes.len()', 'length')
  text=COMMON+ANN+"""fn stage(){
 let bytes:[u8;768]=kani::any();let length:usize=kani::any();let mut suffix=0u8;
 let mut out=(||->ProgramResult{SEGMENT suffix+=1;Ok(())})();CORRUPT
 let expected=length==768&&bytes[..4]==POOL_V1_PAIR_FOREST_LANE_MAGIC&&bytes[4]==POOL_V1_PAIR_FOREST_LANE_VERSION&&usize::from(bytes[5])<POOL_V1_PAIR_FOREST_LANE_COUNT&&bytes[6]==POOL_V1_PAIR_FOREST_LANE_COUNT as u8&&bytes[7]==POOL_V1_PAIR_TREE_DEPTH as u8&&bytes[8..40]==POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING&&bytes[73..80].iter().all(|b|*b==0);
 assert!(out==if expected{Ok(())}else{Err(ProgramError::InvalidAccountData)}&&suffix==if expected{1}else{0},"arbitrary length header Result prefix");}
 """.replace('SEGMENT',actual).replace('CORRUPT','out=if out.is_ok(){Err(ProgramError::InvalidAccountData)}else{Ok(())};' if mode=='inverse' else '')
 elif part=='absolute':
  segment='let tree = &bytes[POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES..];'
  text=COMMON+ANN+"""fn stage(){let bytes:[u8;768]=kani::any();let i:usize=kani::any();kani::assume(i<32);SEGMENT
  let mut observed=tree[16..48][i];CORRUPT
  assert!(observed==bytes[96+i],"absolute root original byte window");}
  """.replace('SEGMENT',segment).replace('CORRUPT','observed^=1;' if mode=='inverse' else '')
 elif part=='iteration':
  segment="""*node = reply.map_err(|_|ProgramError::InvalidAccountData)?;
  if (next_leaf_index >> level) & 1 == 0 && *node != v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[level] {return Err(ProgramError::InvalidAccountData);}"""
  text=COMMON+ANN+"""fn stage(){let before=digest();let words=digest();let ok:bool=kani::any();let next_leaf_index:u64=kani::any();let level:usize=kani::any();let word:usize=kani::any();kani::assume(level<20&&word<8);let mut after=before;let node=&mut after;
 let reply=if ok{Ok(words)}else{Err(aspis_statement::AtomicStatementError::NonCanonicalDigest)};let mut suffix=0u8;
 let mut out=(||->ProgramResult{SEGMENT suffix+=1;Ok(())})();CORRUPT
 let guard=(next_leaf_index>>level)&1!=0||words==v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[level];let expected=ok&&guard;
 assert!(out==if expected{Ok(())}else{Err(ProgramError::InvalidAccountData)}&&after[word].0==if ok{words[word].0}else{before[word].0}&&suffix==if expected{1}else{0},"one iteration assignment before rejection and Result");}
 """.replace('SEGMENT',segment).replace('CORRUPT','after[word].0^=1;' if mode=='inverse' else '')
 elif part.startswith('box'):
  start=FROZEN.index('    Ok(Box::new(PoolV1PairForestLaneStateV1',FROZEN.index('fn decode_lane_from_pool_release'));end=FROZEN.index('\n}',start);segment=FROZEN[start:end]
  ctor=segment.strip()[3:-1]
  text=COMMON+ANN+"""fn stage(){let bytes:[u8;768]=kani::any();let master:[u8;32]=kani::any();let next_leaf_index:u64=kani::any();let root=digest();let frontier=frontier();
 let mut frame:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<32);let before=frame[i];
 let out=CTOR;let first=(&*out as *const PoolV1PairForestLaneStateV1) as usize;let returned=out;let mut ptr=(&*returned as *const PoolV1PairForestLaneStateV1) as usize;
 let other=CTOR;
 drop(returned);CORRUPT
 assert!(PROPERTY,"Box move allocation identity unique live allocation and cleanup frame");drop(other);}
 """.replace('CTOR',ctor)
  prop={'boxmove':'ptr==first','boxunique':'ptr!=(&*other as *const PoolV1PairForestLaneStateV1) as usize','boxframe':'frame[i]==before'}[part]
  # For uniqueness, both allocations must be LIVE at the observation; moving
  # drop after the assertion prevents reuse of the first allocation address.
  if part=='boxunique':text=text.replace('drop(returned);CORRUPT','CORRUPT').replace('drop(other);','drop(returned);drop(other);')
  corrupt={'boxmove':'ptr^=1;','boxunique':'ptr=(&*other as *const PoolV1PairForestLaneStateV1) as usize;','boxframe':'frame[i]^=1;'}[part]
  text=text.replace('PROPERTY',prop).replace('CORRUPT',corrupt if mode=='inverse' else '')
 elif part=='status':
  segment='solana_program::pubkey::PubkeyError::from(status)'
  text=COMMON+ANN+"""fn stage(){use solana_program::pubkey::PubkeyError;let status:u64=kani::any();kani::assume(status==1||status==2);let mut out=SEGMENT;CORRUPT
 assert!(out==if status==1{PubkeyError::InvalidSeeds}else{PubkeyError::IllegalOwner},"actual SDK nonzero status conversion");}
 """.replace('SEGMENT',segment).replace('CORRUPT','out=if status==1{PubkeyError::IllegalOwner}else{PubkeyError::InvalidSeeds};' if mode=='inverse' else '')
 elif part=='pdaoutput':
  segment='Pubkey::from(bytes)'
  text=COMMON+ANN+"""fn stage(){let bytes:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<32);let out=SEGMENT;let mut observed=out.to_bytes()[i];CORRUPT
 assert!(observed==bytes[i],"actual SDK returned output byte unchanged");}
 """.replace('SEGMENT',segment).replace('CORRUPT','observed^=1;' if mode=='inverse' else '')
 elif part=='statuspanic':
  segment='solana_program::pubkey::PubkeyError::from(status)'
  text=COMMON+ANN+"""fn stage(){let status:u64=kani::any();kani::assume(status>2);let _out=SEGMENT;assert!(false,"SDK must abort before this suffix");}
 """.replace('SEGMENT',segment)
 else:raise ValueError(part)
 return text,segment

def attempt(a,part,mode):
 text,segment=shape(part,mode);mod='NLA_tail'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(part=part,source=P,segment=segment,mode=mode,domain='source stage prestate; lengths arbitrary usize for length cut; Box returning arm only; status1or2 for conversion; status>2 for panic witness',limits='no allocator totality, deployed syscall ABI or row closure is claimed'),indent=1)+'\n')
 return submit(a,'r1_pool_adapter::'+mod+'::stage',P,mod,text,mode)
