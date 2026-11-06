from NKP_lane import *
FROZEN=subprocess.check_output(['git','show','4bb3b3f5:'+P],text=True)
def shape(part,mode):
 if part=='header':
  start=FROZEN.index('    if bytes.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES',FROZEN.index('fn decode_lane_from_pool_release'))
  end=FROZEN.index('    let root = decode_digest_canonical(',start)
  segment=FROZEN[start:end]
  text=COMMON+ANN+'''fn stage(){
 let input:[u8;769]=kani::any();let length:usize=kani::any();kani::assume(length<=769);let bytes=&input[..length];
 let mut result=(||->ProgramResult{
 SEGMENT
 Ok(())})();
 CORRUPT
 let expected=bytes.len()==POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES&&bytes[..4]==POOL_V1_PAIR_FOREST_LANE_MAGIC&&bytes[4]==POOL_V1_PAIR_FOREST_LANE_VERSION&&usize::from(bytes[5])<POOL_V1_PAIR_FOREST_LANE_COUNT&&bytes[6]==POOL_V1_PAIR_FOREST_LANE_COUNT as u8&&bytes[7]==POOL_V1_PAIR_TREE_DEPTH as u8&&bytes[8..40]==POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING&&bytes[73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES].iter().all(|byte|*byte==0)&&bytes[40..72]!=[0u8;32]&&{
 let tree=&bytes[POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES..];tree[..4]==POOL_V1_TREE_STATE_MAGIC&&tree[4]==POOL_V1_TREE_STATE_VERSION&&tree[5]==POOL_V1_PAIR_TREE_DEPTH as u8&&tree[6]==POOL_V1_TREE_HASH_VERSION&&tree[7]==POOL_V1_DIGEST_ENCODING_VERSION&&u64::from_le_bytes(tree[8..16].try_into().unwrap())<=POOL_V1_PAIR_CAPACITY};
 assert!(if expected{matches!(result,Ok(()))}else{matches!(result,Err(ProgramError::InvalidAccountData))},"lane header ordered Result");
}'''.replace('SEGMENT',segment)
 else:
  start=FROZEN.index('    if next_leaf_index == 0 && root != V7_PAIR_EMPTY_ROOTS',FROZEN.index('fn decode_lane_from_pool_release'))
  end=FROZEN.index('    Ok(Box::new',start);segment=FROZEN[start:end]
  text=COMMON+ANN+'''fn stage(){use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
 let next_leaf_index:u64=kani::any();let root=digest();
 let mut result=(||->ProgramResult{SEGMENT Ok(())})();CORRUPT
 let expected=next_leaf_index!=0||root==V7_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH];
 assert!(if expected{matches!(result,Ok(()))}else{matches!(result,Err(ProgramError::InvalidAccountData))},"lane zero-root ordered Result");
}'''.replace('SEGMENT',segment)
 text=text.replace('CORRUPT','result=if result.is_ok(){Err(ProgramError::InvalidAccountData)}else{Ok(())};' if mode=='inverse' else '')
 return text,segment

def attempt(a,part,mode):
 text,segment=shape(part,mode);mod='NKP_lane_prefix'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(part=part,source=P,segment=segment,segment_sha256=sha(segment.encode()),exact_frozen_substring=segment in FROZEN,mode=mode,domain='arbitrary bounded native byte inputs0..769 for header, arbitrary next/root for terminal guard',modifies=[]),indent=1)+'\n')
 return submit(a,'r1_pool_adapter::'+mod+'::stage',P,mod,text,mode)
