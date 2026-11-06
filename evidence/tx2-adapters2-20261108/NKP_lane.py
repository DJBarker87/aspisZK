from NKP_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
COMMON='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn digest()->[M31;8]{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
fn frontier()->[[M31;8];20]{let raw:[[u32;8];20]=kani::any();raw.map(|r|r.map(|x|M31(x)))}
'''
ANN='''#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
def constructor(field,mode):
 compares=['out.bump==bytes[72]','out.master[i]==master[i]','out.lane_id==bytes[5]','out.tree.next_leaf_index==next_leaf_index','out.tree.root[word].0==root[word].0','out.tree.frontier[level][word].0==frontier[level][word].0']
 corrupt=compares[field].split('==')[0]+' ^= 1;' if mode=='inverse' else ''
 # Identical frozen Box constructor; arbitrary full constructor pre-state.
 return COMMON+ANN+'''fn constructor(){
 let bytes:[u8;768]=kani::any();let master:[u8;32]=kani::any();let next_leaf_index:u64=kani::any();let root=digest();let frontier=frontier();
 let i:usize=kani::any();let level:usize=kani::any();let word:usize=kani::any();kani::assume(i<32&&level<20&&word<8);
 let mut out=Box::new(PoolV1PairForestLaneStateV1{bump:bytes[72],master,lane_id:bytes[5],tree:IncrementalMerkleTreeV1{next_leaf_index,root,frontier}});
 CORRUPT
 assert!(COMPARE,"lane constructor returned selected field");
}'''.replace('CORRUPT',corrupt).replace('COMPARE',compares[field])

def iteration(field,mode):
 if field==0:
  return COMMON+'''
struct Log{count:u8,length:usize,input:u8}
fn oracle(bytes:&[u8;32],canonical:bool,words:[M31;8],log:&mut Log,i:usize)->Result<[M31;8],aspis_statement::AtomicStatementError>{log.count+=1;log.length=bytes.len();log.input=bytes[i];if canonical{Ok(words)}else{Err(aspis_statement::AtomicStatementError::NonCanonicalDigest)}}
'''+ANN+'''fn iteration(){
 let tree:[u8;688]=kani::any();let level:usize=kani::any();let i:usize=kani::any();let word:usize=kani::any();kani::assume(level<20&&i<32&&word<8);
 let words=digest();let canonical:bool=kani::any();let mut log=Log{count:0,length:0,input:0};
 let start=48+32*level;
 let result=(||->Result<[M31;8],ProgramError>{Ok(oracle(tree[start..start+32].try_into().map_err(|_|ProgramError::InvalidAccountData)?,canonical,words,&mut log,i).map_err(|_|ProgramError::InvalidAccountData)?)})();
 CORRUPT
 let good=log.count==1&&log.length==32&&log.input==tree[48+32*level+i]&&match result{Ok(node)=>canonical&&node[word].0==words[word].0,Err(e)=>!canonical&&e==ProgramError::InvalidAccountData};
 assert!(good,"lane iteration exact bytes and reply");
}'''.replace('CORRUPT','log.input ^= 1;' if mode=='inverse' else '')
 if field==1:
  return COMMON+ANN+'''fn iteration(){
 let before=digest();let words=digest();let canonical:bool=kani::any();let word:usize=kani::any();kani::assume(word<8);
 let mut frontier_node=before;
 let result=(||->ProgramResult{let node=&mut frontier_node;*node=(if canonical{Ok(words)}else{Err(aspis_statement::AtomicStatementError::NonCanonicalDigest)}).map_err(|_|ProgramError::InvalidAccountData)?;Ok(())})();
 CORRUPT
 let expected=if canonical{words[word].0}else{before[word].0};
 assert!(frontier_node[word].0==expected&&matches!(result,Ok(()))==canonical,"lane iteration selected write and error frame");
}'''.replace('CORRUPT','frontier_node[word].0 ^= 1;' if mode=='inverse' else '')
 if field==2:
  return COMMON+ANN+'''fn iteration(){
 let mut frontier=frontier();let level:usize=kani::any();let other:usize=kani::any();let word:usize=kani::any();kani::assume(level<20&&other<20&&other!=level&&word<8);
 let before=frontier[other][word].0;let words=digest();let canonical:bool=kani::any();
 let _result=(||->ProgramResult{let node=&mut frontier[level];*node=(if canonical{Ok(words)}else{Err(aspis_statement::AtomicStatementError::NonCanonicalDigest)}).map_err(|_|ProgramError::InvalidAccountData)?;Ok(())})();
 CORRUPT
 assert!(frontier[other][word].0==before,"lane iteration untouched coordinate");
}'''.replace('CORRUPT','frontier[other][word].0 ^= 1;' if mode=='inverse' else '')
 assert field==3
 return COMMON+ANN+'''fn iteration(){
 let next_leaf_index:u64=kani::any();let level:usize=kani::any();kani::assume(level<20);let node=digest();
 let mut result=(||->ProgramResult{if(next_leaf_index>>level)&1==0&&node!=v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[level]{return Err(ProgramError::InvalidAccountData);}Ok(())})();
 CORRUPT
 let expected=(next_leaf_index>>level)&1!=0||node==v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[level];
 assert!(if expected{matches!(result,Ok(()))}else{matches!(result,Err(ProgramError::InvalidAccountData))},"lane iteration guard exact Result");
}'''.replace('CORRUPT','result=if result.is_ok(){Err(ProgramError::InvalidAccountData)}else{Ok(())};' if mode=='inverse' else '')

def attempt(a,part,field,mode):
 text=globals()[part](field,mode);mod='NKP_lane'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,part=part,field=field,mode=mode,domain='arbitrary full prestate; level/other<20,word<8,byte<32; untouched cut requires other!=level',retired=['NKF_K064','NKF_K067'],model='NKF_LaneFactor/NKF_LaneConstructor/NKF_LaneTrace'),indent=1)+'\n')
 return submit(a,'r1_pool_adapter::'+mod+'::'+part,P,mod,text,mode)
