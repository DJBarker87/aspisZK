from NLK_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
FROZEN=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+P],text=True)
start=FROZEN.index('fn decode_lane_from_pool_release(');end=FROZEN.index('\n#[inline(never)]',start)
ORIGINAL=FROZEN[start:end]
COMMON='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
ANN='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
HELP='''
fn digest()->[M31;8]{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}
struct State{root:Result<[M31;8],aspis_statement::AtomicStatementError>,loop_ok:bool,frontier:[[M31;8];20],root_calls:u8,loop_calls:u8,allocated:usize,input_byte:u8,coordinate:usize,next:u64}
fn root(input:&[u8;32],s:&mut State)->Result<[M31;8],aspis_statement::AtomicStatementError>{s.root_calls+=1;s.input_byte=input[s.coordinate];s.root}
fn loop_summary(_tree:&[u8],next:u64,s:&mut State)->Result<[[M31;8];20],ProgramError>{s.loop_calls+=1;s.next=next;if s.loop_ok{Ok(s.frontier)}else{Err(ProgramError::InvalidAccountData)}}
'''
def attempt(a,field,mode):
 body=ORIGINAL.replace('fn decode_lane_from_pool_release(','fn invocation(').replace('    bytes: &[u8],','    bytes: &[u8],s:&mut State,')
 rstart=body.index('    let root = decode_digest_canonical(');rend=body.index('    let mut frontier',rstart)
 rootseg=body[rstart:rend];rootnew=rootseg.replace('decode_digest_canonical(', 'root(').replace('    )\n    .map_err','    s)\n    .map_err')
 body=body[:rstart]+rootnew+body[rend:]
 lstart=body.index('    let mut frontier');lend=body.index('    if next_leaf_index == 0',lstart)
 loopseg=body[lstart:lend]
 body=body[:lstart]+'    let frontier=loop_summary(tree,next_leaf_index,s)?;\n'+body[lend:]
 old='    Ok(Box::new(PoolV1PairForestLaneStateV1 {'
 body=body.replace(old,'    let boxed=Box::new(PoolV1PairForestLaneStateV1 {')
 body=body.replace('    }))\n}', '    });\n    s.allocated=(&*boxed as *const PoolV1PairForestLaneStateV1) as usize;\n    Ok(boxed)\n}')
 text=COMMON+HELP+body+ANN+'''fn stage(){
 let bytes:[u8;768]=kani::any();let length:usize=kani::any();kani::assume(length<=768);let input=&bytes[..length];
 let coordinate:usize=kani::any();let word:usize=kani::any();let level:usize=kani::any();kani::assume(coordinate<32&&word<8&&level<20);
 let root_ok:bool=kani::any();let root_words=digest();let loop_ok:bool=kani::any();let raw:[[u32;8];20]=kani::any();let frontier=raw.map(|r|r.map(M31));
 let mut state=State{root:if root_ok{Ok(root_words)}else{Err(aspis_statement::AtomicStatementError::NonCanonicalDigest)},loop_ok,frontier,root_calls:0,loop_calls:0,allocated:0,input_byte:0,coordinate,next:0};
 let out=invocation(input,&mut state);
 let header=length==768&&bytes[..4]==POOL_V1_PAIR_FOREST_LANE_MAGIC&&bytes[4]==POOL_V1_PAIR_FOREST_LANE_VERSION&&usize::from(bytes[5])<POOL_V1_PAIR_FOREST_LANE_COUNT&&bytes[6]==POOL_V1_PAIR_FOREST_LANE_COUNT as u8&&bytes[7]==POOL_V1_PAIR_TREE_DEPTH as u8&&bytes[8..40]==POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING&&bytes[73..80].iter().all(|b|*b==0);
 let mut master=[0u8;32];for j in 0..32{master[j]=bytes[40+j];}
 let next=u64::from_le_bytes([bytes[88],bytes[89],bytes[90],bytes[91],bytes[92],bytes[93],bytes[94],bytes[95]]);
 let prefix=header&&master!=[0u8;32]&&bytes[80..84]==POOL_V1_TREE_STATE_MAGIC&&bytes[84]==POOL_V1_TREE_STATE_VERSION&&bytes[85]==POOL_V1_PAIR_TREE_DEPTH as u8&&bytes[86]==POOL_V1_TREE_HASH_VERSION&&bytes[87]==POOL_V1_DIGEST_ENCODING_VERSION&&next<=POOL_V1_PAIR_CAPACITY;
 let accepted=prefix&&root_ok&&loop_ok&&(next!=0||root_words==v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS[20]);
 let mut observed=match out.as_ref(){Ok(v)=>FIELD,Err(_)=>true};CORRUPT
 assert!(PROPERTY,"complete lane invocation source-prefix loop-summary allocation-site and returned-carrier window");
}
'''
 fields={'scalar':'v.bump==bytes[72]&&v.lane_id==bytes[5]&&v.tree.next_leaf_index==next&&v.master[coordinate]==bytes[40+coordinate]', 'root':'v.tree.root[word].0==root_words[word].0','frontier':'v.tree.frontier[level][word].0==raw[level][word]','owner':'(&**v as *const PoolV1PairForestLaneStateV1) as usize==state.allocated'}
 props={'scalar':'observed&&out.is_ok()==accepted&&match out{Err(e)=>e==ProgramError::InvalidAccountData,Ok(_)=>true}', 'root':'observed&&state.root_calls==if prefix{1}else{0}&&if prefix{state.input_byte==bytes[96+coordinate]}else{true}', 'frontier':'observed&&state.loop_calls==if prefix&&root_ok{1}else{0}&&if prefix&&root_ok{state.next==next}else{true}', 'owner':'observed&&(state.allocated!=0)==accepted'}
 text=text.replace('FIELD',fields[field]).replace('PROPERTY',props[field]).replace('CORRUPT','observed=false;' if mode=='inverse' else '')
 mod='NLK_lane_invocation'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,frozen_function_sha256=sha(ORIGINAL.encode()),source_function=ORIGINAL,field=field,mode=mode,root_segment=rootseg,loop_segment=loopseg,loop_rule='rule B: loop_summary is paired with NKP_LaneInduction.compose/NLA_LaneAssemble.source_steps; no whole native loop credit',domain='arbitrary input extent0..768, all byte contents and full typed root/loop replies; arbitrary field coordinate; returning allocator only native, universal Reservation in Lean',limits='cut requires SAME-byte CLOSED decoder and concrete loop law; allocator partiality is NOT asserted by native returning Box'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
