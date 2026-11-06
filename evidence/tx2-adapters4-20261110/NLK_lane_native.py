from NLK_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
FROZEN=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+P],text=True)
COMMON='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
ANN='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
def attempt(a,part,mode):
 if part=='layout':
  segment='core::mem::size_of::<PoolV1PairForestLaneStateV1>()'
  text=COMMON+ANN+'fn stage(){ let mut size='+segment+'; '+('size+=1;' if mode=='inverse' else '')+' assert!(size==720 && core::mem::align_of::<PoolV1PairForestLaneStateV1>()==8,"complete lane allocation layout"); }'
 elif part=='prefix':
  start=FROZEN.index('    let master:',FROZEN.index('fn decode_lane_from_pool_release'))
  end=FROZEN.index('    let root =',start);segment=FROZEN[start:end]
  text=COMMON+ANN+'''fn stage(){let bytes:[u8;768]=kani::any();let coordinate:usize=kani::any();kani::assume(coordinate<32);let mut suffix=0u8;
 let mut out=(||->Result<([u8;32],u64),ProgramError>{ SEGMENT suffix+=1;Ok((master,next_leaf_index))})(); CORRUPT
 let mut master=[0u8;32];for j in 0..32 {master[j]=bytes[40+j];}
 let next=u64::from_le_bytes([bytes[88],bytes[89],bytes[90],bytes[91],bytes[92],bytes[93],bytes[94],bytes[95]]);
 let valid=master!=[0u8;32]&&bytes[80..84]==POOL_V1_TREE_STATE_MAGIC&&bytes[84]==POOL_V1_TREE_STATE_VERSION&&bytes[85]==POOL_V1_PAIR_TREE_DEPTH as u8&&bytes[86]==POOL_V1_TREE_HASH_VERSION&&bytes[87]==POOL_V1_DIGEST_ENCODING_VERSION&&next<=POOL_V1_PAIR_CAPACITY;
 let good=match out {Ok((m,n))=>valid&&m[coordinate]==bytes[40+coordinate]&&n==next,Err(e)=>!valid&&e==ProgramError::InvalidAccountData};
 assert!(good&&suffix==if valid{1}else{0},"complete pre-root source prefix Result values and no-suffix");}
 '''.replace('SEGMENT',segment).replace('CORRUPT','out=Err(ProgramError::InvalidArgument);' if mode=='inverse' else '')
 else:raise ValueError(part)
 mod='NLK_lane'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(part=part,source=P,segment=segment,segment_sha256=sha(segment.encode()),mode=mode,modifies='only local output/suffix; input unchanged',limits='local named cut only; no complete row credit'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
