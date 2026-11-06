from NLA_native import *
P="programs/r1-cost-probe/src/r1_pool_adapter.rs"
COMMON='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\nfn digest()->[M31;8]{[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())]}\nfn frontier()->[[M31;8];20]{let raw:[[u32;8];20]=kani::any();raw.map(|r|r.map(|x|M31(x)))}\n'
ANN='#[kani::proof] #[kani::unwind(35)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
FROZEN=subprocess.check_output(['git','show','4bb3b3f5:'+P],text=True)
def shape(field,mode):
 start=FROZEN.index('    let root = decode_digest_canonical(',FROZEN.index('fn decode_lane_from_pool_release'))
 end=FROZEN.index('    let mut frontier',start)
 segment=FROZEN[start:end]
 # Explicit-constructor oracle, unconstrained full reply. Coordinates are projections of the SAME call.
 call=segment.replace('decode_digest_canonical(', 'oracle(').replace('    )\n    .map_err', '      &mut log, coordinate, reply)\n    .map_err')
 text=COMMON+"""
 struct Log{calls:u8,length:usize,byte:u8}
 fn oracle(input:&[u8;32],log:&mut Log,i:usize,reply:Result<[M31;8],aspis_statement::AtomicStatementError>)->Result<[M31;8],aspis_statement::AtomicStatementError>{log.calls+=1;log.length=input.len();log.byte=input[i];reply}
 """+ANN+"""fn root_stage(){
 let tree:[u8;688]=kani::any();let coordinate:usize=kani::any();let word:usize=kani::any();kani::assume(coordinate<32&&word<8);
 let ok:bool=kani::any();let words=digest();
 let reply=if ok{Ok(words)}else{Err(aspis_statement::AtomicStatementError::NonCanonicalDigest)};
 let mut log=Log{calls:0,length:0,byte:0};let mut suffix=0u8;
 let mut result=(||->Result<[M31;8],ProgramError>{SEGMENT suffix+=1;Ok(root)})();
 CORRUPT
 let good=PROPERTY;assert!(good,"root stage exact bytes Result and prefix");
 }""".replace('SEGMENT',call)
 props=['log.calls==1&&log.length==32&&log.byte==tree[16+coordinate]', 'match result{Ok(node)=>ok&&node[word].0==words[word].0,Err(e)=>!ok&&e==ProgramError::InvalidAccountData}', 'suffix==if ok{1}else{0}']
 corrupt=['log.byte^=1;','result=if ok{Err(ProgramError::InvalidAccountData)}else{Ok(words)};','suffix^=1;']
 return text.replace('PROPERTY',props[field]).replace('CORRUPT',corrupt[field] if mode=='inverse' else ''),segment

def attempt(a,field,mode):
 text,segment=shape(field,mode);mod='NLA_lane_root'
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,segment=segment,segment_sha256=sha(segment.encode()),field=field,mode=mode,domain='arbitrary688-byte tree, coordinate<32,word<8, full canonical decoder reply type; noncanonical is its only error variant',modifies='local log, root reply and suffix counter',absolute_window='96..128; 80-byte header plus tree16..48',no_credit_until='matched negative control and SAME-call Lean composition'),indent=1)+'\n')
 return submit(a,'r1_pool_adapter::'+mod+'::root_stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 a,field,mode=sys.argv[1:];attempt(a,int(field),mode)
