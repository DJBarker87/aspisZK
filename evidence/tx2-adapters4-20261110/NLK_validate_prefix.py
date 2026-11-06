from NLK_native import *
P='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+P],text=True)
def attempt(a,mode):
 start=s.index('    if instruction_data.len() !=',s.index('fn validate_asq8('));end=s.index('    if request.verifier_profile',start);segment=s[start:end]
 body=segment.replace('decode_pool_v1_pair_forest_terminal_request_v1(instruction_data)','oracle(instruction_data,&mut log,coordinate,error)')
 text='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
use aspis_statement::pool_v1::PoolV1PairForestTerminalFormatErrorV1 as F;
struct Log{calls:u8,len:usize,byte:u8}
fn oracle(bytes:&[u8],log:&mut Log,i:usize,e:F)->Result<PoolV1PairForestTerminalRequestV1,F>{log.calls+=1;log.len=bytes.len();log.byte=bytes[i];Err(e)}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage(){let bytes:[u8;320]=kani::any();let length:usize=kani::any();kani::assume(length<=320);let instruction_data=&bytes[..length];let coordinate:usize=kani::any();kani::assume(coordinate<320);let which:u8=kani::any();kani::assume(which<3);let error=match which{0=>F::WrongLength,1=>F::WrongMagic,_=>F::WrongVersion};let mut log=Log{calls:0,len:0,byte:0};let mut suffix=0u8;
let out=(||->ProgramResult{BODY suffix+=1;Ok(())})();CORRUPT
assert!(out==Err(ProgramError::InvalidInstructionData)&&suffix==0&&if length==320{log.calls==1&&log.len==320&&log.byte==bytes[coordinate]}else{log.calls==0},"owned242 exact request rejection prefix and SAME received instruction bytes");}
'''.replace('BODY',body).replace('CORRUPT','suffix^=1;' if mode=='inverse' else '')
 mod='NLK_validate_prefix'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,segment=segment,segment_sha256=sha(segment.encode()),mode=mode,domain='instruction extent0..320; arbitrary byte observer; request Err arm (WrongLength/Magic/Version samples); no caller or slot access after rejection',limits='242 independent rejection cut only; no success-child/auth/scan/reconstruct closure'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::owned::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
