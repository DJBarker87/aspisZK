from NGL_prepare import update,E,P
import json
I=json.loads((E/'NGL_NATIVE_INPUTS.json').read_text());s=I[P+'NGL_entry.rs']
# Only one formatting shape is launched first; a timeout requires a new split.
for bad in [False,True]:
 name='error_parse_wrong' if bad else 'error_parse'
 log='log_parse_wrong' if bad else 'log_parse'
 expected='r1:error:Semantic' if bad else 'r1:error:Parse'
 s+='\nfn '+log+'(message:&str){assert_eq!(message,"'+expected+'");}\n'
 s+='''#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(solana_program::log::sol_log,'''+log+''')]
fn '''+name+'''(){let r=error(verifier::Error::Parse);assert_eq!(r,ProgramError::InvalidInstructionData);}
'''
s+='\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
update({P+'NGL_entry.rs':s},'error_leaf')
