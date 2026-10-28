from pathlib import Path
import sys
sys.dont_write_bytecode=True
from NBP_patch_sources import added_patch,pieces
E=Path(__file__).resolve().parent
variants=['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation']
s='''static mut NBP_INDEX: usize = 0;
static mut NBP_CALLS: usize = 0;
static mut NBP_EXPECT: &str = "";
fn NBP_log(s: &str) {unsafe {
 assert!(s.len()==NBP_EXPECT.len());
 assert!(s.as_bytes()[NBP_INDEX]==NBP_EXPECT.as_bytes()[NBP_INDEX]);
 NBP_CALLS+=1;
}}
'''
for v in variants:
 s+=f'''#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(solana_program::log::sol_log, NBP_log)]
fn NBP_error_{v}() {{
 let i: usize=kani::any();kani::assume(i<{len('r1:error:'+v)});
 unsafe {{NBP_INDEX=i;NBP_CALLS=0;NBP_EXPECT="r1:error:{v}";}}
 assert!(super::error(aspis_r1_cost_probe::verifier::Error::{v})==solana_program::program_error::ProgramError::InvalidInstructionData);
 unsafe {{assert!(NBP_CALLS==1);}}
 kani::cover!(i=={len('r1:error:'+v)-1});
}}
'''
import subprocess,difflib
p='programs/r1-cost-probe/src/lib.rs';old=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
new=old+'\n#[cfg(kani)]\nmod NBP_error;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/programs/r1-cost-probe/src/NBP_error.rs'))
(E/'NBP_error.patch').write_text(patch)
for k in range(1,9):
 name=f'NBP_Decode{k}' if k<8 else 'NBP_DecodeSuccess'
 s='''import NBP_DecodeWord
set_option autoImplicit false
noncomputable section
namespace '''+name+'''
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_DecodeWord
'''
 hs='\n    '.join(f'(h{i} : word bytes {i} '+('>= P)' if i==k else '< P)') for i in range(min(k+1,8)))
 result='ok (.Err .NonCanonicalDigest)' if k<8 else 'ok (.Ok (NBG_WideBytes.limbs bytes))'
 s+=f'theorem result (bytes : Array U8 32#usize)\n    {hs} :\n    atomic_statement.decode_digest_canonical bytes = {result} := by\n'
 s+='  have len : bytes.val.length = 32 := by simpa using bytes.property\n'
 s+='  simp [word,NBG_WideBytes.word,P,len] at '+' '.join(f'h{i}' for i in range(min(k+1,8)))+'\n'
 simp=[f'not_le.mpr h{i}' if i<k else f'h{i}' for i in range(min(k+1,8))]
 s+='''  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,'''+','.join(simp)+('' if k<8 else ',NBG_WideBytes.limbs,NBG_WideBytes.word,len')+']\n'
 s+=f'#print axioms result\nend {name}\n'
 Path('lean/'+name+'.lean').write_text(s)
