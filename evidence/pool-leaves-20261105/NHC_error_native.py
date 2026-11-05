"""Actual frozen error conversion; exhaustive valid enum constructor domain."""
from pathlib import Path
import sys,subprocess,difflib,json,re
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';p='programs/aspis-pool/src/error.rs';src=subprocess.check_output(['git','show',rev+':'+p],text=True)
variants=re.findall(r'^    (\w+) = (0x[0-9a-fA-F_]+),',src,re.M);assert len(variants)==54
s='use super::*;\n'
s+='pub(super) fn reference(error:PoolV1ProgramError)->ProgramError{match error{'+','.join('PoolV1ProgramError::'+n+'=>ProgramError::Custom('+v+('^1' if mode=='negative' else '')+')' for n,v in variants)+'}}\n'
s+='''#[kani::proof_for_contract(<ProgramError as core::convert::From<PoolV1ProgramError>>::from)]
#[kani::unwind(2)]
fn association(){
 let choice:u8=kani::any();kani::assume(choice<54);
 let e=match choice{
'''+''.join(str(i)+'=>PoolV1ProgramError::'+n+',\n' for i,(n,v) in enumerate(variants))+'_=>unreachable!(),};\nlet r=ProgramError::from(e);assert!(r==reference(e));\n}\n'
after=src.replace('    fn from(error:', '    #[cfg_attr(kani,kani::requires(true))]\n    #[cfg_attr(kani,kani::ensures(|r| *r == NHC_ErrorConversion::reference(error)))]\n    #[cfg_attr(kani,kani::modifies())]\n    fn from(error:')+'\n#[cfg(kani)]\n#[path="NHC_ErrorConversion.rs"]\nmod NHC_ErrorConversion;\n'
patch=''.join(difflib.unified_diff(src.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NHC_ErrorConversion.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NHC_native.patch').write_text(patch);(E/'NHC_CURRENT.json').write_text(json.dumps(dict(kind='actual Pool error conversion contract',mode=mode,source=s,domain='all 54 valid PoolV1ProgramError constructors; no external preconditions',modifies=[],production_credit=False,callsite_contract_credit='requires ProgramError shape fidelity controls before use'),indent=1)+'\n')
print('error::NHC_ErrorConversion::association')
