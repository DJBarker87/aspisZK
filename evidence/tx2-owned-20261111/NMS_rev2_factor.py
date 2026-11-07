"""Factor one finite suffix, retaining exact source text for rfl checking."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
text=(E/'NMS_R2N_242Code.lean').read_text()
body=text[text.index('def body '):text.index('\ntheorem emitted')]
start=body.index('                  let o ← effects.op9 accounts')
end=re.search(r'^ {16}\| core.ops.control_flow.ControlFlow.Break residual',body[start:],re.M).start()+start
fragment=body[start:end]
# Last source line belongs to cf4, tail contains cf5/cf6/cf7 intact.
fragment='\n'.join(line[18:] if line.startswith(' '*18) else line for line in fragment.rstrip().splitlines())
fragment=re.sub(r'\bval3\b','authenticated',fragment)
fragment=re.sub(r'\bval\b','request',fragment)
newbody=body[:start]+'                  afterAuth effects val val3 accounts\n'+body[end:]
newbody=newbody.replace('def body ','def prefixBody ',1)
header='''import NMS_R2N_242Code
import NMS_R2N_RawTry
set_option autoImplicit false
noncomputable section
namespace NMS_R2Code242Factor
open Aeneas Aeneas.Std Result AdapterRw
open NMS_Effect242 (Effects AuthCall)
'''
source=header+'''def afterAuth (effects : Effects RSL.Spec)
 (request : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1)
 (authenticated : r1_pool_adapter.AuthenticatedAsq8Accounts)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 RSL.Spec (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError) := do
'''+''.join(' '+l+'\n' for l in fragment.splitlines())+'\n'+newbody.replace('Effects M','Effects RSL.Spec').replace('AuthCall M','AuthCall RSL.Spec').replace('  M (core.result','  RSL.Spec (core.result')+'''

theorem source (effects : Effects RSL.Spec) (auth : AuthCall RSL.Spec)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 prefixBody effects auth program accounts data slot =
 NMS_R2N_242Code.body effects auth program accounts data slot := rfl
#print axioms source
end NMS_R2Code242Factor
'''
(E/'NMS_R2Code242Factor.lean').write_text(source)
(E/'NMS_R2_FACTOR_PROVENANCE.json').write_text(json.dumps(dict(input='NMS_R2N_242Code.lean',sha256=hashlib.sha256(text.encode()).hexdigest(),replacement='single after-authenticate suffix factored definitionally; source theorem rfl'),indent=2)+'\n')
