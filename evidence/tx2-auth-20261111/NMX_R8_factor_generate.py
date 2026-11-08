from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
s=(E/'NMX_R8_Code241.lean').read_text();body=s[s.index('def body '):s.index('\nend NMX_R8_Code241')]
start=body.index('                  let s1 ←');stop=body.index('\n                | core.ops.control_flow.ControlFlow.Break residual',start)+1
enc=body[start:stop];body=body[:start]+'                  afterEncode ops effects val val1 val2 proof_start val3 val4\n'+body[stop:]
start=body.index('            let proof_start ←');stop=body.index('\n          | core.ops.control_flow.ControlFlow.Break residual',start)+1
reads=body[start:stop];body=body[:start]+'            afterReads ops effects val val1 val2\n'+body[stop:]
start=body.index('        let oa ←');stop=body.index('\n      | core.ops.control_flow.ControlFlow.Break residual',start)+1
after=body[start:stop];body=body[:start]+'        afterValidate ops effects val accounts\n'+body[stop:]
body=body.replace('def body ','def head ')
header='''import NMX_R8_Code241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_Factor241
open Aeneas Aeneas.Std Result AdapterRw NMX_R8_Code241
variable {M : Type → Type} [Monad M] [MonadLift Result M]
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError
'''
def dedent(s,n):return '\n'.join(l[n:] if l.strip() else '' for l in s.splitlines())+'\n'
code=header+'''def afterEncode (ops : Ops) (effects : Effects M)
 (val : r1_pool_adapter.ValidatedAsqa) (val1 val2 : Slice U8)
 (proof_start val3 : Usize) (val4 : Array U8 1880#usize) : M Reply := do
'''+dedent(enc,17)+'''\ndef afterReads (ops : Ops) (effects : Effects M)
 (val : r1_pool_adapter.ValidatedAsqa) (val1 val2 : Slice U8) : M Reply := do
'''+dedent(reads,11)+'''\ndef afterValidate (ops : Ops) (effects : Effects M)
 (val : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) : M Reply := do
'''+dedent(after,7)+'\n'+body+'''

theorem source (ops : Ops) (effects : Effects M)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 head ops effects p accounts data slot = NMX_R8_Code241.body ops effects p accounts data slot := by
 unfold head afterValidate afterReads afterEncode NMX_R8_Code241.body
 rfl
#print axioms source
end NMX_R8_Factor241
end
'''
(E/'NMX_R8_Factor241.lean').write_text(code)
(E/'NMX_R8_FACTOR_SOURCE.json').write_text(json.dumps(dict(source='NMX_R8_Code241.lean',source_sha256=hashlib.sha256(s.encode()).hexdigest(),destination_sha256=hashlib.sha256(code.encode()).hexdigest(),changes='Only named continuation slices, literal source expressions/control unchanged; kernel source equality required'),indent=1)+'\n')
