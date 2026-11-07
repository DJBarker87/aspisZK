from pathlib import Path
import textwrap,hashlib,json
b=Path(__file__).resolve().parent
src=(b.parent/'tx2-auth-20261111/NMX_AdapterRwModel_source.txt').read_text()
s=src[src.index('def r1_pool_adapter.owned.stage2_owned '):src.index('\nend AdapterRw',src.index('def r1_pool_adapter.owned.stage2_owned '))].rstrip()
start=s.index('            let proof_start ←')
end=s.index('\n          | core.ops.control_flow.ControlFlow.Break residual =>',start)+1
after=s[start:end].rstrip()
reads_start=s.index('        let oa ← Slice.index_usize accounts 0#usize')
reads_end=s.index('\n      | core.ops.control_flow.ControlFlow.Break residual =>',reads_start)+1
reads=s[reads_start:reads_end].replace(after,'            afterReads ops val val1 val2')
head=s.replace(s[reads_start:reads_end],'        reads ops accounts val\n')
head=head.replace('def r1_pool_adapter.owned.stage2_owned (ops : Ops)','def head (ops : Ops)',1)
preamble='''import NNH_Tx2ConcreteInputs
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2Fission
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
'''
out=preamble+'''def afterReads (ops : Ops) (val : r1_pool_adapter.ValidatedAsqa) (val1 val2 : Slice U8) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
'''+textwrap.indent(textwrap.dedent(after),'  ')+'\n\n'+'''def reads (ops : Ops) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (val : r1_pool_adapter.ValidatedAsqa) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
'''+textwrap.indent(textwrap.dedent(reads),'  ')+'\n\n'+head+'''

theorem source (ops : Ops) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (clock : core.result.Result U64 solana_program_error.ProgramError) :
 r1_pool_adapter.owned.stage2_owned ops program accounts data clock=head ops program accounts data clock := by rfl
#print axioms source
end NNH_Stage2Fission
'''
(b/'NNH_Stage2Fission.lean').write_text(out)
(b/'NNH_STAGE2_FISSION_SOURCE.json').write_text(json.dumps(dict(input='evidence/tx2-auth-20261111/NMX_AdapterRwModel_source.txt',sha256=hashlib.sha256(src.encode()).hexdigest(),method='literal continuation fission; theorem rfl checks unchanged full source'),indent=1)+'\n')
