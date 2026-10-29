from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RunJoin_PrepareScalarContext49.lean').read_text();args=s[s.index('  (variant :'):s.index(' :\n  Result (core.result.Result prover.PreparedOpening')]
body=s[s.index('  := do\n')+len('  := do\n'):s.index('\n\n\ntheorem source')]
cut=body.index('    let a ←\n');prefix=body[:cut];suffix=body[cut:];suffix='\n'.join(line[4:] if line.startswith('    ') else line for line in suffix.splitlines())
head='''import R1Z.PV_RunJoin_PrepareScalarContext49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareClaimContinuation50
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
'''
continuation=head+'\ndef run\n'+args+'''
  (coefficients : alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize))
  (y1 : alloc.vec.Vec U8) : Result (core.result.Result prover.PreparedOpening verifier.Error) := do
'''+ '\n'.join('  '+line for line in suffix.splitlines())+'\n#print axioms run\nend R1Z.PV_RunJoin_PrepareClaimContinuation50\n'
# Reuse arguments: declaration names without structural type parsing.
call='variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail scalar'
head2=head.replace('PV_RunJoin_PrepareScalarContext49','PV_RunJoin_PrepareClaimContinuation50').replace('namespace R1Z.PV_RunJoin_PrepareClaimContinuation50','namespace R1Z.PV_RunJoin_PrepareClaimHead50')
headsource=head2+'\ndef run\n'+args+'''
  (continuation : alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize) →
    alloc.vec.Vec U8 → Result (core.result.Result prover.PreparedOpening verifier.Error)) :
  Result (core.result.Result prover.PreparedOpening verifier.Error) := do
'''+prefix+'    continuation coefficients y1\n\ntheorem source\n'+args+''' :
    PV_RunJoin_PrepareScalarContext49.run '''+call+'''=
      run '''+call+'''
        (PV_RunJoin_PrepareClaimContinuation50.run '''+call+''') := by rfl
#print axioms run
#print axioms source
end R1Z.PV_RunJoin_PrepareClaimHead50
'''
for n,b in [('PV_RunJoin_PrepareClaimContinuation50.lean',continuation),('PV_RunJoin_PrepareClaimHead50.lean',headsource)]:
 p=L/n
 if '--check' in sys.argv:assert p.read_text()==b,n
 else:p.write_text(b)
print('prepare head generator', 'checked' if '--check' in sys.argv else 'written')
