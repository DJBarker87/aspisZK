from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RunJoin_PrepareScalarContext49.lean').read_text()
a=s[s.index('  (variant :'):s.index(' :\n  Result (core.result.Result prover.PreparedOpening')]
body=s[s.index('  := do\n')+len('  := do\n'):s.index('\n\n\ntheorem source')]
head='import R1Z.PV_RunJoin_PrepareScalarContext49\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RunJoin_PrepareBatchContext50\nopen Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull\nvariable [ExternalTypes] [ExternalFuns]\n'
batch='\n  (batch : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize) →\n    aspis_core.field.wide_exact.WideExact → Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact))'
call='variant hash backend sem coefficient_result constructor materialize claim inactiveValue tail scalar'
out=head+'\ndef run\n'+a+batch+" :\n  Result (core.result.Result prover.PreparedOpening verifier.Error) := do\n"+body.replace('let q ← prover.opening_batch s3 gamma','let q ← batch s3 gamma')+'\n\ntheorem source\n'+a+" :\n    PV_RunJoin_PrepareScalarContext49.run "+call+"=\n      run "+call+" prover.opening_batch := by rfl\n#print axioms run\n#print axioms source\nend R1Z.PV_RunJoin_PrepareBatchContext50\n"
p=L/'PV_RunJoin_PrepareBatchContext50.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
print('batch context checked' if '--check' in sys.argv else 'batch context generated')
