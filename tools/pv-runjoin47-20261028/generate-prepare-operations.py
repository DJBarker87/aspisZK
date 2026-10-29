"""Keep all prepare calls and branches, exposing the three checked source inputs."""
from pathlib import Path
R=Path(__file__).resolve().parents[2]
s=(R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PrepareContext47.lean').read_text()
s=s.replace('import R1Z.PV_RunJoin_WeightConstructorInstalled47','import R1Z.PV_RunJoin_PrepareWeight47\nimport R1Z.PV_RunJoin_CoefficientsInstalled46')
s=s.replace('PV_RunJoin_PrepareContext47','PV_RunJoin_PrepareOperations47')
s=s.replace('  (constructor : Result (core.result.Result weights.Weights verifier.Error)) :','''  (coefficient_result : Result (alloc.vec.Vec (Array aspis_core.field.wide_exact.WideExact 1024#usize)))
  (constructor : Result (core.result.Result weights.Weights verifier.Error))
  (materialize : weights.Weights → aspis_core.field.wide_exact.WideExact →
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error)) :''')
s=s.replace('let coefficients ← prover.opening_coefficients variant s','let coefficients ← coefficient_result')
s=s.replace('let r1 ← weights.Weights.materialize val kappa','let r1 ← materialize val kappa')
s=s.replace('run variant hash backend sem (weights.Weights.new variant sem.alpha sem.z)','''run variant hash backend sem
        (prover.opening_coefficients variant (alloc.vec.Vec.deref backend.messages))
        (weights.Weights.new variant sem.alpha sem.z) weights.Weights.materialize''')
(R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PrepareOperations47.lean').write_text(s)
