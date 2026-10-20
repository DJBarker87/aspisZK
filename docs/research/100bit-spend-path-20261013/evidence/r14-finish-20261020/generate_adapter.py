from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[2]
src=root/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean'
s=src.read_text()
round=s[s.index('def verifier.finish_relation_round\n'):s.index('/-- [aspis_r1_cost_probe::verifier::finish_relation]:')]
finish=s[s.index('def verifier.finish_relation\n'):s.index('/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::value]:')]
replacements={
 'weights.field':'ops.field','weights.QUARTER':'ops.quarter',
 'aspis_core.field.wide_exact.WideExact.add':'ops.add',
 'aspis_core.field.wide_exact.WideExact.mul_m31':'ops.mulM',
 'core.cmp.PartialEq.ne.trait_default\n      aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact':'ops.ne',
 'verifier.polynomial':'ops.polynomial','trace.value':'ops.trace',
 'verifier.finish_relation_round':'verifier.finishRelationRoundWithOps',
 'transport.Variant.folds':'ops.folds','weights.Weights.new':'ops.newWeights',
 'weights.Weights.pair':'ops.pair','verifier.mark':'ops.mark',
 'verifier.finish_query_dot':'ops.dot',
}
for old,new in replacements.items():
 round=round.replace(old,new); finish=finish.replace(old,new)
# The deeper indentation of the two duplicated comparisons is preserved.
import re
finish=re.sub(r'core.cmp.PartialEq.ne.trait_default\s+aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact','ops.ne',finish)
round=round.replace('def verifier.finishRelationRoundWithOps\n','def verifier.finishRelationRoundWithOps (ops : FinishOps W)\n')
finish=finish.replace('def verifier.finish_relation\n','def verifier.finishRelationWithOps (ops : FinishOps W)\n')
finish=finish.replace('verifier.finishRelationRoundWithOps v.', 'verifier.finishRelationRoundWithOps ops v.')
header='''import Stage2ContinuationTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
namespace Stage2Finish
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev K := aspis_core.field.QM31
abbrev M := aspis_core.field.M31
/-- Typed backend frontiers of the emitted finish, not correctness axioms. -/
structure FinishOps (W : Type) where
  field : Slice U8 → Usize → Result E
  quarter : Result M
  add : E → E → Result E
  mulM : E → M → Result E
  ne : E → E → Result Bool
  polynomial : Slice U8 → E → Result E
  trace : U16 → Usize → E → Result Unit
  folds : transport.Variant → Result Usize
  newWeights : transport.Variant → Array K 10#usize → Array aspis_core.circle.SecureCirclePoint 2#usize → Result (core.result.Result W verifier.Error)
  pair : W → Slice E → Slice U8 → E → Result (core.result.Result E verifier.Error)
  mark : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit
  dot : Slice U8 → Slice K → Result (core.result.Result E verifier.Error)
variable {W : Type}
'''
# namespaces remain nested; generated names resolve there
out=header+round+finish+'\nend Stage2Finish\nend AspisR1Stage2\n'
target=root/'lean/Stage2FinishBody.lean'
import sys
if '--check' in sys.argv:
 assert target.read_text()==out
else: target.write_text(out)
print(json.dumps({'generated_source':str(src.relative_to(root)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'adapter':str(target.relative_to(root)),'adapter_sha256':hashlib.sha256(out.encode()).hexdigest(),'check':'exact emitted bodies with listed typed callee substitution','replacements':replacements},indent=2))
