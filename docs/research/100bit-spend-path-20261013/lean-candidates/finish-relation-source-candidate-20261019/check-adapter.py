from pathlib import Path
import re
p=Path(__file__).resolve().parent
raw=p/'raw-generated'
clean=lambda t:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',t,flags=re.M)
ops='''
/-- Universally quantified arithmetic, pairing, decoder and dot backends.
No template axioms are imported. Source candidate equivalence remains OPEN. -/
structure FinishOps (W D : Type) where
  eq : aspis_core.field.WideExact → aspis_core.field.WideExact → Result Bool
  add : aspis_core.field.WideExact → aspis_core.field.WideExact → Result aspis_core.field.WideExact
  mulM31 : aspis_core.field.WideExact → aspis_core.field.M31 → Result aspis_core.field.WideExact
  quarter : Result aspis_core.field.M31
  newWeights : transport.Variant → Array aspis_core.field.QM31 10#usize → Array aspis_core.circle.SecureCirclePoint 2#usize → Result (core.result.Result W verifier.Error)
  pair : W → Slice aspis_core.field.WideExact → Slice U8 → aspis_core.field.WideExact → Result (core.result.Result aspis_core.field.WideExact verifier.Error)
  field : Slice U8 → Usize → Result aspis_core.field.WideExact
  newDot : Result D
  pushDot : D → aspis_core.field.WideExact → aspis_core.field.QM31 → Result ((core.result.Result Unit Unit) × D)
  finishDot : D → Result aspis_core.field.WideExact
  polynomial : Slice U8 → aspis_core.field.WideExact → Result aspis_core.field.WideExact
'''
t=clean((raw/'Funs.lean').read_text()).replace('import AspisR1FinishRelationCurrent.FunsExternal\n','');t=t.replace('namespace AspisR1FinishRelationCurrent\n','namespace AspisR1FinishRelationCurrent\n'+ops,1)
name='aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact';start=t.index('impl_def '+name);end=t.index('\n}',start)+2
t=t[:start]+f'''def {name} {{W D : Type}} (ops : FinishOps W D) :
  core.cmp.PartialEq aspis_core.field.WideExact aspis_core.field.WideExact := {{
  eq := ops.eq
  ne := core.cmp.PartialEq.ne.trait_default ({name} ops)
}}'''+t[end:]
# Add explicit operation arguments only to functions that use them.
for n in ['verifier.finish_relation_round','verifier.finish_query_dot_loop.body','verifier.finish_query_dot_loop','verifier.finish_query_dot','verifier.finish_relation']:
 t=t.replace('def '+n+'\n','def '+n+'\n  {W D : Type} (ops : FinishOps W D)\n')
# Apply operations to all function calls, leaving declaration heads intact.
for n in ['verifier.finish_relation_round','verifier.finish_query_dot_loop.body','verifier.finish_query_dot_loop','verifier.finish_query_dot']:
 t=re.sub(r'(?<!def )\b'+re.escape(n)+r'(?=\s)',n+' ops',t)
# Some longer prefixes share the shorter function names; replacements require whitespace above.
t=t.replace(name+' lhs rhs','('+name+' ops) lhs rhs').replace(name+' val3','('+name+' ops) val3').replace(name+'\n                      val4','('+name+' ops)\n                      val4').replace(name+' val2','('+name+' ops) val2').replace(name+'\n                    val3','('+name+' ops)\n                    val3')
for a,b in [('aspis_core.field.WideExact.add','ops.add'),('aspis_core.field.WideExact.mul_m31','ops.mulM31'),('weights.QUARTER','ops.quarter'),('weights.Weights.new','ops.newWeights'),('weights.Weights.pair','ops.pair'),('weights.field','ops.field'),('fast_pairing.EbyKDot.new','ops.newDot'),('fast_pairing.EbyKDot.push','ops.pushDot'),('fast_pairing.EbyKDot.finish','ops.finishDot'),('verifier.polynomial','ops.polynomial')]:t=t.replace(a,b)
t=t.replace('fast_pairing.EbyKDot','D');t=t.replace('def aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact {W D : Type}',
 'impl_def aspis_core.field.WideExact.Insts.CoreCmpPartialEqWideExact {W D : Type}')
assert t==(p/'sources/FinishCandidateExplicitOps.lean').read_text()
types=clean((raw/'Types.lean').read_text()).replace('import AspisR1FinishRelationCurrent.TypesExternal\n','')
assert types==(p/'sources/AspisR1FinishRelationCurrent/Types.lean').read_text()
print('Candidate generated body preserved under explicit backend parameterization; resource settings removed')
