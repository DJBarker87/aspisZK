"""Retained correction after build-002's dependency-cycle failure; not a rerun."""
from pathlib import Path
D=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
S=D/'base/src'
p=S/'llbc/TypesUtils.ml'
s=p.read_text()
a=s.index('(* ProverRwRngExtractor:')
b=s.index('let concat_generic_args',a)
helper=s[a:b].replace('Values.VScalar','Charon.Values.VScalar').replace('Values.SignedScalar','Charon.Values.SignedScalar')
p.write_text(s[:a]+s[b:])
p=S/'llbc/Types.ml'
p.write_text(p.read_text()+'\n'+helper)
for rel in ['llbc/TypesAnalysis.ml','symbolic/SymbolicToPureTypes.ml']:
    p=S/rel
    p.write_text(p.read_text().replace('TypesUtils.prover_rw_nonzero_i32_pattern','Types.prover_rw_nonzero_i32_pattern'))

# Never allow the new type to flow through the old generic cast/equality
# paths, whose default cases can accept types other than scalar literals.
p=S/'interp/InterpExpressions.ml'
s=p.read_text()
needle='  let v, ctx, cc = eval_operand config span op ctx in'
# Restrict edits to the symbolic unary evaluator, leaving all unrelated
# existing concrete behavior unchanged (concrete refined literals reject).
a=s.index('let eval_unary_op_symbolic ')
b=s.index('let eval_unary_op ',a)
body=s[a:b]
assert needle in body
body=body.replace(needle,needle+'''
  (match v.ty with
  | TPattern _ -> [%craise] span "ProverRwRngExtractor: refined unary/cast operation unsupported"
  | _ -> ());''',1)
s=s[:a]+body+s[b:]
a=s.index('let eval_binary_op_symbolic ')
b=s.index('let eval_binary_op ',a)
body=s[a:b]
needle='  let (v1, v2), ctx, cc = eval_two_operands config span op1 op2 ctx in'
assert needle in body
body=body.replace(needle,needle+'''
  (match (v1.ty, v2.ty) with
  | TPattern _, _ | _, TPattern _ ->
      [%craise] span "ProverRwRngExtractor: refined binary/comparison operation unsupported"
  | _ -> ());''',1)
s=s[:a]+body+s[b:]
p.write_text(s)
print('Moved recognizer below analysis layer; rejected refined cast/comparison')
