#!/usr/bin/env python3
"""Keep the three entire emitted loop definitions, parameterizing only query_values."""
from pathlib import Path
import re,json,hashlib,sys
B=Path(__file__).resolve().parents[3];E=B/'evidence/stage2-continuation-20261020'
s=(E/'generated/AspisR1Stage2/Funs.lean').read_text();parts=[]
for name in ['verifier.candidate.query_loop_loop.body','verifier.candidate.query_loop_loop','verifier.candidate.query_loop']:
 a=s.index('def '+name+'\n');z=s.index('\n/--',a);parts.append(s[a:z])
original='\n\n'.join(parts);body=original
for name in ['verifier.candidate.query_loop_loop.body','verifier.candidate.query_loop_loop','verifier.candidate.query_loop']:
 body=body.replace('def '+name+'\n','def '+name+'\n  (call : QueryCall)\n',1)
body=body.replace('verifier.candidate.query_values proof p a g obs geometry pending','call proof p a g obs geometry pending')
body=body.replace('=> verifier.candidate.query_loop_loop.body proof', '=> verifier.candidate.query_loop_loop.body call proof')
body=body.replace('verifier.candidate.query_loop_loop (core.result.Result.Ok', 'verifier.candidate.query_loop_loop call (core.result.Result.Ok')
header='''import Stage2ContinuationTypes
import Stage2ContinuationOwnedLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
abbrev QueryCall := Slice U8 → verifier.Prepared → verifier.Accumulator →
  Array aspis_core.field.wide_exact.WideExact 29#usize →
  Option (verifier.Phase → Result Unit) → verifier.QueryGeometry →
  verifier.BatchedWeights → Result (core.result.Result
    (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
'''
target=B/'lean/Stage2ContinuationQueryLoop.lean'
expected=header+body+'\nend AspisR1Stage2\n'
if '--check' in sys.argv:assert target.read_text().startswith(expected),'emitted loop bodies changed'
else:target.write_text(expected)
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
(E/'proofs/query-loop-binding.json').write_text(json.dumps(dict(entire_three_definitions=True,generated_bodies_sha256=sha(original),parameterized_bodies_sha256=sha(body),only_callee_parameterized='verifier.candidate.query_values',scope='Actual emitted types and full loop/control-flow bodies; query operation universally quantified'),indent=2)+'\n')
