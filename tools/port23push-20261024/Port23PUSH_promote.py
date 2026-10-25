#!/usr/bin/env python3
"""Checkable header/carrier adaptation; external primitive remains explicit."""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/port23push-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
t=(E/'Port23PUSH-generated/Types.lean.txt').read_text();f=(E/'Port23PUSH-generated/Funs.lean.txt').read_text()
t=t[t.index('namespace Port23PUSH'):t.rindex('end Port23PUSH')]
f=f[f.index('namespace Port23PUSH')+len('namespace Port23PUSH'):f.rindex('end Port23PUSH')]
needle='MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter\n        row1'
assert f.count(needle)==1
f=f.replace(needle,'arrayIntoIter row1')
f=f.replace('def verifier.update_residue_row\n','def verifier.update_residue_row (arrayIntoIter : ArrayIntoIter)\n')
f=f.replace('def verifier.BatchedWeights.push\n','def verifier.BatchedWeights.push (arrayIntoIter : ArrayIntoIter)\n')
f=f.replace('verifier.update_residue_row a power','verifier.update_residue_row arrayIntoIter a power')
f=f.replace('def verifier.Port23PUSH_push\n','def verifier.Port23PUSH_push (arrayIntoIter : ArrayIntoIter)\n')
f=f.replace('verifier.BatchedWeights.push b index','verifier.BatchedWeights.push arrayIntoIter b index')
# Every emitted definition body retained except the ONE explicitly exposed
# external constant and corresponding threaded parameter at the two callers.
header='''import Aeneas
import Aeneas.Std.RangeIter
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow Error
'''
alias='''
/-- Uninterpreted missing external ABI, not a trust field or equality premise. -/
abbrev ArrayIntoIter := Array U64 4#usize →
  Result (core.slice.iter.IterMut U64 × ((core.slice.iter.IterMut U64 → core.slice.iter.IterMut U64) → Array U64 4#usize))
'''
content=header+t+alias+f+'\nend Port23PUSH\nend\n'
if '--check' in sys.argv:
 assert (L/'Port23PUSH_Source.lean').read_text()==content, 'promotion drift'
 print('exact declaration adaptation matches')
 sys.exit(0)
(L/'Port23PUSH_Source.lean').write_text(content)
p=L/'Port23PUSH_Source.lean'
(E/'promotion.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),adaptation='headers/imports; generated external template ABI mismatches caller, explicit parameter uses caller-required transformer ABI; external arrayIntoIter made explicit and threaded through exactly update/push/free root; no external axiom compiled',source_claim='parametric source-emitted semantics, no native primitive instance or effects established'),indent=2)+'\n')
