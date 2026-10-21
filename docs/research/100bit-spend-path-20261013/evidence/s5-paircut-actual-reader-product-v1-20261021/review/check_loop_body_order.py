#!/usr/bin/env python3
from pathlib import Path
import re
p=Path(__file__).resolve().parent.parent
g=(p.parent/'s5-paircut-transparent-field-v1-20261021/generated/AspisR1WeightsPairCut/Funs.lean').read_text() if (p.parent/'s5-paircut-transparent-field-v1-20261021/generated/AspisR1WeightsPairCut/Funs.lean').exists() else None
# Packet-local extracted body is included for portability.
g=(p/'review/AspisR1WeightsPairCut.Funs.lean').read_text()
m=(p/'review/S5PairCutLoopFoldV1.lean').read_text()
def section(t,a,b): return t[t.index(a):t.index(b,t.index(a))]
body=section(g,'def weights.push_byte_products_loop.body','def weights.push_byte_products_loop\n')
post=section(m,'def pushByteProductsPostPush','theorem callback_body_success_continue')
after=section(m,'def pushByteProductsAfterNextAt','/-- Full one-iteration body adapter.')
model=section(m,'def pushByteProductsBodyWith','theorem callback_body_success_continue')
ordered=['IteratorRange.next','weights.field f j','Slice.index_usize scratch j','fast_pairing.EbyKDot.push','Result.map_err','Result.Insts.CoreOpsTry.branch','ControlFlow.Continue','ControlFlow.Break','from_residual']
pos=-1
for token in ordered:
 q=body.find(token,pos+1); assert q>=0,('emitted operation missing/out of order',token); pos=q
assert 'weights.field f j' in body and 'weights.field' not in after
assert 'read bytes j' in after and 'Slice.index_usize scratch j' in after and 'EbyKDot.push' in after
assert 'Result.Ok ()' in post and 'Result.Err' in post and 'Parse' in post
assert 'next iter' in model and 'pushByteProductsAfterNextAt' in model
print('PASS: extracted body and parameterized skeleton preserve inspected read/index/push/error branch sequence')
print('LIMIT: structural source check only; no Lean equality between generated Funs body and manual model is proved.')
