#!/usr/bin/env python3
from pathlib import Path
import hashlib,sys
D=Path(__file__).resolve().parent
raw=Path('docs/research/100bit-spend-path-20261013/lean-candidates/s3-s9-factored-helper-sourcecut-v2-20261021/generated/AspisR1S9FactoredCut')
def norm(s,funs=False):
 s=s.replace('AspisR1S9FactoredCut','AspisR1S9HelperP6')
 if funs:
  s=s.replace('import AspisR1S1HelperP6.Types','import AspisR1S9HelperP6.Types')
  s=s.replace('import AspisR1S9HelperP6.FunsExternal','import AspisR1S9HelperP6.ExternalSlotsV1')
 return '\n'.join(x for x in s.splitlines() if 'set_option maxHeartbeats' not in x and 'set_option maxRecDepth' not in x and 'maxHeartbeats' not in x and 'maxRecDepth' not in x)+'\n'
expected=norm((raw/'Types.lean').read_text())
actual=(D/'sources/AspisR1S9HelperP6/Types.lean').read_text()
errors=[]
if expected!=actual: errors.append('Types not exact under namespace/resource-option normalization')
f=norm((raw/'Funs.lean').read_text(),True)
# The source-emitted operation bodies are retained, but six external fail/panic
# implementations are replaced by the explicit typed operation projections.
repls=[
('''def field.QM31.mul
  (self : field.QM31) (_r : field.QM31) : Result field.QM31 := do
  fail panic''','''def field.QM31.mul
  (self : field.QM31) (r : field.QM31) : Result field.QM31 :=
  FieldOps.qmMul self r'''),
('''def field.QM31.square (self : field.QM31) : Result field.QM31 := do
  fail panic''','''def field.QM31.square (self : field.QM31) : Result field.QM31 :=
  FieldOps.qmSquare self'''),
('''def field.WideExact.add
  (self : field.WideExact) (_r : field.WideExact) :
  Result field.WideExact
  := do
  fail panic''','''def field.WideExact.add
  (self : field.WideExact) (r : field.WideExact) :
  Result field.WideExact := FieldOps.wideAdd self r'''),
('''def field.WideExact.mul
  (self : field.WideExact) (_r : field.WideExact) :
  Result field.WideExact
  := do
  fail panic''','''def field.WideExact.mul
  (self : field.WideExact) (r : field.WideExact) :
  Result field.WideExact := FieldOps.wideMul self r'''),
('''def field.WideExact.mul_m31
  (self : field.WideExact) (_r : field.M31) : Result field.WideExact := do
  fail panic''','''def field.WideExact.mul_m31
  (self : field.WideExact) (r : field.M31) : Result field.WideExact :=
  FieldOps.wideMulM31 self r'''),
('''def field.WideExact.mul_qm31
  (self : field.WideExact) (_r : field.QM31) : Result field.WideExact := do
  fail panic''','''def field.WideExact.mul_qm31
  (self : field.WideExact) (r : field.QM31) : Result field.WideExact :=
  FieldOps.wideMulQM31 self r''')]
for a,b in repls:
 if f.count(a)!=1: errors.append('expected exactly one original fail stub: '+a[:30])
 f=f.replace(a,b)
marker='namespace AspisR1S9HelperP6\n'
if f.count(marker)!=1: errors.append('namespace marker mismatch')
f=f.replace(marker,marker+'\nvariable [FieldOps]\n',1)
# Reconcile raw closure lowering with the selected FnOnce/FnMut trait ABI.
a='''  call_once :=
    weights.kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once'''
b='''  call_once := fun c i => do
    let (value, _) ←
      weights.kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once c i
    ok value'''
if f.count(a)!=1: errors.append('raw FnOnce field slot not unique')
f=f.replace(a,b)
a='''  call_mut :=
    weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut'''
b='''  call_mut := fun c i => do
    let (value, c1, back) ←
      weights.kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut c i
    ok (value, back c1)'''
if f.count(a)!=1: errors.append('raw FnMut field slot not unique')
f=f.replace(a,b)
# Resolve namespace references only through absolute, definitionally identical names.
for a,b in [
('weights.PERM','_root_.AspisR1S9HelperP6.weights.PERM'),
('weights.QUARTER','_root_.AspisR1S9HelperP6.weights.QUARTER'),
('weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact','_root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact'),
('weights.factored_s2_libra_weights_loop.body','_root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop.body'),
('weights.factored_s2_libra_weights_loop\n','_root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop\n'),
('weights.kpowers 4#usize q','_root_.AspisR1S9HelperP6.weights.kpowers 4#usize q')]: f=f.replace(a,b)
# Reverse the four name-only edits to declaration headers (not body references).
for a,b in [
('def _root_.AspisR1S9HelperP6.weights.QUARTER','def weights.QUARTER'),
('def _root_.AspisR1S9HelperP6.weights.PERM','def weights.PERM'),
('def _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop.body','def weights.factored_s2_libra_weights_loop.body'),
('def _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop\n','def weights.factored_s2_libra_weights_loop\n')]: f=f.replace(a,b)
a='let low ← weights.Weights.scalar_factor q1 ap0'
b='let low ← _root_.AspisR1S9HelperP6.weights.Weights.scalar_factor q1 ap0'
if f.count(a)!=1: errors.append('shadowed scalar_factor reference not unique')
f=f.replace(a,b)
a='''    let terms ←
      core.array.from_fn 4#usize'''
b='''    let (terms, _) ←
      core.array.from_fn 4#usize'''
if f.count(a)!=1: errors.append('generated from_fn second callsite not unique')
f=f.replace(a,b)
if f!=(D/'sources/AspisR1S9HelperP6/Funs.lean').read_text(): errors.append('Funs differs outside exact six operation slots + ABI adapters + absolute names')
ops=(D/'sources/AspisR1S9HelperP6/ExternalSlotsV1.lean').read_text()
for sig in ['qmMul :','qmSquare :','wideAdd :','wideMul :','wideMulM31 :','wideMulQM31 :','def core.array.from_fn','iterFold :']:
 if sig not in ops: errors.append('missing typed interface '+sig)
if '\naxiom ' in ops or '\naxiom ' in f: errors.append('axiom declaration found')
if 'sorry' in f or 'sorry' in ops: errors.append('sorry found')
if 'maxHeartbeats' in f or 'maxRecDepth' in f or 'maxHeartbeats' in ops or 'maxRecDepth' in ops: errors.append('resource override found')
if errors: print('\n'.join(errors));sys.exit(1)
print('PASS source checker: generated Types exact modulo namespace/options; Funs exact except six typed field slots, two Fn ABI adapters, and name qualification')
for p in sorted((D/'sources').rglob('*.lean')): print(hashlib.sha256(p.read_bytes()).hexdigest(),p.relative_to(D))
