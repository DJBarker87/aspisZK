from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/ports3-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(E/'current-children/Funs.lean').read_text();a=s.index('def verifier.BatchedWeights.finish_loop.body');b=s.index('/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::new::',a);body=s[a:b]
body=body.replace('verifier.BatchedWeights.value self i','value self i')
body=body.replace('core.iter.adapters.enumerate.IteratorEnumerate.next\n      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT\n      aspis_core.field.QM31) iter','ops.next iter')
body=body.replace('core.iter.traits.iterator.Iterator.enumerate.trait_default\n      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT\n      aspis_core.field.QM31) im','ops.enumerate im')
for name in ['verifier.BatchedWeights.finish_loop.body','verifier.BatchedWeights.finish_loop','verifier.BatchedWeights.finish']:
 body=body.replace('def '+name+'\n','def '+name+' (ops : Ops)\n  (value : verifier.BatchedWeights → Usize → Result aspis_core.field.QM31)\n')
body=body.replace('verifier.BatchedWeights.finish_loop.body self','verifier.BatchedWeights.finish_loop.body ops value self').replace('verifier.BatchedWeights.finish_loop iter','verifier.BatchedWeights.finish_loop ops value iter')
header='''import Port3_NativePendingPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeFlushBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev Enum := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut aspis_core.field.QM31)
structure Ops where
  next : Enum → Result (Option (Usize × aspis_core.field.QM31) × Enum ×
    (Enum → Option (Usize × aspis_core.field.QM31) → Enum))
  enumerate : core.slice.iter.IterMut aspis_core.field.QM31 →
    Result (Enum × ((Enum → Enum) → core.slice.iter.IterMut aspis_core.field.QM31))
'''
out=header+body+'\n#print axioms verifier.BatchedWeights.finish\nend AspisR1.Port3_NativeFlushBody\nend\n';(L/'Port3_NativeFlushBody.lean').write_text(out)
(E/'flush-current-emission.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'module_sha256':hashlib.sha256(out.encode()).hexdigest(),'substitutions':['Explicit local BatchedWeights.value leaf','Current mutable std next/enumerate ABI represented by typed LOCAL leaves. Existing std does not supply these signatures; native std-to-S8 lowering remains OPEN. No concrete std equality assumed.']},indent=2)+'\n')
