from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/ports3-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(E/'current-children/Funs.lean').read_text()
a=s.index('def verifier.BatchedWeights.new_loop.body');b=s.index('/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}',a)
blocks=s[a:b];blocks=blocks[:blocks.rfind('\n\n')]
# Replace only declaration names and the explicit allocator/error-map leaves.
for old,new in [('verifier.BatchedWeights.new_loop.body','body'),('verifier.BatchedWeights.new_loop','run'),('verifier.BatchedWeights.new.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError','allocationError')]:blocks=blocks.replace(old,new)
start=blocks.index('def verifier.BatchedWeights.new\n');loop=blocks[:start];ctor=blocks[start:]
ctor=ctor.replace('def verifier.BatchedWeights.new\n','def extracted {AllocError : Type}\n  (filled : Usize → Row → Result (core.result.Result (alloc.vec.Vec Row) AllocError))\n')
ctor=re.sub(r'aspis_core.r0.heap.filled\s*\(Array.Insts.CoreMarkerCopy 4#usize\s*core.marker.CopyU64\)', 'filled',ctor)
ctor=ctor.replace('core.result.Result.map_err','Port3_Constructor.core.result.Result.map_err')
header='''import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativePendingBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev Row := Array U64 4#usize

def allocationError {AllocError : Type} : core.ops.function.FnOnce Unit AllocError verifier.Error :=
  ⟨fun _ _ => ok .Allocation⟩

'''
source=header+loop+ctor+'''
end AspisR1.Port3_NativePendingBody
end
'''
(L/'Port3_NativePendingBody.lean').write_text(source)
(E/'pending-current-emission.json').write_text(json.dumps({'generated_funs_sha256':hashlib.sha256(s.encode()).hexdigest(),'module_sha256':hashlib.sha256(source.encode()).hexdigest(),'source':'current-children/Funs.lean','allocation':'Fixed emitted Array Copy token is bound by the filled leaf; allocator error carrier is a type parameter, consumed only by the emitted Allocation map_err. No type template or axiom is imported.','substitutions':['new_loop.body -> body','new_loop -> run','new -> extracted(filled)','allocation closure -> allocationError','map_err -> existing fully generic emitted map_err']},indent=2)+'\n')
