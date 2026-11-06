import NJT_ClaimsRef_Types
set_option autoImplicit false
noncomputable section
namespace NJT_ClaimsRef
open Aeneas Aeneas.Std Result
-- Pure std conversion, the pinned Aeneas list carrier, and same-call children.
-- No raw external template is imported.
def alloc.vec.Vec.into_boxed_slice {T : Type} (_ : Type) (v : Aeneas.Std.alloc.vec.Vec T) : Result (Slice T) := ok v

def aspis_core.field.QM31.Insts.CoreCloneClone.clone
 (q : aspis_core.field.QM31) : Result aspis_core.field.QM31 := ok q

def aspis_core.r0.heap.filled {T : Type} (copy : core.marker.Copy T) (n : Usize) (value : T) :
 Result (core.result.Result (Aeneas.Std.alloc.vec.Vec T) aspis_core.r0.Error) := do
 let out ← Aeneas.Std.alloc.vec.Vec.resize copy.cloneInst (Aeneas.Std.alloc.vec.Vec.new T) n value
 ok (.Ok out)

def r1_wire.Prefix.validated_record := AspisR1.ClaimsUnrolledFinish.sourceRecord

def r1_wire.ValidatedRecord.decode_k := AspisR1.ClaimsUnrolledFinish.sourceDecode
end NJT_ClaimsRef
end
