import NKE_ResumeCodec
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeProgram
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def recordRaw (n : Usize) (reader : verifier.Reader) : NKE_Free.Program Event (Array U8 n × verifier.Reader) :=
 NKE_Free.record (NKE_ResumeCodec.raw n reader) (NJC_ConcreteUnwrap.raw n reader)
def recordK (reader : verifier.Reader) : NKE_Free.Program Event (core.result.Result K verifier.Error × verifier.Reader) :=
 NKE_Free.record (NKE_ResumeCodec.k reader) (NIL_FreshOps.readK reader)
def recordE (reader : verifier.Reader) : NKE_Free.Program Event (core.result.Result E verifier.Error × verifier.Reader) :=
 NKE_Free.record (NKE_ResumeCodec.e reader) (NIL_FreshOps.readE reader)
def recordSemantic (bytes : Slice U8) (cursor : Usize) : NKE_Free.Program Event (core.result.Result (Array K 10#usize × Usize) verifier.Error) :=
 NKE_Free.record (NKE_ResumeCodec.semantic bytes cursor) (NIL_FreshOps.semantic bytes cursor)
def recordWeights (bytes : Slice U8) (cursor : Usize) (weights : alloc.vec.Vec K) : NKE_Free.Program Event (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error) :=
 NKE_Free.record (NKE_ResumeCodec.weights bytes cursor weights) (NIL_FreshOps.weights bytes cursor weights)
def recordValidate (queries : Array U32 22#usize) : NKE_Free.Program Event (core.result.Result Unit verifier.Error) :=
 NKE_Free.record (NKE_ResumeCodec.validate queries) (NJC_ValidateEmission.verifier.validate_checkpoint_queries queries)
def recordFilled (r : NP6_StdModel.Reservation) (copy : core.marker.Copy K) (n : Usize) (value : K) :
 NKE_Free.Program Event (core.result.Result (alloc.vec.Vec K) aspis_core.r0.Error) :=
 NKE_Free.record (NKE_ResumeCodec.filled n value) (NIL_FreshOps.filled (NJC_FilledClause.reserved r) copy n value)
def recordAny {F : Type} (inst : core.ops.function.FnMut F U8 Bool) (it : core.slice.iter.Iter U8) (f : F) :
 NKE_Free.Program Event (Bool × core.slice.iter.Iter U8) :=
 NKE_Free.record (NKE_ResumeCodec.headerAny it) (NIL_FreshOps.any inst it f)
def recordDigest {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (chunks : Slice (Slice U8)) :
 NKE_Free.Program Event (Array U8 32#usize) :=
 NKE_Free.record (NKE_ResumeCodec.digest chunks) ((NIL_FreshOps.digest d).digest hash chunks)


end NKE_ResumeProgram
