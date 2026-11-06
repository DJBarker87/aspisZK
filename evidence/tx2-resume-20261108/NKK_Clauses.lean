import NKK_LogClauses
import NJU_ResumeObserved
import NJZ_Readers
import NJJ_Any
set_option autoImplicit false
noncomputable section
namespace NKK_Clauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

/-- Complete returning/error/abort child replies, at each event's own arguments.
This supplies the (aq) child clauses, not a native parent certificate. -/
def Clause (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) : Event → Prop
 | .raw n reader reply => reply=NJC_ConcreteUnwrap.raw n reader
 | .k reader reply => reply=NJZ_Readers.k reader
 | .e reader reply => reply=NJZ_Readers.e reader
 | .semantic bytes cursor reply => reply=NIL_FreshOps.semantic bytes cursor
 | .weights bytes cursor before reply => reply=NIL_FreshOps.weights bytes cursor before
 | .validate queries reply => reply=NJC_ValidateEmission.verifier.validate_checkpoint_queries queries
 | .filled n value reply => reply=NIL_FreshOps.filled (NJC_FilledClause.reserved reservation)
    (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x)) n value
 | .headerAny it reply => reply= (NJJ_Any.any it)
 | .digest chunks reply => reply=(NIL_FreshOps.digest d).digest hash chunks

theorem raw (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (n : Usize) (r : verifier.Reader) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordRaw n r) := by
 apply NKK_LogClauses.record
 rfl

theorem k (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (r : verifier.Reader) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordK r) := by
 apply NKK_LogClauses.record
 exact (NJZ_Readers.k_reference r).symm

theorem e (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (r : verifier.Reader) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordE r) := by
 apply NKK_LogClauses.record
 exact (NJZ_Readers.e_reference r).symm

theorem semantic (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (bytes : Slice U8) (cursor : Usize) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordSemantic bytes cursor) := by
 apply NKK_LogClauses.record
 rfl

theorem weights (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (bytes : Slice U8) (cursor : Usize) (before : alloc.vec.Vec K) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordWeights bytes cursor before) := by
 apply NKK_LogClauses.record
 rfl

theorem validate (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (queries : Array U32 22#usize) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordValidate queries) := by
 apply NKK_LogClauses.record
 rfl

theorem filled (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (n : Usize) (value : K) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordFilled reservation (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x)) n value) := by
 apply NKK_LogClauses.record
 rfl

theorem headerAny (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (it : core.slice.iter.Iter U8) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordAny (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool (NIL_FreshOps.digest d)) it ()) := by
 apply NKK_LogClauses.record
 exact NJJ_Any.installed (NIL_FreshOps.digest d) it

theorem digest (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (chunks : Slice (Slice U8)) :
 NKK_LogClauses.Holds (Clause reservation d hash) (recordDigest d hash chunks) := by
 apply NKK_LogClauses.record
 rfl

#print axioms raw
#print axioms k
#print axioms e
#print axioms semantic
#print axioms weights
#print axioms validate
#print axioms filled
#print axioms headerAny
#print axioms digest
end NKK_Clauses
