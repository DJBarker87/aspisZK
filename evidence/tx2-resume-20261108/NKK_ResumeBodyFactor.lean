import NKK_FieldStages
import NKK_RawPrefix
set_option autoImplicit false
noncomputable section
namespace NKK_ResumeBodyFactor
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def afterRoots (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize) :
 List (Array U8 32#usize) × verifier.Reader → NJU_Log.Run Event
 (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
 | ([state,a3,a4],r) => NKK_FieldStages.gamma r fun g k a0 a1 rho last=>
   queryBlockG reservation d bytes v i4 end1 state a3 a4 g k a0 a1 rho last
 | _ => liftM (Result.fail .panic)

/-- The native raw32 triple and five-field G feed the actual query
continuation. Prior state/roots and every error/abort prefix are retained. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize) :
 resumeBodyG reservation d bytes v i4 end1=
 (NKK_RawPrefix.literal 32#usize 3 {bytes,«at»:=80#usize} >>=
  afterRoots reservation d bytes v i4 end1) := by
 unfold resumeBodyG afterRoots NKK_FieldStages.gamma NKK_FieldStages.withE NKK_FieldStages.withK NKK_Try.emitted
 simp only [NKK_RawPrefix.literal,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NJU_Log.prod_cases]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NJU_Log.prod_cases])

#print axioms source
end NKK_ResumeBodyFactor
