import NKE_ResumeClausesTactic
import NKE_ResumeClauses5
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeClauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
theorem run  (reservation : NP6_StdModel.Reservation)
  {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
  (bytes : Slice Std.U8) (proof : Slice Std.U8) (public1 : Slice Std.U8)
  (v : transport.Variant) (hash : H)  :
 NKE_EventAll.Holds Clause (NJU_ResumeObserved.run reservation d bytes proof public1 v hash) := by
 simp only [NJU_ResumeObserved.run,NJU_Log.prod_cases,NJU_ResumeObserved.recordRaw,NJU_ResumeObserved.recordK,NJU_ResumeObserved.recordE,NJU_ResumeObserved.recordSemantic,NJU_ResumeObserved.recordWeights,NJU_ResumeObserved.recordValidate,NJU_ResumeObserved.recordFilled,NJU_ResumeObserved.recordAny,NJU_ResumeObserved.recordDigest]
 repeat' first
 | nke_zeta
 | nke_bind
 | nke_intro
 | nke_lift
 | nke_pure
 | nke_resume_record
 | nke_resume_tail
 | split
#print axioms run
end NKE_ResumeClauses
