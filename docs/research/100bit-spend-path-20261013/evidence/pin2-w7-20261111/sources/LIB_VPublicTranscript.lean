import LIB_VCode
import NHG_Lengths
import PIN2_S1SemanticCodeVerifyExactV1
/-! PIN2 W10 (2026-11-11), coordinator-approved DEFINITION CHANGE: the observed library child
`code` (the publicTranscript child of LIB_VLib.library = NNH_Libraries.VL) is the PIN2 lifted
public transcript on the frozen carriers, `S1SemanticCode.publicTranscriptPIN2` (the PIN2 call
`AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript` on the copies, result copied back),
in place of the frozen `NHG_PublicTranscript.packetCode`.  `source` and `law_exact` are restated
to `publicTranscriptPIN2`; `publicTranscript`, `eval`, `returns`, `functional` are unchanged text. -/
set_option autoImplicit false
noncomputable section
namespace LIB_VPublicTranscript
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 AspisR1PublicPreparation
def code (a : Public × RSL.B32) (env : RSL.Env) :=
 S1SemanticCode.publicTranscriptPIN2 (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2)
def publicTranscript : RSL.Child (Public × RSL.B32) (Except WErr Transcript) :=
 ⟨fun _=>True,fun a=>LIB_VCode.law LIB_VRecords.host (code a)⟩
def eval (a : Public × RSL.B32) (env : RSL.Env) : Except WErr Transcript :=
 LIB_VResult.value LIB_VRecords.host (.error .Public) (PreparedHashCode.run (code a env)).2
theorem source (a : Public × RSL.B32) (env : RSL.Env) :
 PreparedHashCode.run (code a env) = PreparedHashCode.run
 (S1SemanticCode.publicTranscriptPIN2 (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2)) :=
 rfl
theorem law_exact (a : Public × RSL.B32) (env : RSL.Env) (o : RSL.Obs (Except WErr Transcript)) :
 publicTranscript.law a env o ↔ o=LIB_VCode.obs env LIB_VRecords.host
 (PreparedHashCode.run (S1SemanticCode.publicTranscriptPIN2 (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2))) := by
 change (o=LIB_VCode.obs env LIB_VRecords.host (PreparedHashCode.run (code a env))) ↔ _
 rw [source]
theorem returns (a : Public × RSL.B32) (env : RSL.Env) :
 NND_Returned.Returns (publicTranscript.law a) env (eval a env) :=
 LIB_VResult.returns LIB_VRecords.host (Except.error .Public : Except WErr Transcript)
  (fun e=>(PreparedHashCode.run (code a e)).2)
  (fun e=>LIB_VCode.events e (PreparedHashCode.run (code a e)).1) env
theorem functional : RSL.Child.Functional publicTranscript := fun _ _ => LIB_VCode.functional _ _
#print axioms source
#print axioms law_exact
#print axioms returns
#print axioms functional
end LIB_VPublicTranscript
