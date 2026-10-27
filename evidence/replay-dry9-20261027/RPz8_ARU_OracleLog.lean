import RPz8_ARU_Issued
import RPz8_ARS_AccountReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_OracleLog
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge

theorem coherent {X : Type} (H : Bytes → State) (p : Program Bytes State X) :
    ∀ q ∈ (eval H p).1, q.2 = H q.1 := by
  induction p with
  | done x => simp only [eval,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | ask address next ih =>
    intro q member
    rcases List.mem_cons.mp member with equal | tail
    · cases equal; rfl
    · exact ih (H address) q tail

/-- Replaying a successful ideal source program transports only the issued
native return agreement; no global oracle record is constructed. -/
theorem agrees {X : Type} (hashv : Parts → Result Digest) (native H : Bytes → State)
    (code : Code X) (value : X) (success : (run hashv code []).1 = ok value)
    (original : ARS_QueryTransport.Agrees native (run hashv code []).2)
    (same : eval H (SdkC_Oracle.program code) = eval native (SdkC_Oracle.program code)) :
    ARS_QueryTransport.Agrees H (run hashv code []).2 := by
  have exactRun := ARS_QueryTransport.accepted hashv native code value success original
  intro q member digest returned
  have read : (flatten q.parts,decodeState digest) ∈ readLog (run hashv code []).2 := by
    apply List.mem_filterMap.mpr
    exact ⟨q,member,by simp only [returned]⟩
  have logs := congrArg Prod.fst (same.trans exactRun)
  dsimp only at logs
  rw [←logs] at read
  exact coherent H _ _ read

#print axioms coherent
#print axioms agrees
end AspisR1.ARU_OracleLog
end
