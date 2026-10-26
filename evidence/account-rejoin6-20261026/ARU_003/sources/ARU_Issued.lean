import ARU_WrapperAccepted
import P6C_Issued
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Issued
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge MultiproofConePhysicalTransport

/-- The installed issued boundary needs only this run's successful addresses. -/
theorem derive {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (value : A) (accepted : (run hashv code []).1 = ok value)
    (agrees : ARS_QueryTransport.Agrees H (run hashv code []).2) :
    P6C_Issued.Boundary hashv H (run hashv code []).2 := by
  intro q member
  obtain ⟨digest,returned,actual⟩ := P6C_Accepted.actual_calls_ok hashv code value accepted q member
  have decoded := agrees q member digest returned
  have same : digest = rawOracle H q.parts := by
    change digest = encodeState (H (flatten q.parts))
    rw [←decoded,array_roundtrip]
  have hash := actual.trans (congrArg Result.ok same)
  refine ⟨returned.trans (congrArg Result.ok same),hash,?_,?_⟩
  · exact (S2W_DigestExtraction.digest_eq_hashv hashv () q.parts).trans hash
  · rw [digest_trace,hash,List.nil_append]

#print axioms derive
end AspisR1.ARU_Issued
end
