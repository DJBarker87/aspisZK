import SdkC_Oracle
import RPx_AttemptPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_OracleCoverage
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- Exact reached-read condition for total-oracle representation. Pure
rejection and divergence are allowed, but an oracle read must return the
oracle's value. This is a proof obligation, not an adopted runtime law. -/
def Covered {A : Type} (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) : Code A → Prop
  | .done _ => True
  | .step r k => match r with
    | .ok x => Covered H hashv (k x)
    | _ => True
  | .read parts k => hashv parts = .ok (encodeState (H (flatten parts))) ∧
      Covered H hashv (k (encodeState (H (flatten parts))))

theorem exact {A : Type} (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (code : Code A)
    (covered : Covered H hashv code) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv code before).1 = (eval H (SdkC_Oracle.program code)).2 ∧
    SdkC_Source.readLog (SdkC_Source.run hashv code before).2 =
      SdkC_Source.readLog before ++ (eval H (SdkC_Oracle.program code)).1 ∧
    RPx_AttemptPrefix.addresses (SdkC_Source.run hashv code before).2 =
      RPx_AttemptPrefix.addresses before ++ (eval H (SdkC_Oracle.program code)).1.map Prod.fst := by
  induction code generalizing before with
  | done x => exact ⟨rfl,(List.append_nil _).symm,(List.append_nil _).symm⟩
  | step r k ih =>
    cases r with
    | ok x => exact ih x covered before
    | fail e => exact ⟨rfl,(List.append_nil _).symm,(List.append_nil _).symm⟩
    | div => exact ⟨rfl,(List.append_nil _).symm,(List.append_nil _).symm⟩
  | read parts k ih =>
    obtain ⟨answer,next⟩ := covered
    obtain ⟨result,reads,attempts⟩ := ih _ next
      (before ++ [⟨parts,.ok (encodeState (H (flatten parts)))⟩])
    simp only [SdkC_Source.run,answer,SdkC_Oracle.program,eval]
    refine ⟨result,?_,?_⟩
    · rw [reads,SdkC_Oracle.readLog_append]
      simp only [SdkC_Source.readLog,List.filterMap_cons,List.filterMap_nil,decode_encode,
        List.append_assoc,List.singleton_append]
    · rw [attempts]
      simp only [RPx_AttemptPrefix.addresses,List.map_append,List.map_cons,List.map_nil,
        List.append_assoc,List.singleton_append]

/-- The literal digest helper's original result is represented in H iff its
one syscall returns precisely H's answer. Includes the original error outcome. -/
theorem digest_iff (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (parts : SdkC_Source.Parts) :
    (SdkC_Source.run hashv (SdkC_Source.digestCode parts) []).1 =
      (eval H (SdkC_Oracle.program (SdkC_Source.digestCode parts))).2 ↔
    hashv parts = .ok (encodeState (H (flatten parts))) := by
  rw [SdkC_Source.digest_trace]
  simp only [SdkC_Source.digestCode,SdkC_Oracle.program,eval,S2W_DigestExtraction.toBytes]

#print axioms exact
#print axioms digest_iff
end AspisR1.ARR_OracleCoverage
end
