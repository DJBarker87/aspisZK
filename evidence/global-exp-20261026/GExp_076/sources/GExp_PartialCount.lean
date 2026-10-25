import GExp_CountLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_PartialCount
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

theorem attempts {A : Type} (code : Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv code before).2.length ≤
      before.length + (eval H (SdkC_Oracle.program code)).1.length := by
  induction code generalizing before with
  | done a => exact Nat.le_refl _
  | step r k ih => cases r with
    | ok a => exact ih a before
    | fail e => exact Nat.le_refl _
    | div => exact Nat.le_refl _
  | read parts k ih =>
    cases actual : hashv parts with
    | ok digest =>
      have decoded : decodeState digest = H (flatten parts) :=
        (syscall.returningValue parts digest actual).trans (p1.realization _)
      have encoded : encodeState (H (flatten parts)) = digest := by
        rw [← decoded]; exact array_roundtrip digest
      have rest := ih digest (before ++ [⟨parts,.ok digest⟩])
      simp only [SdkC_Source.run,actual,SdkC_Oracle.program,eval,encoded,
        List.length_append,List.length_singleton,List.length_cons] at rest ⊢
      omega
    | fail e =>
      simp only [SdkC_Source.run,actual,SdkC_Oracle.program,eval,
        List.length_append,List.length_singleton,List.length_cons]
      omega
    | div =>
      simp only [SdkC_Source.run,actual,SdkC_Oracle.program,eval,
        List.length_append,List.length_singleton,List.length_cons]
      omega

theorem from_count {A : Type} (code : Code A) (n : Nat) (bound : GExp_CountLaws.count n code)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv code before).2.length ≤ before.length+n :=
  (attempts code hashv sha256 H p1 syscall before).trans (Nat.add_le_add_left (bound H) _)

#print axioms attempts
#print axioms from_count
end AspisR1.GExp_PartialCount
end
