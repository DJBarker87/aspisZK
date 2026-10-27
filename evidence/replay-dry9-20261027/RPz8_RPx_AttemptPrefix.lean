import RPz8_GExp_ReadPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_AttemptPrefix
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

def addresses (log : SdkC_Source.Log) : List Bytes := log.map (fun q=>flatten q.parts)

/-- Includes the failing/diverging syscall's address, unlike readLog, which
records successful answers only. Occurrence order and duplicates survive. -/
theorem transport {A : Type} (code : Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (before : SdkC_Source.Log) :
    ∃ kept remaining : List Bytes,
      addresses (SdkC_Source.run hashv code before).2=addresses before++kept ∧
      (eval H (SdkC_Oracle.program code)).1.map Prod.fst=kept++remaining := by
  induction code generalizing before with
  | done a => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
  | step r k ih => cases r with
    | ok a => exact ih a before
    | fail e => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
    | div => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
  | read parts k ih =>
    cases actual : hashv parts with
    | ok digest =>
      have decoded : decodeState digest=H (flatten parts) :=
        (syscall.returningValue parts digest actual).trans (p1.realization _)
      have encoded : encodeState (H (flatten parts))=digest := by
        rw [←decoded];exact array_roundtrip digest
      obtain ⟨kept,remaining,native,ideal⟩ := ih digest (before++[⟨parts,.ok digest⟩])
      refine ⟨flatten parts::kept,remaining,?_,?_⟩
      · simp only [SdkC_Source.run,actual]
        rw [native]
        simp only [addresses,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]
      · simp only [SdkC_Oracle.program,eval,encoded,List.map_cons,ideal,List.cons_append]
    | fail error =>
      refine ⟨[flatten parts],(eval H (SdkC_Oracle.program (k (encodeState (H (flatten parts)))))).1.map Prod.fst,?_,?_⟩
      · simp only [SdkC_Source.run,actual,addresses,List.map_append,List.map_cons,List.map_nil]
      · simp only [SdkC_Oracle.program,eval,List.map_cons,List.singleton_append]
    | div =>
      refine ⟨[flatten parts],(eval H (SdkC_Oracle.program (k (encodeState (H (flatten parts)))))).1.map Prod.fst,?_,?_⟩
      · simp only [SdkC_Source.run,actual,addresses,List.map_append,List.map_cons,List.map_nil]
      · simp only [SdkC_Oracle.program,eval,List.map_cons,List.singleton_append]

#print axioms transport
end AspisR1.RPx_AttemptPrefix
end
