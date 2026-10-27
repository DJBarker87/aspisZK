import RPz8_ARS_QueryTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_QueryPrefix
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

open RPx_AttemptPrefix

/- Only successful answers issued in THIS partial run are constrained.
Unlike the old export this requires neither global P1 nor global RuntimeSyscall.
A failed final attempt is retained, with no invented source continuation. -/

/-- Includes the failing/diverging syscall's address, unlike readLog, which
records successful answers only. Occurrence order and duplicates survive. -/
theorem transport {A : Type} (code : Code A)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H : Bytes → State) (before : SdkC_Source.Log)
    (agrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv code before).2) :
    ∃ kept remaining : List Bytes,
      addresses (SdkC_Source.run hashv code before).2=addresses before++kept ∧
      (eval H (SdkC_Oracle.program code)).1.map Prod.fst=kept++remaining := by
  induction code generalizing before with
  | done a => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
  | step r k ih => cases r with
    | ok a => exact ih a before agrees
    | fail e => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
    | div => exact ⟨[],[],(List.append_nil _).symm,rfl⟩
  | read parts k ih =>
    cases actual : hashv parts with
    | ok digest =>
      have decoded : decodeState digest=H (flatten parts) :=
        by
          apply agrees ⟨parts,.ok digest⟩ ?_ digest rfl
          obtain ⟨suffix,layout⟩ := SdkC_Source.prefix_preserved hashv (k digest) (before++[⟨parts,.ok digest⟩])
          simp only [SdkC_Source.run,actual]
          rw [layout]
          exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
      have encoded : encodeState (H (flatten parts))=digest := by
        rw [←decoded];exact array_roundtrip digest
      obtain ⟨kept,remaining,native,ideal⟩ := ih digest (before++[⟨parts,.ok digest⟩])
        (by simpa only [SdkC_Source.run,actual] using agrees)
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
end AspisR1.BEk_QueryPrefix
end
