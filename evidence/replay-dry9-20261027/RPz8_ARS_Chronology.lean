import RPz8_ARS_AccountReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_Chronology
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution ARS_AccountReplay

/-- This is query-agreement transport, not collision-event transport. -/
theorem component {X Y : Type} (whole : Program Bytes State X) (part : Program Bytes State Y)
    (native H : Bytes → State) (consistent : Consistent whole native H)
    (included : ∀ address ∈ (eval native part).1.map Prod.fst,
      address ∈ (eval native whole).1.map Prod.fst) :
    eval H part = eval native part := by
  apply OracleProgramReplay.eval_eq_of_agrees native H part
  intro address member
  exact consistent address (included address member)

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (native H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval native (firstCode c hashv copy allocator id (eval native a.first).2)).2 =
      ok (.Ok (saved,post,final)))
    (consistent : Consistent (account c hashv copy allocator id a) native H)

include first consistent
/-- All four pieces of the chronology, including response-dependent second
choice, have exactly their original log and result. -/
theorem pieces :
    eval H a.first = eval native a.first ∧
    eval H (firstCode c hashv copy allocator id (eval native a.first).2) =
      eval native (firstCode c hashv copy allocator id (eval native a.first).2) ∧
    eval H (a.second (eval native a.first).2 saved post final) =
      eval native (a.second (eval native a.first).2 saved post final) ∧
    eval H (secondCode c hashv allocator id
      (eval native (a.second (eval native a.first).2 saved post final)).2) =
      eval native (secondCode c hashv allocator id
        (eval native (a.second (eval native a.first).2 saved post final)).2) := by
  have chronology := accepted_eval c hashv copy allocator id a native saved post final first
  dsimp only at chronology
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    apply component (account c hashv copy allocator id a) _ native H consistent
    intro address member
    rw [chronology]
    simp only [List.map_append,List.mem_append]
  · exact Or.inl member
  · exact Or.inr (Or.inl member)
  · exact Or.inr (Or.inr (Or.inl member))
  · exact Or.inr (Or.inr (Or.inr member))

#print axioms component
#print axioms pieces
end AspisR1.ARS_Chronology
end
