import ART_AccountChronology
import ARS_Chronology
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_QueriedPieces
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment ARS_NativeAccount ART_PartialAccount

theorem chronology {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native H : Bytes → State) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval native (wrapper hashv (firstSyntax c hashv copy allocator id (eval native a.first).2))).2 =
      ok (.Ok (saved,post,final)))
    (consistent : ARS_AccountReplay.Consistent (ART_PartialAccount.account c hashv copy allocator id a) native H) :
    eval H a.first = eval native a.first ∧
    eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval native a.first).2)) =
      eval native (wrapper hashv (firstSyntax c hashv copy allocator id (eval native a.first).2)) ∧
    eval H (a.second (eval native a.first).2 saved post final) =
      eval native (a.second (eval native a.first).2 saved post final) ∧
    eval H (wrapper hashv (secondSyntax c hashv allocator id
      (eval native (a.second (eval native a.first).2 saved post final)).2)) =
      eval native (wrapper hashv (secondSyntax c hashv allocator id
        (eval native (a.second (eval native a.first).2 saved post final)).2)) := by
  have original := ART_AccountChronology.first_ok c hashv copy allocator id a native saved post final first
  dsimp only at original
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    apply ARS_Chronology.component (ART_PartialAccount.account c hashv copy allocator id a) _ native H consistent
    intro address member
    rw [original]
    simp only [List.map_append,List.mem_append]
  · exact Or.inl member
  · exact Or.inr (Or.inl member)
  · exact Or.inr (Or.inr (Or.inl member))
  · exact Or.inr (Or.inr (Or.inr member))

#print axioms chronology
end AspisR1.ART_QueriedPieces
end
