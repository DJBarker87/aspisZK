import RPz7_CPG_Game
import RPz7_Hir_ReaderEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPG_Accepted
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPG_Game CPP_BankState Hist_RuntimeEntry MultiproofConeCanonical

variable {Tx A F C : Type} (p : Observations Tx A) (t u : Tx)
    (e1 e2 : Entry) (saved : alloc.vec.Vec U8) (actions : List (Action A))
    (c : DrvC_Installation.Configuration F C)
    (keyLaw : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id system : S2W_ExtractionBoundary.Program) (notSystem : id ≠ system)
    (game : DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 final2 : A) (post1 post2 : Heap (Nat → Record))

include game extraction std

theorem writer_positive
    (accepted : first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1))) :
    0 < (p.bank t).lamports ((p.layout t).handles 2).1 := by
  have native := (first_accepted n1 copy std allocator e1 id data1 state1 final1 saved post1 accepted).1
  have source := (extraction.stage1 id e1.first data1).symm.trans native
  have size := checkpoint_size e1 (DrvC_Installation.sdk c) id data1 saved source
  rw [game.consecutive.2.1] at size
  change ((entry p t).buffers ((p.layout t).handles 2).1).val.length = 1768 at size
  by_contra bad
  have zero : (p.bank t).lamports ((p.layout t).handles 2).1 = 0 := by omega
  rw [CPG_Projection.dead p t _ zero] at size
  simp only [List.length_nil] at size
  omega

include keyLaw notSystem in
theorem writer_ordinary
    (accepted : first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1))) :
    ordinary p system t ((p.layout t).handles 2).1 := by
  have flags := CPS_EntryFlags.writer (DrvC_Installation.sdk c) n1 n2 hashv extraction
    copy std allocator e1 id data1 state1 final1 saved post1 accepted
  have owner := CPS_Ordinary.owner (DrvC_Installation.sdk c) keyLaw n1 n2 hashv extraction
    copy std allocator e1 id data1 state1 final1 saved post1 accepted
  rw [game.consecutive.2.1] at flags owner
  exact ⟨flags.1,fun same => notSystem (owner.symm.trans same)⟩

omit std in
theorem reader_positive
    (accepted : second n2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2))) :
    0 < (p.bank u).lamports ((p.layout u).handles 6).1 := by
  have native := (second_accepted n2 allocator e2 id data2 slot state2 final2 post2 accepted).1
  have source := (extraction.stage2 id (e2.second secondSizes) data2 slot).symm.trans native
  rw [game.consecutive.2.2] at source
  have marker := Hir_ReaderEntry.marker c (cached (p.bank u)).cells
    (CPP_BankState.layout (cached (p.bank u)) (p.layout u)) id data2 slot source
  have length := marker.1
  by_contra bad
  have zero : (p.bank u).lamports ((p.layout u).handles 6).1 = 0 := by omega
  have empty := CPG_Projection.dead p u ((p.layout u).handles 6).1 zero
  change 0 < ((entry p u).buffers ((p.layout u).handles 6).1).val.length at length
  rw [empty] at length
  simp only [List.length_nil] at length
  omega

#print axioms writer_positive
#print axioms writer_ordinary
#print axioms reader_positive
end AspisR1.CPG_Accepted
end
