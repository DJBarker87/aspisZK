import CPH_Game
import CPG_Accepted
import CPR_SourceBank
import Hiq_FirstShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_Protection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry Hist_Store

/-- The protected key is the accepted writer's CP, in the observed bank.
Unlike Rc2_Protection.Facts this has no arbitrary-bank owner/marker/funding guards. -/
def Facts {Tx A : Type} (p : Observations Tx A) (t : Tx)
    (saved : alloc.vec.Vec U8) (id : S2W_ExtractionBoundary.Program) : Prop :=
  let bank := CPR_SourceBank.afterCopy (cached (p.bank t)) ((p.layout t).handles 2).1 saved
  let key := ((p.layout t).handles 2).1
  (bank.cells key).owner = id ∧ Initialized (bank.cells key).data ∧
  0 < bank.lamports key ∧
  (∀ event ∈ p.physicalEvents t, S2X.Preserves key event) ∧
  (p.parentTentative t).cells key = bank.cells key ∧
  bank.lamports key ≤ (p.parentTentative t).lamports key

theorem derive {Tx A F C : Type} (p : Observations Tx A) (t u : Tx)
    (e1 e2 : Entry) (saved : alloc.vec.Vec U8) (actions : List (Action A))
    (c : DrvC_Installation.Configuration F C)
    (keyLaw : (DrvC_Installation.sdk c).op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program)
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id)
    (data1 : Slice U8) (state1 final1 : A) (post1 : Heap (Nat → Record))
    (accepted1 : first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1))) :
    Facts p t saved id := by
  have native := (first_accepted n1 copy std allocator e1 id data1 state1 final1 saved post1 accepted1).1
  have source := (extraction.stage1 id e1.first data1).symm.trans native
  have owner := CPR_SourceBank.copied_owner (DrvC_Installation.sdk c) keyLaw id
    (cached (p.bank t)) (CPP_BankState.layout (cached (p.bank t)) (p.layout t)) data1 saved
    (by simpa only [game.consecutive.2.1, CPG_Projection.entry] using source)
  have marker := CPR_SourceBank.copied_marker (cached (p.bank t)) ((p.layout t).handles 2).1 saved
    (Hiq_FirstShape.source c id e1.first data1 saved source).1
  have positive := CPG_Accepted.writer_positive (game := CPH_Game.recordedInstance game)
    (c := c) (extraction := extraction) (std := std) (accepted := accepted1)
  have frame := CPP_BankHistory.protection (DrvC_Installation.sdk c) keyLaw n1 n2
    (fun id accounts data => (extraction.stage1 id accounts data).symm) copy std allocator id
    (CPR_SourceBank.afterCopy (cached (p.bank t)) ((p.layout t).handles 2).1 saved)
    actions ((p.layout t).handles 2).1 owner marker positive
  rw [CPG_RuntimeTrace.result game.recorded.1.2.2] at frame
  exact ⟨owner,marker,positive,frame⟩

#print axioms derive
end AspisR1.CPH_Protection
end
