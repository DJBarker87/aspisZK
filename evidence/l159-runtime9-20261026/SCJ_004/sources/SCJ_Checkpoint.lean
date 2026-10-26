import CPH_Top
import CPG_History
import SCE_SecondCutBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Checkpoint
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry MultiproofConeCanonical
open S2W_NativeConsolidation S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
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
    (game : CPG_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 final2 : A) (post1 post2 : Heap (Nat → Record))
    (accepted1 : first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)))
    (accepted2 : second n2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2)))
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (adjacent p) (ordinary p system) (before p)
      (tentative p) (success p) (loaded p))

include keyLaw extraction std notSystem game accepted1 accepted2 RuntimePersistence
/-- CPH's derived history on the very cuts supplied here. No saved/loaded
equality, version record or history conclusion is assumed. -/
theorem same_saved (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s) :
    bytesOf s.checkpoint.val = bytesOf saved.val := by
  let version := CPG_History.on_cuts (game := game) (c := c) (keyLaw := keyLaw)
    (extraction := extraction) (std := std) (notSystem := notSystem)
    (accepted1 := accepted1) (accepted2 := accepted2)
    (RuntimePersistence := RuntimePersistence) (f := f) (s := s) (cuts := cuts)
  have persisted := S2X.checkpoint_persistence _ _ version
  have native := (first_accepted n1 copy std allocator e1 id data1 state1 final1 saved post1 accepted1).1
  have source := (extraction.stage1 id e1.first data1).symm.trans native
  have shape := Hiq_FirstShape.source c id e1.first data1 saved source
  exact persisted.trans (Hist_CommittedPayload.copied _ n1 n2 hashv extraction
    copy std allocator e1 id data1 state1 final1 saved post1 accepted1 shape.2)

/-- The physical entry buffer of those cuts, rather than an independently
selected entry. This is the CPH conclusion that a per-world game must index. -/
theorem entry_saved (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s) :
    bytesOf (e2.buffers (e2.handles 6).1).val = bytesOf saved.val := by
  exact (SCE_SecondCutBytes.checkpoint _ _ _ saved f s cuts).symm.trans
    (same_saved (p := p) (t := t) (u := u) (e1 := e1) (e2 := e2)
      (saved := saved) (actions := actions) (c := c) (keyLaw := keyLaw)
      (n1 := n1) (n2 := n2) (hashv := hashv) (extraction := extraction)
      (copy := copy) (std := std) (allocator := allocator) (id := id)
      (system := system) (notSystem := notSystem) (game := game)
      (data1 := data1) (data2 := data2) (slot := slot) (state1 := state1)
      (state2 := state2) (final1 := final1) (final2 := final2)
      (post1 := post1) (post2 := post2) (accepted1 := accepted1)
      (accepted2 := accepted2) (RuntimePersistence := RuntimePersistence) f s cuts)

#print axioms entry_saved

#print axioms same_saved
end AspisR1.SCJ_Checkpoint
end
