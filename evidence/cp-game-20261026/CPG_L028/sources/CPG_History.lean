import CPG_Accepted
import CPR_DataWriter
import CPS_BankRecorder
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPG_History
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPG_Game CPP_BankState Hist_RuntimeEntry MultiproofConeCanonical
open S2W_NativeConsolidation S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

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
    (accepted1 : first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)))
    (accepted2 : second n2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2)))
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (adjacent p) (ordinary p system) (before p)
      (tentative p) (success p) (loaded p))

include game

theorem tentative_view :
    tentative p t ((p.layout t).handles 2).1 =
      CPR_DataPersistence.snapshot
        (CPP_BankHistory.run n1 n2 copy allocator id
          (CPR_SourceBank.afterCopy (cached (p.bank t)) ((p.layout t).handles 2).1 saved) actions).1
        ((p.layout t).handles 2).1 := by
  exact congrArg (fun bank => CPR_DataPersistence.snapshot bank ((p.layout t).handles 2).1)
    (congrArg Prod.fst (CPG_RuntimeTrace.result game.recorded.2.2)).symm

/-- Source event computation matches the independently observed physical trace,
using the SAME recorded step witnesses as the final-bank correspondence. -/
theorem physical_result :
    result p n1 n2 copy allocator id t = (p.parentTentative t,p.physicalEvents t) := by
  unfold result
  rw [game.recorded.1,game.recorded.2.1]
  exact CPG_RuntimeTrace.result game.recorded.2.2

include extraction accepted2 in
theorem entry2_view :
    loaded p u ((p.layout t).handles 2).1 =
      some (bytesOf (e2.buffers (e2.handles 6).1).val) := by
  have positive := CPG_Accepted.reader_positive (game := game) (c := c)
    (extraction := extraction) (accepted := accepted2)
  rw [game.checkpoint.1,game.consecutive.2.2]
  exact CPG_Projection.live p u _ positive

include keyLaw extraction std notSystem accepted1 accepted2 RuntimePersistence

/-- The SAME actual source cuts receive the constructed history. None of its
three ledger fields is an input. RuntimePersistence is an explicit named
hypothesis of the approved byte-only law, not a Lean axiom. -/
def on_cuts (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s) :
    S2X.CheckpointVersionBinding
      (S2W_EntryWriteHistory.payloadBytes S2W_ReturnedCheckpoint.encode (post1.payload (e1.heap.accounts 2).1) 1768)
      (bytesOf s.checkpoint.val) := by
  have positive := CPG_Accepted.writer_positive (game := game) (c := c)
    (extraction := extraction) (std := std) (accepted := accepted1)
  have eligible := CPG_Accepted.writer_ordinary (game := game) (c := c)
    (keyLaw := keyLaw) (extraction := extraction) (std := std)
    (notSystem := notSystem) (accepted := accepted1)
  exact CPR_DataWriter.on_cuts c keyLaw n1 n2 hashv extraction copy std allocator id
    (cached (p.bank t)) (CPP_BankState.layout (cached (p.bank t)) (p.layout t))
    e1 e2 game.consecutive.2.1 data1 state1 final1 saved post1 accepted1 actions positive
    (adjacent p) (ordinary p system) (before p) (tentative p)
    (success p) (loaded p) RuntimePersistence t u ((p.layout t).handles 2).1
    (CPG_Game.next game) eligible
    (tentative_view (game := game))
    game.parent
    (entry2_view (game := game) (c := c) (extraction := extraction) (accepted2 := accepted2))
    f s cuts

#print axioms tentative_view
#print axioms physical_result
#print axioms entry2_view
#print axioms on_cuts
end AspisR1.CPG_History
end
