import NNC_Persistence
set_option autoImplicit false
noncomputable section
namespace NNC_NativePersistence
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Persistence from the approved runtime law, TX1 acceptance and game.
Writer protection and ordinary eligibility are derived, not extra hypotheses;
no accepted2, second extraction success, or reader model law is used. -/
theorem persisted {Tx A F C : Type} (p : CPG_Projection.Observations Tx A) (t u : Tx)
 (c : DrvC_Installation.Configuration F C)
 (keyLaw : (DrvC_Installation.sdk c).op36=Hist_Authority.keyEq)
 (e1 e2 : Entry) (saved : alloc.vec.Vec U8) (actions : List (CPP_BankState.Action A))
 (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
 (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
 (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
 (std : TrustedStd copy) (allocator : Allocator A)
 (id system : S2W_ExtractionBoundary.Program) (notSystem : id≠system)
 (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions n1 n2 copy allocator id)
 (runtime : CPR_DataPersistence.TwoTransactionLaw
  (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system)
  (CPG_Projection.before p) (CPG_Projection.tentative p)
  (CPG_Projection.success p) (CPG_Projection.loaded p))
 (data1 : Slice U8) (state1 final1 : A) (post1 : Heap (Nat → Record))
 (accepted1 : first n1 copy allocator e1 id data1 state1=ok (.Ok (saved,post1,final1)))
 (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s)
 (length : s.checkpoint.val.length=1768) : bytesOf s.checkpoint.val=bytesOf saved.val := by
 have protection := CPH_Protection.derive p t u e1 e2 saved actions c keyLaw n1 n2 hashv
  extraction copy std allocator id game data1 state1 final1 post1 accepted1
 have eligible := CPG_Accepted.writer_ordinary (game := CPH_Game.recordedInstance game)
  (c := c) (keyLaw := keyLaw) (notSystem := notSystem) (extraction := extraction)
  (std := std) (accepted := accepted1)
 exact NNC_Persistence.persisted p t u (DrvC_Installation.sdk c) e1 e2 saved actions n1 n2
  copy allocator id system game runtime eligible protection f s cuts length
#print axioms persisted
end NNC_NativePersistence
