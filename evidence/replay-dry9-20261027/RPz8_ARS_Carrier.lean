import RPz8_ARS_Coverage
import RPz8_ARQ_BankCut
import RPz8_SCE_PublicProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_Carrier
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation

/-- Exact stored-proof and physical-public projections of the runtime RunView.
The physical checkpoint is a separate entry buffer, not a RunView field. -/
theorem projection {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State) (run : F3T_Experiment.RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run) :
    run.2.1.stored = (eval H (submission a)).2.stored ∧
    run.2.1.physical.bytes = (eval H (submission a)).2.publicBytes :=
  ⟨SCE_Projection.stored c hashv copy allocator id a H run observed,
    SCE_PublicProjection.bytes c hashv copy allocator id a H run observed⟩

/-- The same bank-supported entry loads exactly the saved native checkpoint.
No global oracle witness is needed for this persistence conclusion. -/
theorem checkpoint {A C Tx : Type}
    (base : DrvC_Installation.Configuration FIo_Install.W C) (err : C)
    (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (accepted1 : first native1 copy allocator (eval H a.first).2.entry CPH_Program.verifier
      (eval H a.first).2.data (eval H a.first).2.state = ok (.Ok (saved,post1,final1)))
    (accepted2 : let j := (eval H (a.second (eval H a.first).2 saved post1 final1)).2
      second native2 allocator j.entry CPH_Program.verifier j.data j.slot j.state = ok (.Ok (post2,final2)))
    (p : CPG_Projection.Observations Tx A) (t u : Tx) (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u (eval H a.first).2.entry
      (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry saved actions
      native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8))
      (CPG_Projection.before p) (CPG_Projection.tentative p) (CPG_Projection.success p) (CPG_Projection.loaded p))
    :
    MultiproofConeCanonical.bytesOf ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry.buffers
      ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry.handles 6).1).val = MultiproofConeCanonical.bytesOf saved.val := by
  exact SCJ_NativeLoaded.entry_loaded (p := p) (t := t) (u := u)
    (e1 := (eval H a.first).2.entry)
    (e2 := (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry)
    (saved := saved) (actions := actions) (c := FIp_Install.configuration err base reservation)
    (keyLaw := Rc5_Install.key err (FIp_Install.select reservation base) reservation)
    (n1 := native1) (n2 := native2) (hashv := hashv) (extraction := extraction)
    (copy := copy) (std := std) (allocator := allocator) (id := CPH_Program.verifier)
    (system := Hist_Nonvacuity.key 0#u8) (notSystem := CPH_Program.not_system)
    (game := CPH_Game.recordedInstance game)
    (data1 := (eval H a.first).2.data)
    (data2 := (eval H (a.second (eval H a.first).2 saved post1 final1)).2.data)
    (slot := (eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot)
    (state1 := (eval H a.first).2.state)
    (state2 := (eval H (a.second (eval H a.first).2 saved post1 final1)).2.state)
    (final1 := final1) (final2 := final2) (post1 := post1) (post2 := post2)
    (accepted1 := accepted1) (accepted2 := accepted2)
    (RuntimePersistence := RuntimePersistence)


#print axioms projection
#print axioms checkpoint
end AspisR1.ARS_Carrier
end
