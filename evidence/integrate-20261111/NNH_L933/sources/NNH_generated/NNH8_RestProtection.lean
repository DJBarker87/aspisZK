import NNH8_Exec
set_option autoImplicit false
noncomputable section
/-! Run 7: NNW_ protection conjunct producers restated at NOC_Run5bHost.S_host (namespace swap only). -/
namespace AspisR1.NNH8_ProtOwner
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :

 let bank := CPR_SourceBank.afterCopy (CPG_Projection.cached (c.world.p.bank c.world.t))
   ((c.world.p.layout c.world.t).handles 2).1 c.world.saved
 let key := ((c.world.p.layout c.world.t).handles 2).1
 (bank.cells key).owner = CPH_Program.verifier := by
 exact (CPH_Protection.derive c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions (configuration c)
    (Rc5_Install.key c.fixed.indexError (FIp_Install.select c.fixed.reservation (base c)) c.fixed.reservation)
    n1 n2 (hashv c) ext copy std NNE_AbortIndicator.allocator CPH_Program.verifier game.1
    c.i.data true true (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1).1
#print axioms AspisR1.NNH8_ProtOwner.produce
end AspisR1.NNH8_ProtOwner
namespace AspisR1.NNH8_ProtMarker
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :

 let bank := CPR_SourceBank.afterCopy (CPG_Projection.cached (c.world.p.bank c.world.t))
   ((c.world.p.layout c.world.t).handles 2).1 c.world.saved
 let key := ((c.world.p.layout c.world.t).handles 2).1
 Hist_Store.Initialized (bank.cells key).data := by
 exact (CPH_Protection.derive c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions (configuration c)
    (Rc5_Install.key c.fixed.indexError (FIp_Install.select c.fixed.reservation (base c)) c.fixed.reservation)
    n1 n2 (hashv c) ext copy std NNE_AbortIndicator.allocator CPH_Program.verifier game.1
    c.i.data true true (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1).2.1
#print axioms AspisR1.NNH8_ProtMarker.produce
end AspisR1.NNH8_ProtMarker
namespace AspisR1.NNH8_ProtPositive
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :

 let bank := CPR_SourceBank.afterCopy (CPG_Projection.cached (c.world.p.bank c.world.t))
   ((c.world.p.layout c.world.t).handles 2).1 c.world.saved
 let key := ((c.world.p.layout c.world.t).handles 2).1
 0 < bank.lamports key := by
 exact (CPH_Protection.derive c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions (configuration c)
    (Rc5_Install.key c.fixed.indexError (FIp_Install.select c.fixed.reservation (base c)) c.fixed.reservation)
    n1 n2 (hashv c) ext copy std NNE_AbortIndicator.allocator CPH_Program.verifier game.1
    c.i.data true true (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1).2.2.1
#print axioms AspisR1.NNH8_ProtPositive.produce
end AspisR1.NNH8_ProtPositive
namespace AspisR1.NNH8_ProtPreserves
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :

 let bank := CPR_SourceBank.afterCopy (CPG_Projection.cached (c.world.p.bank c.world.t))
   ((c.world.p.layout c.world.t).handles 2).1 c.world.saved
 let key := ((c.world.p.layout c.world.t).handles 2).1
 ∀ event ∈ c.world.p.physicalEvents c.world.t, S2X.Preserves key event := by
 exact (CPH_Protection.derive c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions (configuration c)
    (Rc5_Install.key c.fixed.indexError (FIp_Install.select c.fixed.reservation (base c)) c.fixed.reservation)
    n1 n2 (hashv c) ext copy std NNE_AbortIndicator.allocator CPH_Program.verifier game.1
    c.i.data true true (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1).2.2.2.1
#print axioms AspisR1.NNH8_ProtPreserves.produce
end AspisR1.NNH8_ProtPreserves
namespace AspisR1.NNH8_ProtCells
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :

 let bank := CPR_SourceBank.afterCopy (CPG_Projection.cached (c.world.p.bank c.world.t))
   ((c.world.p.layout c.world.t).handles 2).1 c.world.saved
 let key := ((c.world.p.layout c.world.t).handles 2).1
 (c.world.p.parentTentative c.world.t).cells key = bank.cells key := by
 exact (CPH_Protection.derive c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions (configuration c)
    (Rc5_Install.key c.fixed.indexError (FIp_Install.select c.fixed.reservation (base c)) c.fixed.reservation)
    n1 n2 (hashv c) ext copy std NNE_AbortIndicator.allocator CPH_Program.verifier game.1
    c.i.data true true (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1).2.2.2.2.1
#print axioms AspisR1.NNH8_ProtCells.produce
end AspisR1.NNH8_ProtCells
namespace AspisR1.NNH8_ProtLamports
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :

 let bank := CPR_SourceBank.afterCopy (CPG_Projection.cached (c.world.p.bank c.world.t))
   ((c.world.p.layout c.world.t).handles 2).1 c.world.saved
 let key := ((c.world.p.layout c.world.t).handles 2).1
 bank.lamports key ≤ (c.world.p.parentTentative c.world.t).lamports key := by
 exact (CPH_Protection.derive c.world.p c.world.t c.world.u c.i.entry c.j.entry c.world.saved
    c.world.actions (configuration c)
    (Rc5_Install.key c.fixed.indexError (FIp_Install.select c.fixed.reservation (base c)) c.fixed.reservation)
    n1 n2 (hashv c) ext copy std NNE_AbortIndicator.allocator CPH_Program.verifier game.1
    c.i.data true true (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) ac1).2.2.2.2.2
#print axioms AspisR1.NNH8_ProtLamports.produce
end AspisR1.NNH8_ProtLamports
namespace AspisR1.NNH8_Protection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx NOC_Run5bHost
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
theorem produce (c : Ctx W Tx) (n1 : S2W_ExtractionBoundary.First)
 (n2 : S2W_ExtractionBoundary.Second)
 (ext : (S_host L copy std).Extraction c n1 n2)
 (ac1 : (S_host L copy std).Accepted1 c n1)
 (game : (S_host L copy std).Game c n1 n2)
 (queries : (S_host L copy std).Queries c n1) :
 CPH_Protection.Facts c.world.p c.world.t c.world.saved CPH_Program.verifier := by
 exact ⟨NNH8_ProtOwner.produce L copy std c n1 n2 ext ac1 game queries,
  NNH8_ProtMarker.produce L copy std c n1 n2 ext ac1 game queries,
  NNH8_ProtPositive.produce L copy std c n1 n2 ext ac1 game queries,
  NNH8_ProtPreserves.produce L copy std c n1 n2 ext ac1 game queries,
  NNH8_ProtCells.produce L copy std c n1 n2 ext ac1 game queries,
  NNH8_ProtLamports.produce L copy std c n1 n2 ext ac1 game queries⟩
#print axioms AspisR1.NNH8_Protection.produce
end AspisR1.NNH8_Protection
end
