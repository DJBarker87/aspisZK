import NNH_Run5bSplit
import NNH_Run5bHeadline
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNW_ProtectionPositive
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NNH_Run5bCtx NNH_Run5bHost
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
#print axioms produce
end AspisR1.NNW_ProtectionPositive
end
