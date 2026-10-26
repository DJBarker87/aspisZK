import F3X_GameFixture
import Rc2_History
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_FixtureHistory
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2W_NativeConsolidation
open S2W_CommittedCheckpoint S2W_EntryWriteHistory S2W_ReturnedCheckpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Instantiate the approved runtime item and the two-entry symbolic game.
The same source-bank actions supply the final bytes AND recorded events. -/
theorem binding {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (e1 e2 : Entry) (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (H : Bytes → State) (f : FirstCut) (s : SecondCut)
    (history : Rc2_History.Facts c hashv n1 n2 copy allocator id e1 e2 saved post1 H f s)
    (keyLaw : (DrvC_Installation.sdk c).op36=Hist_Authority.keyEq)
    (initial : CPP_BankState.Bank) (layout : Hist_RuntimeEntry.Layout)
    (entry1 : e1=Hist_RuntimeEntry.load initial.cells (CPP_BankState.layout initial layout))
    (actions : List (CPP_BankState.Action A)) (positive : 0 < initial.lamports (layout.handles 2).1)
    (entry2 : F3X_GameFixture.loaded
      (CPP_BankHistory.run n1 n2 copy allocator id
        (CPR_SourceBank.afterCopy initial (layout.handles 2).1 saved) actions).1 true (layout.handles 2).1=
      some (bytesOf (e2.buffers (e2.handles 6).1).val)) :
    ∃ version : S2X.CheckpointVersionBinding
      (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val),
      version.events=(eval H (CPS_BankRecorder.program c hashv n1 n2 copy allocator id
        (CPR_SourceBank.afterCopy initial (layout.handles 2).1 saved) actions)).2.2 ∧
      bytesOf s.checkpoint.val=payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 := by
  let final := (CPP_BankHistory.run n1 n2 copy allocator id
    (CPR_SourceBank.afterCopy initial (layout.handles 2).1 saved) actions).1
  exact history keyLaw initial layout entry1 actions positive Bool Nat
    F3X_GameFixture.next F3X_GameFixture.ordinary (F3X_GameFixture.before initial)
    (F3X_GameFixture.tentative final) F3X_GameFixture.success (F3X_GameFixture.loaded final)
    (F3X_GameFixture.RuntimePersistence initial final) false true (layout.handles 2).1
    ⟨rfl,rfl⟩ trivial rfl rfl entry2

#print axioms binding
end AspisR1.F3X_FixtureHistory
end
