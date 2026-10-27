import CPR_RuntimeBinding
import Hiq_KeyLaw
import Hist_CommittedPayload
import Hist_SecondSnapshot
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_SourceBank
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState CPR_Persistence
open S2W_NativeConsolidation MultiproofConeCanonical

/-- Bank projection immediately after the actual native copy. Balance is framed
by the source; transaction settlement and later load are separate operations. -/
def afterCopy (initial : Bank) (key : Nat) (saved : alloc.vec.Vec U8) : Bank :=
  ⟨commit initial.cells key saved,initial.lamports⟩

theorem copied_data (initial : Bank) (key : Nat) (saved : alloc.vec.Vec U8) :
    byteLedger (afterCopy initial key saved).cells key = bytesOf saved.val :=
  congrArg bytesOf (commit_data initial.cells key saved)

theorem copied_marker (initial : Bank) (key : Nat) (saved : alloc.vec.Vec U8)
    (marker : Initialized saved.deref) :
    Initialized ((afterCopy initial key saved).cells key).data := by
  change Initialized (put initial.cells key ⟨(initial.cells key).owner,saved.deref⟩ key).data
  rw [put_here]
  exact marker

theorem copied_owner (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (id : S2W_ExtractionBoundary.Program) (initial : Bank) (layout : Layout)
    (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops id (load initial.cells layout).first data = ok (.Ok saved)) :
    ((afterCopy initial (layout.handles 2).1 saved).cells (layout.handles 2).1).owner = id := by
  apply (commit_owner initial.cells (layout.handles 2).1 saved).trans
  apply Hist_RuntimeEntry.accepted_owner ops id initial.cells layout data saved
  simpa only [Hiq_KeyLaw.installed_eq ops keyLaw] using accepted

/-- Reindex only the saved/loaded indices, preserving the actual computed key,
ledger and events. No empty history is fabricated. -/
def on_cuts (ops : AdapterRw.Ops) (e1 e2 : Entry) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops e1.first (e2.second secondSizes) saved f s)
    (initial : Bank) (key : Nat)
    (history : S2X.CheckpointVersionBinding
      (byteLedger (afterCopy initial key saved).cells key)
      (bytesOf (e2.buffers (e2.handles 6).1).val)) :
    S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) where
  key := history.key
  ledger := history.ledger
  events := history.events
  savedAtCommit := history.savedAtCommit.trans (copied_data initial key saved)
  loadedAtEntry := (congrArg bytesOf (Hist_SecondSnapshot.on_cuts ops e1 e2 saved f s cuts)).trans history.loadedAtEntry
  noInterveningWrite := history.noInterveningWrite

#print axioms copied_data
#print axioms copied_marker
#print axioms copied_owner
#print axioms on_cuts
end AspisR1.CPR_SourceBank
end
