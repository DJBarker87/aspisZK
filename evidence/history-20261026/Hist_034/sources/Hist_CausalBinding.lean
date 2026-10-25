import Hist_RuntimeEntry
import Hist_Persistence
import Hist_SecondSnapshot
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_CausalBinding
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2W_D189Entry S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Causally paired runtime loads. Same-key selection is explicit and belongs
to the runtime experiment, not an alleged cross-transaction program check.
The source marker is derived from the actual installed writer by the consumer. -/
def version (base : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (initial final : Store) (layout1 layout2 : Layout)
    (data1 : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned (Hist_Authority.install base)
      program (load initial layout1).first data1 = ok (.Ok saved))
    (events : List S2X.AccountEvent)
    (trace : Trace (Hist_Authority.install base) program
      (commit initial (layout1.handles 2).1 saved) events final)
    (sameKey : (layout2.handles 6).1 = (layout1.handles 2).1)
    (marker : Initialized saved.deref)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (Hist_Authority.install base) (load initial layout1).first
      ((load final layout2).second S2W_D189Wrappers.secondSizes) saved f s) :
    S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) := by
  let key := (layout1.handles 2).1
  let committed := commit initial key saved
  have owner : (committed key).owner = program :=
    (commit_owner initial key saved).trans
      (Hist_RuntimeEntry.accepted_owner base program initial layout1 data1 saved accepted1)
  have initialized : Initialized (committed key).data := by
    change Initialized (put initial key ⟨(initial key).owner,saved.deref⟩ key).data
    rw [put_here]
    exact marker
  let history := Hist_Persistence.binding (Hist_Authority.install base) program committed final key events trace owner initialized
  have stored : byteLedger committed key = bytesOf saved.val :=
    congrArg bytesOf (commit_data initial key saved)
  have loaded : bytesOf s.checkpoint.val = byteLedger final key := by
    rw [Hist_SecondSnapshot.on_cuts (Hist_Authority.install base) (load initial layout1) (load final layout2) saved f s cuts]
    change bytesOf (final (layout2.handles 6).1).data.val = _
    rw [sameKey]
    rfl
  refine ⟨key, history.ledger, events, ?_, ?_, history.noInterveningWrite⟩
  · exact history.savedAtCommit.trans stored
  · exact loaded.trans history.loadedAtEntry

#print axioms version
end AspisR1.Hist_CausalBinding
end
