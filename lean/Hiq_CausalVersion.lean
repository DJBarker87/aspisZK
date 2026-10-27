import Hiq_KeyLaw
import Hist_CommittedPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_CausalVersion
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2W_D189Entry S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def version (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (id : S2W_ExtractionBoundary.Program) (initial final : Store) (l1 l2 : Layout)
    (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops id (load initial l1).first data = ok (.Ok saved))
    (events : List S2X.AccountEvent)
    (trace : Trace ops id (commit initial (l1.handles 2).1 saved) events final)
    (sameKey : (l2.handles 6).1 = (l1.handles 2).1) (marker : Initialized saved.deref)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops (load initial l1).first ((load final l2).second S2W_D189Wrappers.secondSizes) saved f s) :
    S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) := by
  apply Hist_CausalBinding.version ops id initial final l1 l2 data saved
  · simpa only [Hiq_KeyLaw.installed_eq ops keyLaw] using accepted
  · simpa only [Hiq_KeyLaw.installed_eq ops keyLaw] using trace
  · exact sameKey
  · exact marker
  · simpa only [Hiq_KeyLaw.installed_eq ops keyLaw] using cuts

#print axioms version
end AspisR1.Hiq_CausalVersion
end
