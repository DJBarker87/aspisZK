import Hiq_DrvVersion
import Hiq_RuntimeHistory
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_ComputedVersion
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry Hiq_RuntimeAction
open S2W_D189Entry S2W_D189Wrappers S2W_NativeConsolidation MultiproofConeCanonical DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def version {F C : Type} (c : Configuration F C)
    (law : (sdk c).op36 = Hist_Authority.keyEq)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (id : S2W_ExtractionBoundary.Program) (initial : Store) (l1 l2 : Layout)
    (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c) id (load initial l1).first data = ok (.Ok saved))
    (actions : List Action) (sameKey : (l2.handles 6).1 = (l1.handles 2).1)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) (load initial l1).first
      ((load (Hiq_RuntimeHistory.run (sdk c) id (commit initial (l1.handles 2).1 saved) actions).1 l2).second secondSizes) saved f s) :
    S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val) := by
  have shape := Hiq_DrvShape.on_cuts c _ _ saved f s cuts owner ports
  exact Hiq_CausalVersion.version (sdk c) law id initial _ l1 l2 data saved accepted _
    (Hiq_RuntimeHistory.classified (sdk c) law id _ actions) sameKey shape.1 f s cuts

#print axioms version
end AspisR1.Hiq_ComputedVersion
end
