import DrvC_NativePair
import Hist_SdkShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DrvShape
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation S2W_D189Entry

theorem on_cuts {F C : Type} (c : Configuration F C)
    (e1 : Entry) (accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk c) e1.first accounts2 saved f s)
    (owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (ports : Port5Q1_QueryPorts.SessionAPrimitives c.query) :
    Hist_Store.Initialized saved.deref ∧ saved.val.length = 1768 := by
  rw [cphy_dictionary,Uni_Install.compose_tx1] at cuts
  exact Hist_SdkShape.on_cuts _ (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry
    c.boundaries c.std e1 accounts2 saved f s cuts owner ports

#print axioms on_cuts
end AspisR1.Hiq_DrvShape
end
