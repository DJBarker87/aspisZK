import NNV_PreparedAtHost
import LIBC_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CurrentFlush
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller

theorem slot {W Tx : Type} (c : Ctx W Tx) (b : verifier.BatchedWeights)
 (old : Slice aspis_core.field.QM31) :
 (DrvC_Installation.currentInstalled (configuration c)).op17 b old = Tx1Q_Install.flush b old := rfl

theorem returned {W Tx : Type} (c : Ctx W Tx) (a : LIBC_Finish.Args)
 (domain : LIBC_Finish.Domain a) :
 (DrvC_Installation.currentInstalled (configuration c)).op17 (Tx1Q_Carriers.unPending a.1)
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a.2)).weights.deref =
 .ok (Tx1Q_Carriers.slice Tx1Q_Carriers.unK (NJJ_Flush.output a.1)) := by
 obtain ⟨p,start,finish,d⟩ := domain
 have round := congrArg (fun s : AspisR1Stage2.verifier.Accumulator => s.weights.deref)
  (Tx1Q_Carriers.accumulator_roundtrip (LIBC_VStateCarriers.toAcc a.2))
 change Tx1Q_Carriers.slice Tx1Q_Carriers.k
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a.2)).weights.deref =
  (LIBC_VStateCarriers.toAcc a.2).weights.deref at round
 rw [slot]
 unfold Tx1Q_Install.flush
 rw [Tx1Q_Carriers.pending_roundtrip,round,NJJ_Flush.source a.1 _ d.progress.2.1 d.width,bind_tc_ok]
#print axioms slot
#print axioms returned
end AspisR1.NNV_CurrentFlush
end
