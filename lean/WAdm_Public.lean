import Tx1Q_Accepted
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Public
open S2W_D189Entry S2W_NativeConsolidation

/-- public1880 is an output of the exact caller read, for ANY published cuts
of this execution. No independent decoder or second accepted run is chosen. -/
theorem reached (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (e : Entry) (accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapterOps ops B std) e.first accounts2 saved f s) :
    f.pub = e.buffers (e.handles 1).1 ∧ f.pub.val.length = 1880 := by
  have same := Result.ok.inj (cuts.public1Index.symm.trans (first_index e).2.1)
  have read := cuts.public1Read
  rw [same] at read
  exact AspisS6SdkStage1ReuseFactored.public_read e
    (ClaimsUnrolledSdk.sdkOps adapterOps ops B std) f.pub read

#print axioms reached
end AspisR1.WAdm_Public
end
