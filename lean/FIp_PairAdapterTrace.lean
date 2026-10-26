import FIp_PairFinalCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_PairAdapterTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem reached (r : NP6_StdModel.Reservation) (w : FIo_Install.W)
    (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8)
    (kappa out : AspisR1Stage2.Stage2Finish.E)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut : NE) (parts k : Array NE 7#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧
      FIo_Native.weights.powers 7#usize (FIo_Install.toE kappa)=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok nativeOut := by
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨parts,k,hp,hs⟩ := @FIp_PairFinalCall.reached (FIo_Install.allocation r)
    (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa) nativeOut hn
  exact ⟨nativeOut,parts,k,hn,he,hp,hs⟩

#print axioms reached
end AspisR1.FIp_PairAdapterTrace
end
