import FJr_InactiveMeaning
import FJc_PairInactiveTrace
import FJc_LowPowers
import FJc_InactiveValue
import FJc_InstalledParts
import FGm_GroupDispatch
import FJc_SliceCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_Part0Meaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE wide)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8) (kappa out : AspisR1Stage2.Stage2Finish.E)
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut a0 a1 : NE) (parts k : Array NE 7#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=ok a0 ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=ok a1 ∧
      FIo_Native.weights.powers 7#usize (FIo_Install.toE kappa)=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok nativeOut ∧
      FIp_ArrayValue.value parts 0=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide a0)) FJr_InactiveRaw.raw)) := by
  letI := FIo_Install.allocation r
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  have variantS2 : (FIo_Install.toWeights w).variant=.S2 := variant
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨a0,a1,ap0,ap1,low,inactive,before,after,parts,k,libra,h0,hp0,h1,hp1,hl,hi,hu,hlib,hk,hsum⟩ :=
    FJc_PairInactiveTrace.reached (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa) nativeOut folds hn
  have ca0 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 0#usize a0 halpha h0
  have ca1 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 1#usize a1 halpha h1
  have vl := FJc_LowPowers.value a0 a1 ap0 ap1 low ca0 ca1 hp0 hp1 hl
  have call := hi
  rw [FGm_GroupDispatch.same (FIo_Install.toWeights w) f low variantS2 len] at call
  have vi := FJc_InactiveValue.value f low inactive vl.1 call
  have update := FJc_ArrayUpdateValue.value before after 0#usize inactive 0 hu
  have frame := FJc_LibraFrame.value f libra after parts _ hlib 0 (by decide)
  have literal := FJr_InactiveMeaning.value f low (decodeWide (wide a0)) (decodeWide (wide a1)) vl.2
  refine ⟨nativeOut,a0,a1,parts,k,hn,he,h0,h1,hk,hsum,?_⟩
  rw [frame,update,if_pos (by rfl),vi.2,literal]

#print axioms value
end AspisR1.FJr_Part0Meaning
end
