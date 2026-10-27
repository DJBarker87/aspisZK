import RPu_FJc_PairInactiveTrace
import RPu_FJc_InactiveValue
import RPu_FJc_LowPowers
import RPu_FJc_SliceCanonical
import RPu_FGm_GroupDispatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InactiveFinalValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
/-- The actual final seven-part array's part0 has the grouped inactive VALUE
of the SAME original final-message and low operands from that Pair call. -/
theorem value [FIo_Native.Allocation] (self : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (folds : Slice.len alpha=2#usize) (variant : self.variant=.S2) (len : f.val.length=2048)
    (halpha : ∀ x∈alpha.val,FIo_WideValues.Canon x)
    (run : FIo_Native.weights.Weights.pair self alpha f kappa=ok (.Ok out)) :
    ∃ (low : Array NE 16#usize) (parts k : Array NE 7#usize),
      FIo_ArrayCanon.Holds low ∧
      FIo_Native.weights.powers 7#usize kappa=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out ∧
      FIp_ArrayValue.value parts 0=FJc_InactiveValue.sumPrefix f low 12 := by
  obtain ⟨a0,a1,ap0,ap1,low,inactive,before,after,parts,k,libra,h0,hp0,h1,hp1,hl,hi,hu,hlib,hk,hsum⟩ :=
    FJc_PairInactiveTrace.reached self alpha f kappa out folds run
  have ca0 := FJc_SliceCanonical.read alpha 0#usize a0 halpha h0
  have ca1 := FJc_SliceCanonical.read alpha 1#usize a1 halpha h1
  have vl := FJc_LowPowers.value a0 a1 ap0 ap1 low ca0 ca1 hp0 hp1 hl
  have call := hi
  rw [FGm_GroupDispatch.same self f low variant len] at call
  have vi := FJc_InactiveValue.value f low inactive vl.1 call
  have update := FJc_ArrayUpdateValue.value before after 0#usize inactive 0 hu
  have sourceZero : (0#usize).val=0 := by scalar_tac
  rw [sourceZero,if_pos rfl] at update
  have frame := FJc_LibraFrame.value f libra after parts _ hlib 0 (by decide)
  exact ⟨low,parts,k,vl.1,hk,hsum,frame.trans (update.trans vi.2)⟩
#print axioms value
end AspisR1.FJc_InactiveFinalValue
end
