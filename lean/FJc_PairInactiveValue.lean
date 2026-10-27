import FJc_PairInactiveCall
import FJc_LowPowers
import FJc_InactiveValue
import FGm_GroupDispatch
import FJc_SliceCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_PairInactiveValue
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
/-- One actual Pair's inactive subcall, with its OWN low canonicality derived.
No low array or inactive output is independently selected by the caller. -/
theorem value [FIo_Native.Allocation] (self : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (folds : Slice.len alpha=2#usize) (variant : self.variant=.S2) (len : f.val.length=2048)
    (halpha : ∀ x∈alpha.val,FIo_WideValues.Canon x)
    (run : FIo_Native.weights.Weights.pair self alpha f kappa=ok (.Ok out)) :
    ∃ (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (low : Array NE 16#usize) (inactive : NE),
      Slice.index_usize alpha 0#usize=ok a0 ∧
      FIo_Native.weights.powers 4#usize a0=ok ap0 ∧
      Slice.index_usize alpha 1#usize=ok a1 ∧
      FIo_Native.weights.powers 4#usize a1=ok ap1 ∧
      FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
        (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok low ∧
      FIo_Native.weights.grouped_inactive_pair self f low=ok inactive ∧
      FIo_ArrayCanon.Holds low ∧ FIo_WideValues.Canon inactive ∧
      decodeWide (wide inactive)=FJc_InactiveValue.sumPrefix f low 12 ∧
      ∀ s,s<16 → FIp_ArrayValue.value low s=
        (decodeM FIo_Native.weights.QUARTER*decodeM FIo_Native.weights.QUARTER) •
        (decodeWide (wide a0)^FJc_LowModel.perm (s%4)*decodeWide (wide a1)^FJc_LowModel.perm (s/4)) := by
  obtain ⟨a0,a1,ap0,ap1,low,inactive,h0,hp0,h1,hp1,hl,hi⟩ :=
    FJc_PairInactiveCall.reached self alpha f kappa out folds run
  have ca0 := FJc_SliceCanonical.read alpha 0#usize a0 halpha h0
  have ca1 := FJc_SliceCanonical.read alpha 1#usize a1 halpha h1
  have vl := FJc_LowPowers.value a0 a1 ap0 ap1 low ca0 ca1 hp0 hp1 hl
  have call := hi
  rw [FGm_GroupDispatch.same self f low variant len] at call
  have vi := FJc_InactiveValue.value f low inactive vl.1 call
  exact ⟨a0,a1,ap0,ap1,low,inactive,h0,hp0,h1,hp1,hl,hi,vl.1,vi.1,vi.2,vl.2⟩
#print axioms value
end AspisR1.FJc_PairInactiveValue
end
