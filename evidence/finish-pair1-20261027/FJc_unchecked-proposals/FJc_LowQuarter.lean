import FJc_Quarter
import FJc_LowPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_LowQuarter
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
/-- Exact quarter constant transport on the original low-power operands. -/
theorem value (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (low : Array NE 16#usize)
    (ha0 : FIo_WideValues.Canon a0) (ha1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (run : FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
      (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok low) :
    FIo_ArrayCanon.Holds low ∧ ∀ s,s<16 → FIp_ArrayValue.value low s=
      (RoundPairing.quarter (K:=ZMod 2147483647)*RoundPairing.quarter (K:=ZMod 2147483647)) •
      (decodeWide (wide a0)^FJc_LowModel.perm (s%4)*decodeWide (wide a1)^FJc_LowModel.perm (s/4)) := by
  have h := FJc_LowPowers.value a0 a1 ap0 ap1 low ha0 ha1 hp0 hp1 run
  simpa only [FJc_Quarter.value] using h
#print axioms value
end AspisR1.FJc_LowQuarter
end
