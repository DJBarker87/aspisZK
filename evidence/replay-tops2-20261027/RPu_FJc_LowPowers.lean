import RPu_FJc_LowValue
import RPu_FJc_PermTable
import RPu_FIp_PowersValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_LowPowers
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)

theorem value (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (low : Array NE 16#usize)
    (ha0 : FIo_WideValues.Canon a0) (ha1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (run : FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
      (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok low) :
    FIo_ArrayCanon.Holds low ∧ ∀ s,s<16 → FIp_ArrayValue.value low s=
      (decodeM FIo_Native.weights.QUARTER*decodeM FIo_Native.weights.QUARTER) •
      (decodeWide (wide a0)^FJc_LowModel.perm (s%4)*decodeWide (wide a1)^FJc_LowModel.perm (s/4)) := by
  have p0 := FIp_PowersValue.powers 4#usize a0 ap0 ha0 hp0
  have p1 := FIp_PowersValue.powers 4#usize a1 ap1 ha1 hp1
  have v := FJc_LowValue.sixteen ap0 ap1 p0.1 p1.1 low run
  refine ⟨v.1,?_⟩
  intro s hs
  rw [v.2 s hs,FJc_LowModel.value,p0.2 _ (FJc_PermTable.bound _ (Nat.mod_lt s (by decide))),
    p1.2 _ (FJc_PermTable.bound _ (by omega))]
#print axioms value
end AspisR1.FJc_LowPowers
end
