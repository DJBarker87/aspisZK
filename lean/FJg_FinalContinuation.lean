import FJc_LibraFrame
import FJc_ArrayUpdateValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_FinalContinuation
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE wide)
/-- The actual inactive write and Libra continuation preserve part1 and set
part0 in one SAME final array, independent of all other previous parts. -/
theorem value (f : Slice U8) (libra : Array NE 4#usize)
    (highParts lowParts parts : Array NE 7#usize) (inactive : NE)
    (hu : Array.update highParts 0#usize inactive=ok lowParts)
    (hl : FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f lowParts libra=ok parts) :
    FIp_ArrayValue.value parts 1=FIp_ArrayValue.value highParts 1 ∧
    FIp_ArrayValue.value parts 0=AspisR1CurrentWide.Proof.decodeWide (wide inactive) := by
  constructor
  · rw [FJc_LibraFrame.value f libra lowParts parts _ hl 1 (by decide),
      FJc_ArrayUpdateValue.value highParts lowParts 0#usize inactive 1 hu,
      if_neg (by decide)]
  · rw [FJc_LibraFrame.value f libra lowParts parts _ hl 0 (by decide),
      FJc_ArrayUpdateValue.value highParts lowParts 0#usize inactive 0 hu,
      if_pos (by decide)]
#print axioms value
end AspisR1.FJg_FinalContinuation
end
