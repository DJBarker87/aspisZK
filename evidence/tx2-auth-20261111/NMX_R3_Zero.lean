import NCV_ZeroRun
import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_Zero
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier

theorem byte_zero (x : U8) : byte x = 0 ↔ x = 0#u8 := by
  change byte x = byte 0#u8 ↔ x = 0#u8
  exact ⟨fun h => byte_injective h, fun h => congrArg byte h⟩

/-- All-zero test on arbitrary bytes, including the empty slice. -/
theorem predicate (b : Slice U8) : NCV_ZeroRun.AllZero b 0 ↔
    (b.val.map byte).all (· == 0) = true := by
  simp only [List.all_map, Function.comp_def, List.all_eq_true, beq_iff_eq, byte_zero]
  constructor
  · intro h x hx
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp hx
    have test := h i (Nat.zero_le i) hi
    simpa only [NCV_ZeroStep.byte, List.getElem?_eq_getElem hi, Option.getD_some, same] using test
  · intro h i _ hi
    have test := h b.val[i] (List.getElem_mem hi)
    simpa only [NCV_ZeroStep.byte, List.getElem?_eq_getElem hi, Option.getD_some] using test

theorem value (b : Slice U8) (cap : b.val.length ≤ 768) :
    NCV_Reference.zero b = ok ((b.val.map byte).all (· == 0)) := by
  classical
  rw [NCV_ZeroRun.value b cap]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact predicate b
#print axioms byte_zero
#print axioms predicate
#print axioms value
end NMX_R3_Zero
