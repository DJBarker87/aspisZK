import PV_L2C_DecodeRange
set_option autoImplicit false
namespace PV_L2C_GeneratedRange
open Aeneas Aeneas.Std Result

/-- The planner finishes every generated digest limb with `% P`, regardless
of the preceding checked or wrapping seed arithmetic. -/
def remainder (x : U32) : U32 := ⟨BitVec.umod x.bv (2147483647#u32).bv⟩

theorem remainder_result (x : U32) :
    x % (2147483647#u32) = ok (remainder x) := by rfl
#print axioms remainder_result

theorem remainder_val (x : U32) :
    (remainder x).val = x.val % 2147483647 := by rfl
#print axioms remainder_val

theorem remainder_range (x : U32) : (remainder x).val < 2147483647 := by
  rw [remainder_val]
  exact Nat.mod_lt _ (by decide)
#print axioms remainder_range

theorem generated_digest (prior : Fin 8 → U32) :
    ∀ i, (remainder (prior i)).val < 2147483647 :=
  fun i => remainder_range (prior i)
#print axioms generated_digest

theorem rejects_raw_P (x : U32) : remainder x ≠ 2147483647#u32 := by
  intro h
  have hb := remainder_range x
  rw [h] at hb
  exact Nat.lt_irrefl 2147483647 hb
#print axioms rejects_raw_P
end PV_L2C_GeneratedRange
