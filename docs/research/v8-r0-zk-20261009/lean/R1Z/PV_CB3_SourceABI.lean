import R1Z.PV_CB3_SourcePass
namespace R1Z.PV_CB3_SourceABI
open Aeneas Aeneas.Std
open PV_CB3_SourcePass (values)
set_option autoImplicit false

/-- The numeric representation determines the actual source word vector. -/
theorem values_injective {xs ys : List U32} (h : values xs = values ys) : xs = ys := by
  apply (List.map_inj_right (f := fun x : U32 => x.val)
    (fun _ _ hv => UScalar.eq_of_val_eq hv)).mp
  exact h

theorem array_values_injective {n : Usize} {xs ys : Array U32 n}
    (h : values xs.val = values ys.val) : xs = ys := by
  exact Subtype.ext (values_injective h)

def pack32 (word : BitVec 32) : U32 := ⟨word⟩

theorem pack32_value (word : BitVec 32) : (pack32 word).val = word.toNat := by
  exact (UScalar.bv_toNat (pack32 word)).symm

theorem pack32_injective {x y : BitVec 32} (h : pack32 x = pack32 y) : x = y := by
  exact congrArg (fun z : U32 => z.bv) h

#print axioms values_injective
#print axioms array_values_injective
#print axioms pack32_value
#print axioms pack32_injective
end R1Z.PV_CB3_SourceABI
