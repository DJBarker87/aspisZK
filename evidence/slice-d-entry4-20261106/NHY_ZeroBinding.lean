import NGL_ArrayEquality
open Aeneas Aeneas.Std Result
namespace NHY_ZeroBinding
attribute [local instance] Classical.propDecidable
def binding_ref (value : Array Std.U8 32#usize) : Result Bool := do
  let a := Array.repeat 32#usize 0#u8
  core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 value a


theorem source (value : Array U8 32#usize) :
    binding_ref value = ok (decide (value=Array.repeat 32#usize 0#u8)) := by
  unfold binding_ref
  exact NGL_ArrayEquality.eq_value value (Array.repeat 32#usize 0#u8)
#print axioms source
end NHY_ZeroBinding
