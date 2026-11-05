import NJA_Small

set_option autoImplicit false
namespace NJA_Arity
open Aeneas Aeneas.Std Result NJA_Multiproof

theorem two_bits : multiproof.Arity.bits .Two = ok 1#u32 := rfl
theorem eight_bits : multiproof.Arity.bits .Eight = ok 3#u32 := rfl

theorem two_width : multiproof.Arity.width .Two = ok 2#usize := rfl
theorem eight_width : multiproof.Arity.width .Eight = ok 8#usize := rfl

theorem two_levels : multiproof.Arity.levels .Two = ok 18#u32 := rfl
theorem eight_levels : multiproof.Arity.levels .Eight = ok 6#u32 := rfl

-- Exact emitted reads, including their failure result; no successful-read premise.
theorem index_result (indices : Array U32 16#usize) (index : Usize) :
    multiproof.index_at indices index = Array.index_usize indices index := rfl

theorem value_result (values : Array (Array U8 32#usize) 16#usize) (index : Usize) :
    multiproof.value_at values index = Array.index_usize values index := rfl

#print axioms two_bits
#print axioms eight_bits
#print axioms two_width
#print axioms eight_width
#print axioms two_levels
#print axioms eight_levels
#print axioms index_result
#print axioms value_result
end NJA_Arity
