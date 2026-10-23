import ImportUnionNamedDiscriminant
open Aeneas.Std
namespace ImportUnionAdapterChecks
@[import_union_discriminant isize]
inductive Error where | a | b
namespace Other
@[import_union_discriminant isize]
inductive Error where | a | b
end Other
@[import_union_discriminant u8 [1,2]]
inductive Tagged (α : Type) where | a (v : α) | b

theorem first_tag : Tagged.read_discriminant (Tagged.a (α := Nat) 7) = 1#u8 := rfl
theorem second_tag : read_discriminant (Tagged.b (α := Nat)) = 2#u8 := rfl
theorem default_tag : read_discriminant Error.b = 1#isize := rfl
#print axioms first_tag
#print axioms second_tag
#print axioms default_tag
#check Error.instDiscriminant
#check Other.Error.instDiscriminant
#check Tagged.instDiscriminant
end ImportUnionAdapterChecks
