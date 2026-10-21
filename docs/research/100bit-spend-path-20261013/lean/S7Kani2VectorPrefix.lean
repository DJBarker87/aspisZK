import S7Kani2ConstructorInvariant

/-! Restriction from the maximum 110-entry storage to any shorter constructor
vector is valid for in-bounds writes. This is a list-storage lemma; the P6
binding must still identify Rust Vec updates with these list updates. -/
set_option autoImplicit false
namespace S7Kani2VectorPrefix

theorem restrict_write {α : Type} (storage : List α) (length index : Nat) (value : α) :
    (storage.set index value).take length = (storage.take length).set index value := by
  exact List.take_set

theorem inverse_write_bounds (length cursor : Nat)
    (hlen : length≤110) (hcur : 0<cursor ∧ cursor≤length) :
    cursor-1<length ∧ cursor-1<110 := by omega

#print axioms restrict_write
#print axioms inverse_write_bounds
end S7Kani2VectorPrefix
