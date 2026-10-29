import PV_B3P_PreparedBinding13227
namespace PV_B3P_PreparedNative14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227
set_option autoImplicit false
/-- The deployed private payload, copied field for field. This abstraction does
not assume that arbitrary U32 limbs are canonical field representatives. -/
structure NativePrepared14 where
  components : Array (Array U32 3#usize) 3#usize

def to_reference14 (value : NativePrepared14) : reference_field.PreparedQm31Multiplier :=
  ⟨value.components⟩
def from_reference14 (value : reference_field.PreparedQm31Multiplier) : NativePrepared14 :=
  ⟨value.components⟩

theorem prepared_components14 (value : NativePrepared14) :
    (to_reference14 value).components = value.components := rfl

theorem prepared_roundtrip14 (value : NativePrepared14) :
    from_reference14 (to_reference14 value) = value := by cases value; rfl

theorem prepared_reverse_roundtrip14 (value : reference_field.PreparedQm31Multiplier) :
    to_reference14 (from_reference14 value) = value := by cases value; rfl

def map_array14 {α β : Type} {n : Usize} (f : α → β) (values : Array α n) : Array β n :=
  ⟨values.val.map f,by simp only [List.length_map,values.property]⟩

theorem map_array_index14 {α β : Type} {n : Usize} (f : α → β)
    (values : Array α n) (index : Usize) :
    Array.index_usize (map_array14 f values) index =
      (do let value ← Array.index_usize values index; .ok (f value)) := by
  change (match (values.val.map f)[index.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some value => Result.ok value) = (do
      let value ← (match values.val[index.val]? with
        | none => Result.fail Error.arrayOutOfBounds
        | some value => Result.ok value)
      .ok (f value))
  rw [List.getElem?_map]
  cases h : values.val[index.val]? <;> rfl
#print axioms prepared_components14
#print axioms prepared_roundtrip14
#print axioms prepared_reverse_roundtrip14
#print axioms map_array_index14
end PV_B3P_PreparedNative14227
