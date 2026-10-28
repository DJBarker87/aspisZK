import NDO_JHb_S2K_ResultPayload

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultHeader
open StatementAdmission

theorem take_setSlice_prefix {T : Type} (xs src : List T) (offset n : Nat)
    (before : n ≤ offset) (size : n ≤ xs.length) :
    (xs.setSlice! offset src).take n = xs.take n := by
  have room : n ≤ (xs.take offset).length := by simp only [List.length_take]; omega
  simp only [List.setSlice!]
  rw [List.append_assoc,List.take_append_of_le_length room,List.take_take,Nat.min_eq_left before]

theorem magic (s : Statement) :
    (ResultPayload.bytes s).val.take 4 = [65#u8,83#u8,82#u8,56#u8] := by
  unfold ResultPayload.bytes
  generalize Array.repeat 792#usize 0#u8 = output
  simp only [ResultEncoding.stores]
  simp [take_setSlice_prefix,List.take_set_of_le,output.property]
  simp [List.setSlice!,output.property]

#print axioms take_setSlice_prefix
#print axioms magic
end AspisR1.S2K.ResultHeader
