import R1Z.PV_CBL_LibraryShapes
namespace R1Z.PV_CBL_BufferReference
open PV_CBL_LibraryShapes
set_option autoImplicit false

/-- The value-only default field shape in block-buffer 0.10.4. Source/default
array initialization and native association are not asserted by this model. -/
def initial {A : Type} (array : A) : Buffer A := ⟨array,0#u8,()⟩

def data {T : Type} (flatten : T→List Aeneas.Std.U8) (v : Buffer T) : List Aeneas.Std.U8 :=
  (flatten v.buffer).take v.pos.val

theorem initial_pos {A : Type} (a : A) : (initial a).pos.val=0 := rfl

theorem initial_data {T : Type} (flatten : T→List Aeneas.Std.U8) (a : T) :
    data flatten (initial a)=[] := by simp [data,initial]

theorem data_length {T : Type} (flatten : T→List Aeneas.Std.U8) (v : Buffer T)
    (h : v.pos.val≤(flatten v.buffer).length) : (data flatten v).length=v.pos.val := by
  simp only [data,List.length_take,Nat.min_eq_left h]

#print axioms initial
#print axioms data
#print axioms initial_pos
#print axioms initial_data
#print axioms data_length
end R1Z.PV_CBL_BufferReference
