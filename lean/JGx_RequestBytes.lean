import JGx_MagicGate
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_RequestBytes
open Aeneas Aeneas.Std Result

def magic : Slice U8 := ⟨[65#u8,83#u8,81#u8,56#u8],by simp;scalar_tac⟩
def value (payload : Array U8 316#usize) : Slice U8 :=
  ⟨magic.val++payload.val,by simp only [List.length_append,magic,List.length_cons,List.length_nil,payload.property];scalar_tac⟩

theorem length (payload : Array U8 316#usize) : Slice.len (value payload)=320#usize := by
  apply UScalar.eq_of_val_eq
  change (magic.val++payload.val).length=320
  rw [List.length_append,payload.property]
  rfl
#print axioms length

theorem first (payload : Array U8 316#usize) :
    (value payload).val.take 4=magic.val := by
  change (magic.val++payload.val).take 4=magic.val
  have size : magic.val.length=4 := rfl
  have h : (magic.val++payload.val).take magic.val.length=magic.val := List.take_left
  simpa only [size] using h
#print axioms first
end AspisR1.JGx_RequestBytes
end
