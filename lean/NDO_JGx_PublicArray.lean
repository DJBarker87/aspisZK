import RPz8_JFx_NativeBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_PublicArray
open Aeneas Aeneas.Std Result

def value : Array U8 1880#usize := ⟨JFx_NativeBytes.publicInput.val,JFx_NativeBytes.publicBytes_length⟩

theorem source : Array.to_slice value=JFx_NativeBytes.publicInput := rfl
#print axioms source

theorem length : Slice.len (Array.to_slice value)=1880#usize := by
  apply UScalar.eq_of_val_eq
  exact JFx_NativeBytes.publicBytes_length
#print axioms length
end AspisR1.JGx_PublicArray
end
