import NMT_R2_Bytes
set_option autoImplicit false
noncomputable section
namespace NMT_R2_InputSlice
open Aeneas Aeneas.Std RSL NMT_R2_Bytes

def statement (bytes : Bytes) (length : bytes.length = 1880) : Slice U8 :=
 ⟨native bytes,by
  have bound : 1880 ≤ Usize.max := by scalar_tac
  simpa only [native,List.length_map,length] using bound⟩

theorem statement_length (bytes : Bytes) (length : bytes.length = 1880) :
 (statement bytes length).val.length = 1880 := by
 simp only [statement,native,List.length_map,length]

theorem statement_bytes (bytes : Bytes) (length : bytes.length = 1880) :
 (statement bytes length).val.map NMT_345.byte = bytes := bytes_native bytes
#print axioms statement_length
#print axioms statement_bytes
end NMT_R2_InputSlice
end
