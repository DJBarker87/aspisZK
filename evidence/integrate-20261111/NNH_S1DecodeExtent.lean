import NNH_S1DecodeOk
set_option autoImplicit false
noncomputable section
namespace NNH_S1DecodeExtent
open RSL NNH_Libraries

theorem source (bytes : Bytes) (statement : C.Statement) (success : C.decodeStatement bytes=some statement) :
 bytes.length=1880 := by
 change LIBC_S1.decode bytes=some statement at success
 unfold LIBC_S1.decode at success
 split at success
 · assumption
 · cases success
#print axioms source
end NNH_S1DecodeExtent
