import LIBC_Filled
import LIBC_ExpandSemantic
import LIBC_ExpandValues
import LIBC_WideView
set_option autoImplicit false
noncomputable section
namespace LIBC_VPrepare
open RSL
abbrev filled : Child Nat (Except Unit Bytes) := LIBC_Filled.child
abbrev expandSemantic : Child (Bytes × Bytes) (Except LIB_VCarriers.CodecErr Bytes) := LIBC_ExpandSemantic.child
abbrev expandValues : Child (Bytes × Bytes) (Except LIB_VCarriers.CodecErr Bytes) := LIBC_ExpandValues.child
abbrev wideView : Child (Bytes × Bytes × Bytes) (Except LIB_VCarriers.VErr LIB_VCarriers.View) := LIBC_WideView.child
theorem filled_exact : filled = LIBC_Filled.child := rfl
theorem expandSemantic_exact : expandSemantic = LIBC_ExpandSemantic.child := rfl
theorem expandValues_exact : expandValues = LIBC_ExpandValues.child := rfl
theorem wideView_exact : wideView = LIBC_WideView.child := rfl
#print axioms filled_exact
#print axioms expandSemantic_exact
#print axioms expandValues_exact
#print axioms wideView_exact
end LIBC_VPrepare
