import LIBC_VTx1A
import LIB_ParseShapeTotal
set_option autoImplicit false
noncomputable section
namespace LIB_VTx1A
abbrev parseShape := LIB_ParseShapeTotal.child
abbrev canonicalScan := LIBC_VTx1A.canonicalScan
abbrev accNew := LIBC_VTx1A.accNew
abbrev weightsNew := LIBC_VTx1A.weightsNew
abbrev finish := LIBC_VTx1A.finish
theorem parseShape_domain (proof : RSL.Bytes) : parseShape.dom proof := True.intro
theorem parseShape_functional : RSL.Child.Functional parseShape := LIB_ParseShapeTotal.functional
#print axioms parseShape_domain
#print axioms parseShape_functional
end LIB_VTx1A
