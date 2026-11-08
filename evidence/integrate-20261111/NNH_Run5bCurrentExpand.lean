import NNH_Run5bCurrentShape
import LIBC_ExpandSemantic
import LIBC_ExpandValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bCurrentExpand
open Aeneas Aeneas.Std Result NNH_Run5bCurrentShape
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem semantic_slot (src dst : Slice U8) :
 (current m env err r).op10 src dst =
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues src dst := rfl

theorem semantic (src dst : Slice U8) (ns : src.val.length=7015) (nd : dst.val.length=13831) :
 (current m env err r).op10 src dst = .ok (.Ok (),LIBC_ExpandSemanticModel.output src) := by
 rw [semantic_slot]
 exact LIBC_ExpandSemanticModel.source src dst ns nd

#print axioms semantic_slot
#print axioms semantic
end AspisR1.NNH_Run5bCurrentExpand
end
