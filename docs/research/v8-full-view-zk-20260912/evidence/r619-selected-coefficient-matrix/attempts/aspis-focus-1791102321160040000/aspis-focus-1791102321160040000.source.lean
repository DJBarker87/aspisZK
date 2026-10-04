import AspisR618SelectedMatrix.Funs
import AspisV8R19.R159WideBaseExecution
import AspisV8R19.R161WrappedMulExecution
set_option autoImplicit false
namespace AspisV8R19.R619MatrixPrimitiveBridge
open AspisV8R15.ExactTowerBase (M31Exact)
open AspisV8R19.ComplexBaseExecution (encodeBase)
theorem add_encoded (a b : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.add (encodeBase a) (encodeBase b) = .ok (encodeBase (a+b)) := by
  change AspisR156FullFreeze.aspis_core.field.M31.add (encodeBase a) (encodeBase b) = .ok (encodeBase (a+b))
  exact AspisV8R19.R159WideBaseExecution.add_encode a b
theorem sub_encoded (a b : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.sub (encodeBase a) (encodeBase b) = .ok (encodeBase (a-b)) := by
  change AspisR156FullFreeze.aspis_core.field.M31.sub (encodeBase a) (encodeBase b) = .ok (encodeBase (a-b))
  exact AspisV8R19.R159WideBaseExecution.sub_encode a b
theorem double_encoded (a : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.double (encodeBase a) = .ok (encodeBase (a+a)) := by
  change AspisR156FullFreeze.aspis_core.field.M31.double (encodeBase a) = .ok (encodeBase (a+a))
  exact AspisV8R19.R159WideBaseExecution.double_encode a
theorem neg_encoded (a : M31Exact) :
    AspisR618SelectedMatrix.aspis_core.field.M31.neg (encodeBase a) = .ok (encodeBase (-a)) := by
  change AspisR156FullFreeze.aspis_core.field.M31.neg (encodeBase a) = .ok (encodeBase (-a))
  exact AspisV8R19.R161WrappedMulExecution.neg_encode a
end AspisV8R19.R619MatrixPrimitiveBridge
