import NDO_JGp_Rows
import NDO_JFn_Basis
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Basis02
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
def node : U32 := 1734224569#u32
/-- Numeric identity for the SAME source node constructor. -/
theorem node_call : JFv_TX2_NodeCall.sourceCall (JGp_Rows.value 2).lineZ=ok node := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_NodeCall.source (JGp_Rows.value 2).lineZ
  norm_num [JGp_Rows.value,JGp_Row2.value] at value
  have same : z=node := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms node_call

theorem factor0 : doubledFactor (S7JoinBasisMachine.decode node) 0=(1734224569 : M31Exact) := by
  rfl
#print axioms factor0

theorem factor1 : doubledFactor (S7JoinBasisMachine.decode node) 1=(820909939 : M31Exact) := by
  rw [doubledFactor,factor0]
  norm_num [M31Exact,P] <;> decide
#print axioms factor1

theorem factor2 : doubledFactor (S7JoinBasisMachine.decode node) 2=(492590140 : M31Exact) := by
  rw [doubledFactor,factor1]
  norm_num [M31Exact,P] <;> decide
#print axioms factor2

theorem factor3 : doubledFactor (S7JoinBasisMachine.decode node) 3=(187108776 : M31Exact) := by
  rw [doubledFactor,factor2]
  norm_num [M31Exact,P] <;> decide
#print axioms factor3

theorem factor4 : doubledFactor (S7JoinBasisMachine.decode node) 4=(902201605 : M31Exact) := by
  rw [doubledFactor,factor3]
  norm_num [M31Exact,P] <;> decide
#print axioms factor4

theorem factor5 : doubledFactor (S7JoinBasisMachine.decode node) 5=(2058568080 : M31Exact) := by
  rw [doubledFactor,factor4]
  norm_num [M31Exact,P] <;> decide
#print axioms factor5
end AspisR1.JHl_Basis02
end
