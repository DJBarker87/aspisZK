import NDO_JGp_Rows
import NDO_JFn_Basis
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Basis03
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
def node : U32 := 548654413#u32
/-- Numeric identity for the SAME source node constructor. -/
theorem node_call : JFv_TX2_NodeCall.sourceCall (JGp_Rows.value 3).lineZ=ok node := by
  obtain ⟨z,run,canon,value⟩ := JFv_TX2_NodeCall.source (JGp_Rows.value 3).lineZ
  norm_num [JGp_Rows.value,JGp_Row3.value] at value
  have same : z=node := UScalar.eq_of_val_eq value
  exact same ▸ run
#print axioms node_call

theorem factor0 : doubledFactor (S7JoinBasisMachine.decode node) 0=(548654413 : M31Exact) := by
  rfl
#print axioms factor0

theorem factor1 : doubledFactor (S7JoinBasisMachine.decode node) 1=(224041153 : M31Exact) := by
  rw [doubledFactor,factor0]
  norm_num [M31Exact,P] <;> decide
#print axioms factor1

theorem factor2 : doubledFactor (S7JoinBasisMachine.decode node) 2=(1014813006 : M31Exact) := by
  rw [doubledFactor,factor1]
  norm_num [M31Exact,P] <;> decide
#print axioms factor2

theorem factor3 : doubledFactor (S7JoinBasisMachine.decode node) 3=(915137383 : M31Exact) := by
  rw [doubledFactor,factor2]
  norm_num [M31Exact,P] <;> decide
#print axioms factor3

theorem factor4 : doubledFactor (S7JoinBasisMachine.decode node) 4=(238086242 : M31Exact) := by
  rw [doubledFactor,factor3]
  norm_num [M31Exact,P] <;> decide
#print axioms factor4

theorem factor5 : doubledFactor (S7JoinBasisMachine.decode node) 5=(1653151249 : M31Exact) := by
  rw [doubledFactor,factor4]
  norm_num [M31Exact,P] <;> decide
#print axioms factor5
end AspisR1.JHl_Basis03
end
