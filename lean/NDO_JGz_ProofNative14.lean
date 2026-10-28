import NDO_JGz_SHAP56
import RPz8_JFx_DataProof14
set_option autoImplicit false
namespace AspisR1.JGz_ProofNative14
open Aeneas Aeneas.Std
def chunks : List (List Nat) := [JGz_SHAP56.B896.input,JGz_SHAP56.B897.input,JGz_SHAP56.B898.input,JGz_SHAP56.B899.input]
def tail : List Nat := List.replicate 7 0
theorem cell00 : JGz_SHAP56.B896.input=(JFx_DataProof14.c00 ++ JFx_DataProof14.c01).map (fun x=>x.val) := by rfl
#print axioms cell00
theorem cell01 : JGz_SHAP56.B897.input=(JFx_DataProof14.c02 ++ JFx_DataProof14.c03).map (fun x=>x.val) := by rfl
#print axioms cell01
theorem cell02 : JGz_SHAP56.B898.input=(JFx_DataProof14.c04 ++ JFx_DataProof14.c05).map (fun x=>x.val) := by rfl
#print axioms cell02
theorem cell03 : JGz_SHAP56.B899.input=(JFx_DataProof14.c06 ++ JFx_DataProof14.c07).map (fun x=>x.val) := by rfl
#print axioms cell03
theorem tail_native : JFx_DataProof14.c08.map (fun x=>x.val)=tail := by rfl
#print axioms tail_native
theorem native : JFx_DataProof14.bytes.map (fun x=>x.val)=chunks.flatten ++ tail := by
  unfold chunks
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [cell00,cell01,cell02,cell03]
  rw [←tail_native]
  simp only [JFx_DataProof14.bytes,List.map_append,List.append_assoc]
#print axioms native
end AspisR1.JGz_ProofNative14
