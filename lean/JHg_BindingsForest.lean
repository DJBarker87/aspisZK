import JHg_AuditForest
import JHg_World
import JFu_PublicDigest00
import JFs_Cell00
import JFs_Cell01
set_option autoImplicit false
namespace AspisR1.JHg_BindingsForest
open Aeneas Aeneas.Std Result

theorem master : (JHg_DataForest.bytes.drop 8).take 32=(JHg_World.e2.snapshot 1 384 384).key.val := by
  rw [JHg_AuditForest.master];rfl
#print axioms master
theorem forest_key : (JHg_World.e2.snapshot 2 192 192).key.val=JFs_Cell01.bytes := rfl
#print axioms forest_key
theorem root : (JHg_DataForest.bytes.drop 80).take 32=(JFx_NativeBytes.publicInput.val.drop 112).take 32 := by
  rw [JHg_AuditForest.root,JFu_PublicDigest00.selected];rfl
#print axioms root
end AspisR1.JHg_BindingsForest
