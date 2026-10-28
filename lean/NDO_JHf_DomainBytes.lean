import JHb_DataMaster
import JHb_DataForest
import NDO_JFs_PublicValue
set_option autoImplicit false
namespace AspisR1.JHf_DomainBytes
open Aeneas Aeneas.Std Result

/-- Native identity layout: master[64+112,64+144). -/
def master : Array U8 32#usize :=
  ⟨(JHb_DataMaster.bytes.drop 176).take 32,by decide⟩
/-- Native checkpoint layout: checkpoint[40,72). -/
def checkpoint : Array U8 32#usize :=
  ⟨(JHb_DataForest.bytes.drop 40).take 32,by decide⟩

theorem master_first : master.val[0]?=some 0#u8 := rfl
#print axioms master_first
theorem checkpoint_first : checkpoint.val[0]?=some 0#u8 := rfl
#print axioms checkpoint_first
theorem public_first : JFt_SnapshotValue.value.deployment_domain.val[0]?=some 5#u8 := rfl
#print axioms public_first

theorem mismatch : master ≠ JFt_SnapshotValue.value.deployment_domain := by
  intro same
  have h:=congrArg (fun a : Array U8 32#usize=>a.val[0]?) same
  rw [master_first,public_first] at h
  have bad : (0#u8 : U8)=5#u8 := Option.some.inj h
  exact (by decide : (0#u8 : U8) ≠ 5#u8) bad
#print axioms mismatch

theorem agrees : checkpoint=master := by apply Subtype.ext;rfl
#print axioms agrees
end AspisR1.JHf_DomainBytes
