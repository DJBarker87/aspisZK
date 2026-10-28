import NDO_JHf_DomainBytes
set_option autoImplicit false
namespace AspisR1.JHf_OffsetModel
open Aeneas Aeneas.Std Result
/-- Exact small field assembled by the wrong supplementary-image offset:
16 reserved zero bytes followed by the first16 master-key bytes. -/
def wrong : List U8 := List.replicate 16 0#u8 ++ JFs_Cell00.bytes.take 16

theorem master : JHf_DomainBytes.master.val=wrong := rfl
#print axioms master

theorem forest : JHf_DomainBytes.checkpoint.val=wrong := by
  rw [JHf_DomainBytes.agrees,master]
#print axioms forest

theorem retained_public : JFt_SnapshotValue.value.deployment_domain.val=List.replicate 32 5#u8 := rfl
#print axioms retained_public
end AspisR1.JHf_OffsetModel
