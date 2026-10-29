import R1Z.PV_OWNB_LinkFields
import R1Z.PV_OWNB_U16Agreement
set_option autoImplicit false
namespace R1Z.PV_OWNB_LinkUnique
open PV_OWN_Link PV_OWN_Bytes PV_OWNB_Padding
 theorem unique (a b : Link) (raw : Bytes)
 (ha:Agrees (PV_OWNB_LinkBytes.encode a) raw) (hb:Agrees (PV_OWNB_LinkBytes.encode b) raw) : a=b := by
 have hp:=PV_OWNB_U16Agreement.unique a.producer b.producer raw
  (PV_OWNB_LinkFields.producer a raw ha) (PV_OWNB_LinkFields.producer b raw hb)
 have hc:=PV_OWNB_U16Agreement.unique a.consumer b.consumer (fun i=>raw (2+i))
  (PV_OWNB_LinkFields.consumer a raw ha) (PV_OWNB_LinkFields.consumer b raw hb)
 have hk:=PV_OWNB_KindAgreement.unique a.kind b.kind (fun i=>raw (4+i))
  (PV_OWNB_LinkFields.kind a raw ha) (PV_OWNB_LinkFields.kind b raw hb)
 cases a; cases b; cases hp; cases hc; cases hk; rfl
#print axioms unique
end R1Z.PV_OWNB_LinkUnique
