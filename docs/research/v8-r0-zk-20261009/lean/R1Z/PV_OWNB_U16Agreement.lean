import R1Z.PV_OWNB_Padding
import R1Z.PV_OWN_U16
set_option autoImplicit false
namespace R1Z.PV_OWNB_U16Agreement
open PV_OWN_Bytes PV_OWNB_Padding
theorem unique (a b : UInt16) (raw : Bytes)
 (ha:Agrees (PV_OWN_U16.encode a) raw) (hb:Agrees (PV_OWN_U16.encode b) raw) : a=b := by
 apply PV_OWN_U16.injective
 intro i hi
 have total (v : UInt16) : ∃ b, PV_OWN_U16.encode v i=some b := by
  by_cases h0:i=0
  · subst i; exact ⟨_,rfl⟩
  · have h1:i=1 := by omega
    subst i; exact ⟨_,rfl⟩
 obtain ⟨av,hav⟩:=total a
 obtain ⟨bv,hbv⟩:=total b
 have hraw:some av=some bv := (ha i av hav).symm.trans (hb i bv hbv)
 exact hav.trans (hraw.trans hbv.symm)
#print axioms unique
end R1Z.PV_OWNB_U16Agreement
