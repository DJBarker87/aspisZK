import XSf_A3Powers
import LPq_SelectedDomain
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSf_A3Ports
open AspisR1 AspisR1ClaimPreparedBridge

def back (x : C.E) : LPi_FieldValues.NE := LPq_ReadPorts.backE (toClaimE x)

theorem roundtrip (x : C.E) : LPq_Powers.claim (back x)=toClaimE x := rfl

theorem canonical (x : C.E) : LPi_FieldValues.canonE (back x) ↔ XRy_WideMultiply.Canonical x := Iff.rfl

theorem weights (g : XSa_DotRun.Coeff) (hg : XSa_DotRun.canonical g) :
 LPq_ReadPorts.WeightsCanonical (arr toClaimE g) := by
 intro v hv
 obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
 obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
 have hb : i<29 := by have h := g.property; change g.val.length=29 at h; omega
 let j := XRn_Join_usize i
 have hj : j.val=i := XRy_ClaimSelect.usize_value i (by omega)
 have hjb : j.val<29 := by omega
 have hc := hg j hjb
 change XRy_WideMultiply.Canonical x
 simpa only [XSa_DotRun.cell,hj,he] using hc

#print axioms roundtrip
#print axioms canonical
#print axioms weights
end XSf_A3Ports
