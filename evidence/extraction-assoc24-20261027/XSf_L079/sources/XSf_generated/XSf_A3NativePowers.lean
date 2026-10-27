import XSf_A3Ports
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSf_A3NativePowers
open AspisR1 AspisR1ClaimPreparedBridge

theorem map_back {N : Usize} (a : Array LPi_FieldValues.NE N) :
 arr XSf_A3Ports.back (arr LPq_FieldPorts.wide a)=a := by
 apply Subtype.ext
 change (a.val.map LPq_FieldPorts.wide).map XSf_A3Ports.back=a.val
 rw [List.map_map]
 have h : XSf_A3Ports.back ∘ LPq_FieldPorts.wide=id := by funext x; rfl
 rw [h,List.map_id]

/-- Reuses LPq's paired native/cohort powers, then identifies its output with
THIS observed public array. No independent native power result is assumed. -/
theorem observed {N : Usize} (x : C.E) (hx : XRy_WideMultiply.Canonical x)
 (g : Array C.E N) (hp : powersPublic N x=ok g) :
 FIo_Native.weights.powers N (XSf_A3Ports.back x)=ok (arr XSf_A3Ports.back g) := by
 obtain ⟨native,hn,ht⟩ := LPq_Powers.source N (XSf_A3Ports.back x) hx
 rw [XSf_A3Ports.roundtrip] at ht
 have actual := powersPublic_success x g hp
 have hs : arr LPq_Powers.claim native=arr toClaimE g := Result.ok.inj (ht.symm.trans actual)
 have he := congrArg (arr LPq_ReadPorts.backE) hs
 have hnback : arr LPq_ReadPorts.backE (arr LPq_Powers.claim native)=native := by
   apply Subtype.ext
   change (native.val.map LPq_Powers.claim).map LPq_ReadPorts.backE=native.val
   rw [List.map_map]
   have h : LPq_ReadPorts.backE ∘ LPq_Powers.claim=id := by funext z; rfl
   rw [h,List.map_id]
 have hgback : arr LPq_ReadPorts.backE (arr toClaimE g)=arr XSf_A3Ports.back g := by
   apply Subtype.ext
   change (g.val.map toClaimE).map LPq_ReadPorts.backE=g.val.map XSf_A3Ports.back
   rw [List.map_map]
   rfl
 rw [hnback,hgback] at he
 simpa only [he] using hn

#print axioms map_back
#print axioms observed
end XSf_A3NativePowers
