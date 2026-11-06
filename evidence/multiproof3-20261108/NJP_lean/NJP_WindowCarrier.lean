import NJP_DigestCarrier
import MultiproofConeRead32

set_option autoImplicit false
noncomputable section
namespace NJP_WindowCarrier
open Aeneas Aeneas.Std Result NJP_RowModel NJP_DigestCarrier
open MultiproofConeRef

def bytes (physical : Slice U8) (at1 : Nat) : List U8 := (physical.val.drop at1).take 32

theorem length (physical : Slice U8) (at1 : Nat) (available : at1+32 ≤ physical.val.length) :
 (bytes physical at1).length=32 := by
 simp only [bytes,List.length_take,List.length_drop]
 omega

/-- Full borrowed-window payload, obtained from every arbitrary-offset byte
coordinate; no allocation size or zero-filled outside region is assumed. -/
theorem contents (physical : Slice U8) (at1 : Nat) (available : at1+32 ≤ physical.val.length) :
 (encode (window (fun n => physical.val[n]!) at1)).val=bytes physical at1 := by
 apply List.ext_getElem
 · rw [length physical at1 available]
   simp only [encode,List.length_ofFn]
 · intro j left right
   have byte_bound : j < 32 := by simpa only [encode,List.length_ofFn] using left
   simp only [encode,List.getElem_ofFn,bytes,List.getElem_take,List.getElem_drop]
   change physical.val[at1+j]! = physical.val[at1+j]'_
   exact getElem!_pos _ _ (by omega)

def view (physical : Slice U8) (at1 : Nat) : Slice U8 :=
 ⟨bytes physical at1,by
   have bound := physical.property
   simp only [bytes,List.length_take,List.length_drop]
   scalar_tac⟩

theorem reader (physical : Slice U8) (at1 : Nat) (available : at1+32 ≤ physical.val.length) :
 reference.read32 (view physical at1)=ok (encode (window (fun n => physical.val[n]!) at1)) := by
 obtain ⟨out,read,same⟩ := AspisR1.MultiproofConeRead32.read32_total (view physical at1)
   (by change 32 ≤ (bytes physical at1).length;rw [length physical at1 available])
 have out_contents : out.val=bytes physical at1 := by
   simpa only [view,bytes,List.take_take,Nat.min_self] using same
 have out_eq : out=encode (window (fun n => physical.val[n]!) at1) :=
   Subtype.ext (out_contents.trans (contents physical at1 available).symm)
 simpa only [out_eq] using read

theorem missing_iff (byteLength at1 : Nat) (cursor : at1 ≤ byteLength) :
 byteLength-at1 < 32 ↔ byteLength < at1+32 := by omega

#print length
#print axioms length
#print contents
#print axioms contents
#print reader
#print axioms reader
#print missing_iff
#print axioms missing_iff
end NJP_WindowCarrier
end
