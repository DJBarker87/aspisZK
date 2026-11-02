import NEO_TailReference
import NEB_InstalledOpening
set_option autoImplicit false
namespace NEO_TailPackets
open Aeneas Aeneas.Std Result AspisR1

theorem admitted (u : Usize) (h : u.val < 262144) :
 NEO_TailRef.checked u = ok (.Ok u) := by
 have small : u < 262144#usize := by change u.val < 262144; exact h
 simp only [NEO_TailRef.checked,if_pos small]

theorem accepted (u f : Usize)
 (h : NEO_TailRef.checked u = ok (.Ok f)) : f=u ∧ f.val<262144 := by
 unfold NEO_TailRef.checked at h
 split at h
 · rename_i small
   change u.val < 262144 at small
   cases Result.ok.inj h
   exact ⟨rfl,small⟩
 · cases h

theorem opening (proof : Slice U8) (h : proof.val.length=57607)
 (i : Usize) (b : i.val<22) :
 ∃ view, NEO_TailRef.opening proof i=ok view ∧ view.val.length=832 ∧
 MultiproofConeCanonical.bytesOf view.val =
 OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) (10055+i.val*832) 832 := by
 rw [NEO_TailReference.opening]
 exact Port4B_Opening.opening_exact proof h i b

#print axioms admitted
#print axioms accepted
#print axioms opening
end NEO_TailPackets
