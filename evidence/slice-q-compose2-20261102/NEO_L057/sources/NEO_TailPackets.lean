import NEO_TailReference
import NEB_InstalledOpening
set_option autoImplicit false
namespace NEO_TailPackets
open Aeneas Aeneas.Std Result AspisR1

theorem admitted {C : Type} (error : C) (u : Usize) (h : u.val < 262144) :
 (do let r ← NEO_TailRef.checked u
     ok (match r with | .Ok x => (core.result.Result.Ok x : core.result.Result Usize C) | .Err _ => .Err error)) = ok (.Ok u) := by
 rw [← NEO_TailReference.checked error u]
 exact NEB_GeometryIndices.admitted error u h

theorem accepted {C : Type} (error : C) (u f : Usize)
 (h : (do let r ← NEO_TailRef.checked u
          ok (match r with | .Ok x => (core.result.Result.Ok x : core.result.Result Usize C) | .Err _ => .Err error)) = ok (.Ok f)) :
 f=u ∧ f.val<262144 := by
 rw [← NEO_TailReference.checked error u] at h
 exact NEB_GeometryIndices.accepted error u f h

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
