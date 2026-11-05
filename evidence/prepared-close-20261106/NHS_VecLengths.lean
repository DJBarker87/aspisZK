import NHL_PreparedOpening
import NFW_Invert
set_option autoImplicit false
namespace AspisR1.NHS_VecLengths
open Aeneas Aeneas.Std Result
/-- Cloning preserves length even for an arbitrary element clone operation. -/
theorem clone_length {T : Type} (f : T → Result T) (s out : Slice T)
 (call : Slice.clone f s=ok out) : out.val.length=s.val.length := by
 unfold Slice.clone at call
 obtain ⟨copy,_,last⟩ := NFW_Invert.bind _ _ _ call
 have same := Result.ok.inj last
 subst out
 exact copy.property

theorem extend_length {T : Type} (clone : core.clone.Clone T)
 (v out : alloc.vec.Vec T) (s : Slice T)
 (call : alloc.vec.Vec.extend_from_slice clone v s=ok out) :
 out.val.length=v.val.length+s.val.length := by
 unfold alloc.vec.Vec.extend_from_slice at call
 split at call
 · split at call
   · rename_i copy cloned
     have same := Result.ok.inj call
     subst out
     rw [List.length_append,clone_length clone.clone s copy cloned]
   · cases call
   · cases call
 · cases call
#print axioms clone_length
#print axioms extend_length
end AspisR1.NHS_VecLengths
