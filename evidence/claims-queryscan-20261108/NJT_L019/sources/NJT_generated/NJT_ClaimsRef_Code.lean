import NJT_ClaimsRef_Funs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_ClaimsRef_Code
open Aeneas Aeneas.Std Result
open AspisR1ClaimsUnrolledParent

def singleton (value : Claims) : Slice Claims := ⟨[value], by simp; scalar_tac⟩

theorem clone_array {T : Type} (n : Usize) (c : core.clone.Clone T)
 (law : ∀ value, c.clone value = ok value) (a : Array T n) :
 (core.clone.CloneArray n c).clone a = ok a := by
 change Array.clone c.clone a = ok a
 obtain ⟨out,run,same⟩ := WP.spec_imp_exists
   (Array.clone_spec (s:=a) (by intro value member; exact law value))
 simpa only [same] using run

theorem filled_one (value : Claims) :
 NJT_ClaimsRef.aspis_core.r0.heap.filled
  (Array.Insts.CoreMarkerCopy 3#usize (Array.Insts.CoreMarkerCopy 29#usize
    NJT_ClaimsRef.aspis_core.field.QM31.Insts.CoreMarkerCopy)) 1#usize value =
 ok (.Ok (singleton value)) := by
 let cq := NJT_ClaimsRef.aspis_core.field.QM31.Insts.CoreCloneClone
 have hq : ∀ q, cq.clone q = ok q := fun _ => rfl
 have rows : ∀ r : Row, (core.clone.CloneArray 29#usize cq).clone r = ok r :=
   fun r => clone_array 29#usize cq hq r
 have allrows := clone_array 3#usize (core.clone.CloneArray 29#usize cq) rows value
 obtain ⟨out,run,shape⟩ := WP.spec_imp_exists
   (alloc.vec.Vec.resize_spec (core.clone.CloneArray 3#usize (core.clone.CloneArray 29#usize cq))
    (alloc.vec.Vec.new Claims) 1#usize value allrows)
 have same : out = singleton value := by
   apply Subtype.ext
   simpa only [alloc.vec.Vec.new] using shape
 unfold NJT_ClaimsRef.aspis_core.r0.heap.filled
 rw [run,same]
 rfl

#print axioms clone_array
#print axioms filled_one
end AspisR1.NJT_ClaimsRef_Code
end
