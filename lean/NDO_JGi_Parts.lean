import NDO_JGi_DotTotal
import CurrentClaimPartsUpdates
set_option autoImplicit false
namespace AspisR1.JGi_Parts
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim Concrete

def CanonicalArray (a : Array E 7#usize) : Prop := ∀ j h,Canonical (cell a j h)

theorem update (a : Array E 7#usize) (i : Usize) (x : E) (hi : i.val<7)
    (ha : CanonicalArray a) (hx : Canonical x) :
    ∃ out,Array.update a i x=ok out ∧ CanonicalArray out := by
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists (Array.update_spec a i x (by simpa only [a.property,show (7#usize).val=7 from rfl] using hi))
  refine ⟨out,call,?_⟩
  intro j hj
  rw [ClaimParts.update_cells a out i x hi call j hj]
  split
  · exact hx
  · exact ha j hj
#print axioms update

theorem zero : CanonicalArray (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) := by
  intro j hj
  simp only [cell,Array.repeat,List.getElem_replicate]
  exact zero_canonical
#print axioms zero

theorem initial (inactive : E) (h : Canonical inactive) :
    ∃ parts,Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) 0#usize inactive=ok parts ∧
      CanonicalArray parts := update _ _ _ (by decide) zero h
#print axioms initial
end AspisR1.JGi_Parts
