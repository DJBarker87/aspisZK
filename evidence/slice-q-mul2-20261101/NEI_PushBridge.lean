import NEG_PushAssociation
import NEI_RowBridge
set_option autoImplicit false
noncomputable section
namespace NEI_PushBridge
open Aeneas Aeneas.Std Result
abbrev BW := NEG_PushActual.BatchedWeights
abbrev Power := NEG_RowAssociation.Power
abbrev rowRead (b : BW) (index : Usize) :=
 alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) b.raw index
/-- Same full carrier, selected child input, returned row, Vec restoration and
unchanged terms; unrestricted Result equality. -/
theorem same_call (b : BW) (index : Usize) (p : Power) (basis : U32) :
 NEG_PushActual.BatchedWeights.push b index p basis =
 (do let row ← rowRead b index
     let out ← NEG_RowIsolated.update_residue_row row p basis
       ((b.terms &&& 3#usize)=3#usize)
     ok ({b with raw := b.raw.set index out} : BW)) := by
 rw [NEG_PushAssociation.source,Port26ROW.owned_push_complete]
 simp only [NEG_RowAssociation.emitted_to_owned,rowRead,bind_assoc_eq,bind_tc_ok]

def Domain (b : BW) (index : Usize) (p : Power) (basis : U32) : Prop :=
 index.val < b.raw.val.length ∧
 ∀ row, rowRead b index=ok row → NEI_RowBridge.Domain row p basis

theorem complete (b : BW) (index : Usize) (p : Power) (basis : U32)
 (domain : Domain b index p basis) :
 ∃ row out,
 rowRead b index=ok row ∧ NEI_RowBridge.Domain row p basis ∧
 NEG_RowIsolated.update_residue_row row p basis ((b.terms &&& 3#usize)=3#usize)=ok out ∧
 NEG_PushActual.BatchedWeights.push b index p basis=
 ok ({b with raw := b.raw.set index out} : BW) := by
 obtain ⟨row,read,_⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b.raw index domain.1)
 have hr : rowRead b index=ok row := read
 have safe := domain.2 row hr
 obtain ⟨out,run,_⟩ := NEI_RowBridge.complete row p basis _ safe
 refine ⟨row,out,hr,safe,run,?_⟩
 rw [same_call,hr]
 simp only [bind_tc_ok,run]
#print axioms same_call
#print axioms complete
end NEI_PushBridge
end
