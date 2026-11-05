import NHI_ScalarDomain
import NHI_GroupTablesExtracted
set_option autoImplicit false
namespace NHI_GroupTables
open Aeneas Aeneas.Std Result

theorem groups : NHI_GroupTablesRef.S2_INACTIVE_GROUPS=FIo_Native.weights.S2_INACTIVE_GROUPS := by
 unfold NHI_GroupTablesRef.S2_INACTIVE_GROUPS FIo_Native.weights.S2_INACTIVE_GROUPS
 rfl

theorem masks : NHI_GroupTablesRef.S2_INACTIVE_MASKS=FIo_Native.weights.S2_INACTIVE_MASKS := by
 unfold NHI_GroupTablesRef.S2_INACTIVE_MASKS FIo_Native.weights.S2_INACTIVE_MASKS
 rfl

theorem source (j group : Usize) : NHI_GroupTablesRef.group_tables_ref j group=
 (do let g ← Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS j
     let m ← Array.index_usize FIo_Native.weights.S2_INACTIVE_MASKS group
     ok (g,m)) := by
 unfold NHI_GroupTablesRef.group_tables_ref
 rw [groups,masks]

theorem bounded_entries : ∀ g∈FIo_Native.weights.S2_INACTIVE_GROUPS.val,g.val<12 := by
 simp [FIo_Native.weights.S2_INACTIVE_GROUPS,Array.make]

theorem selected_group (j : Usize) (hj : j.val<64) :
 ∃ g,Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS j=ok g ∧ g.val<12 := by
 let g := NHI_ScalarDomain.pick FIo_Native.weights.S2_INACTIVE_GROUPS j.val hj
 exact ⟨g,NHI_ScalarDomain.index _ j hj,
  NHI_ScalarDomain.canon_pick (fun x : U8=>x.val<12) _ bounded_entries j.val hj⟩

#print axioms groups
#print axioms masks
#print axioms source
#print axioms bounded_entries
#print axioms selected_group
end NHI_GroupTables
