import RPt_JFo_Prepared
import NDO_JGp_Keys0
import NDO_JGp_Keys1
import NDO_JGp_Keys2
import Port4B_SortInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGr_Keys
open Aeneas Aeneas.Std Result

def q := Port4B_KeyInstall.queries JFo_Prepared.value.queries
def raw (kind : Nat) : Array U64 16#usize :=
  Port4B_KeyInstall.keyArray JFo_Prepared.value.queries 0 kind

theorem build (kind : Usize) (bound : kind.val<3) :
    Port4B_Install.leaves.op4 JFo_Prepared.value.queries 0#usize 10#usize kind=
      ok (raw kind.val) := by
  change Port4B_KeyInstall.build _ _ _ _=_
  unfold Port4B_KeyInstall.build
  rw [if_pos rfl]
  rw [dif_pos (show (10#usize).val=(OraclePortSelectedDraft.batchPositions 0).length ∧
      (0#usize=0#usize ∨ 0#usize=10#usize) ∧ kind.val<3 from
    ⟨by decide,Or.inl rfl,bound⟩)]
  rfl
#print axioms build

theorem prefix_keys (kind : Nat) :
    (raw kind).val.take 10=(OraclePortSelectedDraft.batchPositions 0).map
      (MultiproofConeSortOrder.packed q 0 kind) := by
  change ((Port4B_KeyInstall.prefixKeys JFo_Prepared.value.queries 0 kind)++
    List.replicate (16-(Port4B_KeyInstall.prefixKeys JFo_Prepared.value.queries 0 kind).length) 0#u64).take 10=_
  have len : (Port4B_KeyInstall.prefixKeys JFo_Prepared.value.queries 0 kind).length=10 := by
    simp only [Port4B_KeyInstall.prefixKeys,OraclePortSelectedDraft.batchPositions,
      if_true,List.length_map,List.length_range]
  rw [←len,List.take_left]
  rfl
#print axioms prefix_keys

theorem source (kind : Nat) : ∃ out : Array U64 16#usize,
    Port4B_Install.leaves.op5 (raw kind) 10#usize=ok out ∧
    Port4B_LeafLoop.KeyStream q 0 kind out 0#usize
      (OraclePortFrozenOrder.sortedPositions q 0 kind) := by
  obtain ⟨out,run,_front,_suffix⟩ := MultiproofConeSortOrder.sorted_positions q 0 kind
    (raw kind) 10#usize (by decide) (prefix_keys kind)
  rw [MultiproofConeSortOrder.source_start_one _ _ (by decide)] at run
  refine ⟨out,run,?_⟩
  exact (Port4B_SortInstall.key_stream Port4B_Install.leaves q 0 kind
    (raw kind) out 10#usize (by decide) (by decide) (prefix_keys kind) run).2
#print axioms source
end AspisR1.JGr_Keys
end
