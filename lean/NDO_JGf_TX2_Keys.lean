import RPt_JFo_Prepared
import Port4B_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_Keys
open Aeneas Aeneas.Std Result

def raw (kind : Nat) : Array U64 16#usize :=
  Port4B_KeyInstall.keyArray JFo_Prepared.value.queries 1 kind

/-- The actual installed packed-key child returns; no successful-call premise. -/
theorem source (kind : Usize) (bound : kind.val<3) :
    Port4B_Install.leaves.op4 JFo_Prepared.value.queries 10#usize 12#usize kind=
      ok (raw kind.val) := by
  change Port4B_KeyInstall.build _ _ _ _=_
  unfold Port4B_KeyInstall.build
  rw [if_neg (by decide : ¬10#usize=0#usize)]
  rw [dif_pos (show (12#usize).val=(OraclePortSelectedDraft.batchPositions 1).length ∧
      (10#usize=0#usize ∨ 10#usize=10#usize) ∧ kind.val<3 from
    ⟨by decide,Or.inr rfl,bound⟩)]
  rfl
#print axioms source

/-- Exact prefix provenance consumed by the independently proved sorting law. -/
theorem prefix_keys (kind : Nat) :
    (raw kind).val.take 12=(OraclePortSelectedDraft.batchPositions 1).map
      (MultiproofConeSortOrder.packed (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 1 kind) := by
  change ((Port4B_KeyInstall.prefixKeys JFo_Prepared.value.queries 1 kind)++
    List.replicate (16-(Port4B_KeyInstall.prefixKeys JFo_Prepared.value.queries 1 kind).length) 0#u64).take 12=_
  have len : (Port4B_KeyInstall.prefixKeys JFo_Prepared.value.queries 1 kind).length=12 := by
    simp only [Port4B_KeyInstall.prefixKeys,OraclePortSelectedDraft.batchPositions,
      show ¬(1:Nat)=0 from by decide,if_false,List.length_map,List.length_range]
  rw [← len,List.take_left]
  rfl
#print axioms prefix_keys
end AspisR1.JGf_TX2_Keys
end
