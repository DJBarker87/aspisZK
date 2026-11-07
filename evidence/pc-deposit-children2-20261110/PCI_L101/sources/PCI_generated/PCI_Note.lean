import PCI_NoteRef.Funs
import PCF_ArrayIndex
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_Note
universe u v
abbrev Digest := Array U32 8#usize
/-- Frozen spend.rs155-166 input order; raw words retained without a canonicality restriction. -/
def input (owner : Digest) (value asset : U32) (salt : Digest) : Array U32 18#usize :=
  Array.make 18#usize [owner.val[0]!, owner.val[1]!, owner.val[2]!, owner.val[3]!, owner.val[4]!, owner.val[5]!, owner.val[6]!, owner.val[7]!, value, asset, salt.val[0]!, salt.val[1]!, salt.val[2]!, salt.val[3]!, salt.val[4]!, salt.val[5]!, salt.val[6]!, salt.val[7]!]
/-- NCO reference value, extracted under the pinned tools; no hash or product is evaluated. -/
theorem extracted_input (owner : Digest) (value asset : U32) (salt : Digest) :
    PCI_NoteRef.note_input owner value asset salt = ok (input owner value asset salt) := by
  unfold PCI_NoteRef.note_input
  simp only [PCF_ArrayIndex.result owner 0#usize (by scalar_tac), PCF_ArrayIndex.result owner 1#usize (by scalar_tac), PCF_ArrayIndex.result owner 2#usize (by scalar_tac), PCF_ArrayIndex.result owner 3#usize (by scalar_tac), PCF_ArrayIndex.result owner 4#usize (by scalar_tac), PCF_ArrayIndex.result owner 5#usize (by scalar_tac), PCF_ArrayIndex.result owner 6#usize (by scalar_tac), PCF_ArrayIndex.result owner 7#usize (by scalar_tac), PCF_ArrayIndex.result salt 0#usize (by scalar_tac), PCF_ArrayIndex.result salt 1#usize (by scalar_tac), PCF_ArrayIndex.result salt 2#usize (by scalar_tac), PCF_ArrayIndex.result salt 3#usize (by scalar_tac), PCF_ArrayIndex.result salt 4#usize (by scalar_tac), PCF_ArrayIndex.result salt 5#usize (by scalar_tac), PCF_ArrayIndex.result salt 6#usize (by scalar_tac), PCF_ArrayIndex.result salt 7#usize (by scalar_tac), bind_tc_ok]
  rfl

/-- The generic hash sees exactly one request; its full reply, state and ordered
    effects remain those of that same invocation, including an abort prefix. -/
def applyHash {State : Type u} {Outcome : Type v} (hash : U32 → Array U32 18#usize → State → Outcome)
    (owner : Digest) (value asset : U32) (salt : Digest) (state : State) : Outcome :=
  hash 1095958531#u32 (input owner value asset salt) state

theorem forwarding {State : Type u} {Outcome : Type v} (hash : U32 → Array U32 18#usize → State → Outcome)
    (owner : Digest) (value asset : U32) (salt : Digest) (state : State) :
    applyHash hash owner value asset salt state =
      hash 1095958531#u32 (input owner value asset salt) state := rfl

#print axioms extracted_input
#print axioms forwarding
end PCI_Note
