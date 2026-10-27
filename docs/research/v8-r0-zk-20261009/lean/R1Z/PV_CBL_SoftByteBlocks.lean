import R1Z.PV_CBL_SoftByteSource
import R1Z.PV_CBL_SoftBlocksAppend
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_SoftByteBlocks
set_option autoImplicit false
abbrev State := Array U32 8#usize
abbrev Block := Array U8 64#usize
def reference (state : State) : List Block → Result State
  | [] => ok state
  | b::bs => do
      let next ← PV_CBL_SoftByteSource.reference state b
      reference next bs
def value (state : State) (blocks : List Block) : State :=
  blocks.foldl PV_CBL_SoftByteSource.value state
theorem source (state : State) (blocks : List Block) : reference state blocks = ok (value state blocks) := by
  induction blocks generalizing state with
  | nil => rfl
  | cons b bs ih =>
    rw [reference,PV_CBL_SoftByteSource.source,bind_tc_ok,ih]
    rfl
theorem append (state : State) (a b : List Block) :
    reference state (a++b) = (do
      let next ← reference state a
      reference next b) := by
  simp only [source,bind_tc_ok]
  exact congrArg ok (List.foldl_append)
#print axioms reference
#print axioms value
#print axioms source
#print axioms append
end R1Z.PV_CBL_SoftByteBlocks
