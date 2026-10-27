import R1Z.PV_CBL_SoftBlockSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_SoftBlocks
set_option autoImplicit false
abbrev State := Array U32 8#usize
abbrev Block := Array U32 16#usize
def step (state : State) (block : Block) : State :=
  PV_CBL_FallbackStateCodec.encode (PV_CBL_SoftBlockSource.value (PV_CBL_FallbackStateCodec.decode state) block)
/-- Explicit fold of the proved block; no byte parser or native dispatcher is claimed. -/
def source (state : State) : List Block → Result State
  | [] => ok state
  | block::rest => do
      let state ← PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state block
      source state rest
def value (state : State) (blocks : List Block) : State := blocks.foldl step state
theorem composed (state : State) (blocks : List Block) : source state blocks = ok (value state blocks) := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block rest ih =>
    rw [source,PV_CBL_SoftBlockSource.source,bind_tc_ok,ih]
    rfl
#print axioms step
#print axioms source
#print axioms value
#print axioms composed
end R1Z.PV_CBL_SoftBlocks
