import R1Z.PV_RDB2F_ConcreteSoft
namespace R1Z.PV_RDB2F_SoftOuter
open Aeneas Aeneas.Std Result PV_RDB2E_ShaHandles
set_option autoImplicit false
abbrev Block := Array U8 64#usize
/-- Source state_cpy; each block loads all sixteen words, then restores state_cpy. -/
def blocks : List Block → State → Result State
  | [],state_cpy => ok state_cpy
  | block::tail,state_cpy => do
      let block_u32 ← PV_CBL_ShaBytes.sha_load64 block
      let state_cpy ← PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state_cpy block_u32
      blocks tail state_cpy

theorem compression_trace (input : List Block) (state : State) :
    blocks input state=PV_DL_CompressionTrace.run PV_RDB2F_ConcreteSoft.software
      (input.map (fun b => b.val)) state := by
  induction input generalizing state with
  | nil => rfl
  | cons block tail ih =>
    simp only [blocks,List.map_cons,PV_DL_CompressionTrace.run,
      PV_RDB2F_ConcreteSoft.fixed_block,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro words hw
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next hn
    exact ih next

/-- Whole-array copy occurs after the last block, including the empty input. -/
def compress (state : State) (input : List Block) : Result State := do
  let state_cpy ← blocks input state
  ok state_cpy

theorem final_store (state : State) (input : List Block) :
    compress state input=blocks input state := by
  unfold compress
  cases blocks input state <;> rfl

theorem full_list (state : State) (input : List Block) :
    compress state input=PV_DL_CompressionTrace.run PV_RDB2F_ConcreteSoft.software
      (input.map (fun b => b.val)) state := by rw [final_store,compression_trace]

#print axioms compression_trace
#print axioms final_store
#print axioms full_list
end R1Z.PV_RDB2F_SoftOuter
