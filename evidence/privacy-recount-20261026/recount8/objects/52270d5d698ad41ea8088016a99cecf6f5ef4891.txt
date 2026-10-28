import R1Z.PV_RDB2D_SHAModel
namespace R1Z.PV_RDB2D_SHAState
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Core := PV_DL_ShaFinal.Core
abbrev HashState := PV_DL_ShaFinal.State
structure Restored where
  core : Core
  buffer : List U8
  cursor : Nat
  output : List U8

def finalize (compress : HashState → List U8 → Result HashState) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) (_oldOutput : Array U8 32#usize) : Result Restored := do
  let (core,buffer,cursor,out) ← PV_DL_ShaFinal.reference compress core buffer pos
  ok ⟨core,buffer,cursor,out⟩

def completeState (compress : HashState → List U8 → Result HashState) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) : Result Restored := do
  let after ← PV_DL_CompressionTrace.run compress
    (PV_CBL_PaddingModel.blocks buffer.val pos.val
      (PV_DL_LengthEncoding.suffix (PV_CBL_ShaBitLength.bitLength pos core.block_len)).val) core.state
  ok ⟨⟨after,core.block_len⟩,
    PV_CBL_PaddingModel.first buffer.val pos.val
      (PV_DL_LengthEncoding.suffix (PV_CBL_ShaBitLength.bitLength pos core.block_len)).val,
    0,(PV_DL_ShaSerialize.array after).val⟩

/-- Full four-component model Result equality; no compression-success premise.
The concrete compression implementation/source cone is still required. -/
theorem all_mutable_fields (compress : HashState → List U8 → Result HashState) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) (out : Array U8 32#usize) (h : pos.val<64) :
    finalize compress core buffer pos out=completeState compress core buffer pos := by
  unfold finalize
  rw [PV_DL_ShaFinal.source_reference compress core buffer pos h]
  simp only [PV_DL_ShaFinal.value,completeState,bind_assoc_eq,bind_tc_ok] <;> rfl

theorem output_fully_overwritten (compress : HashState → List U8 → Result HashState) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) (left right : Array U8 32#usize) :
    finalize compress core buffer pos left=finalize compress core buffer pos right := rfl

theorem arbitrary_caller {A : Type} (compress : HashState → List U8 → Result HashState) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) (out : Array U8 32#usize) (h : pos.val<64)
    (caller : Restored → Result A) :
    (finalize compress core buffer pos out >>= caller)=
      (completeState compress core buffer pos >>= caller) := by rw [all_mutable_fields _ _ _ _ _ h]

#print axioms all_mutable_fields
#print axioms output_fully_overwritten
#print axioms arbitrary_caller
end R1Z.PV_RDB2D_SHAState
