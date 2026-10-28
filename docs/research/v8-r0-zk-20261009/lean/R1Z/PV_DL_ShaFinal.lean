import R1Z.PV_DL_LengthEncoding
import R1Z.PV_DL_ShaSerialize
import R1Z.PV_CBL_ShaCore
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_ShaFinal
set_option autoImplicit false
abbrev State := Array U32 8#usize
abbrev Core := PV_CBL_ShaCore.Core

/-- Owned complete finalizer; the compression backend remains a parameter.
The native block counter is unchanged by finalization. -/
def reference (compress : State → List U8 → Result State) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) :
    Result (Core × List U8 × Nat × List U8) := do
  let (state,retained,cursor) ← PV_DL_LengthEncoding.finalize compress core.state
    core.block_len buffer pos
  let out ← PV_DL_ShaSerialize.reference state.val
  ok (⟨state,core.block_len⟩,retained,cursor,out)

def value (compress : State → List U8 → Result State) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) :
    Result (Core × List U8 × Nat × List U8) := do
  let state ← PV_DL_CompressionTrace.run compress
    (PV_CBL_PaddingModel.blocks buffer.val pos.val
      (PV_DL_LengthEncoding.suffix (PV_CBL_ShaBitLength.bitLength pos core.block_len)).val) core.state
  ok (⟨state,core.block_len⟩,
    PV_CBL_PaddingModel.first buffer.val pos.val
      (PV_DL_LengthEncoding.suffix (PV_CBL_ShaBitLength.bitLength pos core.block_len)).val,
    0,(PV_DL_ShaSerialize.array state).val)

theorem source_reference (compress : State → List U8 → Result State) (core : Core)
    (buffer : Array U8 64#usize) (pos : Usize) (h : pos.val<64) :
    reference compress core buffer pos=value compress core buffer pos := by
  unfold reference
  rw [PV_DL_LengthEncoding.source compress core.state core.block_len buffer pos h]
  simp only [PV_DL_FinalizeParam.model,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  unfold value
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro state hs
  rw [PV_DL_ShaSerialize.total]
  rfl

theorem identity_run (events : List (List U8)) (state : State) :
    PV_DL_CompressionTrace.run (fun state _ => ok state) events state=ok state := by
  induction events with
  | nil => rfl
  | cons block tail ih => simp only [PV_DL_CompressionTrace.run,bind_tc_ok,ih]

theorem nonvacuous (core : Core) (buffer : Array U8 64#usize) (pos : Usize)
    (h : pos.val<64) :
    ∃ result, reference (fun state _ => ok state) core buffer pos=ok result := by
  rw [source_reference _ core buffer pos h]
  unfold value
  rw [identity_run]
  exact ⟨_,rfl⟩

#print axioms identity_run
#print axioms nonvacuous
#print axioms reference
#print axioms value
#print axioms source_reference
end R1Z.PV_DL_ShaFinal
