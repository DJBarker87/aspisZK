import NDE_Reference11.Funs
import NDE_RowBridge
import RPv_FJe_PackedRawAfter
import RPv_FJe_PackedRawCallbacks
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NDN_PackedReference
open AspisR1

theorem after (table : FJe_PackedRawAfter.Table) (bound : U64) :
    NDE_Reference11.packed_after_ref table bound = FJe_PackedRawAfter.source table bound := rfl

theorem matrix (input : FJb_RawRowCallbacks.Input) (row limb : Usize)
    (hl : limb.val < 4) :
    (do let a ← Array.index_usize input 0#usize
        let a0 ← Array.index_usize a limb
        let b ← Array.index_usize input 1#usize
        let b0 ← Array.index_usize b limb
        let c ← Array.index_usize input 2#usize
        let c0 ← Array.index_usize c limb
        let d ← Array.index_usize input 3#usize
        let d0 ← Array.index_usize d limb
        let out ← NDE_Reference11.matrix_cell_ref a0 b0 c0 d0 row
        ok (out,(input,row))) = FJe_PackedRawCallbacks.call (input,row) limb := by
  rcases row with ⟨rv,rp⟩
  obtain ⟨a,ha,_⟩ := NDE_RowBridge.read_total input 0#usize (by decide)
  obtain ⟨b,hb,_⟩ := NDE_RowBridge.read_total input 1#usize (by decide)
  obtain ⟨c,hc,_⟩ := NDE_RowBridge.read_total input 2#usize (by decide)
  obtain ⟨d,hd,_⟩ := NDE_RowBridge.read_total input 3#usize (by decide)
  obtain ⟨a0,ha0,_⟩ := NDE_RowBridge.read_total a limb hl
  obtain ⟨b0,hb0,_⟩ := NDE_RowBridge.read_total b limb hl
  obtain ⟨c0,hc0,_⟩ := NDE_RowBridge.read_total c limb hl
  obtain ⟨d0,hd0,_⟩ := NDE_RowBridge.read_total d limb hl
  simp only [FJe_PackedRawCallbacks.call,
    FIq_Native.state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut,
    ha,hb,hc,hd,ha0,hb0,hc0,hd0,bind_tc_ok,NDE_Reference11.matrix_cell_ref,lift]
  split <;> first | rfl | (simp only [bind_tc_ok,bind_assoc_eq]; rfl)

#print axioms matrix
end NDN_PackedReference
end
