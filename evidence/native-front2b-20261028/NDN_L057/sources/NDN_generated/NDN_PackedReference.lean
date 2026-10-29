import NDE_Reference11.Funs
import NDE_RowBridge
import RPv_FJe_PackedRawAfter
import RPv_FJe_PackedRawCallbacks
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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
  change _ = (do
    let a ← Array.index_usize input 0#usize
    let a0 ← Array.index_usize a limb
    let b ← Array.index_usize input 1#usize
    let b0 ← Array.index_usize b limb
    let c ← Array.index_usize input 2#usize
    let c0 ← Array.index_usize c limb
    let d ← Array.index_usize input 3#usize
    let d0 ← Array.index_usize d limb
    match row.val with
    | 0 => do
      let x ← 2#u64 * core.convert.num.FromU64U32.from a0
      let y ← 3#u64 * core.convert.num.FromU64U32.from b0
      let z ← x+y
      let z ← z+core.convert.num.FromU64U32.from c0
      let z ← z+core.convert.num.FromU64U32.from d0
      ok (z,(input,row))
    | 1 => do
      let x ← 2#u64 * core.convert.num.FromU64U32.from b0
      let z ← core.convert.num.FromU64U32.from a0+x
      let y ← 3#u64 * core.convert.num.FromU64U32.from c0
      let z ← z+y
      let z ← z+core.convert.num.FromU64U32.from d0
      ok (z,(input,row))
    | 2 => do
      let z ← core.convert.num.FromU64U32.from a0+core.convert.num.FromU64U32.from b0
      let x ← 2#u64 * core.convert.num.FromU64U32.from c0
      let z ← z+x
      let y ← 3#u64 * core.convert.num.FromU64U32.from d0
      let z ← z+y
      ok (z,(input,row))
    | 3 => do
      let x ← 3#u64 * core.convert.num.FromU64U32.from a0
      let z ← x+core.convert.num.FromU64U32.from b0
      let z ← z+core.convert.num.FromU64U32.from c0
      let y ← 2#u64 * core.convert.num.FromU64U32.from d0
      let z ← z+y
      ok (z,(input,row))
    | _ => fail .panic)
  obtain ⟨a,ha,_⟩ := NDE_RowBridge.read_total input 0#usize (by decide)
  obtain ⟨b,hb,_⟩ := NDE_RowBridge.read_total input 1#usize (by decide)
  obtain ⟨c,hc,_⟩ := NDE_RowBridge.read_total input 2#usize (by decide)
  obtain ⟨d,hd,_⟩ := NDE_RowBridge.read_total input 3#usize (by decide)
  obtain ⟨a0,ha0,_⟩ := NDE_RowBridge.read_total a limb hl
  obtain ⟨b0,hb0,_⟩ := NDE_RowBridge.read_total b limb hl
  obtain ⟨c0,hc0,_⟩ := NDE_RowBridge.read_total c limb hl
  obtain ⟨d0,hd0,_⟩ := NDE_RowBridge.read_total d limb hl
  simp only [ha,hb,hc,hd,ha0,hb0,hc0,hd0,bind_tc_ok,NDE_Reference11.matrix_cell_ref,lift]
  split <;> simp_all only [bind_tc_ok,bind_tc_fail,bind_assoc_eq]

#print axioms after
#print axioms matrix
end NDN_PackedReference
end
