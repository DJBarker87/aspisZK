import R1Z.PV_RunJoin_FlatBytes35
import R1Z.PV_RunJoin_BytePrefix40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningCell41
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

def piece (w : aspis_core.field.wide_exact.WideExact) (n : Nat) : List U8 :=
  (PV_RunJoin_FlatBytes35.wire w).val.take n

theorem length (w : aspis_core.field.wide_exact.WideExact) (n : Nat) (hn : n≤32) :
    (piece w n).length=n := by
  rw [piece,List.length_take,(PV_RunJoin_FlatBytes35.wire w).property]
  exact Nat.min_eq_left hn

/-- A full serializer/index/append Result for an arbitrary wide value.
No canonicality assumption is needed: the source deliberately takes n bytes. -/
theorem append (ops : ExternalFuns) (w : aspis_core.field.wide_exact.WideExact)
    (out : alloc.vec.Vec U8) (n : Usize) (hn : n.val≤32)
    (room : out.length+n.val≤Usize.max) :
    ∃ next, (do
      let bytes ← @aspis_core.field.wide_exact.WideExact.to_le_bytes _
        (ProverRwP6BodyCandidate.selected ops) w
      let s ← core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice U8)) bytes { «end»:=n }
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s)=.ok next ∧
      next.val=out.val ++ piece w n.val := by
  obtain ⟨s,next,hs,hnxt,hv⟩ := PV_RunJoin_BytePrefix40.append
    (Array.to_slice (PV_RunJoin_FlatBytes35.wire w)) out n
    (by change n.val≤32;exact hn) room
  refine ⟨next,?_,hv⟩
  rw [PV_RunJoin_FlatBytes35.installed ops w]
  simp only [bind_tc_ok]
  change (do
    let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (Array.to_slice (PV_RunJoin_FlatBytes35.wire w)) { «end»:=n }
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s)=.ok next
  rw [hs]
  exact hnxt
#print axioms length
#print axioms append
end R1Z.PV_RunJoin_OpeningCell41
