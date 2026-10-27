import JGj_ZeroSubtract
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalZeroCall
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
open FJb_TailCell (cell)
abbrev Callback := state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
theorem source (a : Raw) (w : Words) (i : Usize) (hi : i.val<(4#usize).val)
    (ha : Bound a (61*P)) (hw : Canonical w) :
    ∃ out,Callback.call_mut (a,w) i=ok (out,(a,w)) := by
  let x := cell a ⟨i.val,hi⟩
  let y := cell w ⟨i.val,hi⟩
  have rx : Array.index_usize a i=ok x := RawPoseidonExternalRowReads.array_index_usize_ok a i hi
  have ry : Array.index_usize w i=ok y := RawPoseidonExternalRowReads.array_index_usize_ok w i hi
  obtain ⟨out,ro⟩ := JGj_ZeroSubtract.success x y (ha _) (hw _)
  have paired : (do let out ← JGj_ZeroSubtract.source x y;ok (out,(a,w)))=ok (out,(a,w)) := by rw [ro,bind_tc_ok]
  refine ⟨out,?_⟩
  change (do
    let x ← Array.index_usize a i
    let p ← UScalar.add x (FJb_WideSum4.wide field.P)
    let y ← Array.index_usize w i
    let out ← UScalar.sub p (FJb_WideSum4.wide y)
    ok (out,(a,w)))=ok (out,(a,w))
  simp only [rx,ry,bind_tc_ok]
  simpa only [JGj_ZeroSubtract.source,bind_assoc_eq] using paired
#print axioms source
end AspisR1.JGj_InternalZeroCall
end
