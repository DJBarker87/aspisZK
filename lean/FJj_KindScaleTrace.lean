import FJj_RegularTrace
set_option autoImplicit false
namespace AspisR1.FJj_KindScaleTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)

theorem index : Usize.wrapping_sub 2#usize 1#usize=1#usize := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_sub_val_eq]
  have size : 16≤UScalar.size .Usize := by
    rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h|h <;> simp [h]
  have v1 : (1#usize).val=1 := by scalar_tac
  have v2 : (2#usize).val=2 := by scalar_tac
  rw [v1,v2,show 2+(UScalar.size .Usize-1)=1+UScalar.size .Usize by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem reached (row : Array (Array NQ 4#usize) 5#usize) (ap1 : Array NE 4#usize)
    (s0 : NE) (tensor : Slice NQ) (back : Slice NQ → alloc.vec.Vec NQ)
    (scratchOut : alloc.vec.Vec NQ) (scale : NE)
    (run : (do
      let low1 ← Array.index_usize row 1#usize
      let s1 ← FIo_Native.weights.Weights.scalar_factor low1 ap1
      let scale ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul s0 s1
      ok (back tensor,scale))=ok (scratchOut,scale)) :
    ∃ low1 s1,Array.index_usize row 1#usize=ok low1 ∧
      FIo_Native.weights.Weights.scalar_factor low1 ap1=ok s1 ∧
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul s0 s1=ok scale ∧ scratchOut=back tensor := by
  obtain ⟨low1,hlow,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s1,hs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨scale',hm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨low1,s1,hlow,hs1,hm,rfl⟩
theorem ok_pair {A : Type} (r : core.result.Result Unit FIo_Native.verifier.Error × A) (u : Unit)
    (h : core.result.Result.Insts.CoreOpsTry.branch r.1=ok (core.ops.control_flow.ControlFlow.Continue u)) :
    r=(.Ok (),r.2) := Prod.ext (FJg_PairProvenance.continued _ _ h) rfl
#print axioms ok_pair
#print axioms index
#print axioms reached
end AspisR1.FJj_KindScaleTrace
