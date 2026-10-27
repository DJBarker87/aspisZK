import RPv_FJj_TensorBody
import RPv_FJj_TensorModelAdvance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorInner
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)
open FJa_ReverseStep (cursor)
open FJj_TensorModelAdvance (expanded FK)

theorem value (self selfOut : FIo_Native.weights.Weights) (k d n e : Usize)
    (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize self.factors k=ok row) (hd : Array.index_usize row d=ok digit)
    (hn : n.val≤16) (he : e.val≤n.val)
    (input out : Slice NQ) (base : Nat → FK)
    (hc : FJf_QMArray.canon digit) (hs : FJj_QMSlice.canon input)
    (inv : ∀ t,FJj_QMSlice.value input t=expanded base digit n.val e.val t)
    (run : FIo_Native.weights.Weights.tensor_loop0_loop0 (cursor e) self k input n d=ok (selfOut,out)) :
    selfOut=self ∧ FJj_QMSlice.canon out ∧ out.val.length=input.val.length ∧
      ∀ t,FJj_QMSlice.value out t=expanded base digit n.val 0 t := by
  generalize hm : e.val=m
  induction m using Nat.strong_induction_on generalizing e input with
  | h m ih =>
    by_cases hz : m=0
    · have ez : e=0#usize := by apply UScalar.eq_of_val_eq;change e.val=0;omega
      subst e
      unfold FIo_Native.weights.Weights.tensor_loop0_loop0 at run
      rw [loop] at run
      have stop := FJj_TensorBody.done self k n d (cursor 0#usize) (cursor 0#usize) input FJa_ReverseStep.stop
      simp only [stop,bind_tc_ok] at run
      cases Result.ok.inj run
      refine ⟨rfl,hs,rfl,?_⟩
      exact inv
    · obtain ⟨j,hj,hnext⟩ := FJa_ReverseStep.step e (by omega)
      unfold FIo_Native.weights.Weights.tensor_loop0_loop0 at run
      rw [loop] at run
      cases hb : FIo_Native.weights.Weights.tensor_loop0_loop0.body self k n d (cursor e) input with
      | fail err => simp only [hb] at run;cases run
      | div => simp only [hb] at run;cases run
      | ok r =>
        obtain ⟨mid,rfl⟩ := FJj_TensorBody.cont self k n d j (cursor e) (cursor j) input hnext r hb
        simp only [hb,bind_tc_ok] at run
        obtain ⟨cm,len,vm⟩ := FJj_TensorCellValue.value self k d n j row digit hr hd
          (cursor e) (cursor j) input mid hc hs hnext hb
        have nextInv : ∀ t,FJj_QMSlice.value mid t=expanded base digit n.val j.val t := by
          intro t
          rw [vm t]
          exact FJj_TensorModelAdvance.value base input digit j n e.val hn (by omega) hj inv t
        have tail : FIo_Native.weights.Weights.tensor_loop0_loop0 (cursor j) self k mid n d=
            ok (selfOut,out) := run
        have result := ih j.val (by omega) j (by omega) mid cm nextInv tail rfl
        exact ⟨result.1,result.2.1,result.2.2.1.trans len,result.2.2.2⟩
#print axioms value
end AspisR1.FJj_TensorInner
end
