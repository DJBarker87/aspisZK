import FJf_EbyKNew
import FJf_QMArray
import FIp_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_HighCell
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)

def term (p : Array NE 4#usize) (q : Array NQ 4#usize) (j : Nat) : AspisWideTower.WideExact :=
  FIp_ArrayValue.value p j*⟨FJf_QMArray.value q j,0⟩

def sumPrefix (p : Array NE 4#usize) (q : Array NQ 4#usize) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumPrefix p q n+term p q n

theorem value (p : Array NE 4#usize) (q : Array NQ 4#usize)
    (hp : FIo_ArrayCanon.Holds p) (hq : FJf_QMArray.canon q)
    (iter cursor : FIo_RangeNext.Range) (dot next : FIo_Native.fast_pairing.EbyKDot)
    (bound : FJf_EbyKCodec.Bound dot)
    (run : FIo_Native.weights.high_dot_loop.body p q iter dot=ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    FJf_EbyKCodec.Bound next ∧ next.count.val=dot.count.val+1 ∧
    FJf_EbyKCodec.model next=FJf_EbyKCodec.model dot+term p q iter.start.val := by
  unfold FIo_Native.weights.high_dot_loop.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
  | some s =>
    obtain ⟨v,hv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨c,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨r,next'⟩,hpush,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases r with
    | Err e => cases run
    | Ok u =>
      cases u
      cases Result.ok.inj run
      have pr := FIo_RangeNext.some_next iter cursor s hn
      have cv := FIo_ArrayCanon.read p s v hp hv
      have cq := hq c (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hc))
      have push := FJf_EbyKPush.value dot next v c cv cq bound hpush
      refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,push.2.1,push.1,?_⟩
      rw [push.2.2,term,FJf_EbyKCodec.scalar,←FIp_ArrayValue.read p s v hv,←FJf_QMArray.read q s c hc,pr.1]

#print axioms value
end AspisR1.FJg_HighCell
end
