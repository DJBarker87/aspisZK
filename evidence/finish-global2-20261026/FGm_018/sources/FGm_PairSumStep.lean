import FGm_ArrayValue
import FGm_RangeDone
import FIo_GroupSubset
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_PairSumStep
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode value)
open scoped BigOperators
abbrev State := FIo_RangeNext.Range × NE

def prefixSum (parts k : Array NE 7#usize) (n : Nat) : AspisWideTower.WideExact :=
  ∑ i ∈ Finset.range n, value k i * value parts i

def Inv (parts k : Array NE 7#usize) (s : State) : Prop :=
  s.1.end=7#usize ∧ s.1.start.val≤7 ∧ FIo_WideValues.Canon s.2 ∧
    decode s.2=prefixSum parts k s.1.start.val

def measure (s : State) := 7-s.1.start.val

theorem step (parts k : Array NE 7#usize)
    (hp : FIo_ArrayCanon.Holds parts) (hk : FIo_ArrayCanon.Holds k)
    (s : State) (inv : Inv parts k s) (out : ControlFlow State NE)
    (run : FIo_Native.weights.Weights.pair_loop9.body parts k s.1 s.2=ok out) :
    match out with
    | .done z => FIo_WideValues.Canon z ∧ decode z=prefixSum parts k 7
    | .cont t => Inv parts k t ∧ measure t<measure s := by
  rcases s with ⟨iter,sum⟩
  rcases inv with ⟨hend,hbound,hcanon,hvalue⟩
  unfold FIo_Native.weights.Weights.pair_loop9.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have same : done sum=out := Result.ok.inj run
    subst out
    have stop := FGm_RangeDone.done_next iter iter' hn
    have done : iter.start.val=7 := by rw [hend] at stop; change 7 ≤ iter.start.val at stop; omega
    exact ⟨hcanon,by simpa only [done] using hvalue⟩
  | some i =>
    obtain ⟨p,hpRead,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [FIo_Native.trace.value,bind_tc_ok] at run
    obtain ⟨kv,hkRead,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have same : cont (iter',next)=out := Result.ok.inj run
    subst out
    have cp := FIo_ArrayCanon.read parts i p hp hpRead
    have ck := FIo_ArrayCanon.read k i kv hk hkRead
    have prod := FIo_WideMulValues.mul kv p product ck cp hproduct
    have sumLaw := FIo_WideValues.add sum product next hcanon prod.1 hnext
    have progress := FIo_RangeNext.some_next iter iter' i hn
    refine ⟨⟨progress.2.1.trans hend,?_,sumLaw.1,?_⟩,?_⟩
    · rw [progress.2.2.1]; have := progress.2.2.2; rw [hend] at this; change iter.start.val < 7 at this; omega
    · change decode next = prefixSum parts k iter'.start.val
      rw [sumLaw.2,prod.2,FGm_ArrayValue.read k i kv hkRead,
        FGm_ArrayValue.read parts i p hpRead,hvalue,progress.1,progress.2.2.1]
      exact (Finset.sum_range_succ _ _).symm
    · simp only [measure,progress.2.2.1]
      have := progress.2.2.2
      rw [hend] at this
      change iter.start.val < 7 at this
      omega

#print axioms step
end AspisR1.FGm_PairSumStep
end
