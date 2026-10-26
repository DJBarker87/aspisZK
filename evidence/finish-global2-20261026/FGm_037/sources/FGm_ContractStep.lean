import FGm_SubsetValue
import FGm_ArrayValue
import FGm_RangeDone
import FIo_GroupSubset
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_ContractStep
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode value)
open scoped BigOperators
abbrev State := FIo_RangeNext.Range × NE

def prefixSum (low : Array NE 16#usize) (cs : Array NE 12#usize) (n : Nat) : AspisWideTower.WideExact :=
  ∑ i ∈ Finset.range n, value cs i * FGm_SubsetStep.prefixSum low (FGm_Indices.index i) 16

def Inv (low : Array NE 16#usize) (cs : Array NE 12#usize) (s : State) : Prop :=
  s.1.end=12#usize ∧ s.1.start.val≤12 ∧ FIo_WideValues.Canon s.2 ∧
    decode s.2=prefixSum low cs s.1.start.val

def measure (s : State) := 12-s.1.start.val

theorem step (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (hlow : FIo_ArrayCanon.Holds low) (hcs : FIo_ArrayCanon.Holds cs)
    (s : State) (inv : Inv low cs s) (out : ControlFlow State NE)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body low cs s.1 s.2=ok out) :
    match out with
    | .done z => FIo_WideValues.Canon z ∧ decode z=prefixSum low cs 12
    | .cont t => Inv low cs t ∧ measure t<measure s := by
  rcases s with ⟨iter,sum⟩
  rcases inv with ⟨hend,hbound,hcanon,hvalue⟩
  dsimp only at hend hbound hcanon hvalue
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have same : done sum=out := Result.ok.inj run
    subst out
    have stop := FGm_RangeDone.done_next iter iter' hn
    have done : iter.start.val=7 := by rw [hend] at stop; change 12 ≤ iter.start.val at stop; omega
    exact ⟨hcanon,by simpa only [done] using hvalue⟩
  | some i =>
    obtain ⟨weight,hweight,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨coefficient,hcoefficient,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have same : cont (iter',next)=out := Result.ok.inj run
    subst out
    have cw := FGm_SubsetValue.value low i weight hlow hweight
    have cc := FIo_ArrayCanon.read cs i coefficient hcs hcoefficient
    have prod := FIo_WideMulValues.mul coefficient weight product cc cw.1 hproduct
    have sumLaw := FIo_WideValues.add sum product next hcanon prod.1 hnext
    have progress := FIo_RangeNext.some_next iter iter' i hn
    refine ⟨⟨progress.2.1.trans hend,?_,sumLaw.1,?_⟩,?_⟩
    · rw [progress.2.2.1]; have := progress.2.2.2; rw [hend] at this; change iter.start.val < 12 at this; omega
    · have readc := FGm_ArrayValue.read cs i coefficient hcoefficient
      change AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide coefficient) = _ at readc
      have readw : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide weight) =
          FGm_SubsetStep.prefixSum low (FGm_Indices.index i.val) 16 := by
        simpa only [FGm_Indices.self] using cw.2
      change AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide sum) = _ at hvalue
      change AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide next) = prefixSum low cs iter'.start.val
      rw [sumLaw.2,prod.2,readc,readw,hvalue,progress.1,progress.2.2.1]
      exact (Finset.sum_range_succ _ _).symm
    · simp only [measure,progress.2.2.1]
      have := progress.2.2.2
      rw [hend] at this
      change iter.start.val < 12 at this
      omega

#print axioms step
end AspisR1.FGm_ContractStep
end
