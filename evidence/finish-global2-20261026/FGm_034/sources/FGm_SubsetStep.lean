import FGm_Indices
import FGm_SubsetSelection
import FGm_ArrayValue
import FGm_RangeDone
import FIo_GroupSubset
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_SubsetStep
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
open FGm_ArrayValue (decode value)
open scoped BigOperators
abbrev State := FIo_RangeNext.Range × NE

def term (low : Array NE 16#usize) (group : Usize) (i : Nat) : AspisWideTower.WideExact :=
  if FGm_SubsetSelection.selected group (FGm_Indices.index i) then value low i else 0

def prefixSum (low : Array NE 16#usize) (group : Usize) (n : Nat) : AspisWideTower.WideExact :=
  ∑ i ∈ Finset.range n, term low group i

def Inv (low : Array NE 16#usize) (group : Usize) (s : State) : Prop :=
  s.1.end=16#usize ∧ s.1.start.val≤16 ∧ FIo_WideValues.Canon s.2 ∧
    decode s.2=prefixSum low group s.1.start.val

def measure (s : State) := 16-s.1.start.val

theorem step (low : Array NE 16#usize) (group : Usize)
    (hlow : FIo_ArrayCanon.Holds low)
    (s : State) (inv : Inv low group s) (out : ControlFlow State NE)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2=ok out) :
    match out with
    | .done z => FIo_WideValues.Canon z ∧ decode z=prefixSum low group 16
    | .cont t => Inv low group t ∧ measure t<measure s := by
  rcases s with ⟨iter,sum⟩
  rcases inv with ⟨hend,hbound,hcanon,hvalue⟩
  dsimp only at hend hbound hcanon hvalue
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have same : done sum=out := Result.ok.inj run
    subst out
    have stop := FGm_RangeDone.done_next iter iter' hn
    have done : iter.start.val=16 := by rw [hend] at stop; change 16 ≤ iter.start.val at stop; omega
    exact ⟨hcanon,by simpa only [done] using hvalue⟩
  | some i =>
    obtain ⟨challenge,hchallenge,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨mask,hmask,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨shift,hshift,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    have progress := FIo_RangeNext.some_next iter iter' i hn
    have decrease : measure (iter',sum)<measure (iter,sum) := by
      simp only [measure,progress.2.2.1]
      have := progress.2.2.2
      rw [hend] at this
      change iter.start.val < 16 at this
      omega
    have bound : iter'.start.val ≤ 16 := by
      rw [progress.2.2.1]
      have := progress.2.2.2
      rw [hend] at this
      change iter.start.val < 16 at this
      omega
    have choice := FGm_SubsetSelection.reached group i mask shift hmask hshift
    have termEq : term low group i.val =
        if mask &&& shift != 0#u16 then value low i.val else 0 := by
      simp only [term,FGm_Indices.self,choice]
    split at run
    · rename_i active
      obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      have same : cont (iter',next)=out := Result.ok.inj run
      subst out
      have added := FIo_WideValues.add sum challenge next hcanon
        (FIo_ArrayCanon.read low i challenge hlow hchallenge) hnext
      refine ⟨⟨progress.2.1.trans hend,bound,added.1,?_⟩,decrease⟩
      have read := FGm_ArrayValue.read low i challenge hchallenge
      change AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide challenge) = _ at read
      change AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide sum) = _ at hvalue
      change AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide next) = _
      rw [added.2,read,hvalue,progress.2.2.1]
      change prefixSum low group iter.start.val+value low i.val = _
      rw [prefixSum,Finset.sum_range_succ]
      rw [←progress.1,termEq,if_pos active]
    · rename_i inactive
      have same : cont (iter',sum)=out := Result.ok.inj run
      subst out
      refine ⟨⟨progress.2.1.trans hend,bound,hcanon,?_⟩,decrease⟩
      change decode sum = _
      rw [hvalue,progress.2.2.1]
      rw [prefixSum,Finset.sum_range_succ]
      rw [←progress.1,termEq,if_neg inactive,add_zero]

#print axioms step
end AspisR1.FGm_SubsetStep
end
