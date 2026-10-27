import RPu_FJc_SubsetValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InactiveContract
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
abbrev State := FIo_GroupSubset.State

def sumPrefix (low : Array NE 16#usize) (cs : Array NE 12#usize) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumPrefix low cs n + FIp_ArrayValue.value cs n * FJc_SubsetModel.sumPrefix low n 16

def Inv (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (stop : Nat) (initial : AspisWideTower.WideExact) (s : State) : Prop :=
  FIo_WideValues.Canon s.2 ∧ s.1.end.val=stop ∧ s.1.start.val≤stop ∧
  decodeWide (wide s.2)=initial+sumPrefix low cs s.1.start.val

def Post (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (stop : Nat) (initial : AspisWideTower.WideExact) (out : NE) : Prop :=
  FIo_WideValues.Canon out ∧ decodeWide (wide out)=initial+sumPrefix low cs stop

theorem step (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (hlow : FIo_ArrayCanon.Holds low) (hcs : FIo_ArrayCanon.Holds cs)
    (stop : Nat) (initial : AspisWideTower.WideExact) (s : State)
    (inv : Inv low cs stop initial s) (out : ControlFlow State NE)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body low cs s.1 s.2=ok out) :
    match out with
    | .done w => Post low cs stop initial w
    | .cont t => Inv low cs stop initial t ∧ FIo_GroupSubset.measure t<FIo_GroupSubset.measure s := by
  rcases s with ⟨iter,w⟩
  dsimp only [Inv] at inv
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    have hn := FIp_RangeNone.none_next iter iter' hn
    have hs : iter.start.val=stop := by have := inv.2.1;have := inv.2.2.1;omega
    exact ⟨inv.1,by simpa only [hs] using inv.2.2.2⟩
  | some group =>
    obtain ⟨weight,hweight,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨coefficient,hcoefficient,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have vw := FJc_SubsetValue.sixteen low group hlow weight hweight
    have cc := FIo_ArrayCanon.read cs group coefficient hcs hcoefficient
    have vp := FIo_WideMulValues.mul coefficient weight product cc vw.1 hproduct
    have va := FIo_WideValues.add w product next inv.1 vp.1 hnext
    have progress := FIo_RangeNext.some_next iter iter' group hn
    have cv := FIp_ArrayValue.read cs group coefficient hcoefficient
    refine ⟨⟨va.1,?_,?_,?_⟩,?_⟩
    · rw [progress.2.1];exact inv.2.1
    · have := inv.2.1;have := progress.2.2.2;rw [progress.2.2.1];omega
    · rw [va.2,vp.2,vw.2,inv.2.2.2,progress.2.2.1,sumPrefix,←cv,progress.1]
      exact add_assoc _ _ _
    · simp only [FIo_GroupSubset.measure,progress.2.1,progress.2.2.1];omega
#print axioms step
end AspisR1.FJc_InactiveContract
end
