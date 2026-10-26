import FIo_GroupSubset
import FIo_Constants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_GroupContract
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
open FIo_GroupSubset (State)

theorem step (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (hlow : FIo_ArrayCanon.Holds low) (hcs : FIo_ArrayCanon.Holds cs)
    (s : State) (inv : FIo_WideValues.Canon s.2) (out : ControlFlow State NE)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body low cs s.1 s.2=ok out) :
    match out with
    | .done w => FIo_WideValues.Canon w
    | .cont t => FIo_WideValues.Canon t.2 ∧ FIo_GroupSubset.measure t<FIo_GroupSubset.measure s := by
  rcases s with ⟨iter,w⟩
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have same : done w=out := Result.ok.inj run
    subst out
    exact inv
  | some group =>
    obtain ⟨weight,hweight,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨coefficient,hcoefficient,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have same : cont (iter',next)=out := Result.ok.inj run
    subst out
    have cw := FIo_GroupSubset.canonical low group hlow _ _ weight FIo_Constants.zero.1 hweight
    have cc := FIo_ArrayCanon.read cs group coefficient hcs hcoefficient
    have cp := (FIo_WideMulValues.mul coefficient weight product cc cw hproduct).1
    have cn := (FIo_WideValues.add w product next inv cp hnext).1
    have progress := FIo_RangeNext.some_next iter iter' group hn
    refine ⟨cn,?_⟩
    simp only [FIo_GroupSubset.measure,progress.2.1,progress.2.2.1]; omega

theorem canonical (low : Array NE 16#usize) (cs : Array NE 12#usize)
    (hlow : FIo_ArrayCanon.Holds low) (hcs : FIo_ArrayCanon.Holds cs)
    (iter : FIo_RangeNext.Range) (w result : NE) (inv : FIo_WideValues.Canon w)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1 iter low cs w=ok result) :
    FIo_WideValues.Canon result := by
  exact FIo_LoopInvariant.preserve
    (fun s : State => FIo_Native.weights.s2_grouped_inactive_pair_loop1.body low cs s.1 s.2)
    (fun s => FIo_WideValues.Canon s.2) FIo_WideValues.Canon FIo_GroupSubset.measure
    (fun s h out hr => by cases out <;> exact step low cs hlow hcs s h _ hr)
    (iter,w) result inv run

#print axioms step
#print axioms canonical
end AspisR1.FIo_GroupContract
end
