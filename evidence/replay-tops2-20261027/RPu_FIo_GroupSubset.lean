import RPt_FIo_ArrayCanon
import RPt_FIo_RangeNext
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_GroupSubset
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
abbrev State := FIo_RangeNext.Range × NE
def measure (s : State) : Nat := s.1.end.val-s.1.start.val

theorem step (low : Array NE 16#usize) (group : Usize)
    (hlow : FIo_ArrayCanon.Holds low) (s : State) (inv : FIo_WideValues.Canon s.2)
    (out : ControlFlow State NE)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2=ok out) :
    match out with
    | .done w => FIo_WideValues.Canon w
    | .cont t => FIo_WideValues.Canon t.2 ∧ measure t<measure s := by
  rcases s with ⟨iter,w⟩
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have same : done w=out := Result.ok.inj run
    subst out
    exact inv
  | some bit =>
    obtain ⟨challenge,hchallenge,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨mask,hmask,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨shift,hshift,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    have progress := FIo_RangeNext.some_next iter iter' bit hn
    have decrease : measure (iter',w)<measure (iter,w) := by
      simp only [measure,progress.2.1,progress.2.2.1]; omega
    split at run
    · obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      have same : cont (iter',next)=out := Result.ok.inj run
      subst out
      exact ⟨(FIo_WideValues.add w challenge next inv
        (FIo_ArrayCanon.read low bit challenge hlow hchallenge) hnext).1,decrease⟩
    · have same : cont (iter',w)=out := Result.ok.inj run
      subst out
      exact ⟨inv,decrease⟩

theorem canonical (low : Array NE 16#usize) (group : Usize)
    (hlow : FIo_ArrayCanon.Holds low) (iter : FIo_RangeNext.Range) (w result : NE)
    (inv : FIo_WideValues.Canon w)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0 iter low group w=ok result) :
    FIo_WideValues.Canon result := by
  exact FIo_LoopInvariant.preserve
    (fun s : State => FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2)
    (fun s => FIo_WideValues.Canon s.2) FIo_WideValues.Canon measure (fun s h out hr => by cases out <;> exact step low group hlow s h _ hr)
    (iter,w) result inv run

#print axioms step
#print axioms canonical
end AspisR1.FIo_GroupSubset
end
