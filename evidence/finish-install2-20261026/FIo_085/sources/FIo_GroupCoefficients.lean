import FIo_ArrayCanon
import FIo_RangeNext
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_GroupCoefficients
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
abbrev Cs := Array NE 12#usize
abbrev State := FIo_RangeNext.Range × Cs

def measure (s : State) : Nat := s.1.end.val-s.1.start.val

theorem step (f : Slice U8) (s : State) (inv : FIo_ArrayCanon.Holds s.2)
    (out : ControlFlow State Cs)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body f s.1 s.2=ok out) :
    match out with
    | .done cs => FIo_ArrayCanon.Holds cs
    | .cont t => FIo_ArrayCanon.Holds t.2 ∧ measure t<measure s := by
  rcases s with ⟨iter,cs⟩
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have same : done cs=out := Result.ok.inj run
    subst out
    exact inv
  | some j =>
    obtain ⟨group,hg,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    obtain ⟨old,hold,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨value,hvalue,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨sum,hsum,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have same : cont (iter',next)=out := Result.ok.inj run
    subst out
    have oldCanon := FIo_ArrayCanon.read cs _ old inv hold
    have valueCanon := FIo_FieldCanonical.field f j value hvalue
    have sumCanon := (FIo_WideValues.add old value sum oldCanon valueCanon hsum).1
    have progress := FIo_RangeNext.some_next iter iter' j hn
    refine ⟨FIo_ArrayCanon.update cs next _ sum inv sumCanon hnext,?_⟩
    simp only [measure,progress.2.1,progress.2.2.1]
    omega

theorem canonical (f : Slice U8) (iter : FIo_RangeNext.Range) (cs result : Cs)
    (inv : FIo_ArrayCanon.Holds cs)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop0 iter f cs=ok result) :
    FIo_ArrayCanon.Holds result := by
  exact FIo_LoopInvariant.preserve
    (fun s : State => FIo_Native.weights.s2_grouped_inactive_pair_loop0.body f s.1 s.2)
    (fun s => FIo_ArrayCanon.Holds s.2) FIo_ArrayCanon.Holds measure (fun s h out hr => by cases out <;> exact step f s h _ hr)
    (iter,cs) result inv run

#print axioms step
#print axioms canonical
end AspisR1.FIo_GroupCoefficients
end
