import FGm_ArrayUpdate
import FIo_RangeNext
import FIo_ScaleValues
import FIo_PowersCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_LowStepCanonical
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
abbrev State := FIo_RangeNext.Range × Array NE 16#usize

def measure (s : State) := s.1.end.val-s.1.start.val

theorem step (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_ArrayCanon.Holds ap0) (ha1 : FIo_ArrayCanon.Holds ap1)
    (s : State) (inv : FIo_ArrayCanon.Holds s.2) (out : ControlFlow State (Array NE 16#usize))
    (run : FIo_Native.weights.Weights.pair_loop7.body ap0 ap1 s.1 s.2=ok out) :
    match out with
    | .done low => FIo_ArrayCanon.Holds low
    | .cont t => FIo_ArrayCanon.Holds t.2 ∧ measure t<measure s := by
  rcases s with ⟨iter,low⟩
  unfold FIo_Native.weights.Weights.pair_loop7.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have same : done low=out := Result.ok.inj run
    subst out
    exact inv
  | some i =>
    obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨ai,hai,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨av,hav,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨bi,hbi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨bv,hbv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨scalar,hscalar,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨scaled,hscaled,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have same : cont (iter',next)=out := Result.ok.inj run
    subst out
    have ca := FIo_ArrayCanon.read ap0 ai av ha0 hav
    have cb := FIo_ArrayCanon.read ap1 bi bv ha1 hbv
    have cp := (FIo_WideMulValues.mul av bv product ca cb hproduct).1
    have cs := FIo_ScaleValues.wide_scale product scaled scalar hscaled
    have updated := FIo_ArrayCanon.update low next i scaled inv cs hnext
    have progress := FIo_RangeNext.some_next iter iter' i hn
    refine ⟨updated,?_⟩
    simp only [measure,progress.2.1,progress.2.2.1]
    omega

#print axioms step
end AspisR1.FGm_LowStepCanonical
end
