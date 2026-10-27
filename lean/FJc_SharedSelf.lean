import FIo_RangeNext
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_SharedSelf
open Aeneas Aeneas.Std Result ControlFlow
abbrev Q := FIo_Native.aspis_core.field.QM31
abbrev W := FIo_Native.weights.Weights
abbrev State := FIo_RangeNext.Range × Array Q 16#usize

def measure (s : State) : Nat := s.1.end.val-s.1.start.val

theorem step (self : W) (s : State) (out : ControlFlow State (W × Array Q 16#usize))
    (run : FIo_Native.weights.Weights.pair_loop1.body self s.1 s.2=ok out) :
    match out with
    | .done r => r.1=self
    | .cont t => True ∧ measure t<measure s := by
  rcases s with ⟨iter,common⟩
  unfold FIo_Native.weights.Weights.pair_loop1.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases Result.ok.inj run;rfl
  | some j =>
    simp only [lift,bind_tc_ok] at run
    obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨c,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨d,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨e,he,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨f,hf,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨g,hg,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have p := FIo_RangeNext.some_next iter cursor j hn
    refine ⟨trivial,?_⟩
    simp only [measure,p.2.1,p.2.2.1];omega

theorem value (self out : W) (iter : FIo_RangeNext.Range) (common result : Array Q 16#usize)
    (run : FIo_Native.weights.Weights.pair_loop1 iter self common=ok (out,result)) : out=self := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.Weights.pair_loop1.body self s.1 s.2)
    (fun _=>True) (fun r : W × Array Q 16#usize=>r.1=self) measure
    (fun s _ r hr=>by cases r <;> exact step self s _ hr)
    (iter,common) (out,result) trivial run
#print axioms step
#print axioms value
end AspisR1.FJc_SharedSelf
end
