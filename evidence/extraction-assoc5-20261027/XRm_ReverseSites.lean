import XRm_ReverseStep
import XRk_Funs
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release XRk_ResultTools
namespace XRm_ReverseSites
abbrev Iter := XRm_Reverse.Rev U32
abbrev Back := Iter → Iter
abbrev State := Iter × Back × U64
abbrev body := sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
abbrev dict := core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT U32

theorem body_cursor (s next : State) (run : body s.1 s.2.1 s.2.2=ok (.cont next)) :
    next.1.iter.i=s.1.iter.i := by
  unfold body sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body at run
  obtain ⟨v,rest,hr,run⟩ := pair_bind_success _ _ _ run
  rcases rest with ⟨it,restore,write⟩
  have hc := XRm_Reverse.cursor dict s.1 it v restore write hr
  cases v with
  | none => cases run
  | some limb =>
    obtain ⟨shift,_,run⟩ := bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    obtain ⟨p,_,run⟩ := bind_success _ _ _ run
    obtain ⟨quotient,_,run⟩ := bind_success _ _ _ run
    obtain ⟨remainder,_,run⟩ := bind_success _ _ _ run
    have same := congrArg (fun t : State => t.1.iter.i) (ControlFlow.cont.inj (Result.ok.inj run))
    exact same.symm.trans hc

/-- Actual finite prefixes of the emitted sampler loop. Each transition is
the SAME loop-body call; no successful whole-loop witness is assumed. -/
inductive Reached (c : sampler.low_base_p_digits.closure_1) : State → Prop
  | initial : Reached c (⟨⟨c.to_slice,0⟩⟩,id,0#u64)
  | step {s next : State} (prior : Reached c s)
      (run : body s.1 s.2.1 s.2.2=ok (.cont next)) : Reached c next

theorem cursor_zero (c : sampler.low_base_p_digits.closure_1) (s : State)
    (reached : Reached c s) : s.1.iter.i=0 := by
  induction reached with
  | initial => rfl
  | step prior run ih => exact (body_cursor _ _ run).trans ih

/-- Every reverseNext call in the adapted emitted Funs: one executable site,
inside this sampler body. The ABI dictionary next_back entry is also covered
on this same reached iterator, including full restored state equality. -/
theorem reverse_site (c : sampler.low_base_p_digits.closure_1) (s : State)
    (reached : Reached c s) :
    XRk_reverseNext dict s.1=XRl_Adapter.originalReverseNext s.1 :=
  XRl_Adapter.reverseNext_at_zero dict s.1 (cursor_zero c s reached)

/-- The concrete caller's actual fresh array/slice/rev prefix is exactly the
initial state used above. This is an all-input construction, not a premise. -/
theorem caller_prefix (c : sampler.low_base_p_digits.closure_1) :
    (do
      let (slice,_) ← lift (Array.to_slice_mut c)
      let (im,_) ← core.slice.Slice.iter_mut slice
      let (it,_) ← XRk_revRestored dict im
      ok ((it,id,0#u64) : State)) = ok (⟨⟨c.to_slice,0⟩⟩,id,0#u64) := by rfl

theorem nonvacuity (c : sampler.low_base_p_digits.closure_1) :
    ∃ s, Reached c s ∧ XRk_reverseNext dict s.1=XRl_Adapter.originalReverseNext s.1 :=
  ⟨_,Reached.initial,reverse_site c _ Reached.initial⟩

#print axioms body_cursor
#print axioms cursor_zero
#print axioms reverse_site
#print axioms caller_prefix
#print axioms nonvacuity
end XRm_ReverseSites
