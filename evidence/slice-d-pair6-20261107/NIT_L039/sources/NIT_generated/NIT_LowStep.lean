import NIT_LowInterpretation
import NIT_IndexLemmas
set_option autoImplicit false
namespace AspisR1.NIT_LowStep
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

/-- Native low_cut is associated to the exact emitted body, including both PERM
lookups and the squared-quarter call, on an arbitrary canonical pre-state. -/
theorem step (ap0 ap1 : Powers) (s : NHX_LowDomain.State) (after : LowCells) (l : Low)
 (cut : cutLow ap0 ap1 s.1.start.val s.2 l after)
 (mulLaw : EMul l.a l.b l.product) (scaleLaw : NIT_LowInterpretation.Scale l.scale_a l.scaled)
 (last : s.1.end.val=16) :
 ∃ rest,NHX_LowDomain.body ap0 ap1 s=ok (.cont (rest,after)) ∧
 core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest) ∧
 rest.end.val=16 ∧ rest.start.val=s.1.start.val+1 ∧ canonical after := by
 have small := cut.1
 obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
 obtain ⟨lo,rem,lov⟩ := UScalar.rem_spec s.1.start (y:=4#usize) (by decide)
 obtain ⟨hi,div,hiv⟩ := UScalar.div_spec s.1.start (y:=4#usize) (by decide)
 have lob : lo.val<4 := by change lo.val=s.1.start.val%4 at lov;omega
 have hib : hi.val<4 := by change hi.val=s.1.start.val/4 at hiv;omega
 obtain ⟨p0,p0run,p0val,p0b⟩ := NIT_IndexLemmas.perm lo lob
 obtain ⟨p1,p1run,p1val,p1b⟩ := NIT_IndexLemmas.perm hi hib
 have p0v : p0.val=perm (s.1.start.val%4) := by rw [p0val,lov];rfl
 have p1v : p1.val=perm (s.1.start.val/4) := by rw [p1val,hiv];rfl
 have cell := NIT_LowInterpretation.low_cell ap0 ap1 s.1.start s.2 after l cut mulLaw scaleLaw
 refine ⟨rest,?_,next,by rw [he];exact last,inc,cell.2⟩
 simp only [NHX_LowDomain.body,FIo_Native.weights.Weights.pair_loop15.body,next,bind_tc_ok]
 dsimp! only
 simp only [rem,div,p0run,p1run,epick_index ap0 p0 p0b,epick_index ap1 p1 p1b,p0v,p1v,bind_tc_ok]
 have mapped := congrArg (fun r : Result LowCells =>
  r >>=fun cells=>ok (ControlFlow.cont (rest,cells) : ControlFlow NHX_LowDomain.State LowCells)) cell.1
 simpa only [bind_assoc_eq,bind_tc_ok] using mapped

#print axioms step
end AspisR1.NIT_LowStep
