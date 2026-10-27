import FJf_U64Array
import FIo_ReduceBounds
import FIo_LoopInvariant
import FIo_RangeNext
import FIp_RangeNone
set_option autoImplicit false
namespace AspisR1.FJf_DotLane
open Aeneas Aeneas.Std Result ControlFlow
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
open FJf_U64Array (cell)

def model (base : Dot) (raw : Array U64 4#usize) (j : Nat) : U64 :=
  U64.wrapping_add (cell base.sums j) (FIo_ReduceBounds.fold (cell raw j))

/-- One actual shipped accumulator-coordinate body, on symbolic state. -/
theorem value (raw : Array U64 4#usize) (iter cursor : FIo_RangeNext.Range) (dot next : Dot)
    (run : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw iter dot=
      ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    ∀ j,cell next.sums j=if iter.start.val=j then model dot raw j else cell dot.sums j := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some i =>
    obtain ⟨old,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨rv,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok] at run
    obtain ⟨sums,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    change Array.update dot.sums i (U64.wrapping_add old (FIo_ReduceBounds.fold rv))=ok sums at hu
    have pr := FIo_RangeNext.some_next iter cursor i hn
    refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,?_⟩
    intro j
    rw [FJf_U64Array.update dot.sums sums i _ hu j]
    by_cases eq : i.val=j
    · rw [if_pos eq,←FJf_U64Array.read dot.sums i old ho,←FJf_U64Array.read raw i rv hr]
      simp only [model,←eq,pr.1,if_true]
    · rw [if_neg eq,if_neg (by rw [←pr.1];exact eq)]
#print axioms value
end AspisR1.FJf_DotLane
