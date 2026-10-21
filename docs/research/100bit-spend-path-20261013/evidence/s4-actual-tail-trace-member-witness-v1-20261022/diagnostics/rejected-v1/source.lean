import FourDotsActualTailLoopTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4TailTraceMemberWitnessV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1
open AspisR1FastDotsActualTailLoopTraceRootV1
abbrev Range := core.ops.range.Range Usize

theorem trace_member_input_witness
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (old out : Tail) (cs : List Contribution)
    (htrace : RunTrace ops a g slot iter old out cs) :
    ∀ c ∈ cs, ∃ (before after : Range) (s0 s1 : Tail),
      InputWitness ops a g slot before after s0 s1 c := by
  induction htrace with
  | done iter old hbody => intro c hc; cases hc
  | @step iter iter' old next out c cs hbody hwitness htail ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hsame | hmem
    · subst x
      exact ⟨iter,iter',old,next,hwitness⟩
    · exact ih x hmem

theorem trace_member_term_lt_two
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (old out : Tail) (cs : List Contribution)
    (htrace : RunTrace ops a g slot {start:=0#usize, «end»:=2#usize} old out cs) :
    ∀ c ∈ cs, c.term.val < 2 := by
  have hindices := actual_tail_trace_term_indices ops a g slot _ old out cs htrace
  change cs.map (fun c => c.term.val) = [0,1] at hindices
  intro c hc
  have hm : c.term.val ∈ cs.map (fun c => c.term.val) := List.mem_map.mpr ⟨c,hc,rfl⟩
  rw [hindices] at hm
  simp only [List.mem_cons, List.mem_singleton] at hm
  omega
#print axioms trace_member_input_witness
#print axioms trace_member_term_lt_two
end AspisR1.S4TailTraceMemberWitnessV1
