import NBB_QueryTrace
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_QueryWitness
open AspisR1Stage2 NBB_QueryTrace
/-- A local advancing callback constructs its own finite driver trace,
including the first error/failure/divergence. No final success is assumed. -/
theorem construct (call : Call) (end1 : Nat)
 (advance : ∀ a a1 b b1, call a b=ok (.Ok (a1,b1)) → a1.next.val=a.next.val+1)
 (a : Acc) (b : BW) : ∃ out, Trace call end1 (.Ok (a,b)) out := by
 induction fuel : end1-a.next.val generalizing a b with
 | zero => exact ⟨ok (.Ok (a,b)),.stop a b (by omega)⟩
 | succ n ih =>
  have active : a.next.val<end1 := by omega
  cases head : call a b with
  | fail e => exact ⟨Result.fail e,.fail active e head⟩
  | div => exact ⟨Result.div,.div active head⟩
  | ok reply =>
   cases reply with
   | Err e => exact ⟨ok (.Err e),.step active head (.error e)⟩
   | Ok pair =>
    rcases pair with ⟨a1,b1⟩
    have next := advance a a1 b b1 head
    obtain ⟨out,tail⟩ := ih a1 b1 (by omega)
    exact ⟨out,.step active head tail⟩

/-- The exact direct cohort query body supplies its next-counter law from
its SAME reached query read and accumulation tail. -/
theorem direct (ops : AspisR1.Port3_NativeQueryBody.Ops) (proof : Slice U8)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (a : Acc) (b : BW) :
 ∃ out, Trace (fun a b => AspisR1.Port3_NativeQueryBody.verifier.candidate.query_values
    ops proof p a g obs geo b) end1.val (.Ok (a,b)) out ∧
 AspisR1.Port3_NativeQueryBody.verifier.candidate.query_loop ops proof p a g obs geo b end1=out := by
 obtain ⟨out,trace⟩ := construct (fun a b =>
  AspisR1.Port3_NativeQueryBody.verifier.candidate.query_values ops proof p a g obs geo b)
  end1.val (fun a a1 b b1 h =>
   (AspisR1.Port3_NativeQueryFrame.query_fields ops proof p a a1 g obs geo b b1 h).2.2) a b
 refine ⟨out,trace,?_⟩
 rw [AspisR1.Port3_NativeQueryFrame.loop_eq]
 exact NBB_QueryTrace.native_result _ proof p g obs geo end1 (.Ok (a,b)) out trace
#print axioms construct
#print axioms direct
end NBB_QueryWitness
