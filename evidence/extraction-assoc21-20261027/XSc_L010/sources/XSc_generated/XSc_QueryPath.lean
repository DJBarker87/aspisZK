import XSc_QueryNext
import XRl_LoopInvariant
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSc_QueryPath
abbrev State := core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error
inductive Reached (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (initial : State) : State → Prop
 | initial : Reached proof p g obs geo end1 initial initial
 | next (a : verifier.Accumulator) (pending : verifier.BatchedWeights) (out : State)
   (previous : Reached proof p g obs geo end1 initial (.Ok (a,pending)))
   (active : a.next<end1)
   (run : verifier.candidate.query_values proof p a g obs geo pending=ok out) :
   Reached proof p g obs geo end1 initial out

def measure (end1 : Usize) : State → Nat
 | .Err _ => 0
 | .Ok (a,_) => end1.val-a.next.val+1

/-- A successful actual query loop determines its own finite chronological path,
including a possible last rejected query. It assumes no selected prefix. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (initial out : State)
 (run : verifier.candidate.query_loop_loop initial proof p g obs geo end1=ok out) :
 Reached proof p g obs geo end1 initial out := by
 unfold verifier.candidate.query_loop_loop at run
 apply XRl_LoopInvariant.preserve _ (Reached proof p g obs geo end1 initial)
  (Reached proof p g obs geo end1 initial) (measure end1) ?_ initial out .initial run
 intro s r hs hr
 cases s with
 | Err e =>
  simp only [verifier.candidate.query_loop_loop.body] at hr
  cases Result.ok.inj hr
  exact hs
 | Ok pair =>
  rcases pair with ⟨a,pending⟩
  unfold verifier.candidate.query_loop_loop.body at hr
  dsimp! only at hr
  split at hr
  · cases Result.ok.inj hr
    exact hs
  · rename_i active
    obtain ⟨next,hquery,hr⟩ := bind_success _ _ _ hr
    cases Result.ok.inj hr
    have ha : a.next<end1 := by change ¬ end1.val≤a.next.val at active; change a.next.val<end1.val; omega
    refine ⟨Reached.next a pending next hs ha hquery,?_⟩
    cases next with
    | Err e => simp only [measure]; change 0<end1.val-a.next.val+1; omega
    | Ok pair =>
     rcases pair with ⟨a1,pending1⟩
     have hn := (XSc_QueryNext.source proof p a a1 g obs geo pending pending1 hquery).2.1
     simp only [measure]
     change a.next.val<end1.val at ha
     omega
#print axioms source
end XSc_QueryPath
