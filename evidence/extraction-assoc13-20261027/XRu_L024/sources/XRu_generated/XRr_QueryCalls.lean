import XRr_QueryFrame
import XRr_QueryStop
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_QueryCalls
abbrev Acc := verifier.Accumulator
abbrev BW := verifier.BatchedWeights
abbrev Call := Acc → BW → Result (core.result.Result (Acc × BW) verifier.Error)
/-- Ordered cuts of the SAME execution; each edge is an actual query call. -/
inductive Calls (call : Call) (end1 : Nat) : Acc → BW → Acc → BW → Nat → Prop
 | done (a : Acc) (b : BW) (atEnd : a.next.val=end1) : Calls call end1 a b a b 0
 | step {a a1 out : Acc} {b b1 bout : BW} {n : Nat}
   (active : a.next.val<end1) (returned : call a b=ok (.Ok (a1,b1)))
   (tail : Calls call end1 a1 b1 out bout n) : Calls call end1 a b out bout (n+1)

theorem source (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (a out : Acc) (b bout : BW) (bound : a.next.val≤end1.val)
 (success : verifier.candidate.query_loop proof p a g obs geo b end1=ok (.Ok (out,bout))) :
 Calls (fun a b => verifier.candidate.query_values proof p a g obs geo b)
 end1.val a b out bout (end1.val-a.next.val) := by
 change verifier.candidate.query_loop_loop (.Ok (a,b)) proof p g obs geo end1=_ at success
 induction fuel : end1.val-a.next.val generalizing a b with
 | zero =>
   have he : a.next.val=end1.val := by omega
   have stopped := XRr_QueryStop.stopped proof p a g obs geo b end1 (by omega)
   change verifier.candidate.query_loop_loop (.Ok (a,b)) proof p g obs geo end1=_ at stopped
   rw [stopped] at success
   have same := core.result.Result.Ok.inj (Result.ok.inj success)
   have ha : a=out := congrArg Prod.fst same
   have hb : b=bout := congrArg Prod.snd same
   subst out
   subst bout
   exact .done a b he
 | succ n ih =>
   have active : a.next.val<end1.val := by omega
   have inactive : ¬end1.val≤a.next.val := by omega
   unfold verifier.candidate.query_loop_loop at success
   rw [Aeneas.Std.loop.eq_def] at success
   simp only [verifier.candidate.query_loop_loop.body] at success
   cases hc : verifier.candidate.query_values proof p a g obs geo b with
   | fail e => simp [hc,inactive] at success
   | div => simp [hc,inactive] at success
   | ok r =>
     have tail : verifier.candidate.query_loop_loop r proof p g obs geo end1=ok (.Ok (out,bout)) := by
       simpa [hc,inactive,verifier.candidate.query_loop_loop,verifier.candidate.query_loop_loop.body] using success
     cases r with
     | Err e =>
       have stop := XRr_QueryStop.rejected (H:=Unit) (proof:=proof) (p:=p) (g:=g) (obs:=obs) (geo:=geo) (end1:=end1) (e:=e)
       rw [stop] at tail
       cases tail
     | Ok pair =>
       rcases pair with ⟨a1,b1⟩
       have hn := (XRr_QueryFrame.query proof p a a1 g obs geo b b1 hc).2.2
       have rest : Calls (fun a b => verifier.candidate.query_values proof p a g obs geo b)
           end1.val a1 b1 out bout n := ih a1 b1 (by omega) tail (by omega)
       exact .step active hc rest

theorem weights (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Nat) (a out : Acc) (b bout : BW) (n : Nat)
 (h : Calls (fun a b => verifier.candidate.query_values proof p a g obs geo b)
   end1 a b out bout n) : out.weights=a.weights ∧ out.next.val=end1 := by
 induction h with
 | done a b he => exact ⟨rfl,he⟩
 | step active returned tail ih =>
   have hf := (XRr_QueryFrame.query proof p _ _ g obs geo _ _ returned).2.1
   exact ⟨ih.1.trans hf,ih.2⟩
#print axioms source
#print axioms weights
end XRr_QueryCalls
