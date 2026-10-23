import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3SuccessorCarryBodyCanonicalV1
import S9ConstructorV3Loop2InnerCanonicalV1
import S9ReverseRangeProgressV1
import S9LoopInvariantPropertyV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3SuccessorCarryLoopCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1

private theorem body_done_same_successor
    (z successor out : Vector) (iter : ReverseRange) (carry : Q)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
      z iter successor carry = .ok (.done out)) : out = successor := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body at hbody
  obtain ⟨next, hnext, hbody⟩ := bind_success_inv _ _ _ hbody
  rcases next with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done successor : ControlFlow (ReverseRange × Vector × Q) Vector) =
      ok (ControlFlow.done out : ControlFlow (ReverseRange × Vector × Q) Vector) at hbody
    exact (ControlFlow.done.inj (Result.ok.inj hbody)).symm
  | some coordinate =>
    obtain ⟨bit, hbit, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨product, hp, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨sum, hsum, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨twice, htwice, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨cell, hcell, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨out, hupdate, hbody⟩ := bind_success_inv _ _ _ hbody
    cases hbody

private def carryStep (z : Vector) (s : ReverseRange × Vector × Q) :
    Result (ControlFlow (ReverseRange × Vector × Q) Vector) :=
  AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
    z s.1 s.2.1 s.2.2

private def carryInvariant (s : ReverseRange × Vector × Q) : Prop :=
  VectorCanonical s.2.1 ∧ CanQ (toProbeQ s.2.2)

private def carryMeasure (s : ReverseRange × Vector × Q) : Nat :=
  s.1.iter.end.val - s.1.iter.start.val

/-- Canonicality of the whole actual reverse carry loop follows from its
same-call arithmetic steps and the checked reverse-range progress theorem. -/
theorem carry_loop_success_canonical
    (z successor out : Vector) (iter : ReverseRange) (carry : Q)
    (hz : VectorCanonical z) (hs : VectorCanonical successor) (hc : CanQ (toProbeQ carry))
    (hloop : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop
      iter z successor carry = .ok out) : VectorCanonical out := by
  let step : (ReverseRange × Vector × Q) → Result (ControlFlow (ReverseRange × Vector × Q) Vector) :=
    carryStep z
  have hdone : ∀ s out, carryInvariant s → step s = .ok (.done out) → VectorCanonical out := by
    rintro ⟨iter, successor, carry⟩ out hinv hstep
    have he := body_done_same_successor z successor out iter carry hstep
    subst out
    exact hinv.1
  have hcontinue : ∀ s s', carryInvariant s → step s = .ok (.cont s') → carryInvariant s' := by
    rintro ⟨iter, successor, carry⟩ ⟨iterNext, successorNext, carryNext⟩ hinv hstep
    exact carry_body_success_canonical z successor successorNext iter iterNext carry carryNext
      hz hinv.1 hinv.2 hstep
  have hdecrease : ∀ s s', step s = .ok (.cont s') → carryMeasure s' < carryMeasure s := by
    rintro ⟨iter, successor, carry⟩ ⟨iterNext, successorNext, carryNext⟩ hstep
    obtain ⟨coordinate, bit, product, sum, twice, cell, hnext, hrest⟩ :=
      carry_body_success_has_execution z successor successorNext iter iterNext carry carryNext hstep
    obtain ⟨hlt, hd, hstart, hend⟩ :=
      AspisR1S9ReverseRangeProgressV1.reverse_next_some_progress iter iterNext coordinate hnext
    simp only [carryMeasure, hstart]
    omega
  have hloop' : Aeneas.Std.loop step (iter, successor, carry) = .ok out := by
    change Aeneas.Std.loop (carryStep z) (iter, successor, carry) = .ok out at hloop
    exact hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property
    step carryMeasure carryInvariant VectorCanonical hdone hcontinue hdecrease
    (iter, successor, carry) out ⟨hs, hc⟩ hloop'

#print axioms carry_loop_success_canonical
end AspisR1S9ConstructorV3SuccessorCarryLoopCanonicalV1
