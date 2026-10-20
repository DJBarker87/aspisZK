import Stage2FinishControl
import Stage2ContinuationFacts
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.Stage2Finish

/-- R13/S7/S8 frontiers can consume these exact successful source calls.
The source first-fold comparison is exposed without assuming matching. -/
theorem query_first_comparison (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (h : verifier.candidate.queryWithOps aops ops proof p a g obs geometry b =
      ok (.Ok (out,bout))) :
    ∃ index u bytes dots inv alpha folded values slot value,
      Array.index_usize p.queries a.next = ok index ∧
      lift (UScalar.cast .Usize index) = ok u ∧
      ops.opening proof a.next = ok bytes ∧ ops.dots bytes g = ok dots ∧
      ops.inverse geometry a.next = ok inv ∧
      Array.index_usize p.alpha 0#usize = ok alpha ∧
      ops.circle alpha dots inv = ok folded ∧ ops.values bytes = ok values ∧
      u % 4#usize = ok slot ∧ Array.index_usize values slot = ok value ∧
      ops.ne folded value = ok false := by
  unfold verifier.candidate.queryWithOps at h
  obtain ⟨index, hi, h⟩ := bind_success _ _ _ h
  obtain ⟨u, hu, h⟩ := bind_success _ _ _ h
  obtain ⟨bytes, hb, h⟩ := bind_success _ _ _ h
  obtain ⟨dots, hd, h⟩ := bind_success _ _ _ h
  iterate 12 obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
  obtain ⟨inv, hinv, h⟩ := bind_success _ _ _ h
  obtain ⟨alpha, ha, h⟩ := bind_success _ _ _ h
  obtain ⟨folded, hf, h⟩ := bind_success _ _ _ h
  iterate 2 obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
  obtain ⟨values, hv, h⟩ := bind_success _ _ _ h
  obtain ⟨slot, hs, h⟩ := bind_success _ _ _ h
  obtain ⟨value, hvalue, h⟩ := bind_success _ _ _ h
  obtain ⟨bad, hbad, h⟩ := bind_success _ _ _ h
  obtain ⟨hfalse, h⟩ := guard_success _ _ _ _ h
  exact ⟨index,u,bytes,dots,inv,alpha,folded,values,slot,value,
    hi,hu,hb,hd,hinv,ha,hf,hv,hs,hvalue,hfalse ▸ hbad⟩

/-- Propagate any invariant along the already proved twelve actual calls. -/
theorem chain_invariant {A B Err : Type} (next : A → Nat)
    (call : Stage2ContinuationLoop.Call A B Err) (I : A → B → Prop)
    (step : ∀ a b a1 b1, next a < 22 →
      call a b = ok (.Ok (),a1,b1) → I a b → I a1 b1)
    {a out : A} {b bout : B} {n : Nat}
    (chain : Stage2ContinuationLoop.Chain next call a b out bout n)
    (initial : I a b) : I out bout := by
  induction chain with
  | done a b he => exact initial
  | step active hc tail ih => exact ih (step _ _ _ _ active hc initial)

/-- End cursor is available independently of the invariant. -/
theorem chain_end {A B Err : Type} (next : A → Nat)
    (call : Stage2ContinuationLoop.Call A B Err)
    {a out : A} {b bout : B} {n : Nat}
    (chain : Stage2ContinuationLoop.Chain next call a b out bout n) : next out = 22 := by
  induction chain with
  | done a b he => exact he
  | step active hc tail ih => exact ih

/-- Compose the stage-2 first facts with a named checkpoint invariant and
per-query preservation law. These laws remain R13/R15/S7/S8 obligations. -/
theorem twelve_calls_invariant (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (I : verifier.Accumulator → verifier.BatchedWeights → Prop)
    (step : ∀ a b a1 b1, a.next.val < 22 →
      Stage2ContinuationOwnedLoop.adapt (fun a b =>
        stage2QueryCall aops ops proof p a g obs geometry b) a b = ok (.Ok (),a1,b1) →
      I a b → I a1 b1)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
    (start : a.next.val = 10) (initial : I a b)
    (h : verifier.candidate.query_loop (stage2QueryCall aops ops)
      proof p a g obs geometry b 22#usize = ok (.Ok (out,bout))) :
    I out bout ∧ out.next.val = 22 := by
  have chain := stage2_twelve_ordered_calls aops ops proof p g obs geometry a out b bout start h
  exact ⟨chain_invariant _ _ I step chain initial,chain_end (fun a : verifier.Accumulator => a.next.val) _ chain⟩

#print axioms query_first_comparison
#print axioms chain_invariant
#print axioms chain_end
#print axioms twelve_calls_invariant
end AspisR1Stage2.Stage2Finish
