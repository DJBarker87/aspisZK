import Stage2QueryChecks
import Mathlib.Algebra.Field.Defs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2.Stage2Finish

/-- Actual accumulator arithmetic, independently of the opaque weight traversal.
The materialized weights are retained; pending raw weights are a separate state. -/
theorem accumulate_arithmetic (ops : AccumulateOps) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (node : Stage2M) (value : Stage2E)
    (b bout : verifier.BatchedWeights)
    (h : verifier.accumulateWithOps ops p a node value b = ok (out,bout)) :
    out.weights = a.weights ∧
    (∃ product, ops.mulE value a.power = ok product ∧
      ops.addE a.rhs product = ok out.rhs) ∧
    ops.mulK a.power p.rho = ok out.power ∧ out.next.val = a.next.val + 1 := by
  have hnext := accumulate_next ops p a out node value b bout h
  unfold verifier.accumulateWithOps at h
  iterate 6 obtain ⟨x, hx, h⟩ := bind_success _ _ _ h
  obtain ⟨product, hm, h⟩ := bind_success _ _ _ h
  obtain ⟨rhs, ha, h⟩ := bind_success _ _ _ h
  obtain ⟨traceResult, ht, h⟩ := bind_success _ _ _ h
  obtain ⟨power, hp, h⟩ := bind_success _ _ _ h
  obtain ⟨next, hn, h⟩ := bind_success _ _ _ h
  cases Result.ok.inj h
  exact ⟨rfl,⟨product,hm,ha⟩,hp,hnext⟩

/-- S8's RHS/power arithmetic step after field interpretation. The source
weight-loop law and finalization remain separate from this proved step. -/
theorem accumulate_decoded {K F : Type} [Field K] [Field F]
    (ops : AccumulateOps) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (node : Stage2M) (value : Stage2E) (b bout : verifier.BatchedWeights)
    (decodeE : Stage2E → F) (decodeK : Stage2K → K) (iota : K →+* F)
    (mulE : ∀ e k result, ops.mulE e k = ok result → decodeE result = decodeE e * iota (decodeK k))
    (addE : ∀ e f result, ops.addE e f = ok result → decodeE result = decodeE e + decodeE f)
    (mulK : ∀ x y result, ops.mulK x y = ok result → decodeK result = decodeK x * decodeK y)
    (h : verifier.accumulateWithOps ops p a node value b = ok (out,bout)) :
    decodeE out.rhs = decodeE a.rhs + decodeE value * iota (decodeK a.power) ∧
    decodeK out.power = decodeK a.power * decodeK p.rho := by
  obtain ⟨hw,⟨product,hm,ha⟩,hp,hn⟩ := accumulate_arithmetic ops p a out node value b bout h
  exact ⟨(addE a.rhs product out.rhs ha).trans
    (congrArg (fun x => decodeE a.rhs + x) (mulE value a.power product hm)),
    mulK a.power p.rho out.power hp⟩

#print axioms accumulate_arithmetic
#print axioms accumulate_decoded
end AspisR1Stage2.Stage2Finish
