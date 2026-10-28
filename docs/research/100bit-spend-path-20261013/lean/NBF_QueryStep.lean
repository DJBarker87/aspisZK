import NBF_Advance
import NBF_QueryCuts
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_QueryStep
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- SAME accepted query provides the exact accumulation cut used to propagate
phase; independent successful child calls are not hypotheses. -/
theorem phase (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
 (size : a.weights.val.length=64) (nextBound : a.next.val<10) (sync : b.terms=a.next)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (hq : ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK a.power) k).val<2^31-1)
 (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
   proof p a g none geometry b=ok (.Ok (out,bout))) :
 out.weights=a.weights ∧ out.next.val=a.next.val+1 ∧ bout.terms=out.next ∧
 S7JoinRowsTrace.Progress out.next.val 0 (Port3_RowsInstall.toBW bout) := by
 obtain ⟨query,opening,dots,inverse,circle,values,line,node,
   hquery,hopening,hdots,hinverse,hcircle,hline,haccum⟩ :=
   NBF_QueryCuts.accepted (NBF_Accumulate.install ops) proof p a out g none geometry b bout run
 exact NBF_Advance.accepted ops p a out node line b bout size nextBound sync progress hq haccum
#print axioms phase
end NBF_QueryStep
