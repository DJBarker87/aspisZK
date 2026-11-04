import NFP_Advance
import NBF_QueryCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_QueryAdvance
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody

theorem accepted (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
 (size : a.weights.val.length=64) (global : a.next.val<22) (localActive : b.terms.val<22)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (power : NBF_PowerStep.Canonical a.power)
 (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
  proof p a g none geometry b=ok (.Ok (out,bout))) :
 out.weights=a.weights ∧ out.next.val=a.next.val+1 ∧ bout.terms.val=b.terms.val+1 ∧
 S7JoinRowsTrace.Progress bout.terms.val 0 (Port3_RowsInstall.toBW bout) := by
 obtain ⟨query,opening,dots,inverse,circle,values,line,node,
  hquery,hopening,hdots,hinverse,hcircle,hline,haccum⟩ :=
  NBF_QueryCuts.accepted (NBF_Accumulate.install ops) proof p a out g none geometry b bout run
 exact NFP_Advance.accepted ops p a out node line b bout size global localActive progress power haccum

/-- The resumed TX2 local counter need not equal the global query index. -/
theorem offset (next local afterNext afterLocal start : Nat)
 (before : local+start=next) (advance : afterNext=next+1)
 (localAdvance : afterLocal=local+1) : afterLocal+start=afterNext := by omega
#print axioms accepted
#print axioms offset
end AspisR1.NFP_QueryAdvance
end
