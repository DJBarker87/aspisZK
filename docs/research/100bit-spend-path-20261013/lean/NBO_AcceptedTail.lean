import NBO_QueryDomains
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace NBO_AcceptedTail
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
open NBO_TailDomain (WideCanonical)
structure PreparedDomain (p : verifier.Prepared) : Prop where
 alpha1 : WideCanonical (p.alpha.val[1]'(by rw [p.alpha.property];decide))
 rho : NBF_PowerStep.Canonical p.rho
/-- Installs the SAME lower callback laws through the existing basis/row
installation; the four relevant callback definitions are unchanged. -/
def installed (ops : Ops) (lower : NBO_QueryDomains.Lower ops) :
 NBO_QueryDomains.Lower (NBF_Accumulate.install ops) :=
 ⟨lower.decode,lower.fromFn,lower.inverse,lower.line⟩
/-- Every line-fold input domain comes from the SAME prefix's producers.
Only named lower operation laws and upstream prepared/geometry domains remain. -/
theorem reached (ops : Ops) (lower : NBO_QueryDomains.Lower ops)
 (proof : Slice U8) (p : verifier.Prepared) (prepared : PreparedDomain p)
 (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (domain : NBO_QueryDomains.GeometryDomain geometry)
 (b bout : verifier.BatchedWeights) (active : a.next.val<10)
 (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
   proof p a g none geometry b=ok (.Ok (out,bout))) :
 ∃ node line, WideCanonical line ∧
 verifier.accumulate_batched_with_node (NBF_Accumulate.install ops)
   p a node line b=ok (out,bout) := by
 rw [NBO_QueryFactor.association] at run
 obtain ⟨cut,hfront,run⟩ := bind_success _ _ _ run
 cases cut with
 | Err error => cases run
 | Ok cut =>
   rcases cut with ⟨circle,values,inverse⟩
   obtain ⟨hvalues,hinverse⟩ := NBO_QueryDomains.front
     (NBF_Accumulate.install ops) (installed ops lower) proof p a.next g geometry
     domain active circle values inverse hfront
   unfold NBO_QueryFactor.suffix at run
   obtain ⟨alpha,halpha,run⟩ := bind_success _ _ _ run
   obtain ⟨line,hline,run⟩ := bind_success _ _ _ run
   have same : alpha=p.alpha.val[1]'(by rw [p.alpha.property];decide) := by
     simpa [Array.index_usize] using halpha.symm
   have canonical : WideCanonical line := lower.line alpha values inverse line
     (by rw [same];exact prepared.alpha1) hvalues hinverse hline
   iterate 9 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
   obtain ⟨pair,haccum,run⟩ := bind_success _ _ _ run
   rcases pair with ⟨a1,b1⟩
   obtain ⟨marked,hmarked,run⟩ := bind_success _ _ _ run
   cases Result.ok.inj run
   exact ⟨_,line,canonical,haccum⟩
/-- rhs and power canonicality are conclusions of the SAME successful
query, with raw progress and scalar inputs supplied by its reached invariant. -/
theorem canonical (ops : Ops) (lower : NBO_QueryDomains.Lower ops)
 (fields : NBO_TailDomain.NBC_Fields ops)
 (proof : Slice U8) (p : verifier.Prepared) (prepared : PreparedDomain p)
 (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (domain : NBO_QueryDomains.GeometryDomain geometry)
 (b bout : verifier.BatchedWeights) (active : a.next.val<10)
 (good : NBF_QueryInvariant.Good a b) (rhs : WideCanonical a.rhs)
 (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
   proof p a g none geometry b=ok (.Ok (out,bout))) :
 WideCanonical out.rhs ∧ NBF_PowerStep.Canonical out.power := by
 obtain ⟨node,line,hcanonical,haccum⟩ := reached ops lower proof p prepared a out g
   geometry domain b bout active run
 exact NBO_TailDomain.accumulate ops fields p a out node line b bout good.weights
   (by rw [good.sync];exact good.phase) good.power prepared.rho rhs hcanonical haccum
#print axioms installed
#print axioms reached
#print axioms canonical
end NBO_AcceptedTail
end
