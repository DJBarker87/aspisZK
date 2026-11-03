import NBO_FieldSemantics
set_option autoImplicit false
noncomputable section
namespace NBO_AllCalls
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Chronological successful prefixes of this SAME actual query body. A
rejected/failing final query still has its input at one of these prefixes. -/
inductive Prefix (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) :
 verifier.Accumulator → verifier.BatchedWeights → Prop
 | initial : Prefix ops proof p g geometry initial pending initial pending
 | step {a out : verifier.Accumulator} {b bout : verifier.BatchedWeights}
   (prior : Prefix ops proof p g geometry initial pending a b)
   (active : a.next.val<10)
   (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
     proof p a g none geometry b=ok (.Ok (out,bout))) :
   Prefix ops proof p g geometry initial pending out bout

def CanonicalWeights (v : alloc.vec.Vec NBF_RowInstall.Q) : Prop :=
 ∀ q ∈ v.val, NBF_PowerStep.Canonical q

theorem initial_weights (base : VTop_Stages.Ops) (reserved : Bool)
 (a : verifier.Accumulator)
 (run : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a)) :
 CanonicalWeights a.weights := by
 obtain ⟨_,weights,_,_,_⟩ := Port3_Initial.accepted_fields base reserved a run
 unfold CanonicalWeights
 rw [weights]
 intro q member
 obtain ⟨_,same⟩ := List.mem_replicate.mp member
 subst q
 intro k
 fin_cases k <;> decide
/-- Every reached caller obtains its row/power/rhs phase and all original
weight embedding inputs from the SAME constructors and earlier returns.
No independent invariant or selected canonical vector is supplied. -/
theorem reached (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (lower : NBO_QueryDomains.Lower ops) (bindings : NBO_FieldSemantics.NBC_Bindings ops)
 (proof : Slice U8) (p : verifier.Prepared) (prepared : NBO_AcceptedTail.PreparedDomain p)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (domain : NBO_QueryDomains.GeometryDomain geometry)
 (initial a : verifier.Accumulator) (pending b : verifier.BatchedWeights)
 (initRun : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok initial))
 (pendingRun : Port3_NativePendingInstall.source reserved initial.weights.deref=ok (.Ok pending))
 (prefixRun : Prefix ops proof p g geometry initial pending a b) :
 NBO_QueryRhs.Good a b ∧ a.weights=initial.weights ∧
 CanonicalWeights a.weights ∧ a.next.val≤10 := by
 have fields := NBO_FieldSemantics.fields ops bindings
 obtain ⟨next,good⟩ := NBF_QueryInitial.good base reserved initial pending initRun pendingRun
 have initialRhs := NBO_TailDomain.initial base reserved initial initRun
 have initialWeights := initial_weights base reserved initial initRun
 induction prefixRun with
 | initial => exact ⟨⟨good,initialRhs⟩,rfl,initialWeights,by rw [next];decide⟩
 | @step a out b bout prior active run ih =>
   have frame := Port3_NativeQueryFrame.query_fields (NBF_Accumulate.install ops)
     proof p a out g none geometry b bout run
   refine ⟨⟨NBF_QueryInvariant.step ops fields.power proof p g geometry prepared.rho
     a out b bout ih.1.1 active run,
     (NBO_AcceptedTail.canonical ops lower fields proof p prepared a out g geometry
       domain b bout active ih.1.1 ih.1.2 run).1⟩,
     frame.2.1.trans ih.2.1,?_,?_⟩
   · rw [frame.2.1];exact ih.2.2.1
   · rw [frame.2.2];omega
#print axioms initial_weights
#print axioms reached
end NBO_AllCalls
end
