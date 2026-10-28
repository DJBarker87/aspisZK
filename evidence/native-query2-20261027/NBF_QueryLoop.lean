import NBF_QueryInitial
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_QueryLoop
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Reuse the inherited driver transport; add only SAME-caller invariant
propagation and the actual reached end counter. -/
theorem accepted (ops : Ops) (field : NBF_PowerStep.NBC_Qm31Canonical ops)
 (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (rho : NBF_PowerStep.Canonical p.rho)
 (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
 (good : NBF_QueryInvariant.Good a b) (bound : a.next.val≤10)
 (run : verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p a g none geometry b 10#usize=ok (.Ok (out,bout))) :
 out.next.val=10 ∧ NBF_QueryInvariant.Good out bout := by
 obtain ⟨result,history,same⟩ := NBB_QueryWitness.direct (NBF_Accumulate.install ops)
   proof p g none geometry 10#usize a b
 have resultEq : result=ok (.Ok (out,bout)) := same.symm.trans run
 subst result
 have preserved := NBF_QueryInvariant.trace ops field proof p g geometry rho (.Ok (a,b))
   (ok (.Ok (out,bout))) history good
 rw [Port3_NativeQueryFrame.loop_eq] at run
 have calls := Port2_QueryLoop.source_calls
   (verifier.candidate.query_values (NBF_Accumulate.install ops)) proof p g none geometry 10#usize
   (fun a a1 b b1 h=> (Port3_NativeQueryFrame.query_fields (NBF_Accumulate.install ops)
     proof p a a1 g none geometry b b1 h).2.2) a out b bout bound run
 exact ⟨Port2_QueryLoop.returned_next _ _ _ _ _ _ _ calls,preserved⟩

theorem from_constructors (base : VTop_Stages.Ops) (reserved : Bool)
 (ops : Ops) (field : NBF_PowerStep.NBC_Qm31Canonical ops)
 (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (rho : NBF_PowerStep.Canonical p.rho)
 (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
 (initial : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a))
 (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b))
 (run : verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p a g none geometry b 10#usize=ok (.Ok (out,bout))) :
 out.next.val=10 ∧ bout.terms.val=10 ∧ out.weights.val.length=64 ∧ bout.raw.val.length=64 ∧
 S7JoinRowsTrace.Progress 10 0 (Port3_RowsInstall.toBW bout) := by
 obtain ⟨next,good⟩ := NBF_QueryInitial.good base reserved a b initial pending
 obtain ⟨finish,after⟩ := accepted ops field proof p g geometry rho a out b bout good
   (by rw [next];decide) run
 exact ⟨finish,by rw [after.sync];exact finish,after.weights,after.phase.2.1,
   by simpa only [finish] using after.phase⟩
#print axioms accepted
#print axioms from_constructors
end NBF_QueryLoop
