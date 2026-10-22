import S9BodyPrefixWitnessV1
import S9AfterSumsTailDispatchV1
import S9SideZeroTailRootV1
import S9ArrayWriteScheduleRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9BodyPrefixSemanticsV1

open AspisR1S9HelperP6

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

structure BodyZeroOutputWitness
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W) where
  execution : BodyPrefixWitness ap0 ap1 extra 0#usize iterNext weights0
    (.cont (iterNext, output))
  output0Canonical : AspisR1.S9SideZeroTailRootV1.canonical
    (AspisR1.S9ArrayWriteScheduleRootV1.cells output ⟨0, by decide⟩)
  output1Canonical : AspisR1.S9SideZeroTailRootV1.canonical
    (AspisR1.S9ArrayWriteScheduleRootV1.cells output ⟨1, by decide⟩)
  outputMeaning : ∀ j : Fin 4,
    AspisR1.S9SideZeroTailRootV1.decode
      (AspisR1.S9ArrayWriteScheduleRootV1.cells output j) =
      if j.val = 0 then AspisR1.S9SideZeroTailRootV1.decode execution.low *
        AspisR1.S9SideZeroTailRootV1.decode execution.all
      else if j.val = 1 then
        (AspisR1.S9SideZeroTailRootV1.decode execution.low *
          AspisR1.S9SideZeroTailRootV1.decode execution.first3) *
        algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact
          (AspisR1.S9SideZeroTailRootV1.qdecode execution.q16)
      else AspisR1.S9SideZeroTailRootV1.decode
        (AspisR1.S9ArrayWriteScheduleRootV1.cells weights0 j)

/-- The rich prefix's exact afterSums success reaches the same successful
side-zero tail call and output. This declaration is only the source/control
cut; it does not invoke the tail's arithmetic result theorem. -/
theorem body_zero_prefix_reaches_tail
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (p : BodyPrefixWitness ap0 ap1 extra 0#usize iterNext weights0
      (.cont (iterNext, output))) :
    AspisR1.S9SideZeroTailRootV1.sideZeroTail
      weights0 p.low p.first3 p.all p.q16 = .ok output := by
  have hsums := p.afterSums
  have hdispatch := AspisR1S9AfterSumsTailDispatchV1.afterSums_side_zero
    ap1 weights0 iterNext p.low p.first2 p.first3 p.all p.q4 p.q16
  rw [hdispatch] at hsums
  obtain ⟨tailOutput, htailOutput, hcont⟩ :=
    bind_success_inv (AspisR1.S9SideZeroTailRootV1.sideZeroTail
      weights0 p.low p.first3 p.all p.q16)
      (fun out => Result.ok (ControlFlow.cont (iterNext, out)))
      (ControlFlow.cont (iterNext, output)) hsums
  have hcont' := Result.ok.inj hcont
  have hpair := ControlFlow.cont.inj hcont'
  have htailEq : tailOutput = output := congrArg Prod.snd hpair
  subst tailOutput
  exact htailOutput

/-- A successful side-zero tail call has the concrete canonical output and
field meaning proved by its totality owner. -/
theorem body_zero_tail_success_nonempty
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (p : BodyPrefixWitness ap0 ap1 extra 0#usize iterNext weights0
      (.cont (iterNext, output)))
    (htail : AspisR1.S9SideZeroTailRootV1.sideZeroTail
      weights0 p.low p.first3 p.all p.q16 = .ok output) :
    Nonempty (BodyZeroOutputWitness ap0 ap1 extra iterNext weights0 output) := by
  have hsideQCan : AspisR1.S9SideZeroTailRootV1.qcanonical p.q16 := by
    change AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ p.q16
    exact p.q16Canonical
  obtain ⟨expected, hexpected, hcan0, hcan1, hformula⟩ :=
    AspisR1.S9SideZeroTailRootV1.sideZeroTail_total_exact
      weights0 p.low p.first3 p.all p.q16 p.lowCanonical
      p.first3Canonical p.allCanonical hsideQCan
  have houtEq : expected = output := Result.ok.inj (hexpected.symm.trans htail)
  subst expected
  exact ⟨{ execution := p, output0Canonical := hcan0, output1Canonical := hcan1, outputMeaning := hformula }⟩

/-- Consume an already-constructed prefix in two small steps: first recover
its concrete tail call, then attach the tail's totality semantics. -/
theorem body_zero_tail_from_prefix_nonempty
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (p : BodyPrefixWitness ap0 ap1 extra 0#usize iterNext weights0
      (.cont (iterNext, output))) :
    Nonempty (BodyZeroOutputWitness ap0 ap1 extra iterNext weights0 output) := by
  have htail := body_zero_prefix_reaches_tail ap0 ap1 extra iterNext weights0 output p
  exact body_zero_tail_success_nonempty ap0 ap1 extra iterNext weights0 output p htail

/-- Construct the prefix once from the actual active-body success, then hand
that record to the small branch consumer above. -/
theorem body_zero_output_witness_nonempty
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (hactive : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra 0#usize iterNext weights0 =
        .ok (.cont (iterNext, output)))
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → canonical x)
    (hextra : ∀ (j : U) (x : Q),
      Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    Nonempty (BodyZeroOutputWitness ap0 ap1 extra iterNext weights0 output) := by
  obtain ⟨p⟩ := body_prefix_witness_nonempty ap0 ap1 extra 0#usize iterNext
    weights0 (.cont (iterNext, output)) hactive hp0 hp1 hextra
  exact body_zero_tail_from_prefix_nonempty ap0 ap1 extra iterNext weights0 output p

noncomputable def body_zero_output_witness
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iterNext : core.ops.range.Range U) (weights0 output : W)
    (hactive : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra 0#usize iterNext weights0 =
        .ok (.cont (iterNext, output)))
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → canonical x)
    (hextra : ∀ (j : U) (x : Q),
      Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    BodyZeroOutputWitness ap0 ap1 extra iterNext weights0 output :=
  Classical.choice (body_zero_output_witness_nonempty ap0 ap1 extra iterNext
    weights0 output hactive hp0 hp1 hextra)

#print axioms body_zero_prefix_reaches_tail
#print axioms body_zero_tail_success_nonempty
#print axioms body_zero_tail_from_prefix_nonempty
#print axioms body_zero_output_witness_nonempty
#print axioms body_zero_output_witness

end AspisR1S9BodyPrefixSemanticsV1
