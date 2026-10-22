import S3S9ConcreteWideMulQM31ScalarProductV1
import S9ArrayWriteScheduleRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S9SideZeroTailRootV1
open AspisR1S9HelperP6
abbrev W := field.WideExact
abbrev Q := field.QM31
abbrev Four := 4#usize
abbrev A := Array W Four
abbrev canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev decode := AspisR1S9CurrentFieldOpsV1.decode
abbrev qcanonical (q : Q) := AspisR1CurrentWide.Proof.CanonicalQM
  (AspisR1S9GeneratedWideMulQM31V2.toQM q)
abbrev qdecode (q : Q) := AspisR1CurrentWide.Proof.decodeQM
  (AspisR1S9GeneratedWideMulQM31V2.toQM q)
local instance : FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

/-- Exactly the first branch's arithmetic and checked writes, before its
iterator/control-flow wrapper. -/
def sideZeroTail (old : A) (low first3 all : W) (q16 : Q) : Result A := do
  let we4 ← field.WideExact.mul low all
  let weights1 ← Array.update old 0#usize we4
  let we5 ← field.WideExact.mul low first3
  let we6 ← field.WideExact.mul_qm31 we5 q16
  Array.update weights1 1#usize we6

theorem sideZeroTail_total_exact (old : A) (low first3 all : W) (q16 : Q)
    (hlow : canonical low) (hfirst3 : canonical first3)
    (hall : canonical all) (hq16 : qcanonical q16) :
    ∃ out, sideZeroTail old low first3 all q16 = .ok out ∧
      canonical (S9ArrayWriteScheduleRootV1.cells out 0) ∧
      canonical (S9ArrayWriteScheduleRootV1.cells out 1) ∧
      ∀ j : Fin 4,
      decode (S9ArrayWriteScheduleRootV1.cells out j) =
        if j.val = 0 then decode low * decode all
        else if j.val = 1 then (decode low * decode first3) *
          algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact
            (qdecode q16)
        else decode (S9ArrayWriteScheduleRootV1.cells old j) := by
  obtain ⟨v0,h0,hc0,hd0⟩ :=
    AspisR1S9ConcreteFieldOpsV1.actualWideMul_total_exact low all hlow hall
  obtain ⟨v1base,hbase,hcbase,hdbase⟩ :=
    AspisR1S9ConcreteFieldOpsV1.actualWideMul_total_exact low first3 hlow hfirst3
  obtain ⟨v1,h1,hc1,hd1⟩ :=
    AspisR1S9ConcreteWideMulQM31ScalarProductV1.concrete_wideMulQM31_total_scalar_product
      v1base q16 hcbase hq16
  obtain ⟨middle,hmiddle,hvmiddle⟩ := WP.spec_imp_exists
    (Array.update_spec old 0#usize v0 (by simpa [Array.length, old.property] using (show (0#usize).val < 4 from by decide)))
  obtain ⟨out,hout,hvout⟩ := WP.spec_imp_exists
    (Array.update_spec middle 1#usize v1 (by simpa [Array.length, middle.property] using (show (1#usize).val < 4 from by decide)))
  have htoWide (x : W) : AspisR1S9GeneratedWideMulQM31V2.toWide x =
      AspisR1S9CurrentFieldOpsV1.toE x := by cases x; rfl
  have hd1final : decode v1 = (decode low * decode first3) *
      algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact
        (qdecode q16) := by
    change decode v1 = _ at hd1
    rw [hd1]
    change (decode v1base) * _ = _
    exact congrArg (fun z : AspisWideTower.WideExact => z *
      algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact
        (qdecode q16)) hdbase
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · change (do
      let a ← AspisR1S9ConcreteFieldOpsV1.actualWideMul low all
      let b ← Array.update old 0#usize a
      let c ← AspisR1S9ConcreteFieldOpsV1.actualWideMul low first3
      let d ← @FieldOps.wideMulQM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps c q16
      Array.update b 1#usize d) = .ok out
    simp only [h0, bind_tc_ok, hmiddle, hbase, h1, hout]
  · rw [S9ArrayWriteScheduleRootV1.update_cells middle out 1#usize v1 (by decide) hout 0,
        S9ArrayWriteScheduleRootV1.update_cells old middle 0#usize v0 (by decide) hmiddle 0]
    simpa using hc0
  · rw [S9ArrayWriteScheduleRootV1.update_cells middle out 1#usize v1 (by decide) hout 1]
    change canonical v1
    exact hc1
  · intro j
    rw [S9ArrayWriteScheduleRootV1.update_cells middle out 1#usize v1 (by decide) hout j,
        S9ArrayWriteScheduleRootV1.update_cells old middle 0#usize v0 (by decide) hmiddle j]
    change decode (if j.val = 1 then v1 else if j.val = 0 then v0 else
      S9ArrayWriteScheduleRootV1.cells old j) = _
    by_cases hzero : j.val = 0
    · simp [hzero, hd0]
    · by_cases hone : j.val = 1
      · simp [hzero, hone, hd1final]
      · simp [hzero, hone]

#print axioms sideZeroTail_total_exact
end AspisR1.S9SideZeroTailRootV1
