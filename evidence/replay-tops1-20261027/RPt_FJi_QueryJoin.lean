import RPt_FJi_MatchingMeaning
import Port3_NativeQueryBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_QueryJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
abbrev E := FIp_DotsAdapter.E
/-- The input and output are existentially exposed by THIS query call, and the
opening608 is fixed to its SAME opening. No independently supplied successful dot. -/
def Meaning (ops : Ops) (proof : Slice U8) (index : Usize) (g : Array E 29#usize) : Prop :=
  ∃ (opening : Slice U8) (dots : Array E 4#usize) (opening608 : Array U8 608#usize),
    ops.op11 proof index=ok opening ∧ FIp_DotsAdapter.dots opening g=ok dots ∧
    opening608.val=opening.val.take 608 ∧ ∀ slot : Fin 4,
      Port5Q1_OpeningValues.values dots slot=FJi_SlotValue.model opening608 (FIp_DotsAdapter.toArray g)
        (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))

theorem value (ops : Ops) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
    (answer : core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
    (installed : ops.op20=FIp_DotsAdapter.dots)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (run : verifier.candidate.query_values ops proof p a g obs geometry pending=ok answer) :
    Meaning ops proof a.next g := by
  unfold verifier.candidate.query_values at run
  obtain ⟨query,hquery,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨opening,hopening,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨dots,hdots,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  rw [installed] at hdots
  obtain ⟨opening608,hprefix,values⟩ := FJi_MatchingMeaning.value opening g dots hg hdots
  exact ⟨opening,dots,opening608,hopening,hdots,hprefix,values⟩
#print axioms value
end AspisR1.FJi_QueryJoin
end
