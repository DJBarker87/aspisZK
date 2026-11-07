import PV_THR2_Spawn361HookTrueSuffixReached
import PV_THR2_Spawn361HookFalseSuffixReached
import PV_THR2_AtReadyInactive
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Spawn361HooksJoined
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Internal Boolean field and actual source control, plus both named returned
cases. Compose the existing retained hook group, including inactive other-arm
segments. No arm is selected as a closure hypothesis. Translator conditional. -/
theorem after {E : Type} (C : Carrier OWNER Data) (b flag : Bool)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 40) c)
    (fresh : c.frame.activation < c.store.nextActivation)
    (hooksCell : c.store.cells ⟨c.frame.activation,14,[]⟩ = some (.boolean flag)) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let q0 := PV_THR2_Source361HookBranch.after B q
    let q1 := PV_THR2_Source361HookTrueFull.after B H q0
    let q2 := PV_THR2_Source361HookFalsePrefix.after B q1
    let q3 := PV_THR2_Source361HookFalseFull.after B H q2
    let q4 := PV_THR2_Source361HookTrueSuffix.after B q3
    let q5 := PV_THR2_Source361HookFalseSuffix.after B q4
    PV_THR2_OwnInitExactReturnedCases.ReturnedAt B H q0
      (PV_THR2_F361.block42 ++ PV_THR2_F361.live.body.drop 41)
      PV_THR2_Source361HookChildren.fnTrueFull [] →
    PV_THR2_OwnInitExactReturnedCases.ReturnedAt B H q2
      (PV_THR2_F361.block51.drop 4 ++ PV_THR2_F361.live.body.drop 41)
      PV_THR2_Source361HookChildren.fnFalseFull [.move (.local 15)] →
    ∃ d, q5.current.status = .running d ∧
      d.frame.activation < d.store.nextActivation ∧
      PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 41) d ∧
      (∀ i, i ≠ 13 → i ≠ 14 → i ≠ 15 → i ≠ 16 → i ≠ 65 →
        d.store.cells ⟨d.frame.activation,i,[]⟩ = c.store.cells ⟨c.frame.activation,i,[]⟩) ∧
      ∃ hook, d.store.cells ⟨d.frame.activation,13,[]⟩ = some hook := by
  intro B q0 q1 q2 q3 q4 q5 returnedTrue returnedFalse
  obtain ⟨d,status,freshD,readyD,keepD⟩ :=
    PV_THR2_Spawn361HookBranchReached.after C b flag q c running ready fresh hooksCell
  change q0.current.status = .running d at status
  cases flag with
  | true =>
    change PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block42 ++ PV_THR2_F361.live.body.drop 41) d at readyD
    obtain ⟨e,statusE,freshE,readyE,keepE,hook,hookE⟩ :=
      PV_THR2_Spawn361HookTrueReached.after C b H q0 d status readyD freshD returnedTrue
    change q1.current.status = .running e at statusE
    have eqq2 : q2 = q1 := by
      
      change PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.block51 ++ PV_THR2_F361.live.body.drop 41) _ q1 = q1
      exact PV_THR2_AtReadyInactive.after _ _ _ q1 e statusE readyE (by
        simp only [List.length_append,List.length_drop,
          show PV_THR2_F361.block42.length = 2 from rfl,
          show PV_THR2_F361.block51.length = 8 from rfl]
        omega)
    have eqq3 : q3 = q1 := by
      dsimp only [q3]; rw [eqq2]
      change PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.block51.drop 4 ++ PV_THR2_F361.live.body.drop 41) _ q1 = q1
      exact PV_THR2_AtReadyInactive.after _ _ _ q1 e statusE readyE (by
        simp only [List.length_append,List.length_drop,
          show PV_THR2_F361.block42.length = 2 from rfl,
          show PV_THR2_F361.block51.length = 8 from rfl]
        omega)
    obtain ⟨u,statusU,freshU,readyU,keepU,liveU⟩ :=
      PV_THR2_Spawn361HookTrueSuffixReached.after C b q1 e statusE readyE freshE
    have q4eq : q4 = PV_THR2_Source361HookTrueSuffix.after B q1 := by
      dsimp only [q4]; rw [eqq3]
    have q5eq : q5 = q4 := by
      change PV_THR2_IntrinsicAtContinuation.after _ _ q4 = q4
      rw [q4eq]
      exact PV_THR2_AtReadyInactive.after _ _ _ _ u statusU readyU (by
        simp only [List.length_append,List.length_drop,
          show PV_THR2_F361.block42.length = 2 from rfl,
          show PV_THR2_F361.block51.length = 8 from rfl]
        omega)
    refine ⟨u,?_,freshU,readyU,?_,hook,?_⟩
    · rw [q5eq,q4eq]; exact statusU
    · intro i n13 n14 n15 n16 n65
      exact (keepU i n65).trans ((keepE i n13).trans (keepD i n14))
    · exact (keepU 13 (by omega)).trans hookE
  | false =>
    change PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.block51 ++ PV_THR2_F361.live.body.drop 41) d at readyD
    have q1eq : q1 = q0 := by
      change PV_THR2_IntrinsicAtContinuation.after _ _ q0 = q0
      exact PV_THR2_AtReadyInactive.after _ _ _ q0 d status readyD (by
        simp only [List.length_append,List.length_drop,
          show PV_THR2_F361.block42.length = 2 from rfl,
          show PV_THR2_F361.block51.length = 8 from rfl]
        omega)
    obtain ⟨e,statusE,freshE,readyE,keepE,refE⟩ :=
      PV_THR2_Spawn361HookFalsePrefixReached.after C b q0 d status readyD freshD
    have q2eq : q2 = PV_THR2_Source361HookFalsePrefix.after B q0 := by
      dsimp only [q2]; rw [q1eq]
    have ret : PV_THR2_OwnInitExactReturnedCases.ReturnedAt B H
        (PV_THR2_Source361HookFalsePrefix.after B q0)
        (PV_THR2_F361.block51.drop 4 ++ PV_THR2_F361.live.body.drop 41)
        PV_THR2_Source361HookChildren.fnFalseFull [.move (.local 15)] := by
      rw [← q2eq]; exact returnedFalse
    obtain ⟨u,statusU,freshU,readyU,keepU,hook,hookU⟩ :=
      PV_THR2_Spawn361HookFalseReached.after C b H _ e _ statusE readyE freshE refE ret
    have q3eq : q3 = PV_THR2_Source361HookFalseFull.after B H
        (PV_THR2_Source361HookFalsePrefix.after B q0) := by
      dsimp only [q3]; rw [q2eq]
    have q4eq : q4 = q3 := by
      change PV_THR2_IntrinsicAtContinuation.after _ _ q3 = q3
      rw [q3eq]
      exact PV_THR2_AtReadyInactive.after _ _ _ _ u statusU readyU (by
        simp only [List.length_append,List.length_drop,
          show PV_THR2_F361.block42.length = 2 from rfl,
          show PV_THR2_F361.block51.length = 8 from rfl]
        omega)
    obtain ⟨v,statusV,freshV,readyV,keepV,liveV⟩ :=
      PV_THR2_Spawn361HookFalseSuffixReached.after C b _ u statusU readyU freshU
    refine ⟨v,?_,freshV,readyV,?_,hook,?_⟩
    · dsimp only [q5]; rw [q4eq,q3eq]; exact statusV
    · intro i n13 n14 n15 n16 n65
      exact (keepV i n65 n15 n16).trans
        ((keepU i n13 n15).trans ((keepE i n15 n16).trans (keepD i n14)))
    · exact (keepV 13 (by omega) (by omega) (by omega)).trans hookU
#print axioms after
end PV_THR2_Spawn361HooksJoined
