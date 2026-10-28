import NDO_JGw_InstalledSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_InitialFacts
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open JGr_Geometry

theorem source (a : verifier.Accumulator)
    (call : installed.op20 .S2=ok (.Ok a)) :
    (Tx1Q_Carriers.accumulator a).weights.val=List.replicate 64 Port2_Initial.zeroK ∧
    (Tx1Q_Carriers.accumulator a).rhs=Port2_Initial.zeroE ∧
    (Tx1Q_Carriers.accumulator a).power=Port2_Initial.oneK ∧ a.next=0#usize := by
  rw [JGw_InstalledSlots.initial] at call
  have native := Tx1Q_PrefixInstall.initial_success true a call
  rw [Port3_Initial.constructor_shell] at native
  obtain ⟨weights,success,eq⟩ := (Port2_Initial.newS2_success _ _).mp native
  obtain ⟨_,contents⟩ := CheckpointBytes3Allocation.filled_success_content
    true 64#usize Port2_Initial.zeroK weights success
  have rhs := congrArg (fun x : VTop_Stages.verifier.Accumulator => x.rhs) eq
  have power := congrArg (fun x : VTop_Stages.verifier.Accumulator => x.power) eq
  have next := congrArg (fun x : VTop_Stages.verifier.Accumulator => x.next) eq
  have hw := congrArg (fun x : VTop_Stages.verifier.Accumulator => x.weights.val) eq
  exact ⟨hw.trans contents,rhs,power,next⟩
#print axioms source
end AspisR1.JGw_InitialFacts
end
