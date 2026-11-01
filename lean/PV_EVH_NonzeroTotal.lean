import PV_EVH_NonzeroSafety
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NonzeroTotal
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open ControlFlow
variable [ExternalTypes] [ExternalFuns]

/-- A symbolic remaining-length invariant, not normalization of 32 input bytes.
The checked source loop terminates without an exceptional primitive result. -/
theorem loop_terminal (bytes : Array U8 32#usize) (remaining fuel : Nat)
    (combined : U8) (i : Usize) (w : World)
    (bound : i.val + remaining = 32) (enough : remaining + 1 ≤ fuel) :
    ∃ out, PV_EVH_NonzeroFlow.loop fuel bytes combined i w =
      ⟨.finished (.ok out),w,[]⟩ := by
  induction remaining generalizing combined i fuel w with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have stop : ¬i < 32#usize := by change ¬i.val < 32; omega
      refine ⟨combined,?_⟩
      have stopStep : PV_EVH_NonzeroStep.run bytes combined i {} =
          PV_EVH_Prefix.lift (.ok (.done combined)) := by
        rw [PV_EVH_NonzeroSafety.step_plain]
        simp only [aspis_prover.state_only_entropy.entropy_nonzero32_loop.body,stop,if_false]
      change PV_EVH_Prefix.bind (PV_EVH_NonzeroStep.run bytes combined i {})
        (fun cf => match cf with
          | .done a => PV_EVH_Prefix.lift (.ok a)
          | .cont next => PV_EVH_PrefixLoop.loop
              (fun (state : U8 × Usize) => PV_EVH_NonzeroStep.run bytes state.1 state.2 {})
              fuel next) w = _
      rw [stopStep]
      rfl
  | succ remaining ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have active : i < 32#usize := by change i.val < 32; omega
      obtain ⟨value,read⟩ := PV_EVH_NonzeroSafety.array_read bytes i active
      have inc := PV_EVH_NonzeroSafety.increment i active
      have nextBound : (Usize.wrapping_add i 1#usize).val + remaining = 32 := by omega
      have nextEnough : remaining + 1 ≤ fuel := by omega
      obtain ⟨out,completed⟩ := ih (fuel := fuel) (combined := combined ||| value)
        (i := Usize.wrapping_add i 1#usize) (w := w) nextBound nextEnough
      refine ⟨out,?_⟩
      have step : PV_EVH_NonzeroStep.run bytes combined i {} =
          PV_EVH_Prefix.lift (.ok (.cont (combined ||| value,Usize.wrapping_add i 1#usize))) := by
        rw [PV_EVH_NonzeroSafety.step_plain]
        simp only [aspis_prover.state_only_entropy.entropy_nonzero32_loop.body,
          active,if_true,read,bind_tc_ok,Aeneas.Std.lift]
      have same : PV_EVH_NonzeroFlow.loop (fuel+1) bytes combined i w =
          PV_EVH_NonzeroFlow.loop fuel bytes (combined ||| value) (Usize.wrapping_add i 1#usize) w := by
        simp only [PV_EVH_NonzeroFlow.loop,PV_EVH_PrefixLoop.loop,step,
          PV_EVH_Prefix.bind,PV_EVH_Prefix.lift,PV_EVH_Prefix.ofM,
          PV_EVH_World.lift,List.nil_append]
      exact same.trans completed

theorem run_terminal (bytes : Array U8 32#usize) (w : World) :
    ∃ out, PV_EVH_NonzeroFlow.run 33 bytes w = ⟨.finished (.ok out),w,[]⟩ := by
  obtain ⟨combined,completed⟩ := loop_terminal bytes 32 33 0#u8 0#usize w rfl (by omega)
  refine ⟨combined != 0#u8,?_⟩
  change PV_EVH_Prefix.bind (PV_EVH_NonzeroFlow.loop 33 bytes 0#u8 0#usize)
    (fun combined => PV_EVH_Prefix.lift (.ok (combined != 0#u8))) w = _
  simp only [PV_EVH_Prefix.bind,completed,PV_EVH_Prefix.lift,
    PV_EVH_Prefix.ofM,PV_EVH_World.lift,List.nil_append]

theorem source_total (bytes : Array U8 32#usize) :
    ∃ out, aspis_prover.state_only_entropy.entropy_nonzero32 bytes = .ok out := by
  obtain ⟨out,completed⟩ := run_terminal bytes {}
  exact ⟨out,PV_EVH_NonzeroFlow.run_fixed 33 bytes {} (.ok out)
    (congrArg PV_EVH_WorldLoop.Prefix.status completed)⟩
#print axioms loop_terminal
#print axioms run_terminal
#print axioms source_total
end PV_EVH_NonzeroTotal
