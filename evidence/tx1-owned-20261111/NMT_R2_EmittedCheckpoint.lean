import NMT_R2_CheckpointMeta
import NMT_R2_CheckpointFinish
import NMT_R2_GetterEquality
import NMT_R2_345Checkpoint
set_option autoImplicit false
noncomputable section
namespace NMT_R2_EmittedCheckpoint
open Aeneas Aeneas.Std NMT_345 RSL NMT_345Observation NMT_R2_Observation NMT_R2_EmittedData
open NMT_R2_CheckpointEquation NMT_R2_CheckpointMeta NMT_R2_CheckpointFinish

def run (keep : Bool) (a : Account) (program : Key) (writable : Bool) : Obs (Except ProgramError Unit) :=
 observe id (mapOuter (mapCore id fromPE) (native keep a program writable))

theorem native_eq (keep : Bool) (a : Account) (program : Key) (writable : Bool) :
 run keep a program writable =
 NMT_R2_345.checkpointObservation keep (account a) (key program) writable := by
 unfold run NMT_R2_345.checkpointObservation
 rw [bad_canonical,native_normalized]
 cases h : bad a program writable with
 | true => rfl
 | false =>
  simp only [Bool.false_eq_true,if_false]
  rw [← NMT_R2_GetterEquality.length_eq]
  exact length_continue _

/-- Unrestricted CLOSED341 emitted/std law; every original account and String
error, not just the snapshot error domain of the historical native packet. -/
theorem emitted_checkpoint (keep : Bool) (a : Account) (program : Key) (writable : Bool) (env : Env) :
 NMT_R2.verifierCheckpoint (account a) (key program) writable env (run keep a program writable) := by
 rw [native_eq]
 exact NMT_R2_345.checkpointObservation_valid keep (account a) (key program) writable env
#print axioms native_eq
#print axioms emitted_checkpoint
end NMT_R2_EmittedCheckpoint
end
