-- Canonical RSL retarget of NMT_R2_EmittedCheckpoint; source/proof structure retained.
import NNG_MetaNative345
import NNG_FinishNative345
import NNG_LengthNative345
import NNG_Model345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckpointGraph345
open Aeneas Aeneas.Std NMT_345 RSL AspisR1.NNG_Obs345 AspisR1.NNG_Pure345 AspisR1.NNG_Observe345
open AspisR1.NNG_EquationNative345 AspisR1.NNG_MetaNative345 AspisR1.NNG_FinishNative345

def run (keep : Bool) (a : Account) (program : Key) (writable : Bool) : Obs (Except ProgramError Unit) :=
 observe id (mapOuter (mapCore id fromPE) (native keep a program writable))

theorem native_eq (keep : Bool) (a : Account) (program : Key) (writable : Bool) :
 run keep a program writable =
 AspisR1.NNG_Phases345.checkpointObservation keep (account a) (key program) writable := by
 unfold run AspisR1.NNG_Phases345.checkpointObservation
 rw [bad_canonical,native_normalized]
 cases h : bad a program writable with
 | true => rfl
 | false =>
  simp only [Bool.false_eq_true,if_false]
  rw [← AspisR1.NNG_LengthNative345.equality]
  exact length_continue _

/-- Unrestricted CLOSED341 emitted/std law; every original account and String
error, not just the snapshot error domain of the historical native packet. -/
theorem emitted_checkpoint (keep : Bool) (a : Account) (program : Key) (writable : Bool) (env : Env) :
 RSL.verifierCheckpoint (account a) (key program) writable env (run keep a program writable) := by
 rw [native_eq]
 exact AspisR1.NNG_Phases345.checkpointObservation_valid keep (account a) (key program) writable env
#print axioms native_eq
#print axioms emitted_checkpoint
end AspisR1.NNG_CheckpointGraph345
end
