import CPR_AdmissionGap
import CPR_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_KeyGap
open Aeneas Aeneas.Std Result Hist_Store CPR_Persistence
open MultiproofConeCanonical AspisV8R19.DuplexFrames

def account (key : Bool) : Image :=
  ⟨⟨Hist_Nonvacuity.key 0#u8,if key then CPR_AdmissionGap.other else Hist_Nonvacuity.checkpoint⟩,1⟩

theorem bytes_different :
    bytesOf (account false).cell.data.val ≠ bytesOf (account true).cell.data.val := by
  intro eq
  have head := congrArg (fun xs : Bytes => xs[0]?) eq
  change some (82 : Fin 256) = some (83 : Fin 256) at head
  exact (by decide : (82 : Fin 256) ≠ 83) (Option.some.inj head)

theorem runtime_law :
    TwoTransactionLaw (fun _ _ : Unit => True) (fun (_ : Unit) (_ : Bool) => True)
      (fun (_ : Unit) key => account key) (fun (_ : Unit) key => account key)
      (fun _ => true) (fun (_ : Unit) key => some (account key)) := by
  intro t u adjacent key eligible
  cases key <;> rfl

/-- A true commit/load law does not correlate independent writer/reader keys.
Both positive accounts have the SAME owner, length and initialized-size data.
This isolates pairing, not a source overwrite or full-verifier counterexample. -/
theorem no_cross_key_history :
    ¬ Nonempty (S2X.CheckpointVersionBinding
      (bytesOf (account false).cell.data.val) (bytesOf (account true).cell.data.val)) := by
  rintro ⟨history⟩
  exact bytes_different (S2X.checkpoint_persistence _ _ history).symm

#print axioms bytes_different
#print axioms runtime_law
#print axioms no_cross_key_history
end AspisR1.CPR_KeyGap
end
