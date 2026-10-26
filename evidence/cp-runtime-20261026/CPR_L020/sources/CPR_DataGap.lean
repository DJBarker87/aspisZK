import CPR_DataPersistence
import CPR_KeyGap
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_DataGap
open Aeneas Aeneas.Std Result Hist_Store MultiproofConeCanonical
open AspisV8R19.DuplexFrames

def original : CPR_Persistence.Image := CPR_Separation.live
def changed : CPR_Persistence.Image := ⟨original.cell,2⟩

theorem narrow_holds :
    CPR_DataPersistence.TwoTransactionLaw (fun _ _ : Unit => True) (fun _ _ : Unit => True)
      (fun _ _ => CPR_DataPersistence.project original)
      (fun _ _ => CPR_DataPersistence.project original) (fun _ => true)
      (fun _ _ => some (bytesOf changed.cell.data.val)) := by
  intro t u adjacent key eligible
  rfl

theorem full_fails :
    ¬ CPR_Persistence.TwoTransactionLaw (fun _ _ : Unit => True) (fun _ _ : Unit => True)
      (fun _ _ => original) (fun _ _ => original) (fun _ => true) (fun _ _ => some changed) := by
  intro law
  have same := Option.some.inj (law () () True.intro () True.intro)
  have balance := congrArg CPR_Persistence.Image.lamports same
  change 2 = 1 at balance
  omega

/-- Old propositions do not constrain the byte-only loader either. -/
theorem old_items_do_not_supply_data_loader (P : Prop) (old : P) :
    P ∧ ¬ CPR_DataPersistence.TwoTransactionLaw
      (fun _ _ : Unit => True) (fun _ _ : Unit => True)
      (fun _ _ => CPR_DataPersistence.project original)
      (fun _ _ => CPR_DataPersistence.project original) (fun _ => true)
      (fun _ _ => none) := by
  refine ⟨old,?_⟩
  intro law
  have impossible := law () () True.intro () True.intro
  change (none : Option Bytes) = some (bytesOf original.cell.data.val) at impossible
  cases impossible

/-- Even the stronger full-image law holds in the independent-key countermodel.
The narrower proposal therefore cannot establish cross-key checkpoint history. -/
theorem key_pairing_still_needed :
    CPR_DataPersistence.TwoTransactionLaw (fun _ _ : Unit => True)
      (fun (_ : Unit) (_ : Bool) => True)
      (fun _ k => CPR_DataPersistence.project (CPR_KeyGap.account k))
      (fun _ k => CPR_DataPersistence.project (CPR_KeyGap.account k))
      (fun _ => true) (fun _ k => some (bytesOf (CPR_KeyGap.account k).cell.data.val)) ∧
    ¬ Nonempty (S2X.CheckpointVersionBinding
      (bytesOf (CPR_KeyGap.account false).cell.data.val)
      (bytesOf (CPR_KeyGap.account true).cell.data.val)) := by
  refine ⟨?_,CPR_KeyGap.no_cross_key_history⟩
  intro t u adjacent key eligible
  cases key <;> rfl

#print axioms narrow_holds
#print axioms full_fails
#print axioms old_items_do_not_supply_data_loader
#print axioms key_pairing_still_needed
end AspisR1.CPR_DataGap
end
