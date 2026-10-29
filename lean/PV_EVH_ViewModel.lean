import PV_EVH_EntropyLoop
import PV_EVH_NonceSource
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ViewModel
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World PV_EVH_Entropy PV_EVH_NonceWorld
variable [ExternalTypes] [ExternalFuns]

/-- MODEL VIEW ONLY. These source-value answers show the erasure hypotheses
are jointly satisfiable. Empty observation adapters are deliberately labelled:
this is neither a native file model nor a ruling-(v) successful prover run. -/
def entropy : EntropyAnswers := fun _ input => getrandom.fill input

def files : Answers where
  pathOf := fun _ => []
  bytesOf := fun _ => []
  writeAll := fun _ f b => ⟨std.fs.File.Insts.StdIoWrite.write_all f b,[],none,none⟩
  sync := fun _ f => ⟨std.fs.File.sync_all f,[],none,none⟩
  openReply := fun c p _ => ([],⟨std.fs.File.open c p,[],none,none⟩)
  optionsOpen := fun c o p _ => ([],⟨std.fs.OpenOptions.open c o p,[],none,none⟩)

theorem entropy_agrees : ∀ n input, entropy n input = getrandom.fill input :=
  fun _ _ => rfl

theorem files_agree : Compatible files where
  write := fun _ _ _ => rfl
  sync := fun _ _ => rfl
  openFile := fun _ _ _ => rfl
  options := fun _ _ _ _ => rfl

/-- Joint non-vacuity of the *erasure domain*. No success, observation adequacy,
opsNative installation, publication or entry source link is concluded. -/
theorem joint_view :
    (∀ n input, entropy n input = getrandom.fill input) ∧ Compatible files :=
  ⟨entropy_agrees,files_agree⟩

#print axioms entropy_agrees
#print axioms files_agree
#print axioms joint_view
end PV_EVH_ViewModel
