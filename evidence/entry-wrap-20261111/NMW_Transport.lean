import NMW_Carrier
import NMW_EntryFold
set_option autoImplicit false
noncomputable section
namespace NMW_Transport
open Aeneas Aeneas.Std AspisR1 NMW_Outcome NMW_FullDispatch NMW_RowSpecs
/-- A required representation lemma for a sibling packet must relate the
WHOLE outcome at mapped original arguments. No returned-only equivalence. -/
def ChildSpec {A B W V E F : Type} (accountView : Slice A ≃ Slice B)
 (world : W ≃ V) (event : E ≃ F) (native : Child A W E) (model : Child B V F)
 (domain : Args A → W → Prop) : Prop :=
 ∀ input before, domain input before →
 NMW_Carrier.outcome world event (native input before) =
 model (NMW_Carrier.args accountView input) (world before)

theorem process_fold {A B W V E F : Type} (accountView : Slice A ≃ Slice B)
 (world : W ≃ V) (event : E ≃ F) (native : Children A W E) (model : Children B V F)
 (parentDomain firstDomain secondDomain : Args A → W → Prop)
 (first : ChildSpec accountView world event native.first model.first firstDomain)
 (second : ChildSpec accountView world event native.second model.second secondDomain)
 (caller1 : CallerClause Hiq_ReleaseRoute.stage1 parentDomain firstDomain)
 (caller2 : CallerClause Hiq_ReleaseRoute.asq8 parentDomain secondDomain)
 (input : Args A) (before : W) (own : parentDomain input before)
 (release : Release input.data) :
 NMW_Carrier.outcome world event (process native input before) =
 process model (NMW_Carrier.args accountView input) (world before) := by
 rcases release with one | two
 · rw [process_first native input before one,
       process_first model (NMW_Carrier.args accountView input) (world before) one]
   exact first input before (caller1 input before own one)
 · rw [process_second native input before two,
       process_second model (NMW_Carrier.args accountView input) (world before) two]
   exact second input before (caller2 input before own two)

theorem entry_fold {A B W V E F : Type} (accountView : Slice A ≃ Slice B)
 (world : W ≃ V) (event : E ≃ F) (native : Children A W E) (model : Children B V F)
 (parentDomain firstDomain secondDomain : Args A → W → Prop)
 (first : ChildSpec accountView world event native.first model.first firstDomain)
 (second : ChildSpec accountView world event native.second model.second secondDomain)
 (caller1 : CallerClause Hiq_ReleaseRoute.stage1 parentDomain firstDomain)
 (caller2 : CallerClause Hiq_ReleaseRoute.asq8 parentDomain secondDomain)
 (input : Args A) (before : W) (own : parentDomain input before) :
 NMW_Carrier.outcome world event (entry native input before) =
 entry model (NMW_Carrier.args accountView input) (world before) := by
 rw [entry_total,entry_total]
 simp only [NMW_Carrier.args_data]
 change NMW_Carrier.outcome world event (match Hiq_ReleaseRoute.route input.data with
 | .first => native.first input before
 | .second => native.second input before
 | .reject => .returned (.Err .InvalidInstructionData) before []) = _
 cases selected : Hiq_ReleaseRoute.route input.data with
 | first => exact first input before (caller1 input before own
     ((Hiq_ReleaseRoute.first_iff input.data).mp selected))
 | second => exact second input before (caller2 input before own
     ((Hiq_ReleaseRoute.second_iff input.data).mp selected).2)
 | reject => rfl
#print axioms process_fold
#print axioms entry_fold
end NMW_Transport
end
