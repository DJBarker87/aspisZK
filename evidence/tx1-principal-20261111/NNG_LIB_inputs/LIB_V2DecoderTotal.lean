import LIB_V2ValidatorTotal
import NHY_RegistryModel
import NCX_Install
set_option autoImplicit false
noncomputable section
namespace LIB_V2DecoderTotal
open Aeneas Aeneas.Std Result LIB_ResultTotal

theorem registry_model (b : Slice U8) : Total (NHY_RegistryModel.body b) := by
 unfold NHY_RegistryModel.body
 repeat' first | exact pure _ | split | apply bind _ _ (LIB_V2ValidatorTotal.registry _) | intro

theorem entry_model (b : Slice U8) : Total (NIJ_EntryModel.body b) := by
 unfold NIJ_EntryModel.body
 repeat' first | exact pure _ | split | apply bind _ _ (LIB_V2ValidatorTotal.entry _) | intro

theorem registry (b : Slice U8) : Total (NCX_Install.op33 b) := by
 unfold NCX_Install.op33
 rw [NHY_RegistryModel.source]
 exact bind _ _ (registry_model b) (fun _ => pure _)

theorem entry (b : Slice U8) : Total (NCX_Install.op34 b) := by
 unfold NCX_Install.op34
 rw [NIJ_EntryModel.source]
 exact bind _ _ (entry_model b) (fun _ => pure _)

#print axioms registry_model
#print axioms entry_model
#print axioms registry
#print axioms entry
end LIB_V2DecoderTotal
end
