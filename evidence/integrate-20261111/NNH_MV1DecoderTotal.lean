import NNH_MV1ValidatorTotal
import NJQ_Canonical
set_option autoImplicit false
noncomputable section
namespace NNH_MV1DecoderTotal
open Aeneas Aeneas.Std Result NNH_MResultTotal

theorem registry_model (b : Slice U8) : Total (NJQ_Registry.model b) := by
 unfold NJQ_Registry.model
 split
 · split
   · split
     · split
       · apply bind _ _ (NNH_MV1ValidatorTotal.registry _)
         intro r
         cases r <;> exact pure _
       · exact pure _
     · exact pure _
   · exact pure _
 · exact pure _

theorem entry_model (b : Slice U8) : Total (NJQ_Entry.model b) := by
 unfold NJQ_Entry.model
 split
 · split
   · split
     · split
       · apply bind _ _ (NNH_MV1ValidatorTotal.status _)
         intro r
         cases r with
         | Err e => exact pure _
         | Ok s =>
           apply bind _ _ (NNH_MV1ValidatorTotal.entry _)
           intro checked
           cases checked <;> exact pure _
       · exact pure _
     · exact pure _
   · exact pure _
 · exact pure _

theorem registry (b : Slice U8) : Total (NJQ_Canonical.registry b) :=
 outer _ _ (registry_model b)

theorem entry (b : Slice U8) : Total (NJQ_Canonical.entry b) :=
 outer _ _ (entry_model b)

#print axioms registry_model
#print axioms entry_model
#print axioms registry
#print axioms entry
end NNH_MV1DecoderTotal
end
