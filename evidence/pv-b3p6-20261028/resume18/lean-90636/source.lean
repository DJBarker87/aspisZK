import PV_B3P_MetadataSource580227
namespace PV_B3P_MetadataFamily580227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_MetadataSource580227
set_option autoImplicit false
/-- Every one of the2 captured incoming calls has this metadata state. -/
def sourceState_224 (_caller : Fin 2) (prior : Store) : Store := equalityState prior 7 7
theorem certificate_224 {α : Type} (caller : Fin 2) (prior : Store) (normal first second : Result α) :
    ¬ diagnostic (condition (sourceState_224 caller prior) 12 = true) ∧
      branch (condition (sourceState_224 caller prior) 12 = true) normal first =
        branch (condition (sourceState_224 caller prior) 12 = true) normal second :=
  equality_certificate prior 7 normal first second
#print axioms certificate_224
/-- Every one of the6 captured incoming calls has this metadata state. -/
def sourceState_241 (_caller : Fin 6) (prior : Store) : Store := packState prior 4 4
theorem certificate_241 {α : Type} (caller : Fin 6) (prior : Store) (normal first second : Result α) :
    ¬ diagnostic (condition (sourceState_241 caller prior) 2 = true) ∧
      branch (condition (sourceState_241 caller prior) 2 = true) normal first =
        branch (condition (sourceState_241 caller prior) 2 = true) normal second :=
  pack_certificate prior 4 0 normal first second
#print axioms certificate_241
end PV_B3P_MetadataFamily580227
