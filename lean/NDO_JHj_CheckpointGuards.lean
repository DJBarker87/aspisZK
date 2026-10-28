import NDO_JHj_MasterGuards
import NDO_JHj_Seeds
set_option autoImplicit false
namespace AspisR1.JHj_CheckpointGuards
open Aeneas Aeneas.Std Result

theorem master : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_AccountValues.checkpoint.master JHj_Seeds.key=ok false := by
  have eq : JHg_AccountValues.checkpoint.master=JHj_Seeds.key := by
    unfold JHj_Seeds.key JHg_World.e2
    rfl
  rw [eq]
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms master

theorem domain : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_AccountValues.checkpoint.deployment_domain JHg_AccountValues.master.identity.deployment_domain=ok false :=
  S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms domain
end AspisR1.JHj_CheckpointGuards
