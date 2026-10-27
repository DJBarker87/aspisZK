import R1Z.PV_Src_ExternalBlocksCopy
import R1Z.PV_Src_ExternalCopyPrefix

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalGroupsCopy
open Aeneas Aeneas.Std Result
open AspisBuilderPoseidonReference PV_Src_ExternalBlockStep

theorem source (s : State) :
    poseidon2.builder_reference.external_owned_loop0 s 0#usize =
      R0PoseidonCopy.ext_groups s := by
  rw [PV_Src_ExternalBlocksCopy.loop 4 s s 0#usize (by decide) (by intros;rfl),
    R0PoseidonCopy.ext_groups]
  exact PV_Src_ExternalCopyPrefix.loop 4 s s (Array.repeat 16#usize 0#u32)
    0#usize (by decide) (by intro j hj;simp at hj)

#print axioms source
end R1Z.PV_Src_ExternalGroupsCopy
