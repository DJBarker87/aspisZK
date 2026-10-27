import R1Z.PDict_RemainingCommute231_28
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Fence in

theorem stage29 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_Fence.native base)) :
    PDict_Fence.selected base (@replace (PDict_Fence.native base) ops other) =
    @replace (PDict_Fence.native base) (PDict_Fence.selected base ops) other := by
  letI : ExternalTypes := PDict_Fence.native base
  let upd (d : @ExternalFuns (PDict_Fence.native base)) : @ExternalFuns (PDict_Fence.native base) :=
    { d with op13 := fence }
  have hu (d : @ExternalFuns (PDict_Fence.native base)) :
      upd (@replace (PDict_Fence.native base) d other) = @replace (PDict_Fence.native base) (upd d) other := by rfl
  change upd (PDict_SaltClear.selected base (@replace (PDict_Fence.native base) ops other)) =
    @replace (PDict_Fence.native base) (upd (PDict_SaltClear.selected base ops)) other
  exact (congrArg upd (stage28 base ops other)).trans (hu (PDict_SaltClear.selected base ops))

#print axioms stage29
end R1Z.PDict_RemainingCommute231
