import R1Z.PDict_RemainingCommute231_27
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_SaltClear in

theorem stage28 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_SaltClear.native base)) :
    PDict_SaltClear.selected base (@replace (PDict_SaltClear.native base) ops other) =
    @replace (PDict_SaltClear.native base) (PDict_SaltClear.selected base ops) other := by
  letI : ExternalTypes := PDict_SaltClear.native base
  let upd (d : @ExternalFuns (PDict_SaltClear.native base)) : @ExternalFuns (PDict_SaltClear.native base) :=
    { d with op238 := fun _ => .ok zero }
  have hu (d : @ExternalFuns (PDict_SaltClear.native base)) :
      upd (@replace (PDict_SaltClear.native base) d other) = @replace (PDict_SaltClear.native base) (upd d) other := by rfl
  change upd (PDict_Array32.selected base (@replace (PDict_SaltClear.native base) ops other)) =
    @replace (PDict_SaltClear.native base) (upd (PDict_Array32.selected base ops)) other
  exact (congrArg upd (stage27 base ops other)).trans (hu (PDict_Array32.selected base ops))

#print axioms stage28
end R1Z.PDict_RemainingCommute231
