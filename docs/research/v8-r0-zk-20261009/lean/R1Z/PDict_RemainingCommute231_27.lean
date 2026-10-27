import R1Z.PDict_RemainingCommute231_26
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Array32 in

theorem stage27 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_Array32.native base)) :
    PDict_Array32.selected base (@replace (PDict_Array32.native base) ops other) =
    @replace (PDict_Array32.native base) (PDict_Array32.selected base ops) other := by
  letI : ExternalTypes := PDict_Array32.native base
  let upd (d : @ExternalFuns (PDict_Array32.native base)) : @ExternalFuns (PDict_Array32.native base) :=
    { d with op211 := fun value => .ok (flatten value) }
  have hu (d : @ExternalFuns (PDict_Array32.native base)) :
      upd (@replace (PDict_Array32.native base) d other) = @replace (PDict_Array32.native base) (upd d) other := by rfl
  change upd (PDict_DigestDelegates.selected base (@replace (PDict_Array32.native base) ops other)) =
    @replace (PDict_Array32.native base) (upd (PDict_DigestDelegates.selected base ops)) other
  exact (congrArg upd (stage26 base ops other)).trans (hu (PDict_DigestDelegates.selected base ops))

#print axioms stage27
end R1Z.PDict_RemainingCommute231
