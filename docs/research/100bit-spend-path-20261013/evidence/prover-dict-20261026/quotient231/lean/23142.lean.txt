import R1Z.PDict_RemainingCommute231_25
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_DigestDelegates in

theorem stage26 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_DigestDelegates.native base)) :
    PDict_DigestDelegates.selected base (@replace (PDict_DigestDelegates.native base) ops other) =
    @replace (PDict_DigestDelegates.native base) (PDict_DigestDelegates.selected base ops) other := by
  letI : ExternalTypes := PDict_DigestDelegates.native base
  let upd (d : @ExternalFuns (PDict_DigestDelegates.native base)) : @ExternalFuns (PDict_DigestDelegates.native base) :=
    { d with
    op2 := PDict_ErrorKind.eq
    op213 := digestUpdate
    op214 := PDict_DigestNew.digestNew }
  have hu (d : @ExternalFuns (PDict_DigestDelegates.native base)) :
      upd (@replace (PDict_DigestDelegates.native base) d other) = @replace (PDict_DigestDelegates.native base) (upd d) other := by rfl
  change upd (PDict_Publication.selected base (@replace (PDict_DigestDelegates.native base) ops other)) =
    @replace (PDict_DigestDelegates.native base) (upd (PDict_Publication.selected base ops)) other
  exact (congrArg upd (stage25 base ops other)).trans (hu (PDict_Publication.selected base ops))

#print axioms stage26
end R1Z.PDict_RemainingCommute231
