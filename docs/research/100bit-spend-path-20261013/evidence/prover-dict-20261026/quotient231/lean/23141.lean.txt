import R1Z.PDict_RemainingCommute231_24
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open Aeneas Aeneas.Std ProverRwFull
open PDict_Publication in

theorem stage25 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_Publication.native base)) :
    PDict_Publication.selected base (@replace (PDict_Publication.native base) ops other) =
    @replace (PDict_Publication.native base) (PDict_Publication.selected base ops) other := by
  letI : ExternalTypes := PDict_Publication.native base
  let upd (d : @ExternalFuns (PDict_Publication.native base)) : @ExternalFuns (PDict_Publication.native base) :=
    { d with
    op27 := PDict_PathTypes.std.path.Path.Insts.CoreConvertAsRefPath.as_ref
    op206 := shaNew }
  have hu (d : @ExternalFuns (PDict_Publication.native base)) :
      upd (@replace (PDict_Publication.native base) d other) = @replace (PDict_Publication.native base) (upd d) other := by rfl
  change upd (PDict_FinalDictionary.selected base (@replace (PDict_Publication.native base) ops other)) =
    @replace (PDict_Publication.native base) (upd (PDict_FinalDictionary.selected base ops)) other
  exact (congrArg upd (stage24 base ops other)).trans (hu (PDict_FinalDictionary.selected base ops))

#print axioms stage25
end R1Z.PDict_RemainingCommute231
