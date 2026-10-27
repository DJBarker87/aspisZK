import R1Z.PDict_RemainingCommute231_37
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_PureDictionary in

theorem stage38 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_PureDictionary.native base)) :
    PDict_PureDictionary.selected base (@replace (PDict_PureDictionary.native base) ops other) =
    @replace (PDict_PureDictionary.native base) (PDict_PureDictionary.selected base ops) other := by
  letI : ExternalTypes := PDict_PureDictionary.native base
  let upd (d : @ExternalFuns (PDict_PureDictionary.native base)) : @ExternalFuns (PDict_PureDictionary.native base) :=
    { d with
    op37 := PDict_PureSource.aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
    op40 := PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone
    op41 := PDict_PureSource.aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq
    op43 := PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c0
    op44 := PDict_PureSource.aspis_core.field.wide_exact.WideExact.impl.c1
    op60 := PDict_PureSource.aspis_core.field.CM31.new
    op235 := PDict_ConstantsSource.leaf_bits
    op236 := PDict_ConstantsSource.max_batch
    op239 := PDict_ConstantsSource.claims
    op240 := PDict_ConstantsSource.lanes
    op260 := PDict_ConstantsSource.domain
  }
  have hu (d : @ExternalFuns (PDict_PureDictionary.native base)) :
      upd (@replace (PDict_PureDictionary.native base) d other) = @replace (PDict_PureDictionary.native base) (upd d) other := by rfl
  change upd (PDict_RejectionStd.selected base (@replace (PDict_PureDictionary.native base) ops other)) =
    @replace (PDict_PureDictionary.native base) (upd (PDict_RejectionStd.selected base ops)) other
  exact (congrArg upd (stage37 base ops other)).trans (hu (PDict_RejectionStd.selected base ops))

#print axioms stage38
end R1Z.PDict_RemainingCommute231
