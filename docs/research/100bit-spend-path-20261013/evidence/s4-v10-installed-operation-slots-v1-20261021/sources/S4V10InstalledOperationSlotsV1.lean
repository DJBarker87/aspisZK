import S4V10LiteralHelperSourceCutV1
import S4ConcreteTailInstallRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsV10InstalledOperationSlotsV1
open AspisR1FastDotsV10LiteralHelperSourceCutV1
open AspisR1FastDotsV10CarrierMapV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev S4Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev U32 := Aeneas.Std.U32

/-- The literal V10 from-limbs adapter on the concrete installed source slot
    is the checked EbyKFinish body transported first to the S4 carrier and then
    to V10. This covers every Result outcome and does not import the V10 raw
    FunsExternal axiom. -/
theorem literal_from_limbs_installed (base : Ops) (limbs : Array U32 8#usize) :
    literalFromLimbs (AspisR1FastDotsConcreteTailInstallRootV1.install base) limbs =
      AspisR1FastDotsV10FactoredHelperTransportV1.mapRes
        (fun o : Option S4Wide => o.map wideFromEbyK)
        (AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent limbs) := by
  have hslot :
      (AspisR1FastDotsConcreteTailInstallRootV1.install base).wideFromLimbs =
        AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent :=
    (AspisR1FastDotsConcreteTailInstallRootV1.source_bindings base).2.2.2.2.1
  unfold literalFromLimbs
  rw [hslot]
  cases h : AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent limbs <;>
    simp [AspisR1FastDotsV10FactoredHelperTransportV1.mapRes]

/-- The literal V10 addition adapter on the concrete installed slot is the
    exact `currentWideAddS4` source body under the same carrier map, for every
    success/failure/divergence outcome. -/
theorem literal_add_installed (base : Ops) (x y : V10Wide) :
    literalAdd (AspisR1FastDotsConcreteTailInstallRootV1.install base) x y =
      AspisR1FastDotsV10FactoredHelperTransportV1.mapRes wideFromEbyK
        (AspisR1FastDotsTailWideAddCurrentV1.currentWideAddS4
          (wideToEbyK x) (wideToEbyK y)) := by
  have hslot :
      (AspisR1FastDotsConcreteTailInstallRootV1.install base).wideAdd =
        AspisR1FastDotsTailWideAddCurrentV1.currentWideAddS4 :=
    (AspisR1FastDotsConcreteTailInstallRootV1.source_bindings base).2.2.2.2.2
  unfold literalAdd
  rw [hslot]

/-- Expand the selected wide-add adapter to the transparent extracted current
    `WideExact.add` body; this is an all-Result equation. -/
theorem current_add_body (x y : S4Wide) :
    AspisR1FastDotsTailWideAddCurrentV1.currentWideAddS4 x y =
      AspisR1FastDotsV10FactoredHelperTransportV1.mapRes
        AspisR1FastDotsTailWideAddCurrentV1.currentToS4E
        (AspisR1CurrentWide.field.wide_exact.WideExact.add
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE y)) := by
  rfl

#print axioms literal_from_limbs_installed
#print axioms literal_add_installed
#print axioms current_add_body

end AspisR1FastDotsV10InstalledOperationSlotsV1
