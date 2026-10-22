import FourDotsTailAcceptedTraceRootV1
import S4TailFinishSourceMapV1
import FourDotsCurrentQmParserRootV1
import S4N8WideFromLimbsABI
import S4TailWideAddCurrentV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsConcreteTailInstallRootV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps

/-- A single operations value combining the retained concrete tail backend,
strict QM parser, checked limb packing and current wide addition. This does
not assert that the remaining head/array operations refine frozen Rust. -/
def install (base : Ops) : Ops :=
  { base with
    ebyKNew := AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource
    ebyKPush := AspisR1EbyKPushDotBackend.pushWithDotBackend
      AspisR1EbyKPushDecodedProductUpdate.QRaw
    ebyKFinish := AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent
    qm31FromBytes := AspisR1FastDotsCurrentQmParserRootV1.parser
    wideFromLimbs := AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent
    wideAdd := AspisR1FastDotsTailWideAddCurrentV1.currentWideAddS4 }

theorem source_bindings (base : Ops) :
    (install base).ebyKNew =
      AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource ∧
    AspisR1FastDotsTailAcceptedTraceRootV1.PushBinding (install base)
      AspisR1EbyKPushDecodedProductUpdate.QRaw ∧
    (install base).ebyKFinish =
      AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent ∧
    (install base).qm31FromBytes =
      AspisR1FastDotsCurrentQmParserRootV1.parser ∧
    (install base).wideFromLimbs =
      AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent ∧
    (install base).wideAdd =
      AspisR1FastDotsTailWideAddCurrentV1.currentWideAddS4 := by
  exact ⟨rfl, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- Construction is no longer an independent successful-callback premise. -/
theorem new_zero (base : Ops) :
    (install base).ebyKNew = .ok EbyKNewToPushStateABI.pushZero :=
  AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource_zero

/-- The unchanged head operations are literal projections of the base. -/
theorem head_preserved (base : Ops) :
    (install base).wideLimbCount = base.wideLimbCount ∧
    (install base).wideToLimbs = base.wideToLimbs ∧
    (install base).m31ReduceU64 = base.m31ReduceU64 ∧
    (install base).m31FromBytes = base.m31FromBytes :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem arrayFromFn_preserved (base : Ops) {T F : Type} (n : Usize)
    (f : core.ops.function.FnMut F Usize T) (state : F) :
    (install base).arrayFromFn n f state = base.arrayFromFn n f state := rfl

#print axioms source_bindings
#print axioms new_zero
#print axioms head_preserved
#print axioms arrayFromFn_preserved

end AspisR1FastDotsConcreteTailInstallRootV1
