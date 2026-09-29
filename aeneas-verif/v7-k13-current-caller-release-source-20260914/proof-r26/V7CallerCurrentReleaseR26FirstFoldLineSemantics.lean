import V7CallerCurrentReleaseR26K1LineBatchFoldBridge

/-!
# Composed first-fold line-batch semantics

This module packages the exact public 16-entry source fold and its K1 weight
transport behind one opaque theorem for the seven-component aggregation.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FirstFoldLineSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchFoldStep
open V7CallerCurrentReleaseR26LineBatchFoldLoop
open V7CallerCurrentReleaseR26LineBatchFold
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open V7CallerCurrentReleaseR26K1LineBatchFoldBridge

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31

local instance : Inhabited RawM31 := ⟨field.M31.ZERO⟩
local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

structure FirstFoldLineFacts
    (alpha : RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (deferredOut : Std.U8) : Prop where
  scalesCanonical : CanonicalQM31Slice scalesOut
  xsCanonical : CanonicalM31Slice xsOut
  scalesLength : scalesOut.val.length = 16
  xsLength : xsOut.val.length = 16
  deferredExact : deferredOut.val = 2
  weights :
    AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64 (exactRaw alpha)
        (lineBatchComponentWeights 4 (alloc.vec.Vec.deref lineScales)
          (alloc.vec.Vec.deref lineXs) 0) =
      lineBatchComponentWeights 3 scalesOut xsOut deferredOut.val

private theorem exact_line_prefix
    (alpha alpha2 alpha3 : RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (deferredOut : Std.U8)
    (hlineScalesLength : lineScales.val.length = 16)
    (hlineXsLength : lineXs.val.length = 16)
    (hlineScales : CanonicalQM31Slice (alloc.vec.Vec.deref lineScales))
    (hlineXs : CanonicalM31Slice (alloc.vec.Vec.deref lineXs))
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run : sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
      (alloc.vec.Vec.deref_mut lineScales).1
      (alloc.vec.Vec.deref_mut lineXs).1 0#u8 alpha alpha2 alpha3 =
        ok (scalesOut, xsOut, deferredOut)) :
    FoldPrefix (generatedQm31ToExact alpha)
        (alloc.vec.Vec.deref lineScales) (alloc.vec.Vec.deref lineXs)
        (scalesOut, xsOut, 16#usize) ∧ deferredOut.val = 2 ∧
      (AspisV5FriRelationCandidateBridge.dualWeightFoldLayer 64 (exactRaw alpha)
          (lineBatchComponentWeights 4 (alloc.vec.Vec.deref lineScales)
            (alloc.vec.Vec.deref lineXs) 0) =
        lineBatchComponentWeights 3 scalesOut xsOut deferredOut.val) := by
  have lineInputScales : (alloc.vec.Vec.deref_mut lineScales).1 =
      alloc.vec.Vec.deref lineScales := rfl
  have lineInputXs : (alloc.vec.Vec.deref_mut lineXs).1 =
      alloc.vec.Vec.deref lineXs := rfl
  have scalesLength :
      (alloc.vec.Vec.deref lineScales).val.length = 16 := by
    change lineScales.val.length = 16
    exact hlineScalesLength
  have xsLength : (alloc.vec.Vec.deref lineXs).val.length = 16 := by
    change lineXs.val.length = 16
    exact hlineXsLength
  have sameLength :
      (alloc.vec.Vec.deref lineXs).val.length =
        (alloc.vec.Vec.deref lineScales).val.length :=
    xsLength.trans scalesLength.symm
  rw [lineInputScales, lineInputXs] at run
  obtain ⟨linePrefix, deferredExact⟩ :=
    fold_line_m31_batch_arity4_exact (alloc.vec.Vec.deref lineScales)
      (alloc.vec.Vec.deref lineXs) 0#u8 alpha alpha2 alpha3 scalesOut xsOut
      deferredOut scalesLength sameLength (by norm_num) hlineScales hlineXs
      halpha halpha2 halpha3 halpha2Exact halpha3Exact run
  have processed := fold_line_m31_batch_arity4_processed
    (alloc.vec.Vec.deref lineScales) (alloc.vec.Vec.deref lineXs) 0#u8 alpha
    alpha2 alpha3 scalesOut xsOut deferredOut scalesLength sameLength
    hlineScales hlineXs halpha halpha2 halpha3 halpha2Exact halpha3Exact run
  have weights := lineBatchFoldCompleted16_transports_weights 3
    (alloc.vec.Vec.deref lineScales) (alloc.vec.Vec.deref lineXs) 0#u8 alpha
    scalesOut xsOut deferredOut processed deferredExact
  exact ⟨linePrefix, by simpa using deferredExact, weights⟩

theorem first_fold_line_facts
    (alpha alpha2 alpha3 : RawQM31)
    (lineScales : alloc.vec.Vec RawQM31)
    (lineXs : alloc.vec.Vec RawM31)
    (scalesOut : Slice RawQM31) (xsOut : Slice RawM31)
    (deferredOut : Std.U8)
    (hlineScalesLength : lineScales.val.length = 16)
    (hlineXsLength : lineXs.val.length = 16)
    (hlineScales : CanonicalQM31Slice (alloc.vec.Vec.deref lineScales))
    (hlineXs : CanonicalM31Slice (alloc.vec.Vec.deref lineXs))
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3)
    (run : sumcheck.WeightAccumulator.impl.fold_line_m31_batch_arity4
      (alloc.vec.Vec.deref_mut lineScales).1
      (alloc.vec.Vec.deref_mut lineXs).1 0#u8 alpha alpha2 alpha3 =
        ok (scalesOut, xsOut, deferredOut)) :
    FirstFoldLineFacts alpha lineScales lineXs scalesOut xsOut deferredOut := by
  have scalesLength :
      (alloc.vec.Vec.deref lineScales).val.length = 16 := by
    change lineScales.val.length = 16
    exact hlineScalesLength
  have xsLength : (alloc.vec.Vec.deref lineXs).val.length = 16 := by
    change lineXs.val.length = 16
    exact hlineXsLength
  obtain ⟨linePrefix, deferredExact, weights⟩ :=
    exact_line_prefix alpha alpha2 alpha3 lineScales lineXs scalesOut xsOut
      deferredOut hlineScalesLength hlineXsLength hlineScales hlineXs halpha
      halpha2 halpha3 halpha2Exact halpha3Exact run
  exact {
    scalesCanonical := linePrefix.currentScalesCanonical
    xsCanonical := linePrefix.currentXsCanonical
    scalesLength := linePrefix.stateScalesLength.trans scalesLength
    xsLength := linePrefix.stateXsLength.trans xsLength
    deferredExact := by simpa using deferredExact
    weights := weights }

#print axioms first_fold_line_facts

end V7CallerCurrentReleaseR26FirstFoldLineSemantics
