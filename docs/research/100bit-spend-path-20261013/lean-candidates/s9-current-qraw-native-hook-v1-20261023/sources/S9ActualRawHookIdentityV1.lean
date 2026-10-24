import S9ActualRawNativeOperandsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualRawHookIdentityV1
private theorem map_left_same :
    AspisR1CanonicalDotFinish.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 =
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 := by
  rfl
private theorem map_right_same :
    AspisR1CanonicalDotFinish.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 =
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 := by
  rfl
private theorem pp_same : AspisR1CanonicalDotFinish.canonical.Q.raw.PP = AspisR1CanonicalQRawUnified.canonical.Q.raw.PP := by
  unfold AspisR1CanonicalDotFinish.canonical.Q.raw.PP AspisR1CanonicalQRawUnified.canonical.Q.raw.PP AspisR1CanonicalDotFinish.canonical.P AspisR1CanonicalQRawUnified.canonical.P
  rfl
private theorem fold_same :
    AspisR1CanonicalDotFinish.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call =
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call := by
  unfold AspisR1CanonicalDotFinish.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
    AspisR1CanonicalDotFinish.canonical.P AspisR1CanonicalQRawUnified.canonical.P
  rfl

/-- Pointwise identity of the exact source-owned raw function used by current
native Dot and by the retained S5 decoded-product consumer. -/
theorem actual_raw_eq_source (a b : Array U32 4#usize) :
    AspisR1S9ActualDotBackendMapV1.actualRaw a b =
      AspisR1CanonicalQRawUnified.canonical.Q.raw a b := by
  change AspisR1CanonicalDotFinish.canonical.Q.raw a b =
    AspisR1CanonicalQRawUnified.canonical.Q.raw a b
  unfold AspisR1CanonicalDotFinish.canonical.Q.raw AspisR1CanonicalQRawUnified.canonical.Q.raw
  rw [map_left_same,map_right_same,pp_same,fold_same]
  simp only [AspisR1CanonicalDotFinish.canonical.P,AspisR1CanonicalQRawUnified.canonical.P]

#print axioms actual_raw_eq_source
end AspisR1S9ActualRawHookIdentityV1
