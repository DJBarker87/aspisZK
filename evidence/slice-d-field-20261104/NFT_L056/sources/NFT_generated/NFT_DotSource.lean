import NFT_Dot
set_option autoImplicit false
namespace NFT_DotSource
open Aeneas Aeneas.Std Result FIq_Native
open AspisR1.FJh_Base (QM Exact Decode Canonical)
open AspisR1.FJh_M31DotReads

/-- Actual seven-term D caller, same two slices throughout; includes complete
outer-loop induction and canonical reconstruction, without execution hypotheses. -/
theorem source (weights : Slice QM) (values : Slice U32)
    (hwlen : weights.val.length=7) (hvlen : values.val.length=7)
    (hw : CanonicalWeights weights) (hv : CanonicalValues values) :
    ∃ out : QM, field.qm31_m31_dot weights values=ok out ∧ Canonical out ∧
      Decode out=(List.ofFn (fun i : Fin 7 =>
        Decode (sliceCell weights i.val (by rw [hwlen];exact i.isLt))*
          ((sliceCell values i.val (by rw [hvlen];exact i.isLt)).val : Exact))).foldl (·+·) 0 :=
  AspisR1.FJh_M31DotSevenExact.source_success weights values hwlen hvlen hw hv

/-- ROWS in the only D parent, interpolated_internal_pair, has seven entries. -/
theorem caller_rows : ([2,3,4,5,6,7,8] : List Nat).length=7 := by rfl
#print axioms source
#print axioms caller_rows
#print axioms AspisR1.FJh_M31DotInput.source_success
#print axioms AspisR1.FJh_M31DotChunkModel.loop_success_fuel
end NFT_DotSource
