import FIw_PackSource
import ExtractedMaskQmPackBase4Semantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_PackWide
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open ExtractedMaskQmPackBase4Semantic (f PackB)

theorem value (values : Slice NQ) (out : NQ) (len : values.length=4)
    (hc : ∀ x∈values.val,Canon x) (run : field.qm31_pack_base4 values=ok out) :
    ∃ copied : Array NQ 4#usize,copied.val=values.val ∧ Canon out ∧
      f (decode out)=R0P.pack4 PackB (fun j=>f (decode (FIw_ArrayValue.cells copied j))) := by
  obtain ⟨copied,same,canon,v⟩ := FIw_PackSource.value values out len hc run
  refine ⟨copied,same,canon,?_⟩
  rw [v]
  exact ExtractedMaskQmPackBase4Semantic.map_mathPack
    (fun j=>FIv_NativeArithmetic.qm (FIw_ArrayValue.cells copied j))
#print axioms value
end AspisR1.FIw_PackWide
end
