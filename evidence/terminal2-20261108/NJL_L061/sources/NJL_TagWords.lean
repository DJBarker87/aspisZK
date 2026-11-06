import NJL_TagData
import NJB_ActiveReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagWords
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
theorem cast64 (x : U32) : (UScalar.cast .U64 x).val=x.val := by scalar_tac
theorem word_bound (value : NQ) (canonical : Canon value) (limb : Fin 4) :
 (NJB_Words.word value limb).val<2147483647 := by
 fin_cases limb
 · exact canonical.1.1
 · exact canonical.1.2
 · exact canonical.2.1
 · exact canonical.2.2
def highWord (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (term : Fin 272) (limb : Fin 4) : U64 :=
 UScalar.cast .U64 (NJB_Words.word (NJB_ActiveReference.high s (NJL_TagData.block term)) limb)
def tagWord (term : Fin 272) : U64 := UScalar.cast .U64 (NJL_TagData.tag term)
theorem domain (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (term : Fin 272) (limb : Fin 4)
 (hs : FIw_ArrayValue.canonical s.high) :
 (highWord s term limb).val<2147483647 ∧ (tagWord term).val<2147483647 := by
 rw [highWord,tagWord,cast64,cast64]
 exact ⟨word_bound _ (hs _ (List.getElem_mem _)) limb,NJL_TagData.tag_bound term⟩
/-- The natural-value product of each EXACT source-read high limb and tag;
this is the paired Lean law for NJB_product, never a Kani multiplier check. -/
theorem product (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (term : Fin 272) (limb : Fin 4)
 (hs : FIw_ArrayValue.canonical s.high) :
 ∃ out,UScalar.mul (highWord s term limb) (tagWord term)=ok out ∧
 out.val=(highWord s term limb).val*(tagWord term).val ∧ out.val≤NJB_TagRaw.B :=
 NJB_TagRaw.product _ _ (domain s term limb hs).1 (domain s term limb hs).2
#print axioms cast64
#print axioms word_bound
#print axioms domain
#print axioms product
end AspisR1.NJL_TagWords
end
