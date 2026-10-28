import NDO_JGl_BoxedNumeric
import NDO_JGl_WordProof
import RPv_FJa_PoseidonSelectors
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_SopsNumeric
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FIv_NativeValue (decode)

theorem block : FIx_HighSumInner.model JGl_NumericData.selectors 57 0 0=
    decode JGl_NumericData.sops.block := by
  jgl_words
#print axioms block

theorem value (s : state_only_poseidon.StateOnlyPoseidonSelectors)
    (run : pool_v1.pair_forest_semantic_terminal.poseidon_selectors JGl_NumericData.selectors=ok s) :
    s=JGl_NumericData.sops := by
  have h := FJa_PoseidonSelectors.value JGl_NumericData.selectors s
    JGl_NumericCanonical.high JGl_NumericCanonical.low run
  have cb : FIv_NativeValue.Canon JGl_NumericData.sops.block :=
    JGl_NumericCanonical.block _ (by simp [JGl_NumericData.sops,JGl_NumericData.block])
  have eq := JGb_DecodeInjective.source s.block JGl_NumericData.sops.block h.2.2.1 cb
    (h.2.2.2.trans block)
  cases s
  cases eq
  have el := h.1
  dsimp only [JGl_NumericData.selectors] at el
  cases el
  rfl
#print axioms value
end AspisR1.JGl_SopsNumeric
end
