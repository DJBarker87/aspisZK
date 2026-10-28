import NBR_SemanticReturn
import NBR_ValuesPort
import NBL_SlicePort
import NBR_RangeGeometry
set_option autoImplicit false
namespace AspisR1.NBR_ProducerBuffers
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation

abbrev semanticInput (proof : Slice U8) := NBL_SlicePort.segment proof 16#usize 7031#usize
abbrev compactInput (proof : Slice U8) := NBL_SlicePort.segment proof 7031#usize 7495#usize
abbrev semanticInitial (logical : Slice U8) := NBL_SlicePort.segment logical 0#usize 13831#usize
abbrev y1Initial (logical : Slice U8) := NBL_SlicePort.segment logical 13831#usize 14759#usize

/-- Both producers are constructed on slices of ONE proof and ONE initial
logical allocation. No selected logical output or expansion Result is an
input. Runtime allocation/borrow ownership remains the NBC boundary. -/
theorem source (proof logical : Slice U8)
    (full : proof.val.length=57607) (allocated : logical.val.length=14759) :
    ∃ semantic y1 : Slice U8,
      compact.expand_semantic nativeValues (semanticInput proof) (semanticInitial logical)=
        ok (.Ok (),semantic) ∧ semantic.val.length=13831 ∧
      LPt_LPn.Expand.NativeTrace (compactInput proof).val (y1Initial logical).val 29 y1.val ∧
      LPt_External.compact.expand_values (compactInput proof) (y1Initial logical)=ok (.Ok (),y1) ∧
      expandValues (compactInput proof) (y1Initial logical)=ok (.Ok (),y1) ∧
      y1.val.length=928 := by
  have semSize : (semanticInput proof).val.length=7015 :=
    NBR_RangeGeometry.length proof 16#usize 7031#usize 7015 (by scalar_tac) (by change 7031≤_;omega)
  have compactSize : (compactInput proof).val.length=464 :=
    NBR_RangeGeometry.length proof 7031#usize 7495#usize 464 (by scalar_tac) (by change 7495≤_;omega)
  have semInitialSize : (semanticInitial logical).val.length=13831 :=
    NBR_RangeGeometry.length logical 0#usize 13831#usize 13831 (by scalar_tac) (by change 13831≤_;omega)
  have yInitialSize : (y1Initial logical).val.length=928 :=
    NBR_RangeGeometry.length logical 13831#usize 14759#usize 928 (by scalar_tac) (by change 14759≤_;omega)
  obtain ⟨semantic,semCall,semLength,_⟩ :=
    NBR_SemanticReturn.source (semanticInput proof) (semanticInitial logical) semSize semInitialSize
  obtain ⟨y1,trace,native,owned⟩ := NBR_ValuesPort.construct (compactInput proof) (y1Initial logical)
    (by omega) (by omega) (by omega)
  have length := LPt_LPl.Expand.length _ _ _ _ (LPt_LPn.Expand.to_inherited _ _ _ _ trace)
  refine ⟨semantic,y1,semCall,semLength,?_,native,owned,length.trans yInitialSize⟩
  simpa only [compactSize] using trace

#print axioms source
end AspisR1.NBR_ProducerBuffers
