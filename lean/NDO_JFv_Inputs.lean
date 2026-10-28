import NDO_JFw_TypedPrefix
import NDO_JFw_ArbitraryInitial
import NDO_JFw_Y1
import NDO_JFw_Range
import NDO_JFw_Selection
import NDO_Rc7_Top
import RPz7_SAP_LiteralTop
set_option autoImplicit false
namespace AspisR1.JFv_Inputs
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation

theorem inhabited : ∃ (expanded y1 : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix),
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=16#usize,«end»:=7031#usize} = ok JFw_RealExpansion.stored ∧
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial = ok (.Ok (),expanded) ∧
    AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded = ok (.Ok pre) ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=7031#usize,«end»:=7495#usize} = ok JFw_Y1.stored ∧
    expandValues JFw_Y1.stored JFw_Y1.initial = ok (.Ok (),y1) ∧ y1.length=928 := by
  obtain ⟨expanded,pre,expand,parse,_⟩ := JFw_Prefix.inhabited
  obtain ⟨y1,values,length,_⟩ := JFw_Y1.inhabited
  refine ⟨expanded,y1,pre,?_,expand,parse,?_,values,length⟩
  · exact JFw_Selection.source
  · have range := JFw_Range.read 7031#usize 7495#usize (by decide) (by decide)
    simpa only [JFw_Y1.stored,show (7031#usize).val=7031 from rfl,
      show (7495#usize).val=7495 from rfl,Nat.reduceSub] using range

#print axioms inhabited
#print AspisR1.Rc7_Top.deployed
#print axioms AspisR1.Rc7_Top.deployed
#print axioms AspisR1.JFw_Prefix.inhabited
#print axioms AspisR1.JFw_TypedPrefix.inhabited
#print axioms AspisR1.JFw_ArbitraryInitial.accepted
#print axioms AspisR1.JFw_Y1.inhabited
end AspisR1.JFv_Inputs
