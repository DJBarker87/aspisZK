import NDO_JFv_Inputs
import NDO_JFv_View
set_option autoImplicit false
namespace AspisR1.JFv_Buffers
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation

theorem inhabited : ∃ (expanded y1 : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (view : AspisR1CurrentCaller.verifier.View) (values : SemanticPrefixCodec.Full),
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
    AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
    expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),y1) ∧ y1.length=928 ∧
    AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof expanded y1=ok (.Ok view) ∧
    SemanticPrefixCodec.decodeFull (PSem_TypedPrefix.completedRecords pre)=some values := by
  obtain ⟨expanded,y1,pre,read,expand,parse,yread,yexpand,length⟩ := JFv_Inputs.inhabited
  obtain ⟨view,viewCall⟩ := JFv_View.current expanded y1
  obtain ⟨values,decode,_⟩ := PSem_TypedPrefix.typed_prefix expanded pre parse
  exact ⟨expanded,y1,pre,view,values,expand,parse,yexpand,length,viewCall,decode⟩

#print axioms inhabited
end AspisR1.JFv_Buffers
