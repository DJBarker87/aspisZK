import NDO_JFv_Claims
set_option autoImplicit false
namespace AspisR1.JFv_ClaimsFixture
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation

theorem source (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    ∃ out,ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok out) := by
  rw [ClaimsUnrolledFinish.claims_value]
  exact JFv_Claims.success bytes pre parsed

theorem inhabited : ∃ (expanded y1 : Slice U8) (pre : r1_wire.Prefix)
    (view : AspisR1CurrentCaller.verifier.View) (out : ClaimsUnrolledFinish.MainClaims),
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
    PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
    expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),y1) ∧ y1.length=928 ∧
    AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof expanded y1=ok (.Ok view) ∧
    ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok out) := by
  obtain ⟨expanded,y1,pre,view,values,expand,parse,expandY,length,viewCall,_⟩ := JFv_Buffers.inhabited
  obtain ⟨out,call⟩ := source expanded pre parse
  exact ⟨expanded,y1,pre,view,out,expand,parse,expandY,length,viewCall,call⟩

#print axioms source
#print axioms inhabited
end AspisR1.JFv_ClaimsFixture
