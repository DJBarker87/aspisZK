import NDO_JGg_InactiveBytes
import RPz7_PAln_InactiveDecode
import NDO_JGe_Payload27
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_InactiveZero
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open AspisR1ClaimPreparedBridge
open MultiproofConeCanonical OraclePortCompactDraft
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

def input : Slice U8 := ⟨List.replicate 32 0#u8,by scalar_tac⟩
def value : AspisR1CandidateParser.field.wide_exact.WideExact :=
  ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
theorem parsed : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled input=ok (some value) := by
  rw [show input=Array.to_slice (Array.repeat 32#usize 0#u8) from rfl,
    UnrolledWideParserRefinement.source_refines]
  rfl
#print axioms parsed

theorem source (semantic : Slice U8) (view : verifier.View)
    (accepted : sourceView JFx_NativeBytes.proof semantic JGe_Payload27.value=ok (.Ok view)) :
    AspisR1CurrentPreparedClaim.Concrete.decode (toClaimE (retainedView view).inactive)=0 := by
  obtain ⟨selected,call,same⟩ := PAln_ViewCuts.current _ _ _ _ accepted
  obtain ⟨actual,out,physical,parse,carrier,length⟩ := PAln_InactiveDecode.physical _ _ _ _ call
  have bytes : actual=input := by
    apply Subtype.ext
    apply MultiproofConeByteEquality.bytes_injective
    have zeros : (JFw_Frames.window 7495 32).val=List.replicate 32 0#u8 := JFz_Scan01.b00_selected
    have selectedBytes := congrArg bytesOf zeros
    exact physical.trans (by simpa only [JFw_Frames.window,bytesOf,slice,List.map_take,List.map_drop,input] using selectedBytes)
  rw [bytes,parsed] at parse
  have outEq : value=out := Option.some.inj (Result.ok.inj parse)
  rw [←same]
  change AspisR1CurrentPreparedClaim.Concrete.decode
    (toClaimE (AspisR1SelectedWideViewV1.prepCarrier selected.inactive))=0
  rw [←carrier,←outEq]
  rfl
#print axioms source
end AspisR1.JHm_InactiveZero
end
