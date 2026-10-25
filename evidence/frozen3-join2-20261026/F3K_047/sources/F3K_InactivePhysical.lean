import F3K_InactiveCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_InactivePhysical
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft

theorem bytes (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view))
    (output : Array U8 32#usize)
    (serialized : sourceBytes (retainedView view).inactive=ok output) :
    bytesOf output.val=slice (bytesOf proof.val) 7495 32 := by
  obtain ⟨selected,call,same⟩ := PAln_ViewCuts.current proof semantic y1 view accepted
  obtain ⟨input,value,physical,parsed,carrier,len⟩ := PAln_InactiveDecode.physical
    proof semantic y1 selected call
  have prep : (retainedView view).inactive=F3K_WideEncoding.prepFromParsed value := by
    rw [← same]
    change AspisR1SelectedWideViewV1.prepCarrier selected.inactive=_
    rw [← carrier]
    rfl
  rw [prep] at serialized
  obtain ⟨encoded,source,roundtrip⟩ := F3K_InactiveCodec.source_roundtrip input value parsed
  have eq : output=encoded := Result.ok.inj (serialized.symm.trans source)
  rw [eq,roundtrip]
  exact physical

theorem row (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view))
    (output : Array U8 32#usize)
    (serialized : sourceBytes (retainedView view).inactive=ok output)
    (p : Parsed) (wire : p.wire=bytesOf proof.val) :
    rowBytes p 28=framed (bytesOf (Array.to_slice output).val) := by
  change framed (slice p.wire 7495 32)=_
  rw [wire,← bytes proof semantic y1 view accepted output serialized]
  rfl

#print axioms bytes
#print axioms row
end AspisR1.F3K_InactivePhysical
end
