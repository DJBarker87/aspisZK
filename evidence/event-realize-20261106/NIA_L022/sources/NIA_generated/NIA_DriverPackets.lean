import NIA_QueryPrefixes
import NIA_BlockCoverage
import NIA_EventInterpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIA_DriverPackets
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation
open NFW_PreparedControl NHL_PreparedScalars

/-- Packet-level export in exactly the unchanged NHZ cut interface.
This is a MODEL packet; physical native constructor installation is still open. -/
theorem constructor_cut (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch) :
 ∃ events, NHZ_DRIVER.Cuts hashv (NIA_ConstructorTrace.code sem v old)
   (NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v () old) events := by
 obtain ⟨events,t⟩ := NIA_ConstructorTrace.source hashv sem v old
 exact ⟨events,.leaf t⟩

/-- Compose on the returned SAME constructor carrier. All three outer Result
arms are retained by Continuation; no suffix is invoked after fail/div. -/
theorem constructor_extension {A : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch)
 (k : Out → Code A) (final : Result A) (suffix : SdkC_Source.Log)
 (tail : NHK_TraceBind.Continuation hashv
   (NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v () old) k final suffix) :
 ∃ events, NHZ_DRIVER.Cuts hashv
   (CheckpointBytes5Effect.bind (NIA_ConstructorTrace.code sem v old) k)
   final (events++suffix) := by
 obtain ⟨events,t⟩ := NIA_ConstructorTrace.source hashv sem v old
 exact ⟨events,.leaf (NHK_TraceBind.append t k final suffix tail)⟩

/-- Literal instantiation of NHZ's existing theorem for the constructed MODEL
packet. `ordering` remains a full code identity and is NOT proved for deployed
TX1. No genuine physical observation is identified by this existential. -/
theorem events_from_constructor {A : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch)
 (k : Out → Code A) (final : Result A) (suffix : SdkC_Source.Log)
 (tail : NHK_TraceBind.Continuation hashv
   (NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v () old) k final suffix)
 (tx1 : Code A)
 (ordering : CheckpointBytes5Effect.bind (NIA_ConstructorTrace.code sem v old) k=tx1) :
 ∃ earlier, NGP_L181.NativeAssociation hashv tx1 ⟨final,earlier++suffix⟩ := by
 obtain ⟨earlier,cuts⟩ := constructor_extension hashv sem v old k final suffix tail
 exact ⟨earlier,NHZ_DRIVER.events_from_cuts hashv tx1 _ _ cuts ordering⟩

#print axioms constructor_cut
#print axioms constructor_extension
#print axioms events_from_constructor
end AspisR1.NIA_DriverPackets
