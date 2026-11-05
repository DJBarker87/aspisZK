import NHS_CallerWidths
import NHS_FoldDomain
import RPz7_F3M_InactiveCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_ConstructorDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- The deployed preparation prefix proves the native scalar/query domains
on its actual View, before either child produces its result. -/
theorem reached (base : AspisR1CurrentCaller.Ops) (reserved : Bool) {H : Type}
 (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (proof : Slice U8)
 (v : AspisR1CurrentCaller.verifier.View) (proofSize : proof.val.length=57607)
 (run : NHL_PrepareModel.Reaches base reserved D proof v)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (hash : Unit)
 (packet : NHL_OpeningPacket.Packet (NGQ_Effects.dictionary hashv) sem
   (AspisR1CurrentCaller.InstalledPreparation.retainedView v) hash) :
 let retained := AspisR1CurrentCaller.InstalledPreparation.retainedView v
 retained.variant=.S2 ∧
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative retained.inactive) ∧
 retained.y1.val.length≤2048 ∧ retained.round0.val.length≤2048 ∧
 (∀ payload, NHL_PreparedOpening.foldPayload retained=ok payload → payload.val.length≤2048) ∧
 NHK_Invocation.Domain packet.opening.row retained.final_message ∧
 (NHL_OpeningPacket.nextRow packet.opening).val≤95 := by
 obtain ⟨variant,y1,round0,round1,final⟩ := NHS_CallerWidths.reached base reserved D proof v proofSize run
 obtain ⟨_,_,semantic,y1Bytes,_,ySize,view,_⟩ := NHL_PrepareDomain.reached base reserved D proof v proofSize run
 have inactive := F3M_InactiveCanonical.source proof semantic y1Bytes v view
 refine ⟨variant,NFW_SampledDomains.gamma_canonical _ inactive,by omega,by omega,?_,
   NHS_QueryPacket.domain hashv sem _ hash packet final,?_⟩
 · intro payload produced
   exact NHS_FoldDomain.bound _ round1 payload produced
 · rcases (NHL_OpeningPacket.fold_fields packet.fold).2.2 with first|second
   · rw [NHL_OpeningPacket.nextRow,first]
     decide
   · rw [NHL_OpeningPacket.nextRow,second]
     decide
#print axioms reached
end AspisR1.NHS_ConstructorDomain
