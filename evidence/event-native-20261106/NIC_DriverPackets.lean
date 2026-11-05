import NIC_PurityFrame
import NIC_AbortPrefix
import NIC_FieldStubs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIC_DriverPackets
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation
open NFW_PreparedControl NHL_PreparedScalars

/-- Primitive scalar abort-prefix packets fit the SAME cut interface. The
continuation is arbitrary and never runs on either unsuccessful Result arm. -/
theorem scalar_stop_cut {A : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (B : PreparedModel.Boundaries) (mode : Bool)
 (before : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
 (stop : NIA_ScalarFailures.Stop) (events : SdkC_Source.Log)
 (packet : NIA_ScalarFailures.BlockStop hashv before row payload stop events)
 (k : (aspis_core.field.WideExact × transcript.Transcript Unit) → Code A) :
 NHZ_DRIVER.Cuts hashv
   (CheckpointBytes5Effect.bind (NIA_ScalarEffects.scalarCode B before row payload mode) k)
   stop.result events := by
 have t := NIA_ScalarFailures.scalar_trace B mode packet
 cases stop with
 | fail error => exact .fail (.leaf t) k
 | div => exact .div (.leaf t) k

/-- Re-instantiation of the adopted chronological driver theorem with the
complete NIA constructor packet, including the scalar/query stopped arms.
The suffix must be installed on THIS returned Out. `ordering` remains the
OPEN parent identification with TX1; this existential is a MODEL observation,
not a physical observer realization or a row promotion. -/
theorem tx1_from_packets {A : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (old : Scratch)
 (k : Out → Code A) (final : Result A) (suffix : SdkC_Source.Log)
 (tail : NHK_TraceBind.Continuation hashv
   (NGN_Emitted.prepared actual (NGQ_Effects.dictionary hashv) sem v () old) k final suffix)
 (tx1 : Code A)
 (ordering : CheckpointBytes5Effect.bind (NIA_ConstructorTrace.code sem v old) k=tx1) :
 ∃ prior, NGP_L181.NativeAssociation hashv tx1 ⟨final,prior++suffix⟩ := by
 obtain ⟨prior,cuts⟩ := NIA_DriverPackets.constructor_extension hashv sem v old k final suffix tail
 exact ⟨prior,NHZ_DRIVER.events_from_cuts hashv tx1 _ _ cuts ordering⟩

#print axioms scalar_stop_cut
#print axioms tx1_from_packets
end AspisR1.NIC_DriverPackets
