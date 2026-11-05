import NHG_Begin
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NHG_BeginFrame
#print r1_wire.Prefix.record
#print r1_wire.Prefix.validated_record

theorem result {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (initial : r1_wire.SemanticTranscript H) :
 (run (NHG_BeginPackets.begin S1SemanticCode.semanticValidated D pre initial)).2=
 r1_wire.begin D pre initial := by
 rw [NHG_Begin.source,run_value,S1SemanticCode.begin_erasure]

theorem effects {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (initial : r1_wire.SemanticTranscript H) :
 (run (NHG_BeginPackets.begin S1SemanticCode.semanticValidated D pre initial)).1=
 (run (S1SemanticCode.begin D pre initial)).1 := by
 rw [NHG_Begin.source]

theorem composed {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (initial : r1_wire.SemanticTranscript H) :
 run (NHG_BeginPackets.begin S1SemanticCode.semanticValidated D pre initial)=
 ((run (S1SemanticCode.begin D pre initial)).1,r1_wire.begin D pre initial) :=
 Prod.ext (effects D pre initial) (result D pre initial)

#print axioms result
#print axioms effects
#print axioms composed
end AspisR1.NHG_BeginFrame
