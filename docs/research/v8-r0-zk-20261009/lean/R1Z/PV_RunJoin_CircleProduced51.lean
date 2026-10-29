import R1Z.PV_RunJoin_ResultWitness51
import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CircleProduced51
open Aeneas Aeneas.Std Result ProverRwFull

def Produced [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (built : host_semantic.BuiltSemantics H) : Prop :=
  ∃ (before middle : host_wire.SemanticTranscript H) (z0 z1 : aspis_core.circle.SecureCirclePoint)
    (framed25 framed26 : Slice U8),
    host_wire.SemanticTranscript.challenge_reference_circle_point D before 25#u8 framed25=ok (.Ok z0,middle) ∧
    host_wire.SemanticTranscript.challenge_reference_circle_point D middle 26#u8 framed26=ok (.Ok z1,built.transcript) ∧
    built.z=Array.make 2#usize [z0,z1]
#print axioms Produced
end R1Z.PV_RunJoin_CircleProduced51
