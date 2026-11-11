import AspisAcceptanceLink
import AspisRows40Literal

/-! The acceptance-to-extraction link on the Aspis 40-row protocol, with the
prefix hypothesis discharged by the rows-33-to-39 agent's
`AspisRows40.Literal.transcript_take33`.

Kind of result: MODEL THEOREM about the literal transcript of the Aspis
protocol (`AspisRows40.Protocol.protocol`). That an accepted Aspis verifier
run supplies `AspisChecks` on this transcript is the acceptance layer above
(the one-transaction game), not proved here. -/
set_option autoImplicit false
noncomputable section
namespace AspisAcceptance
open FS FS2
open AspisR1

/-- On an Aspis transcript of 40 rounds, the Aspis checks and no hit of the
Aspis classifier give a witness of R1's spend relation. -/
theorem aspis_relation (decodePair : Codec) (decoder : LiteralByteProtocol.Decoder)
    (H : LiteralByteProtocol.Address → LiteralByteProtocol.State)
    (pub : LiteralTranscript.Public) (pf : LiteralByteProtocol.Proof)
    (c : AspisChecks decodePair pub
      ((AspisRows40.Protocol.protocol decoder).transcript H pub pf 40).rounds)
    (hno : ¬ GenericNoHit.hitFrom (bad decodePair) pub []
      ((AspisRows40.Protocol.protocol decoder).transcript H pub pf 40).rounds) :
    ∃ w, LiteralProtocol.relation pub w :=
  aspis_relation_of_checks decodePair decoder H pub pf _
    (AspisRows40.Literal.transcript_take33 decoder _ H pub pf 40 (by omega)).2 c hno

#print axioms aspis_relation
end AspisAcceptance
end
