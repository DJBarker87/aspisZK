import NNG_ConcreteCalls136
import NNG_TreeEmission
import NMP_Finish136Transport
import NMP_EmittedContext
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishAdapter137
open Aeneas Aeneas.Std Result
open NMP_ResultTransport (outer inner)

def phase : NNG_verify_finish.verifier.Phase → NMP_prepare.verifier.Phase
 | .Parsed => .Parsed | .Semantic => .Semantic | .SemanticPart i => .SemanticPart i
 | .Prepare => .Prepare | .CheckpointRead => .CheckpointRead | .Merkle i => .Merkle i
 | .Query i => .Query i | .QueryPart i j => .QueryPart i j
 | .CheckpointWrite => .CheckpointWrite | .Relation => .Relation | .Final => .Final

def observer (obs : NMP_Emitted.Observer) : NNG_Emitted.Observer := obs.map (fun f=>fun p=>f (phase p))
def digest {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H) : NNG_verify_finish.aspis_core.digest.Digest32 H :=
 ⟨d.coremarkerCopyInst,d.digest⟩

def childInput {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : AspisR1PublicPreparation.r1_wire.Prefix) (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
 (ch : AspisR1PublicPreparation.r1_wire.Challenges) (obs : NMP_Emitted.Observer) : NNG_Emitted.Parent H Unit :=
 ⟨digest d,NNG_Transport.fromT9 pub,NNG_Transport.fromT12 pre,NNG_Transport.fromT10 t,
 NNG_Transport.fromT3 ch,observer obs,()⟩

/-- Exact complete child136 emitted Result, through the two fresh namespaces. -/
def oldFinish {H : Type} (env : RSL.Env) (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (pub : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : AspisR1PublicPreparation.r1_wire.Prefix) (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
 (ch : AspisR1PublicPreparation.r1_wire.Challenges) (obs : NMP_Emitted.Observer) :=
 outer (inner NNG_Transport.toT11 NNG_Transport.toT13)
 (NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env) (childInput d pub pre t ch obs))

def call {H : Type} (env : RSL.Env) (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (pub : NMP_Emitted.Public) (pre : NMP_prepare.r1_wire.Prefix) (t : NMP_prepare.r1_wire.SemanticTranscript H)
 (ch : NMP_prepare.aspis_core.state_only_prefix.r0.Challenges) (obs : NMP_Emitted.Observer) :=
 NMP_Finish136Transport.adapt (oldFinish env d) pub pre t ch obs

theorem source {H : Type} (env : RSL.Env) (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (pub : NMP_Emitted.Public) (pre : NMP_prepare.r1_wire.Prefix) (t : NMP_prepare.r1_wire.SemanticTranscript H)
 (ch : NMP_prepare.aspis_core.state_only_prefix.r0.Challenges) (obs : NMP_Emitted.Observer) :
 outer (inner NMP_Transport.toT11 NMP_Transport.toT12) (call env d pub pre t ch obs) =
 oldFinish env d (NMP_Transport.toT9 pub) (NMP_Transport.toT13 pre) (NMP_Transport.toT10 t) (NMP_Transport.toT3 ch) obs :=
 NMP_Finish136Transport.same (oldFinish env d) pub pre t ch obs
#print axioms source
end AspisR1.NNG_FinishAdapter137
