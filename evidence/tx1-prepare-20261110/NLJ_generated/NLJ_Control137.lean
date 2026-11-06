import NLJ_FinishPacket
import NHG_PublicTranscript
import NHG_BeginFrame
import NGX_PrefixCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Control137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run Log)
open NLJ_Observed
/-- Fixed emitted parser body, not an independently selected child reply. -/
def parse (bytes : Slice U8) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) :=
 NGX_PrefixCarrier.result (NGX_PrefixSource.computation
  AspisR1PrefixAggregateParser.r1_wire.parse_record_at bytes)
/-- Proposed reviewed parent-cut transcription. The CLOSED children are fixed
body computations; only136 is a packet parameter. This definition does NOT
establish its physical native realization. Prefix byte-frame windows remain
OPEN after K023/K028/K029, so this is not an admitted native row root. -/
def step (native136 : NLC_Finish.Input Unit → NLI_Interface.Observation Unit)
 (s : NLJ_Observed.State Unit) : Log × Result (NLJ_Observed.Post Unit) :=
 let i := s.input
 match s.locals with
 | .parse => run (show Code _ from do
   let r ← parse i.bytes
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok p => pure (.inr (advance s (.mark0 p))))
 | .publicTranscript p => run (show Code _ from do
   let r ← NHG_PublicTranscript.packetCode i.digest i.publicValue i.hash p.c1_root
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok t => pure (.inr (advance s (.begin p t))))
 | .begin p t => run (show Code _ from do
   let (r,after) ← NHG_BeginPackets.begin S1SemanticCode.semanticValidated i.digest p t
   match r with
   | .Err e => pure (.inl (.Err e))
   | .Ok c => pure (.inr (advance s (.mark1 p after c))))
 | .finish p t c =>
   let call := finishInput i p t c
   ((native136 call).log,returnedReply (native136 call).reply)
 | .mark0 _ => run (NLJ_Observed.step s)
 | .mark1 _ _ _ => run (NLJ_Observed.step s)
end AspisR1.NLJ_Control137
end
