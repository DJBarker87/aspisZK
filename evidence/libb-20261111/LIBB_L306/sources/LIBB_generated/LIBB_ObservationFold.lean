import LIBB_ObservationModel
import LIBB_Tx2Domain
import NNC_ObservedWeak
set_option autoImplicit false
noncomputable section
namespace LIBB_ObservationFold
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NLT_NativeInvocation
abbrev Outcome (env : RSL.Env) := NLT_CompleteRoot.End (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()
/-- Only the already required runtime reservation representation, at reached
calls. This is not a new own-input clause of064. -/
def Bound (env : RSL.Env) : Outcome env → Prop
 | .resolved _ records => LIBB_EnvCommon.Bound env records
 | .c04Stopped records _ => LIBB_EnvCommon.Bound env records

theorem resolved_details (env : RSL.Env) (pub proof ck : Slice U8)
 (len : proof.val.length=57607) (publicLen : pub.val.length≤1880)
 (root0 : NLP_InputDomain.Root0 ck proof) (result : R Unit)
 (records : List (LIBB_RecordRender.Record env))
 (native : NLT_CompleteRoot.Native (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
  pub proof ck () (.resolved result records)) :
 ∀ record∈records,NLT_C04Installed.Law (LIBB_PartitionEnv.H env) record.detail := by
 have closed:=(NLT_CompleteRoot.root (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
  pub proof ck () len publicLen root0).1 (.resolved result records) native
 intro record member
 exact (closed.2.2.2.1 record member).2.2.2.2.2.1

theorem stopped_details (env : RSL.Env) (pub proof ck : Slice U8)
 (len : proof.val.length=57607) (root0 : NLP_InputDomain.Root0 ck proof)
 (records : List (LIBB_RecordRender.Record env)) (cut : NLT_C04Stop.Cut (LIBB_PartitionEnv.H env))
 (native : NLT_CompleteRoot.Native (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
  pub proof ck () (.c04Stopped records cut))
 (bound : LIBB_EnvCommon.Bound env records) :
 ∀ record∈records,NLT_C04Installed.Law (LIBB_PartitionEnv.H env) record.detail := by
 obtain ⟨reply,suffix,events⟩:=LIBB_EnvCommon.stopped env pub proof ck len records cut native bound
 intro record member
 apply NLT_C04Installed.at_event (LIBB_PartitionEnv.H env)
  (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
  (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env)) (LIBB_PartitionEnv.digest env)
  pub proof ck () len root0 (actual record)
 change actual record∈(LIBB_Tx2EnvCode.observed env pub proof ck).events
 rw [events]
 exact List.mem_append_left _ (List.mem_map.mpr ⟨record,member,rfl⟩)

/-- Complete source/native observation fold for065, including independently
stopped calls with their exact answered prefix and no fabricated reply. -/
theorem common (env : RSL.Env) (pub proof ck : Slice U8)
 (len : proof.val.length=57607) (publicLen : pub.val.length≤1880)
 (root0 : NLP_InputDomain.Root0 ck proof) (outcome : Outcome env)
 (native : NLT_CompleteRoot.Native (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
  pub proof ck () outcome) (bound : Bound env outcome)
 (trace : NNC_DigestTrace.Trace) (source : NNC_RecordTrace.FromEnd outcome trace) :
 LIBB_ObservationModel.Common env pub proof ck
 ⟨match outcome with
   | .resolved result _ => NNC_WeakSpec.resultExit result
   | .c04Stopped _ _ => .abort,
  NNC_DigestTrace.render trace⟩ := by
 cases outcome with
 | resolved result records =>
  have association:=LIBB_EnvCommon.resolved env pub proof ck len result records native bound
  apply Or.inl
  constructor
  · exact congrArg NNC_WeakSpec.resultExit association.1
  · rw [←association.2]
    exact LIBB_ObservationPieces.records env records trace source bound
     (resolved_details env pub proof ck len publicLen root0 result records native)
 | c04Stopped records cut =>
  obtain ⟨before,stopped,beforeSource,stopSource,rfl⟩:=source
  obtain ⟨reply,suffix,events⟩:=LIBB_EnvCommon.stopped env pub proof ck len records cut native bound
  obtain ⟨log,child,rfl⟩:=stopSource
  have prefix:=LIBB_EnvCommon.stopped_query env pub proof ck len root0 records cut native bound
  apply Or.inr
  refine ⟨records.map actual,cut.proof,cut.prepared,cut.folded,reply,suffix,
   NNC_DigestTrace.render before,LIBB_C04LogGraph.render (cut.inside++cut.pending.answered),events,
   LIBB_ObservationPieces.records env records before beforeSource bound
    (stopped_details env pub proof ck len root0 records cut native bound),?_,?_⟩
  · exact ⟨cut.inside++cut.pending.answered,cut.pending.parts,prefix,rfl⟩
  · rw [NNC_DigestTrace.render_append,LIBB_C04StoppedTrace.stopped child]
/-- Runtime binding for the very outcome observed by064. -/
def Bound064 (env : RSL.Env) {a : NLW_Full064.Args Unit} :
 NLW_Full064.End (LIBB_PartitionEnv.H env) a → Prop
 | .common outcome => Bound env outcome
 | _ => True

/-- The full064 fold consumes the original four own-input clauses. Neither
parser success nor child success is added. Native reservation binding remains
an integration representation clause, outside the byte-input domain. -/
theorem tx2 {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient)
 (domain : NMN_064.Domain (⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩ : NLW_Full064.Args Unit))
 (outcome : NLW_Full064.End (LIBB_PartitionEnv.H env)
  (⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩ : NLW_Full064.Args Unit))
 (events : List (NLW_Full064.Event Ambient Unit))
 (native : NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ outcome events)
 (bound : Bound064 env outcome) (trace : NNC_DigestTrace.Trace)
 (source : NNC_ObservedWeak.TraceOf outcome trace) :
 LIBB_ObservationModel.law pub proof ck env
 ⟨NNC_WeakSpec.exit (LIBB_PartitionEnv.H env) _ outcome,NNC_DigestTrace.render trace⟩ := by
 cases native with
 | observed parsed children parser child =>
  have same:=NMN_064.parser parser
  cases parsed with
  | fail error =>
   change trace=[] at source
   subst trace
   unfold LIBB_ObservationModel.law
   rw [←same]
   unfold LIBB_Tx2EnvTrace.observation LIBB_Tx2EnvTrace.events
   rw [←same,LIBB_ParserGraph.source,←same]
   rfl
  | div =>
   change trace=[] at source
   subst trace
   unfold LIBB_ObservationModel.law
   rw [←same]
   unfold LIBB_Tx2EnvTrace.observation LIBB_Tx2EnvTrace.events
   rw [←same,LIBB_ParserGraph.source,←same]
   rfl
  | ok reply => cases reply with
    | Err error =>
     change trace=[] at source
     subst trace
     unfold LIBB_ObservationModel.law
     rw [←same]
     unfold LIBB_Tx2EnvTrace.observation LIBB_Tx2EnvTrace.events
     rw [←same,LIBB_ParserGraph.source,←same]
     rfl
    | Ok variant =>
     unfold LIBB_ObservationModel.law
     rw [←same]
     exact common env pub proof ck domain.proofExtent domain.publicBound domain.root0
      (children variant) (child variant rfl) bound trace source
#print axioms tx2
#print axioms resolved_details
#print axioms stopped_details
#print axioms common
end LIBB_ObservationFold
end
