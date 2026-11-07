import LIBB_RecordRender
import LIBB_EnvValues
set_option autoImplicit false
noncomputable section
namespace LIBB_ObservationPieces
open Aeneas Aeneas.Std AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- A source C04 abort prefix, at an explicit pending request. No native
execution, Cut, Windows, or selected witness enters this predicate. -/
def Prefix (env : RSL.Env) (e : Event) (events : List RSL.Event) : Prop :=
 ∃ answered parts, NLL_Prefix.At (NLP_C04Chronology.atEvent (LIBB_PartitionEnv.H env) e)
  answered parts ∧ events=LIBB_C04LogGraph.render answered
/-- Exact expansion at one source event. Only a failing C04 event has its
named independent inner-prefix alternative in a resolved invocation. -/
def Piece (env : RSL.Env) (e : Event) (events : List RSL.Event) : Prop :=
 events=LIBB_Tx2EnvTrace.event env e ∨
 ∃ pr p folded error, e=Event.merkle pr p folded (.fail error) ∧ Prefix env e events

def Pieces (env : RSL.Env) (source : List Event) (events : List RSL.Event) : Prop :=
 ∃ pieces : List (List RSL.Event), List.Forall₂ (Piece env) source pieces ∧ events=pieces.flatten

theorem complete (env : RSL.Env) (source : List Event) :
 Pieces env source (source.flatMap (LIBB_Tx2EnvTrace.event env)) := by
 refine ⟨source.map (LIBB_Tx2EnvTrace.event env),?_,by rfl⟩
 induction source with
 | nil => exact .nil
 | cons e es ih => exact .cons (Or.inl rfl) ih

theorem detail_piece (env : RSL.Env) {e : Event}
 (detail : NLT_Subcuts.Detail (LIBB_PartitionEnv.H env) e) (trace : NNC_DigestTrace.Trace)
 (notResume : ∀ ck proof pub reply,e≠Event.resume ck proof pub reply)
 (law : LIBB_C04DetailGraph.RenderLaw (LIBB_PartitionEnv.H env) detail trace) :
 Piece env e (NNC_DigestTrace.render trace) := by
 cases detail with
 | ordinary e notMerkle =>
  have no : LIBB_Tx2EnvTrace.event env e=[] := by
   cases e <;> try rfl
   case resume ck proof pub reply =>
    exact False.elim (notResume _ _ _ _ rfl)
   case merkle pr p folded reply => exact False.elim (notMerkle _ _ _ _ rfl)
  exact Or.inl (law.trans no.symm)
 | returning pr p folded reply inside out child => exact Or.inl law
 | aborting pr p folded error inside pending child =>
  exact Or.inr ⟨pr,p,folded,error,rfl,inside++pending.answered,pending.parts,law.2,law.1⟩

theorem record (env : RSL.Env) (r : LIBB_RecordRender.Record env) (trace : NNC_DigestTrace.Trace)
 (native : NNC_RecordTrace.FromRecord r trace)
 (bound : LIBB_RecordReservation.Bound (LIBB_Tx2Reservation.reservation env) r.entered r.input)
 (law : NLT_C04Installed.Law (LIBB_PartitionEnv.H env) r.detail) :
 Piece env (NLT_NativeInvocation.actual r) (NNC_DigestTrace.render trace) := by
 have rendered:=LIBB_RecordRender.one env r trace native bound law
 rcases r with ⟨e,input,detail⟩
 cases e <;> first | exact Or.inl rendered | exact detail_piece env detail trace (by intros; intro h; cases h) rendered

theorem records (env : RSL.Env) (rs : List (LIBB_RecordRender.Record env))
 (trace : NNC_DigestTrace.Trace) (native : NNC_RecordTrace.Records rs trace)
 (bound : LIBB_EnvCommon.Bound env rs)
 (laws : ∀ r∈rs,NLT_C04Installed.Law (LIBB_PartitionEnv.H env) r.detail) :
 Pieces env (rs.map NLT_NativeInvocation.actual) (NNC_DigestTrace.render trace) := by
 induction native with
 | nil => exact ⟨[],.nil,rfl⟩
 | cons r rest head tail headSource next ih =>
  obtain ⟨pieces,relation,equal⟩:=ih
   (fun r h=>bound r (List.mem_cons_of_mem _ h))
   (fun r h=>laws r (List.mem_cons_of_mem _ h))
  refine ⟨NNC_DigestTrace.render head::pieces,.cons (record env r head headSource
   (bound r List.mem_cons_self) (laws r List.mem_cons_self)) relation,?_⟩
  rw [NNC_DigestTrace.render_append,equal]
  rfl
#print axioms complete
#print axioms detail_piece
#print axioms record
#print axioms detail_piece
#print axioms records
end LIBB_ObservationPieces
end
