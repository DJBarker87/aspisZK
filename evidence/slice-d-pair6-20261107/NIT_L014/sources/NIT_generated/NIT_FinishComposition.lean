import NIT_Cuts
import NIG_FinishPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_FinishComposition
open Aeneas Aeneas.Std Result AspisR1Stage2 NIT_Cuts Classical

/-- Exact transport of the full native Result; all eight errors are injective. -/
theorem pair_port (owner alpha message : Nat) (p : verifier.Prepared)
 (l : PairPort) (out : Reply FE) (afterOwner : Nat)
 (cut : cutPairPort owner alpha message p l out afterOwner) : out=l.reply := by
 rcases cut with ⟨_,_,_,_,_,_,_,_,encoded,_⟩
 exact NIQ_ResultEncoding.returning_injective encoded

def rbind {A B : Type} (reply : Reply A) (next : A → Reply B) : Reply B :=
 match reply with | .Err e=>.Err e | .Ok value=>next value

/-- Native returning skeleton: only the observed replies, comparisons and
source-ordered short circuits. It interprets no opaque child value. -/
def returning (a : verifier.Accumulator) (l : FinishLog) : Reply Unit :=
 rbind (l.round_reply 0) fun _ =>
 rbind (l.round_reply 1) fun claim =>
 rbind (match l.new.error with | some e=>(.Err e : Reply Unit) | none=>.Ok ()) fun _ =>
 rbind l.pair.reply fun pair =>
 if pair≠claim then .Err .Relation else
 rbind l.dot_reply fun actual =>
 if a.next≠22#usize ∨ actual≠a.rhs then .Err .Query else .Ok ()

theorem expected (a : verifier.Accumulator) (l : FinishLog) :
 returning a l=(finishExpected a l).1 := by
 unfold returning finishExpected
 cases h0 : l.round_reply 0 with
 | Err e => rfl
 | Ok first =>
  cases h1 : l.round_reply 1 with
  | Err e => rfl
  | Ok claim =>
   cases hn : l.new.error with
   | some e => rfl
   | none =>
    cases hp : l.pair.reply with
    | Err e => rfl
    | Ok pair =>
     simp only [rbind]
     split
     · rfl
     · cases hd : l.dot_reply with
       | Err e => rfl
       | Ok actual => simp only [rbind];split <;> rfl

/-- The local-record post becomes the exact returning program, using the same
accumulator and the same complete opaque replies, without a success premise. -/
theorem finish_port (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (round0 round1 alpha semanticAlpha z message owner weights : Nat)
 (l : FinishLog) (out : Reply Unit)
 (cut : cutFinishLog v p a round0 round1 alpha semanticAlpha z message owner weights l out) :
 out=returning a l := by
 rcases cut with ⟨_,_,_,_,_,output,_⟩
 exact output.trans (expected a l).symm

/-- Preserve the outer Aeneas abort/nonreturn boundary at each call. -/
def fullBind {A B : Type} (reply : Result (Reply A))
 (next : A → Result (Reply B)) : Result (Reply B) := do
 let r ← reply
 match r with | .Err e=>ok (.Err e) | .Ok value=>next value

theorem rejected_prefix {A B : Type} (e : verifier.Error)
 (next : A → Result (Reply B)) : fullBind (ok (.Err e)) next=ok (.Err e) := rfl

theorem failed_prefix {A B : Type} (e : Error)
 (next : A → Result (Reply B)) : fullBind (fail e) next=fail e := rfl

theorem diverged_prefix {A B : Type} (next : A → Result (Reply B)) :
 fullBind div next=div := rfl

/-- The complete emitted/cohort equation, retaining the primitive caller Domain
at the actual call. It is not yet an assertion about a native pair execution. -/
theorem model (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 NIQ_ResultEncoding.full (Port3_NativeFinishBody.verifier.finish_relation
  (NIG_Slots.installed r) v p a none)=
 NIQ_ResultEncoding.full (NIQ_FinishComposition.packet r v p a) :=
 congrArg NIQ_ResultEncoding.full (NIG_FinishPacket.NHM_finish r proof v p a domain)

#print axioms pair_port
#print axioms expected
#print axioms finish_port
#print axioms rejected_prefix
#print axioms failed_prefix
#print axioms diverged_prefix
#print axioms model
end AspisR1.NIT_FinishComposition
