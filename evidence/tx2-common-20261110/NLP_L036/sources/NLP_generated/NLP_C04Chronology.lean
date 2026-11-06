import NLP_C04Effects
import NLP_C04All
import NLP_EffectOrder
set_option autoImplicit false
noncomputable section
namespace NLP_C04Chronology
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Forward internal-effect expansion at precisely the C04 occurrence. -/
def atEvent (H : Bytes → State) : Event → NLL.History
 | .merkle pr p folded _ => NLL_Parent.plan H pr
   (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
   (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV
 | _ => []
/-- Reviewed nested native cuts at the SAME decoded parent occurrences.
This is universally quantified in the conclusion of the source support law;
it is not a child Result/endpoint hypothesis of a row root. -/
inductive Native (H : Bytes → State) : List Event → NLL.History → Prop where
 | nil : Native H [] []
 | skip (e : Event) (notMerkle : ∀ pr p folded reply,e≠Event.merkle pr p folded reply)
   (rest : List Event) (history : NLL.History) (tail : Native H rest history) :
   Native H (e::rest) history
 | merkle (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize)
   (reply : R Unit) (inside : NLL.History) (out : NLL.Reply)
   (child : NLL_BatchSource.Invocation H pr p folded 1#usize inside out)
   (rest : List Event) (history : NLL.History) (tail : Native H rest history) :
   Native H (Event.merkle pr p folded reply::rest) (inside++history)
/-- Native-to-G direction: install the CLOSED packet on each cut at THAT
occurrence and concatenate in source order, retaining duplicates. -/
theorem fold (H : Bytes → State) (events : List Event)
 (packets : ∀ e∈events,NLP_C04All.Clause H e) (history : NLL.History)
 (native : Native H events history) :
 NLP_EffectOrder.expand (atEvent H) events=history := by
 induction native with
 | nil => rfl
 | skip e notMerkle rest history tail ih =>
   have no : atEvent H e=[] := by
    cases e <;> try rfl
    exact False.elim (notMerkle _ _ _ _ rfl)
   change atEvent H e++NLP_EffectOrder.expand (atEvent H) rest=history
   rw [no,List.nil_append]
   exact ih (fun e mem=>packets e (List.mem_cons_of_mem _ mem))
 | merkle pr p folded reply inside out child rest history tail ih =>
   have packet:=packets (Event.merkle pr p folded reply) (by simp)
   have historyLaw:=(packet.returning inside out child).2.1
   change atEvent H (Event.merkle pr p folded reply)++NLP_EffectOrder.expand (atEvent H) rest=inside++history
   rw [show atEvent H (Event.merkle pr p folded reply)=inside from historyLaw]
   rw [ih (fun e mem=>packets e (List.mem_cons_of_mem _ mem))]
/-- All native cuts in one source invocation, with every packet instantiated
internally. This still does not certify the physical parent invocation. -/
theorem at_actual (H : Bytes → State) (wr rr : NP6_StdModel.Reservation) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0Input : NLP_InputDomain.Root0 ck proof) :
 ∀ history,Native H (run wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash none).events history →
 NLP_EffectOrder.expand (atEvent H)
  (run wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash none).events=history := by
 intro history native
 exact fold H _ (NLP_C04All.source H wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash len root0Input) history native
set_option pp.proofs false
#print Native
#print fold
#print at_actual
#print axioms fold
#print axioms at_actual
end NLP_C04Chronology
