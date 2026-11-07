import NLT_C04StopParent
import NLT_EvalOrder
import NLP_C04Chronology
set_option autoImplicit false
noncomputable section
namespace NLT_C04StopChronology
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation NLT_SiteOrder
/-- A source call of any OTHER rank contributes no C04 internal digest event. -/
theorem not_merkle (H : Bytes → State) (e : Event) (different : rank e≠3) :
 NLP_C04Chronology.atEvent H e=[] := by
 cases e with
 | merkle pr p folded reply => exact False.elim (different rfl)
 | resume .. => rfl
 | powers .. => rfl
 | inactive .. => rfl
 | geometry .. => rfl
 | pending .. => rfl
 | query .. => rfl
 | flush .. => rfl
 | finish .. => rfl
theorem empty (H : Bytes → State) (events : List Event) (none : ∀ e∈events,rank e≠3) :
 NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H) events=[] := by
 induction events with
 | nil => rfl
 | cons e rest ih =>
   change NLP_C04Chronology.atEvent H e++NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H) rest=[]
   rw [not_merkle H e (none e List.mem_cons_self),ih (fun e member=>none e (List.mem_cons_of_mem _ member))]
/-- The whole parent's C04 expansion is this SAME child plan. Native execution
stops at its pending query; the ideal model suffix is not deleted or required
to fail. -/
theorem installed (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (root0 : NLP_InputDomain.Root0 ck proof) (records : List (Occurrence H d hash))
 (cut : NLT_C04Stop.Cut H)
 (stopped : NLT_C04Stop.At H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records cut) :
 let f:=NLT_FrameFromCuts.frame records
 NLL_Prefix.At
  (NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H)
   (run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
    d pub proof ck hash none).events)
  (cut.inside++cut.pending.answered) cut.pending.parts := by
 let f:=NLT_FrameFromCuts.frame records
 obtain ⟨reply,suffix,events⟩:=NLT_C04StopParent.source_prefix H d pub proof ck hash len records cut stopped
 have sourceOrder:=(NLT_EvalOrder.ordered _ 0 (NLT_SiteOrder.source f.resume f.pending
  (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish) d pub proof ck hash)).2
 rw [NKE_CommonEval.source] at sourceOrder
 rw [events] at sourceOrder
 have after:=(List.pairwise_append.mp sourceOrder).2.1
 have greater:=(List.pairwise_cons.mp after).1
 have suffixEmpty:=empty H suffix (fun e member=>by have h:=greater e member;change 3<rank e at h;omega)
 have less:=(NLT_C04StopOrder.ordered _ records cut stopped 0
  (NLT_SiteOrder.source (.Ok ()) (.Ok ()) (NLP_NativeMerkle.action H)
   (NLB_Parent.finish (.Ok ())) d pub proof ck hash)).2.2.2
 have beforeEmpty:=empty H (records.map actual) (by
  intro e member
  obtain ⟨r,member,rfl⟩:=List.mem_map.mp member
  have h:=less r member
  omega)
 have childPrefix:=(NLT_C04StopParent.installed H d pub proof ck hash len root0 records cut stopped).1
 dsimp only
 rw [events,NLP_EffectOrder.append,beforeEmpty]
 change NLL_Prefix.At
  ([]++(NLP_C04Chronology.atEvent H (Event.merkle cut.proof cut.prepared cut.folded reply)++
   NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H) suffix)) _ _
 rw [suffixEmpty,List.nil_append,List.append_nil]
 exact childPrefix
set_option pp.proofs false
#print installed
#print axioms not_merkle
#print axioms empty
#print axioms installed
end NLT_C04StopChronology
