import NMK_Domain
import NMK_CompleteFold
set_option autoImplicit false
noncomputable section
namespace NMN_Relation
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Call-boundary relation under (bl). These are CLOSED callee execution
clauses, not hypotheses about a selected successful result. -/
def Native {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (outcome : End H s.args) (events : List (Event Ambient X)) : Prop :=
 Invocation H s outcome events
/-- Full existing 064 law, including the independent stopped common arm. -/
def RowSpec {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X) : Prop :=
 (∀ outcome events, Native H s outcome events →
   Law H s.args outcome ∧ events=chronology H s outcome) ∧
 (∀ v, NLE_ParseInstall.parse s.args.proof=.ok (.Ok v) →
   ∀ records, ¬NLT_NativeInvocation.Invalid H s.args.digest s.args.hash
    (NLT_NativeSource.skeleton H s.args.digest s.args.publicBytes s.args.proof
      s.args.checkpoint s.args.hash) records)
/-- Semantic composition only. Native certification of this relation is
tracked separately; this file alone grants no candidate/ledger credit. -/
theorem composition {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : NMK_Domain.Caller s.args) : RowSpec H s := by
 constructor
 · intro outcome events native
   exact NLW_064CandidateFold.fold H s domain.publicBound
    ((NLW_RowSpec_065.root0_same _ _).mpr domain.root0) outcome events native
 · intro v parsed records
   exact (NMK_Domain.child H s.args domain v parsed).2 records
#print Native
#print RowSpec
#print composition
#print axioms composition
end NMN_Relation
