import NLW_064CandidateFold
set_option autoImplicit false
noncomputable section
namespace NMK_Domain
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Only predicates of the parent's own input arguments. -/
structure Caller {X : Type} (a : Args X) : Prop where
 publicBound : a.publicBytes.val.length ≤ 1880
 root0 : NLP_InputDomain.Root0 a.checkpoint a.proof
/-- The proof extent is obtained only in the reached successful parse arm. -/
theorem reached {X : Type} (a : Args X) (domain : Caller a)
 (v : transport.Variant) (parsed : NLE_ParseInstall.parse a.proof = .ok (.Ok v)) :
 a.proof.val.length = 57607 ∧ a.publicBytes.val.length ≤ 1880 ∧
 NLP_InputDomain.Root0 a.checkpoint a.proof :=
 ⟨(NLE_ParseInstall.success a.proof v parsed).2, domain.publicBound, domain.root0⟩
/-- Uses the ledger24 CLOSED packet at precisely those arguments. -/
theorem child (H : Bytes → State) {X : Type} (a : Args X) (domain : Caller a)
 (v : transport.Variant) (parsed : NLE_ParseInstall.parse a.proof = .ok (.Ok v)) :
 NLT_CompleteRoot.RowSpec H a.digest a.publicBytes a.proof a.checkpoint a.hash := by
 have h := reached a domain v parsed
 exact NLT_CompleteRoot.root H a.digest a.publicBytes a.proof a.checkpoint a.hash h.1 h.2.1 h.2.2
#print Caller
#print reached
#print child
#print axioms reached
#print axioms child
end NMK_Domain
