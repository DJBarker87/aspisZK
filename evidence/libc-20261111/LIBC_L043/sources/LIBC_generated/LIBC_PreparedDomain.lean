import LIBC_PreparedLaw
import NHS_PreparedPacket
set_option autoImplicit false
noncomputable section
namespace LIBC_PreparedDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1PublicPreparation
/-- CLOSED179 own-input semantic provenance, at this SAME Verified argument.
The witness is not an operation dictionary of the installed preparation law:
that law is fixed to NHL_PreparedScalars.actual. It records the ledger clause
"same successful semantic finish" exactly, for discharge by the earlier call. -/
def Semantic (sem : r1_semantic.Verified Unit) : Prop :=
 ∃ (B : FinishModel.Boundaries) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
   (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
   (before : r1_wire.SemanticTranscript Unit) (challenges : r1_wire.Challenges)
   (obs : Option (RPz7_PhaseIso.Phase → Result Unit)),
 FinishModel.finish AspisS1ExtractedRoundChildren.children
  {B with claims := ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
  (NGQ_Effects.dictionary hashv) pub pre before challenges obs = ok (.Ok sem)
/-- CLOSED179 LPt clause, including R4 compact_check and the SAME expanded
output carrier. Expansion success is not a new runtime premise: this is the
source's own argument provenance, discharged from the earlier CLOSED099. -/
def Expanded (v : verifier.View) : Prop :=
 ∃ compact before : Slice U8,
 compact.val.length=464 ∧ before.val.length=928 ∧
 NFU_Retarget.compact.check_values compact=ok (.Ok ()) ∧
 NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 v.y1.val
/-- Remaining literal dimension/canonicality clauses of the CLOSED179 domain.
Queries, gamma/kappa, powers and constructor success are NOT input premises. -/
def Domain (a : LIBC_PreparedLaw.Args) : Prop :=
 Semantic a.1 ∧ Expanded a.2.1 ∧
 a.2.1.round0.val.length=224 ∧ a.2.1.round1.val.length=224 ∧
 a.2.1.folded_root.isSome=true ∧ a.2.1.final_message.val.length=2048 ∧
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative a.2.1.inactive)
theorem semantic (a : LIBC_PreparedLaw.Args) (h : Domain a) : Semantic a.1 := h.1
theorem compact_check (a : LIBC_PreparedLaw.Args) (h : Domain a) :
 ∃ compact before : Slice U8,
 compact.val.length=464 ∧ before.val.length=928 ∧
 NFU_Retarget.compact.check_values compact=ok (.Ok ()) ∧
 NFU_Retarget.LPn.Expand.NativeTrace compact.val before.val 29 a.2.1.y1.val := h.2.1
theorem y1_width (a : LIBC_PreparedLaw.Args) (h : Domain a) : a.2.1.y1.val.length=928 := by
 obtain ⟨compact,before,_,size,_,trace⟩ := h.2.1
 have inherited := NFU_Retarget.LPn.Expand.to_inherited compact.val before.val a.2.1.y1.val 29 trace
 exact (NFU_Retarget.LPl.Expand.length compact.val before.val a.2.1.y1.val 29 inherited).trans size
#print axioms semantic
#print axioms compact_check
#print axioms y1_width
end LIBC_PreparedDomain
