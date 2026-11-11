import PIN2W11_DropCoe
import NKR_DigestAssociation
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11), NKR batch, PIN2P route (coordinator): `Public` is now the PIN2
`FIw_PublicModel.Public` (W3c `PIN2P.SemanticPublic`) instead of the pre-PIN2 native
`NKI_InitialPrefix.Public`, because this module (or a lemma it uses) applies `ofPublic` to it.
Every pre-PIN2 native read of `p` elaborates through the scoped coercion of `PIN2W11_DropCoe` to
exactly `PIN2P.SemanticPublic.dropDestination p`; where a native clause bundle is destructured,
`pin2_drop` (W3c helper) rewrites its `(dropDestination p).field` projections to `p.field` (rfl).  Statement text is otherwise unchanged; the
digest keys/rows/targets read none of pool, deploymentDomain, destination. -/
noncomputable section
namespace AspisR1.NKR_DigestRoot
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode)
open NKI_InitialPrefix (Openings Selectors)
open FIw_PublicModel (Public)
open scoped AspisR1.PIN2W11_DropCoe
/-- Full251 SAME-input source-reference/adopted-cohort equality and returned
channels. Native parent-cut transcriptions are composed separately. Child
NKI/NJX packet credit remains conditional on the next ledger gate. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ c sums out old,NKR_DigestChildren.Clauses p o s c ∧ NKR_DigestChildren.Canonical c ∧
 NKR_DigestPrefix.run p o s=ok (c,sums) ∧ NKR_DigestPrefix.Frame c sums ∧
 NKR_DigestComplete.reference p o s=ok out ∧ (∀ j,Canon (out j)) ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok old ∧
 FIw_ArrayValue.canonical old ∧ ∀ g,
 decode (out g)=NJB_PackLinearity.pack (fun j=>FIw_ArrayValue.decoded old (NJX_DigestGroups.index g j)) := by
 obtain ⟨c,sums,out,hc,hcan,pc,frame,oc,hout,values⟩ := NKR_DigestComplete.source p o s hp ho hh hl
 obtain ⟨old,oldc,hold,oldv⟩ := NKR_DigestOldPack.source p o s hp ho hh hl
 refine ⟨c,sums,out,old,hc,hcan,pc,frame,oc,hout,oldc,hold,?_⟩
 intro g
 rw [values,NKR_DigestAssociation.model p o s c hp ho hh hc g,oldv] <;> rfl
#print source
#print axioms source
end AspisR1.NKR_DigestRoot
end
