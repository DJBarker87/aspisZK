import PIN2W11_DropCoe
import NKR_DigestRoot
import NJB_DecodeInjective
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11), NKR batch, PIN2P route (coordinator): `Public` is now the PIN2
`FIw_PublicModel.Public` (W3c `PIN2P.SemanticPublic`) instead of the pre-PIN2 native
`NKI_InitialPrefix.Public`, because this module (or a lemma it uses) applies `ofPublic` to it.
Every pre-PIN2 native read of `p` elaborates through the scoped coercion of `PIN2W11_DropCoe` to
exactly `PIN2P.SemanticPublic.dropDestination p`; where a native clause bundle is destructured,
`pin2_drop` (W3c helper) rewrites its `(dropDestination p).field` projections to `p.field` (rfl).  Statement text is otherwise unchanged; the
digest keys/rows/targets read none of pool, deploymentDomain, destination. -/
noncomputable section
namespace AspisR1.NKR_DigestWrapper
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode)
open NKI_InitialPrefix (Openings Selectors)
open FIw_PublicModel (Public)
open scoped AspisR1.PIN2W11_DropCoe
/-- The deployed250 cfg branch forwards251 unchanged. -/
def reference (p : Public) (o : Openings) (s : Selectors) := NKR_DigestComplete.reference p o s
/-- Literal full adopted old public-digest output, packed by the existing
base4 function in each group; no newly invented model substitutes for it. -/
def cohort (p : Public) (o : Openings) (s : Selectors) : Result NKR_DigestChildren.Pair := do
 let old←FIq_Native.pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s
 let a←NJB_PackLaw.reference (NJX_LeftRoot.lane old 0)
 let b←NJB_PackLaw.reference (NJX_LeftRoot.lane old 1)
 ok ![a,b]

/-- Full251/250 typed value equality to packing the SAME actual old body,
including constructor canonicality and both complete returned cells. The
250 native forwarding cut and251 native windows are separate certificates. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ c sums out old,NKR_DigestChildren.Clauses p o s c ∧ NKR_DigestChildren.Canonical c ∧
 NKR_DigestPrefix.run p o s=ok (c,sums) ∧ NKR_DigestPrefix.Frame c sums ∧
 NKR_DigestComplete.reference p o s=ok out ∧ reference p o s=ok out ∧ cohort p o s=ok out ∧
 (∀ j,Canon (out j)) ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok old ∧ FIw_ArrayValue.canonical old := by
 obtain ⟨c,sums,out,old,hc,hcan,pc,frame,oc,hout,oldc,hold,values⟩ := NKR_DigestRoot.source p o s hp ho hh hl
 choose packed packs hpacks vpacks using (fun g : Fin 2=>NJB_PackLaw.result (NJX_LeftRoot.lane old g)
  (fun j=>NJB_ArrayCarrier.canonical_cell old hold _))
 have same : packed=out := by
  funext g
  apply NJB_DecodeInjective.qm _ _ (hpacks g) (hout g)
  rw [vpacks,NJB_PackLinearity.model,values] <;> rfl
 have vector : (![packed 0,packed 1] : NKR_DigestChildren.Pair)=out := by
  rw [same]
  funext g
  fin_cases g <;> rfl
 refine ⟨c,sums,out,old,hc,hcan,pc,frame,oc,oc,?_,hout,oldc,hold⟩
 simp only [cohort,oldc,packs,bind_tc_ok,vector]
#print source
#print axioms source
end AspisR1.NKR_DigestWrapper
end
