import PIN2W11_DropCoe
import NLH_SemanticState
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11), NKR batch, PIN2P route (coordinator): `Public` is now the PIN2
`FIw_PublicModel.Public` (W3c `PIN2P.SemanticPublic`) instead of the pre-PIN2 native
`NKI_InitialPrefix.Public`, because this module (or a lemma it uses) applies `ofPublic` to it.
Every pre-PIN2 native read of `p` elaborates through the scoped coercion of `PIN2W11_DropCoe` to
exactly `PIN2P.SemanticPublic.dropDestination p`; where a native clause bundle is destructured,
`pin2_drop` (W3c helper) rewrites its `(dropDestination p).field` projections to `p.field` (rfl).  Statement text is otherwise unchanged; the
digest keys/rows/targets read none of pool, deploymentDomain, destination. -/
noncomputable section
namespace AspisR1.NLH_DigestWrites
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Openings Selectors)
open FIw_PublicModel (Public)
open scoped AspisR1.PIN2W11_DropCoe
def slot (g : Fin 2) : Fin (24#usize).val := ⟨21+g.val,by change 21+g.val < 24;omega⟩
def write (st : State) (g : Fin 2) (reply : NQ) : State :=
 {st with packed := (NJB_ArrayCarrier.array (fun j => if j=slot g then reply else NJB_ArrayCarrier.cell st.packed j))}
theorem step (pub : Public) (o : Openings) (s : Selectors) (st : State) (g : Fin 2) (reply : NQ)
 (call : field.QM31.add (NJB_ArrayCarrier.cell st.packed (slot g)) (st.digests g)=ok reply) :
 NLH_SemanticState.step pub o s (.digestAdd g) st=ok (write st g reply) := by
 change (do let reply ← field.QM31.add (NJB_ArrayCarrier.cell st.packed (slot g)) (st.digests g)
            ok (write st g reply))=_
 rw [call,bind_tc_ok]
theorem cell (st : State) (g : Fin 2) (reply : NQ) (j : Fin (24#usize).val) :
 NJB_ArrayCarrier.cell (write st g reply).packed j = if j=slot g then reply else NJB_ArrayCarrier.cell st.packed j := by
 exact congrFun (NJB_ArrayCarrier.cell_array _) j
/-- Symbolic sparse frame, never kernel reduction of the whole24-cell array. -/
theorem two (st : State) (a b : NQ) :
 (write (write st 0 a) 1 b).packed=
 NJB_ArrayCarrier.array (NKR_TermSemanticCut.digestFrame st.packed ![a,b]) := by
 change NJB_ArrayCarrier.array (fun j => if j=slot 1 then b else NJB_ArrayCarrier.cell (write st 0 a).packed j)=_
 apply congrArg NJB_ArrayCarrier.array
 funext j
 rw [cell]
 by_cases h21 : j.val=21
 · have same : j=slot 0 := Fin.ext h21
   subst j
   rfl
 · by_cases h22 : j.val=22
   · have same : j=slot 1 := Fin.ext h22
     subst j
     rfl
   · have ne0 : j ≠ slot 0 := by intro h;exact h21 (congrArg Fin.val h)
     have ne1 : j ≠ slot 1 := by intro h;exact h22 (congrArg Fin.val h)
     simp only [if_neg ne0,if_neg ne1,NKR_TermSemanticCut.digestFrame,if_neg h21,if_neg h22]
#print axioms step
#print axioms cell
#print axioms two
end AspisR1.NLH_DigestWrites
end
