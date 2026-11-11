import PIN2W11_DropCoe
import NLH_DigestWrites
import NKR_TermDigestCut
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11), NKR batch, PIN2P route (coordinator): `Public` is now the PIN2
`FIw_PublicModel.Public` (W3c `PIN2P.SemanticPublic`) instead of the pre-PIN2 native
`NKI_InitialPrefix.Public`, because this module (or a lemma it uses) applies `ofPublic` to it.
Every pre-PIN2 native read of `p` elaborates through the scoped coercion of `PIN2W11_DropCoe` to
exactly `PIN2P.SemanticPublic.dropDestination p`; where a native clause bundle is destructured,
`pin2_drop` (W3c helper) rewrites its `(dropDestination p).field` projections to `p.field` (rfl).  Statement text is otherwise unchanged; the
digest keys/rows/targets read none of pool, deploymentDomain, destination. -/
noncomputable section
namespace AspisR1.NLH_DigestChain
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open NKI_InitialPrefix (Openings Selectors)
open FIw_PublicModel (Public)
open scoped AspisR1.PIN2W11_DropCoe
open NLH_DigestWrites
/-- Two scalar writes compose over the SAME complete packed24 state; scalar
locals, digest reply and scalar-array slot remain framed. -/
theorem source (pub : Public) (o : Openings) (s : Selectors) (st : State)
 (hb : FIw_ArrayValue.canonical st.packed) (hd : ∀ g,FIv_NativeValue.Canon (st.digests g)) :
 ∃ final : State,
 NLH_FoldCore.Cuts (NLH_SemanticState.step pub o s) [.digestAdd 0,.digestAdd 1] st (ok final) [.digestAdd 0,.digestAdd 1] ∧
 NKR_TermSemanticCut.digest_reference st.packed st.digests=ok final.packed ∧
 FIw_ArrayValue.canonical final.packed ∧ final.digests=st.digests ∧
 final.locals=st.locals ∧ final.scalars=st.scalars := by
 obtain ⟨replies,out,direct,co,calls,_,_⟩ := NKR_TermSemanticCut.digest_source pub o s st.packed st.digests hb hd
 have c0 : field.QM31.add (NJB_ArrayCarrier.cell st.packed (slot 0)) (st.digests 0)=ok (replies 0) := calls 0
 have c1 : field.QM31.add (NJB_ArrayCarrier.cell st.packed (slot 1)) (st.digests 1)=ok (replies 1) := calls 1
 have second : field.QM31.add (NJB_ArrayCarrier.cell (write st 0 (replies 0)).packed (slot 1))
   ((write st 0 (replies 0)).digests 1)=ok (replies 1) := by
   change field.QM31.add (NJB_ArrayCarrier.cell (write st 0 (replies 0)).packed (slot 1)) (st.digests 1)=_
   rw [cell,if_neg (show slot 1 ≠ slot 0 by decide)]
   exact c1
 let final := write (write st 0 (replies 0)) 1 (replies 1)
 have samePair : ![replies 0,replies 1]=replies := by funext g;fin_cases g <;> rfl
 have equation : NKR_TermSemanticCut.digest_reference st.packed st.digests=
   ok (NJB_ArrayCarrier.array (NKR_TermSemanticCut.digestFrame st.packed ![replies 0,replies 1])) := by
   unfold NKR_TermSemanticCut.digest_reference
   erw [c0,bind_tc_ok,c1,bind_tc_ok]
 have same : final.packed=out := by
   rw [samePair] at equation
   exact (two st (replies 0) (replies 1)).trans (by rw [samePair];exact Result.ok.inj (equation.symm.trans direct))
 refine ⟨final,.next (NLH_DigestWrites.step pub o s st 0 (replies 0) c0)
   (.next (NLH_DigestWrites.step pub o s (write st 0 (replies 0)) 1 (replies 1) second) (.nil final)),?_,?_,rfl,rfl,rfl⟩
 · rw [same];exact direct
 · rw [same];exact co
#print axioms source
end AspisR1.NLH_DigestChain
end
