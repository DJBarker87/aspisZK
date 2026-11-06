import NLH_DigestWrites
import NKR_TermDigestCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_DigestChain
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open NKI_InitialPrefix (Public Openings Selectors)
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
   rw [cell]
   simpa only [if_neg (show slot 1 ≠ slot 0 by decide)] using c1
 let final := write (write st 0 (replies 0)) 1 (replies 1)
 have samePair : ![replies 0,replies 1]=replies := by funext g;fin_cases g <;> rfl
 have equation : NKR_TermSemanticCut.digest_reference st.packed st.digests=
   ok (NJB_ArrayCarrier.array (NKR_TermSemanticCut.digestFrame st.packed ![replies 0,replies 1])) := by
   simp only [NKR_TermSemanticCut.digest_reference,c0,c1,bind_tc_ok]
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
