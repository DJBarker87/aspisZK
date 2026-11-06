import NLH_ScalarChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarTail
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open NKR_TermScalarInvocation (Packet)
open pool_v1.pair_forest_semantic_terminal
/-- The SAME twelve local results feed258; its exact two-word result feeds
230at92. The full packed reply and all untouched local channels are retained. -/
theorem cuts {pub o s before} (p : Packet pub o s before) (st : State)
 (hb : st.packed=before) (hl : st.locals=NLH_ScalarDefs.values p) :
 ∃ final : State,NLH_FoldCore.Cuts (step pub o s) [.scalars,.preweighted] st (ok final) [.scalars,.preweighted] ∧
 final.packed=p.out ∧ final.locals=st.locals ∧ final.digests=st.digests ∧ final.scalars=p.scalars := by
 let middle : State := {st with scalars := p.scalars}
 let final : State := {middle with packed := p.out}
 have scalar : step pub o s .scalars st=ok middle := by
   change (do let values ← scalar_lanes pub.variant (core.option.Option.is_some pub.withdrawal_amount)
               (st.locals 3) (st.locals 5) (st.locals 7) (st.locals 11)
              ok {st with scalars := values})=_
   rw [hl]
   have call : scalar_lanes pub.variant (core.option.Option.is_some pub.withdrawal_amount)
       (NLH_ScalarDefs.values p 3) (NLH_ScalarDefs.values p 5) (NLH_ScalarDefs.values p 7) (NLH_ScalarDefs.values p 11)=ok p.scalars := p.scalar_call
   rw [call,bind_tc_ok]
 have packed : step pub o s .preweighted middle=ok final := by
   change (do let packed ← add_preweighted st.packed 92#usize p.scalars
              ok {middle with packed := packed})=_
   rw [hb,p.packed_call,bind_tc_ok]
 exact ⟨final,.next scalar (.next packed (.nil final)),rfl,rfl,rfl,rfl⟩
#print axioms cuts
end AspisR1.NLH_ScalarTail
end
