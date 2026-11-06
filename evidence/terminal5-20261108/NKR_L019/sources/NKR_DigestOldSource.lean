import NKR_DigestChildren
import RPv_FIy_PublicDigest
import NDO_JGa_PublicDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestOldSource
open Aeneas Aeneas.Std Result WP FIq_Native
open NKI_InitialPrefix (Public Openings Selectors)
open FIw_ArrayValue (canonical)
/-- Generic actual old-cohort prefix: canonical public digests come from the
actual fields; recipient None and Some are both retained. -/
@[step] theorem prefix (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (hz : canonical o.z)
 (hh : canonical s.high) (hl : canonical s.low) :
 FIy_PublicDigestPrefix.run p o s ⦃ out => canonical out ⦄ := by
 have ha:=hp.anchor
 have hn:=hp.nullifier
 have hc:=hp.change
 have zero:=JFy_ZeroArrays.source 8#usize
 unfold FIy_PublicDigestPrefix.run
 cases h : p.recipient with
 | none=>
   simp only [h]
   step* <;> first | assumption | scalar_tac
 | some d=>
   have hr:=hp.recipient d h
   simp only [h]
   step* <;> first | assumption | scalar_tac

/-- Generic exact suffix on arbitrary canonical previous digest; carry20
inactive arm and source index are retained. -/
@[step] theorem suffix (p : Public) (o : Openings) (s : Selectors)
 (before : Array field.QM31 8#usize)
 (hp : NKR_DigestChildren.Domain p) (hz : canonical o.z)
 (hh : canonical s.high) (hl : canonical s.low) (hb : canonical before) :
 FIy_PublicDigestSuffix.run p o s before p.transition.live_snapshot ⦃ out => canonical out ⦄ := by
 have hn:=hp.nextRoot
 have hf:=hp.nextFrontier
 obtain ⟨carry,call,_,bound⟩ := NKR_DigestCarry.source p.transition.live_snapshot.next_pair_index
 unfold FIy_PublicDigestSuffix.run
 rw [call]
 step*
 all_goals first | assumption | scalar_tac | (subst_vars;exact hf _ (List.getElem_mem (by rw [p.transition.candidate_afterstate.next_frontier.property];omega)))

/-- Whole actual old eight-lane cohort totality and exact model value, on the
same generic public/openings/selectors inputs as optimized251. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (hz : canonical o.z)
 (hh : canonical s.high) (hl : canonical s.low) :
 ∃ out,pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok out ∧
 canonical out ∧ FIw_ArrayValue.decoded out=FIy_PublicDigest.model p o s := by
 obtain ⟨initial,pc,hp'⟩ := WP.spec_imp_exists (prefix p o s hp hz hh hl)
 obtain ⟨middle,mc,hm⟩ := JGa_FrontierLoop.source 20 ⟨0#usize,20#usize⟩ o.z s initial
  p.transition.live_snapshot rfl rfl hz hp' hh hl hp.frontier
 obtain ⟨out,oc,hout⟩ := WP.spec_imp_exists (suffix p o s middle hp hz hh hl hm)
 have call : pool_v1.pair_forest_semantic_terminal.public_digest_lanes p o s=ok out := by
  rw [FIy_PublicDigestSource.factor,pc,bind_tc_ok]
  unfold FIy_FrontierLoopStep.loop at mc
  rw [mc,bind_tc_ok,oc]
 exact ⟨out,call,hout,(FIy_PublicDigest.value p o s out hz hh hl hp.anchor hp.nullifier hp.recipient hp.change hp.frontier hp.nextRoot hp.nextFrontier call).2⟩
#print axioms prefix
#print axioms suffix
#print axioms source
end AspisR1.NKR_DigestOldSource
end
