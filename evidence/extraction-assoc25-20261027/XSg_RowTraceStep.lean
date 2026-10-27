import XSg_PushTrace
import XSg_RowLoopPhase
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
noncomputable section
namespace XSg_RowTraceStep
open S7Kani3CallerTrace
/-- Every actual successful row body extends the SAME source-push history;
canonicality and phase come from basis provenance and the cursor invariant. -/
theorem source (old : S8OwnedP6Finish.Weights) (v : alloc.vec.Vec aspis_core.field.QM31)
 (q : aspis_core.field.QM31) (i width : Usize) (basis : XSe_BasisUpdate.Basis)
 (t : Nat) (s : XSg_RowLoopPhase.S) (r : ControlFlow XSg_RowLoopPhase.S verifier.BatchedWeights)
 (canonical : XRp_PowersQAdd.CanonicalQ q) (bm : XSe_BasisUpdate.Canonical basis)
 (small : width.val≤256) (inv : XSg_RowLoopPhase.Inv t width.val s)
 (history : ∃ sum,PushTrace old (XRu_PushTransport.bw s.2) sum)
 (run : verifier.accumulate_batched_with_node_loop1.body v q i width basis s.1 s.2=ok r) :
 match r with
 | .done b => ∃ sum,PushTrace old (XRu_PushTransport.bw b) sum
 | .cont next => ∃ sum,PushTrace old (XRu_PushTransport.bw next.2) sum := by
 rcases s with ⟨iter,b⟩
 rcases inv with ⟨hend,hcursor,hlen,hterms,phase⟩
 dsimp only at hend hcursor hlen hterms phase ⊢
 rcases history with ⟨sum,history⟩
 unfold verifier.accumulate_batched_with_node_loop1.body at run
 obtain ⟨o,next,hn,run⟩ := pair_bind_success _ _ _ run
 cases o with
 | none => cases Result.ok.inj run;exact ⟨sum,history⟩
 | some j =>
  rcases XSg_RangeSource.some iter next j hn with ⟨rj,rs,re,rl⟩
  obtain ⟨m,hm,run⟩ := bind_success _ _ _ run
  have jb : j.val<256 := by omega
  obtain ⟨cell,hread,hval⟩ := WP.spec_imp_exists
   (Array.index_usize_spec basis j (by simp only [Array.length];scalar_tac))
  have same : cell=m := Result.ok.inj (hread.symm.trans hm)
  have mem : m∈basis.val := by rw [←same,hval];exact List.getElem_mem _
  obtain ⟨after,hpush,run⟩ := bind_success _ _ _ run
  obtain ⟨_,_,run⟩ := bind_success _ _ _ run
  obtain ⟨_,_,run⟩ := bind_success _ _ _ run
  obtain ⟨_,_,run⟩ := bind_success _ _ _ run
  obtain ⟨_,_,run⟩ := bind_success _ _ _ run
  obtain ⟨_,_,run⟩ := bind_success _ _ _ run
  obtain ⟨_,_,run⟩ := bind_success _ _ _ run
  obtain ⟨_,_,run⟩ := bind_success _ _ _ run
  obtain ⟨_,_,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  refine ⟨_,XSg_PushTrace.source old b after sum history j q m (by change j.val<b.raw.val.length;omega)
   canonical (bm m mem) ?_ hpush⟩
  simpa only [←hterms,rj] using phase
#print axioms source
end XSg_RowTraceStep
