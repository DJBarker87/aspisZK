import XSg_PushPhase
import XSg_RangeSource
import XSc_PushLoopFrame
import XSe_BasisUpdate
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSg_RowLoopPhase
abbrev S := core.ops.range.Range Usize × verifier.BatchedWeights
def Inv (t width : Nat) (s : S) : Prop :=
 s.1.end.val=width ∧ s.1.start.val≤width ∧ s.2.raw.val.length=width ∧
 s.2.terms.val=t ∧ XSg_Sweep.Inv t s.1.start.val s.2.raw
/-- Preservation for one actual row-loop body. The invariant distinguishes
already processed rows from the SAME untouched suffix. -/
theorem step (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
 (i width : Usize) (basis : XSe_BasisUpdate.Basis) (t : Nat)
 (canon : XRp_PowersQAdd.CanonicalQ q) (bm : XSe_BasisUpdate.Canonical basis)
 (small : width.val≤256) (s : S) (r : ControlFlow S verifier.BatchedWeights)
 (inv : Inv t width.val s)
 (run : verifier.accumulate_batched_with_node_loop1.body v q i width basis s.1 s.2=ok r) :
 match r with
 | .done b => ∀ row∈b.raw.val,XSg_RowPhase.Bound (t+1) row
 | .cont next => Inv t width.val next ∧ XSc_RangeMeasure.remaining next.1<XSc_RangeMeasure.remaining s.1 := by
 rcases s with ⟨iter,b⟩
 rcases inv with ⟨hend,hcursor,hlen,hterms,phase⟩
 dsimp only at hend hcursor hlen hterms phase ⊢
 unfold verifier.accumulate_batched_with_node_loop1.body at run
 obtain ⟨o,next,hn,run⟩ := pair_bind_success _ _ _ run
 cases o with
 | none =>
  cases Result.ok.inj run
  have terminal := XSc_RangeMeasure.terminal iter next hn
  have same : iter.start.val=width.val := by unfold XSc_RangeMeasure.remaining at terminal;omega
  exact XSg_Sweep.final t width.val b.raw (by omega) (by simpa only [same] using phase)
 | some j =>
  rcases XSg_RangeSource.some iter next j hn with ⟨rj,rs,re,rl⟩
  obtain ⟨m,hm,run⟩ := bind_success _ _ _ run
  have jb : j.val<256 := by omega
  obtain ⟨old,hread,hval⟩ := WP.spec_imp_exists
   (Array.index_usize_spec basis j (by simp only [Array.length];scalar_tac))
  have same : old=m := Result.ok.inj (hread.symm.trans hm)
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
  have advanced := XSg_PushPhase.source b after j q m t hterms (by change j.val<b.raw.val.length;omega)
   canon (bm m mem) (by simpa only [rj] using phase) hpush
  rcases XSc_PushFrame.source b after j q m hpush with ⟨flen,fterms⟩
  have decrease := XSc_RangeMeasure.advance iter next j hn
  change (next.end.val=width.val ∧ next.start.val≤width.val ∧ after.raw.val.length=width.val ∧
   after.terms.val=t ∧ XSg_Sweep.Inv t next.start.val after.raw) ∧
   XSc_RangeMeasure.remaining next<XSc_RangeMeasure.remaining iter
  refine ⟨⟨by rw [re];exact hend,by omega,by omega,?_,?_⟩,by omega⟩
  · rw [advanced.2];exact hterms
  · simpa only [rs] using advanced.1
#print axioms step
end XSg_RowLoopPhase
