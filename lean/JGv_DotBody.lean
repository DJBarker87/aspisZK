import JGv_DotOps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotBody
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CurrentWide.Proof AspisR1FinishRelationCurrent JGv_DotOps

theorem step (fm : Slice U8) (ws : Slice Q) (s : State) (j : Usize)
    (length : ws.val.length=64) (bound : j.val<64) (count : s.count.val=j.val)
    (read : ∀ i : Usize,i.val<64 → ∃ x,finishField fm i=ok x ∧ CanonicalFinish x)
    (canonical : ∀ q∈ws.val,CanonQ q) :
    ∃ out next,verifier.finish_query_dot_loop.body ops fm ws s j=ok (.cont (out,next)) ∧
      next.val=j.val+1 ∧ out.count.val=next.val := by
  obtain ⟨x,field,cx⟩ := read j bound
  obtain ⟨q,rq,hq⟩ := WP.spec_imp_exists (Slice.index_usize_spec ws j (by simpa [length] using bound))
  have member : q∈ws.val := by
    rw [hq]
    exact List.getElem_mem _
  obtain ⟨out,pushed,hcount⟩ := JGv_DotOps.push s x q cx (canonical q member) (by omega)
  obtain ⟨next,inc,hnext⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=j) (y:=1#usize) (by scalar_tac))
  have guard : j<Slice.len ws := by scalar_tac
  refine ⟨out,next,?_,by scalar_tac,by scalar_tac⟩
  have nativeField : ops.field fm j=ok x := field
  unfold verifier.finish_query_dot_loop.body
  rw [if_pos guard,nativeField,bind_tc_ok,rq,bind_tc_ok,pushed,bind_tc_ok]
  simp only [bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,inc]
#print axioms step

theorem done (fm : Slice U8) (ws : Slice Q) (s : State) (j : Usize)
    (length : ws.val.length=64) (bound : j.val=64) :
    verifier.finish_query_dot_loop.body ops fm ws s j=ok (.done (s,none)) := by
  have guard : ¬j<Slice.len ws := by scalar_tac
  unfold verifier.finish_query_dot_loop.body
  rw [if_neg guard]
#print axioms done
end AspisR1.JGv_DotBody
end
