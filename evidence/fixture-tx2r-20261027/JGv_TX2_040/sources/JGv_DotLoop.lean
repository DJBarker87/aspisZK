import JGv_DotBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CurrentWide.Proof AspisR1FinishRelationCurrent JGv_DotOps

theorem source (fm : Slice U8) (ws : Slice Q) (s : State) (j : Usize)
    (length : ws.val.length=64) (bound : j.val≤64) (count : s.count.val=j.val)
    (read : ∀ i : Usize,i.val<64 → ∃ x,finishField fm i=ok x ∧ CanonicalFinish x)
    (canonical : ∀ q∈ws.val,CanonQ q) :
    ∃ out,verifier.finish_query_dot_loop ops fm ws s j=ok (out,none) := by
  have spec : WP.spec (verifier.finish_query_dot_loop ops fm ws s j)
      (fun r=>∃ out,r=(out,none)) := by
    unfold verifier.finish_query_dot_loop
    refine loop.spec_decr_nat
      (fun t : State × Usize=>64-t.2.val)
      (fun t=>t.2.val≤64 ∧ t.1.count.val=t.2.val)
      (fun r=>∃ out,r=(out,none))
      (fun t=>verifier.finish_query_dot_loop.body ops fm ws t.1 t.2)
      (s,j) ?_ ?_
    · rintro ⟨dot,index⟩ hs
      rcases hs with ⟨hi,hc⟩
      by_cases hlt : index.val<64
      · obtain ⟨out,next,call,hn,hcount⟩ := JGv_DotBody.step fm ws dot index length hlt hc read canonical
        rw [call,WP.spec_ok]
        exact ⟨⟨by omega,hcount⟩,by omega⟩
      · rw [JGv_DotBody.done fm ws dot index length (by omega),WP.spec_ok]
        exact ⟨dot,rfl⟩
    · exact ⟨bound,count⟩
  obtain ⟨result,call,out,rfl⟩ := WP.spec_imp_exists spec
  exact ⟨out,call⟩
#print axioms source
end AspisR1.JGv_DotLoop
end
