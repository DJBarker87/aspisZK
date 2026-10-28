import NDO_JGi_DotBody
set_option autoImplicit false
namespace AspisR1.JGi_DotTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentPreparedClaim
open JGi_DotOps

theorem loop {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) (iter : ClaimScalar.Range)
    (dot : State) (hend : iter.end.val=29) (hi : iter.start.val≤29)
    (hc : dot.count.val=iter.start.val)
    (read : ∀ l : Usize,l.val<29 → ∃ q,ClaimScalar.read ops sem y1 point l=ok q ∧ CanonQ q)
    (weights : ∀ l : Usize,l.val<29 → ∃ x,Array.index_usize g l=ok x ∧ Concrete.Canonical x) :
    ∃ out,verifier.prepared_claim_dot_loop ops D iter sem y1 g point dot=ok (.Ok out) ∧
      Concrete.Canonical out := by
  have spec : WP.spec (verifier.prepared_claim_dot_loop ops D iter sem y1 g point dot)
      (fun r=>∃ out,r=.Ok out ∧ Concrete.Canonical out) := by
    unfold verifier.prepared_claim_dot_loop
    refine loop.spec_decr_nat
      (fun s : ClaimScalar.Range × r1_semantic.Verified H × Usize × State => 29-s.1.start.val)
      (fun s => s.1.end.val=29 ∧ s.1.start.val≤29 ∧ s.2.1=sem ∧ s.2.2.1=point ∧ s.2.2.2.count.val=s.1.start.val)
      (fun r=>∃ out,r=.Ok out ∧ Concrete.Canonical out)
      (fun s=>verifier.prepared_claim_dot_loop.body ops D y1 g s.1 s.2.1 s.2.2.1 s.2.2.2)
      (iter,sem,point,dot) ?_ ?_
    · rintro ⟨r,se,p,d⟩ hs
      rcases hs with ⟨he,hi,hse,hp,hc⟩
      dsimp only at he hi hse hp hc
      dsimp only
      have read' : ∀ l : Usize,l.val<29 → ∃ q,ClaimScalar.read ops se y1 p l=ok q ∧ CanonQ q := by
        simpa only [hse,hp] using read
      by_cases hlt : r.start.val<29
      · obtain ⟨r',d',call,hs,he',hc'⟩ := JGi_DotBody.step D se y1 g p r d he hlt hc read' weights
        rw [call,WP.spec_ok]
        dsimp only
        exact ⟨⟨he',by omega,hse,hp,hc'⟩,by omega⟩
      · obtain ⟨out,call,canonical⟩ := JGi_DotBody.done D se y1 g p r d he (by omega)
        rw [call,WP.spec_ok]
        dsimp only
        exact ⟨out,rfl,canonical⟩
    · exact ⟨hend,hi,rfl,rfl,hc⟩
  obtain ⟨r,call,out,rfl,canonical⟩ := WP.spec_imp_exists spec
  exact ⟨out,call,canonical⟩
#print axioms loop

theorem source {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize)
    (read : ∀ l : Usize,l.val<29 → ∃ q,ClaimScalar.read ops sem y1 point l=ok q ∧ CanonQ q)
    (weights : ∀ l : Usize,l.val<29 → ∃ x,Array.index_usize g l=ok x ∧ Concrete.Canonical x) :
    ∃ out,verifier.prepared_claim_dot ops D sem y1 g point=ok (.Ok out) ∧ Concrete.Canonical out := by
  obtain ⟨out,call,canonical⟩ := loop D sem y1 g point {start:=0#usize,«end»:=29#usize}
    EbyKNewToPushStateABI.pushZero (by rfl) (by decide) (by rfl) read weights
  refine ⟨out,?_,canonical⟩
  unfold verifier.prepared_claim_dot
  rw [JGi_DotOps.initial,bind_tc_ok,call]
#print axioms source
end AspisR1.JGi_DotTotal
