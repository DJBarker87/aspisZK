import NDO_JGi_ClaimBody
set_option autoImplicit false
namespace AspisR1.JGi_ClaimTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentPreparedClaim Concrete
open JGi_DotOps (ops CanonQ)
open JGi_Parts

theorem loop {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (k parts : Array E 7#usize)
    (iter : ClaimScalar.Range) (hend : iter.end.val=6) (hi : iter.start.val≤6)
    (hk : CanonicalArray k) (hp : CanonicalArray parts)
    (dots : ∀ point : Usize,point.val<6 → ∃ out,
      verifier.prepared_claim_dot ops D sem y1 g point=ok (.Ok out) ∧ Canonical out) :
    ∃ out,verifier.prepared_claim_loop ops D iter sem y1 g k parts=ok (.Ok out) ∧ Canonical out := by
  have spec : WP.spec (verifier.prepared_claim_loop ops D iter sem y1 g k parts)
      (fun r=>∃ out,r=.Ok out ∧ Canonical out) := by
    unfold verifier.prepared_claim_loop
    refine loop.spec_decr_nat
      (fun s : ClaimScalar.Range × Array E 7#usize => 6-s.1.start.val)
      (fun s => s.1.end.val=6 ∧ s.1.start.val≤6 ∧ CanonicalArray s.2)
      (fun r=>∃ out,r=.Ok out ∧ Canonical out)
      (fun s=>verifier.prepared_claim_loop.body ops D sem y1 g k s.1 s.2)
      (iter,parts) ?_ ?_
    · rintro ⟨r,ps⟩ hs
      rcases hs with ⟨he,hi,hc⟩
      dsimp only at he hi hc ⊢
      by_cases hlt : r.start.val<6
      · obtain ⟨r',ps',call,hs,he',hc'⟩ := JGi_ClaimBody.step D sem y1 g k ps r he hlt hc dots
        rw [call,WP.spec_ok]
        dsimp only
        exact ⟨⟨he',by omega,hc'⟩,by omega⟩
      · obtain ⟨out,call,canonical⟩ := JGi_ClaimBody.done D sem y1 g k ps r he (by omega) hk hc
        rw [call,WP.spec_ok]
        exact ⟨out,rfl,canonical⟩
    · exact ⟨hend,hi,hp⟩
  obtain ⟨r,call,out,rfl,canonical⟩ := WP.spec_imp_exists spec
  exact ⟨out,call,canonical⟩
#print axioms loop

theorem source {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (inactive kappa : E)
    (hc : Canonical inactive) (hk : Canonical kappa)
    (read : ∀ point : Usize,point.val<6 → ∀ l : Usize,l.val<29 →
      ∃ q,ClaimScalar.read ops sem y1 point l=ok q ∧ CanonQ q)
    (weights : ∀ l : Usize,l.val<29 → ∃ x,Array.index_usize g l=ok x ∧ Canonical x) :
    ∃ out,verifier.prepared_claim ops D sem y1 inactive g kappa=ok (.Ok out) ∧ Canonical out := by
  obtain ⟨k,powers,canonical⟩ := ClaimPowers.powers_total_exact 7#usize kappa hk
  have powers' : ops.powers 7#usize kappa=ok k := powers
  have kc : CanonicalArray k := by
    intro j hj
    exact (canonical ⟨j.val,hj⟩).1
  obtain ⟨parts,write,pc⟩ := JGi_Parts.initial inactive hc
  have dots := fun point hp => JGi_DotTotal.source D sem y1 g point (read point hp) weights
  obtain ⟨out,call,canonical⟩ := loop D sem y1 g k parts
    {start:=0#usize,«end»:=6#usize} (by rfl) (by decide) kc pc dots
  refine ⟨out,?_,canonical⟩
  unfold verifier.prepared_claim
  simp only [powers',bind_tc_ok,write,call]
#print axioms source
end AspisR1.JGi_ClaimTotal
