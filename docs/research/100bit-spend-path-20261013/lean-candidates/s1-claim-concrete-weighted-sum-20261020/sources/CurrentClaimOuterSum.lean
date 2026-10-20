import CurrentClaimFinalParts
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimParts
open Concrete

theorem final_parts_canonical {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (final : Array E 7#usize) (inactive : E) (hc : Canonical inactive)
    (hzero : cell final 0#usize (by scalar_tac)=inactive)
    (hvalues : ∀ point : Usize, point.val<6 →
      ∃ (i : Usize) (value : E) (hi : i.val<7),
        (point+1#usize : Result Usize)=Result.ok i ∧
        verifier.prepared_claim_dot ops inst sem y1 g point=Result.ok (core.result.Result.Ok value) ∧
        cell final i hi=value)
    (hcanon : ∀ point value, point.val<6 →
      verifier.prepared_claim_dot ops inst sem y1 g point=Result.ok (core.result.Result.Ok value) → Canonical value) :
    ∀ j (hj : j.val<7), Canonical (cell final j hj) := by
  intro j hj
  by_cases hjzero : j.val=0
  · have he : j=0#usize := UScalar.eq_of_val_eq (by simpa using hjzero)
    subst j
    rw [hzero]
    exact hc
  · let p : Usize := Usize.ofNatCore (j.val-1) (by have hb := j.hBounds; omega)
    have hp : p.val=j.val-1 := by simp only [p,Usize.ofNatCore_val_eq]
    have hp6 : p.val<6 := by omega
    obtain ⟨i,value,hib,hinc,hd,hcell⟩ := hvalues p hp6
    have hi := add_one_success_val p i hp6 hinc
    have hij : i=j := UScalar.eq_of_val_eq (by omega)
    subst i
    rw [hcell]
    exact hcanon p value hp6 hd

theorem successful_claim_sum_relation {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive kappa out : E) (g : Array E 29#usize) (hkappa : Canonical kappa) (hinactive : Canonical inactive)
    (hcanon : ∀ point value, point.val<6 →
      verifier.prepared_claim_dot (ClaimPowers.withConcretePowers ops) inst sem y1 g point=
        Result.ok (core.result.Result.Ok value) → Canonical value)
    (h : verifier.prepared_claim (ClaimPowers.withConcretePowers ops) inst sem y1 inactive g kappa=
      Result.ok (core.result.Result.Ok out)) :
    ∃ k final : Array E 7#usize,
      (∀ j : Fin 7, Canonical (k.val[j.val]'(by rw [k.property]; exact j.isLt)) ∧
        decode (k.val[j.val]'(by rw [k.property]; exact j.isLt))=decode kappa^j.val) ∧
      cell final 0#usize (by scalar_tac)=inactive ∧
      (∀ point : Usize, point.val<6 →
        ∃ (i : Usize) (value : E) (hi : i.val<7),
          (point+1#usize : Result Usize)=Result.ok i ∧
          verifier.prepared_claim_dot (ClaimPowers.withConcretePowers ops) inst sem y1 g point=
            Result.ok (core.result.Result.Ok value) ∧ cell final i hi=value) ∧
      Canonical out ∧ decode out=partialSum k final 7 := by
  obtain ⟨k,parts,hpowers,hinit,hchain⟩ := ClaimTrace.successful_claim_has_powered_chain
    ops inst sem y1 inactive kappa out g hkappa h
  obtain ⟨final,hsum,hprefix,hfuture⟩ := chain_final_parts hchain (by scalar_tac) (by scalar_tac)
  have hzero : cell final 0#usize (by scalar_tac)=inactive := by
    rw [hprefix 0#usize (by scalar_tac) (by scalar_tac)]
    have hz := update_cells (Array.repeat 7#usize aspis_core.field.WideExact.ZERO)
      parts 0#usize inactive (by scalar_tac) hinit 0#usize (by scalar_tac)
    simpa only [ite_true] using hz
  have hvalues := fun point hp => hfuture point hp (by scalar_tac)
  have hfinal := final_parts_canonical (ClaimPowers.withConcretePowers ops) inst sem y1 g
    final inactive hinactive hzero hvalues hcanon
  have hk : ∀ j (hj : j.val<7), Canonical (cell k j hj) := by
    intro j hj
    exact (hpowers ⟨j.val,hj⟩).1
  obtain ⟨computed,hcomputed,hc,he⟩ := prepared_claim_sum_total_exact k final hk hfinal
  have hout : computed=out := Result.ok.inj (hcomputed.symm.trans hsum)
  subst computed
  exact ⟨k,final,hpowers,hzero,hvalues,hc,he⟩

#print axioms final_parts_canonical
#print axioms successful_claim_sum_relation
end AspisR1CurrentPreparedClaim.ClaimParts
