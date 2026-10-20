import CurrentClaimOuterTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimTrace
open Concrete

theorem chain_has_ordered_calls {D H : Type} {ops : ClaimDotOps D} {inst : aspis_core.Digest32 H}
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array E 29#usize} {k parts : Array E 7#usize}
    {iter : Range} {out : E} (trace : Chain ops inst sem y1 g k iter parts out)
    (hend : iter.end.val = 6) (hi : iter.start.val ≤ 6) :
    ∃ xs : List (Usize × E), xs.length = 6-iter.start.val ∧
      (∀ j (hj : j < xs.length), (xs[j]'hj).1.val = iter.start.val+j) ∧
      (∀ t ∈ xs, verifier.prepared_claim_dot ops inst sem y1 g t.1 = Result.ok (core.result.Result.Ok t.2)) := by
  induction trace with
  | done r a x he hsum =>
    refine ⟨[],?_,?_,?_⟩
    · simp only [List.length_nil,he,Nat.sub_self]
    · intro j hj; simp at hj
    · intro t ht; simp at ht
  | @step r r' a a' x point i value hn hd hinc hw tail ih =>
    obtain ⟨hpoint,hactive,hstart,hend'⟩ := next_some_step r r' point hn
    have hend1 : r'.end.val = 6 := by rw [hend']; exact hend
    have hi1 : r'.start.val ≤ 6 := by omega
    obtain ⟨xs,hlen,horder,hvalid⟩ := ih hend1 hi1
    refine ⟨(point,value)::xs,?_,?_,?_⟩
    · simp only [List.length_cons,hlen]
      omega
    · intro j hj
      cases j with
      | zero => simpa only [List.getElem_cons_zero,Nat.add_zero] using congrArg UScalar.val hpoint
      | succ j =>
        have hj' : j < xs.length := by simp only [List.length_cons] at hj; omega
        have hv : (xs[j]'hj').1.val = r.start.val+(j+1) := by
          rw [horder j hj',hstart]
          omega
        simpa only [List.getElem_cons_succ,Nat.succ_eq_add_one] using hv
    · intro t ht
      rcases List.mem_cons.mp ht with he | hm
      · subst t; exact hd
      · exact hvalid t hm

theorem successful_claim_has_powered_chain {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive kappa out : E) (g : Array E 29#usize) (hk : Canonical kappa)
    (h : verifier.prepared_claim (ClaimPowers.withConcretePowers ops) inst sem y1 inactive g kappa =
      Result.ok (core.result.Result.Ok out)) :
    ∃ k : Array E 7#usize, ∃ parts : Array E 7#usize,
      (∀ j : Fin 7, Canonical (k.val[j.val]'(by rw [k.property]; exact j.isLt)) ∧
        decode (k.val[j.val]'(by rw [k.property]; exact j.isLt)) = decode kappa^j.val) ∧
      Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) 0#usize inactive = Result.ok parts ∧
      Chain (ClaimPowers.withConcretePowers ops) inst sem y1 g k
        {start:=0#usize,«end»:=6#usize} parts out := by
  obtain ⟨k,parts,hpowers,hparts,hloop⟩ :=
    ClaimPowers.successful_claim_supplies_exact_powers ops inst sem y1 inactive kappa out g hk h
  refine ⟨k,parts,hpowers,hparts,?_⟩
  exact successful_loop_has_chain (ClaimPowers.withConcretePowers ops) inst sem y1 g k parts
    {start:=0#usize,«end»:=6#usize} out (by scalar_tac) (by scalar_tac) hloop

#print axioms chain_has_ordered_calls
#print axioms successful_claim_has_powered_chain
end AspisR1CurrentPreparedClaim.ClaimTrace
