import CurrentClaimPoint5Chain
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimInner
open Concrete

def ReadValid (y1 : Slice U8) (g : Array E 29#usize) (t : Usize × E × E) : Prop :=
  ClaimParser.field y1 t.1=Result.ok t.2.2 ∧ Canonical t.2.2 ∧
  Array.index_usize g t.1=Result.ok t.2.1

theorem chain_has_ordered_reads {D : Type} {ops : ClaimDotOps D} {y1 : Slice U8}
    {g : Array E 29#usize} {iter : Range} {dot : D} {out : E}
    (trace : Point5Chain ops y1 g iter dot out) (hend : iter.end.val=29) (hi : iter.start.val≤29) :
    ∃ xs : List (Usize × E × E), xs.length=29-iter.start.val ∧
      (∀ j (hj : j < xs.length), (xs[j]'hj).1.val=iter.start.val+j) ∧
      (∀ t ∈ xs, ReadValid y1 g t) := by
  induction trace with
  | done r d x he hf =>
    refine ⟨[],?_,?_,?_⟩
    · simp only [List.length_nil,he,Nat.sub_self]
    · intro j hj; simp at hj
    · intro t ht; simp at ht
  | @step r r' d d' x l coeff parsed hn hr hc hw hp tail ih =>
    obtain ⟨hl,hactive,hstart,hend'⟩ := ClaimTrace.next_some_step r r' l hn
    have hend1 : r'.end.val=29 := by rw [hend']; exact hend
    have hi1 : r'.start.val≤29 := by omega
    obtain ⟨xs,hlen,horder,hvalid⟩ := ih hend1 hi1
    refine ⟨(l,coeff,parsed)::xs,?_,?_,?_⟩
    · simp only [List.length_cons,hlen]; omega
    · intro j hj
      cases j with
      | zero => simpa only [List.getElem_cons_zero,Nat.add_zero] using congrArg UScalar.val hl
      | succ j =>
        have hj' : j < xs.length := by simp only [List.length_cons] at hj; omega
        have hv : (xs[j]'hj').1.val=r.start.val+(j+1) := by rw [horder j hj',hstart]; omega
        simpa only [List.getElem_cons_succ,Nat.succ_eq_add_one] using hv
    · intro t ht
      rcases List.mem_cons.mp ht with he | hm
      · subst t; exact ⟨hr,hc,hw⟩
      · exact hvalid t hm

theorem successful_point5_has_exact_reads {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (out : E)
    (h : verifier.prepared_claim_dot (ClaimParser.withParser ops) inst sem y1 g 5#usize=
      Result.ok (core.result.Result.Ok out)) :
    ∃ dot : D, ∃ xs : List (Usize × E × E), ops.newDot=Result.ok dot ∧
      Point5Chain ops y1 g {start:=0#usize,«end»:=29#usize} dot out ∧ xs.length=29 ∧
      (∀ j (hj : j < xs.length), (xs[j]'hj).1.val=j) ∧ (∀ t ∈ xs, ReadValid y1 g t) := by
  unfold verifier.prepared_claim_dot at h
  change (do let dot ← ops.newDot
             verifier.prepared_claim_dot_loop (ClaimParser.withParser ops) inst
               {start:=0#usize,«end»:=29#usize} sem y1 g 5#usize dot)=Result.ok (core.result.Result.Ok out) at h
  cases hn : ops.newDot with
  | fail e => simp only [hn,bind_tc_fail] at h; cases h
  | div => simp only [hn,bind_tc_div] at h; cases h
  | ok dot =>
    simp only [hn,bind_tc_ok] at h
    have ht := point5_successful_loop_has_chain ops inst sem y1 g
      {start:=0#usize,«end»:=29#usize} dot out (by scalar_tac) (by scalar_tac) h
    obtain ⟨xs,hlen,horder,hvalid⟩ := chain_has_ordered_reads ht (by scalar_tac) (by scalar_tac)
    refine ⟨dot,xs,rfl,ht,?_,?_,hvalid⟩
    · simpa only [show (0#usize).val=0 from by rfl,Nat.sub_zero] using hlen
    · simpa only [show (0#usize).val=0 from by rfl,Nat.zero_add] using horder

#print axioms chain_has_ordered_reads
#print axioms successful_point5_has_exact_reads
end AspisR1CurrentPreparedClaim.ClaimInner
