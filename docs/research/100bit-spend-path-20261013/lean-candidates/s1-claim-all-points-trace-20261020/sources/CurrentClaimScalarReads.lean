import CurrentClaimScalarChain
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimScalar
open Concrete

def ReadValid {D H : Type} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) (t : Usize × E × aspis_core.field.QM31) : Prop :=
  read ops sem y1 point t.1=Result.ok t.2.2 ∧
  Array.index_usize g t.1=Result.ok t.2.1

theorem chain_has_ordered_reads {D H : Type} {ops : ClaimDotOps D} {sem : r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array E 29#usize} {point : Usize} {iter : Range} {dot : D} {out : E}
    (trace : Chain ops sem y1 g point iter dot out) (hend : iter.end.val=29) (hi : iter.start.val≤29) :
    ∃ xs : List (Usize × E × aspis_core.field.QM31), xs.length=29-iter.start.val ∧
      (∀ j (hj : j < xs.length), (xs[j]'hj).1.val=iter.start.val+j) ∧
      (∀ t ∈ xs, ReadValid ops sem y1 g point t) := by
  induction trace with
  | done r d x he hf =>
    refine ⟨[],?_,?_,?_⟩
    · simp only [List.length_nil,he,Nat.sub_self]
    · intro j hj; simp at hj
    · intro t ht; simp at ht
  | @step r r' d d' x l coeff scalar hn hr hw hp tail ih =>
    obtain ⟨hl,hactive,hstart,hend'⟩ := ClaimTrace.next_some_step r r' l hn
    have hend1 : r'.end.val=29 := by rw [hend']; exact hend
    have hi1 : r'.start.val≤29 := by omega
    obtain ⟨xs,hlen,horder,hvalid⟩ := ih hend1 hi1
    refine ⟨(l,coeff,scalar)::xs,?_,?_,?_⟩
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
      · subst t; exact ⟨hr,hw⟩
      · exact hvalid t hm

theorem successful_helper_has_exact_reads {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) (out : E)
    (h : verifier.prepared_claim_dot ops inst sem y1 g point=
      Result.ok (core.result.Result.Ok out)) :
    ∃ dot : D, ∃ xs : List (Usize × E × aspis_core.field.QM31), ops.newDot=Result.ok dot ∧
      Chain ops sem y1 g point {start:=0#usize,«end»:=29#usize} dot out ∧ xs.length=29 ∧
      (∀ j (hj : j < xs.length), (xs[j]'hj).1.val=j) ∧ (∀ t ∈ xs, ReadValid ops sem y1 g point t) := by
  unfold verifier.prepared_claim_dot at h
  change (do let dot ← ops.newDot
             verifier.prepared_claim_dot_loop ops inst
               {start:=0#usize,«end»:=29#usize} sem y1 g point dot)=Result.ok (core.result.Result.Ok out) at h
  cases hn : ops.newDot with
  | fail e => simp only [hn,bind_tc_fail] at h; cases h
  | div => simp only [hn,bind_tc_div] at h; cases h
  | ok dot =>
    simp only [hn,bind_tc_ok] at h
    have ht := successful_loop_has_chain ops inst sem y1 g point
      {start:=0#usize,«end»:=29#usize} dot out (by scalar_tac) (by scalar_tac) h
    obtain ⟨xs,hlen,horder,hvalid⟩ := chain_has_ordered_reads ht (by scalar_tac) (by scalar_tac)
    refine ⟨dot,xs,rfl,ht,?_,?_,hvalid⟩
    · simpa only [show (0#usize).val=0 from by rfl,Nat.sub_zero] using hlen
    · simpa only [show (0#usize).val=0 from by rfl,Nat.zero_add] using horder


theorem read_claims_success {D H : Type} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (point l : Usize) (scalar : aspis_core.field.QM31)
    (hsmall : point ≤ 2#usize) (h : read ops sem y1 point l=Result.ok scalar) :
    ∃ row, Array.index_usize sem.claims point=Result.ok row ∧ Array.index_usize row l=Result.ok scalar := by
  unfold read at h
  simp only [hsmall,if_true] at h
  cases hr : Array.index_usize sem.claims point with
  | fail e => simp only [hr,bind_tc_fail] at h; cases h
  | div => simp only [hr,bind_tc_div] at h; cases h
  | ok row =>
    simp only [hr,bind_tc_ok] at h
    exact ⟨row,rfl,h⟩

theorem read_extra_success {D H : Type} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (l : Usize) (scalar : aspis_core.field.QM31)
    (h : read ops sem y1 3#usize l=Result.ok scalar) :
    Array.index_usize sem.extra l=Result.ok scalar := by
  simpa only [read,show ¬(3#usize ≤ 2#usize) from by decide,if_false,
    show (3#usize).val=3 from by rfl] using h

theorem read_before_z1_success {D H : Type} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (l : Usize) (scalar : aspis_core.field.QM31)
    (h : read ops sem y1 4#usize l=Result.ok scalar) :
    Array.index_usize sem.before_z1 l=Result.ok scalar := by
  simpa only [read,show ¬(4#usize ≤ 2#usize) from by decide,if_false,
    show (4#usize).val=4 from by rfl] using h

#print axioms read_claims_success
#print axioms read_extra_success
#print axioms read_before_z1_success

#print axioms chain_has_ordered_reads
#print axioms successful_helper_has_exact_reads
end AspisR1CurrentPreparedClaim.ClaimScalar
