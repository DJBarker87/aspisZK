import S1OwnedQueryContainsTotalV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result ControlFlow

def MemberFrom (a : Array U32 22#usize) (len start : Nat) (candidate : U32) : Prop :=
  ∃ k, start≤k ∧ k<len ∧ a.val[k]?=some candidate

/-- The exact extracted early-exit membership loop reads only the specified
prefix and returns true precisely for membership there. -/
theorem contains_loop_meaning (fuel : Nat) (a : Array U32 22#usize)
    (len : Usize) (candidate : U32) (j : Usize)
    (hlen : len.val≤22) (hj : j.val≤len.val) (hf : len.val-j.val=fuel)
    (out : Option Bool) (call : owned_contains_loop a len candidate j=ok out) :
    out=some true ↔ MemberFrom a len.val j.val candidate := by
  induction fuel generalizing j out with
  | zero =>
    have stop : ¬ j<len := by scalar_tac
    unfold owned_contains_loop at call
    rw [loop.eq_def] at call
    simp only [owned_contains_loop.body,if_neg stop] at call
    have hout : out=none := (Result.ok.inj call).symm
    rw [hout]
    constructor
    · intro h;cases h
    · rintro ⟨k,hj',hk,_⟩
      omega
  | succ fuel ih =>
    have active : j<len := by scalar_tac
    have jb : j.val<a.val.length := by have := a.property;scalar_tac
    have index := AspisS1QueryArrayOperations.index_total a j (by scalar_tac)
    let next : Usize := Usize.ofNatCore (j.val+1) (by scalar_tac)
    have nv : next.val=j.val+1 := by simp [next]
    have add : j+1#usize=ok next := by
      change UScalar.tryMk .Usize (j.val+1)=_
      have hb : UScalar.inBounds .Usize (j.val+1) := by scalar_tac
      simp only [UScalar.tryMk,UScalar.tryMkOpt,
        dif_pos ((UScalar.check_bounds_eq_inBounds .Usize (j.val+1)).mpr hb),Result.ofOption]
      rfl
    unfold owned_contains_loop at call
    rw [loop.eq_def] at call
    simp only [owned_contains_loop.body,if_pos active,index,bind_tc_ok] at call
    by_cases hit : a.val[j.val]'jb=candidate
    · simp only [if_pos hit,bind_tc_ok] at call
      have hout : out=some true := (Result.ok.inj call).symm
      constructor
      · intro _
        exact ⟨j.val,Nat.le_refl _,by scalar_tac,by simp [List.getElem?_eq_getElem jb,hit]⟩
      · intro _;exact hout
    · simp only [if_neg hit,add,bind_tc_ok] at call
      have nextMeaning := ih next (by omega) (by omega) out call
      rw [nextMeaning]
      constructor
      · rintro ⟨k,hk,hl,hvalue⟩
        exact ⟨k,by omega,hl,hvalue⟩
      · rintro ⟨k,hk,hl,hvalue⟩
        have ne : k≠j.val := by
          intro equal
          subst k
          have value : a.val[j.val]'jb=candidate := by
            simpa only [List.getElem?_eq_getElem jb,Option.some.injEq] using hvalue
          exact hit value
        exact ⟨k,by omega,hl,hvalue⟩

theorem contains_meaning (a : Array U32 22#usize) (len : Usize) (candidate : U32)
    (hlen : len.val≤22) (out : Bool) (call : owned_contains a len candidate=ok out) :
    out=true ↔ MemberFrom a len.val 0 candidate := by
  obtain ⟨pending,loopCall⟩ := Total.contains_loop_total len.val a len candidate 0#usize hlen
    (by scalar_tac) (by scalar_tac)
  have meaning := contains_loop_meaning len.val a len candidate 0#usize hlen
    (by scalar_tac) (by scalar_tac) pending loopCall
  unfold owned_contains at call
  rw [loopCall] at call
  cases pending with
  | none =>
    have value : out=false := (Result.ok.inj call).symm
    change (none=some true ↔ MemberFrom a len.val 0 candidate) at meaning
    simpa only [value,Bool.false_eq_true,reduceCtorEq] using meaning
  | some b =>
    have value : out=b := (Result.ok.inj call).symm
    change (some b=some true ↔ MemberFrom a len.val 0 candidate) at meaning
    simpa only [value,Option.some.injEq] using meaning

#print axioms contains_loop_meaning
#print axioms contains_meaning
end AspisS1OwnedQueryBlock.Meaning
