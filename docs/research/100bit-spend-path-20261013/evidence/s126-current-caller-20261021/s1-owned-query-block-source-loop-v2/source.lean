import S1OwnedQueryListStepV1
import S1OwnedQueryBlockModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitScanBody Query31ExplicitListLoop

def sourceWordsFrom (block : Array U8 32#usize) (i : Nat) : List U32 :=
  (List.ofFn (fun j : Fin 8 => sampleWord block j.val)).drop i

theorem sourceWordsFrom_cons (block : Array U8 32#usize) (i : Nat) (hi : i<8) :
    sourceWordsFrom block i=sampleWord block i::sourceWordsFrom block (i+1) := by
  unfold sourceWordsFrom
  rw [List.drop_eq_getElem_cons (by simp;omega)]
  simp only [List.getElem_ofFn]

private theorem mk (n : Nat) (h : UScalar.inBounds .Usize n) :
    UScalar.tryMk .Usize n=ok (Usize.ofNatCore n h) := by
  simp only [UScalar.tryMk,UScalar.tryMkOpt,
    dif_pos ((UScalar.check_bounds_eq_inBounds .Usize n).mpr h),Result.ofOption]
  rfl

/-- Actual extracted block loop, all its successful/stopped paths and complete
returned buffers, refines the fixed mathematical scan. All word calls and
numeric invariants come from this same execution. -/
theorem block_loop_source (fuel : Nat) (s : Query31ExplicitScanBody.CurrentScan) (block : Array U8 32#usize)
    (i : Usize) (hlen : s.accepted_len.val≤22) (hd : s.draws.val≤64)
    (hi : i.val≤8) (hf : 8-i.val=fuel) :
    ∃ (sf : Query31ExplicitScanBody.CurrentScan) (stop : Bool),
      owned_block_loop s.accepted s.accepted_len s.draws block i=
        ok (sf.accepted,sf.accepted_len,sf.draws,if stop then some (pack sf true) else none) ∧
      scanListLoop (sourceWordsFrom block i.val) s=ok (sf,if stop then none else some false) ∧
      Query31ExplicitListLoop.validState sf := by
  induction fuel generalizing s i with
  | zero =>
    have stopped : ¬ i<8#usize := by scalar_tac
    have dropped : sourceWordsFrom block i.val=[] := by
      unfold sourceWordsFrom
      apply List.drop_eq_nil_of_le
      simp only [List.length_ofFn]
      omega
    refine ⟨s,false,?_,?_,Query31ExplicitListLoop.validState_of_bounds s hlen hd⟩
    · unfold owned_block_loop
      rw [loop.eq_def]
      simp only [owned_block_loop.body,if_neg stopped]
      rfl
    · rw [dropped]
      unfold scanListLoop step
      rw [loop.eq_def]
      rfl
  | succ fuel ih =>
    have active : i.val<8 := by omega
    obtain ⟨s1,stop,called,wordModel,valid1⟩ := owned_step_model s (sampleWord block i.val) hlen hd
    have first : owned_block_loop.body block s.accepted s.accepted_len s.draws i=
        afterWord i (pack s1 stop) := by
      rw [body_active block s.accepted s.accepted_len s.draws i active,called]
      rfl
    cases stop with
    | true =>
      refine ⟨s1,true,?_,?_,valid1⟩
      · rw [loop_unroll,first]
        simp only [afterWord,pack,if_true,bind_tc_ok]
      · rw [sourceWordsFrom_cons block i.val active,list_cons_owned s _ _ hlen,called]
        rfl
    | false =>
      let next : Usize := Usize.ofNatCore (i.val+1) (by scalar_tac)
      have nv : next.val=i.val+1 := by simp [next]
      have add : i+1#usize=ok next := by
        change UScalar.tryMk .Usize (i.val+1)=_
        exact mk _ _
      obtain ⟨sf,last,tailCall,tailModel,validFinal⟩ :=
        ih s1 next valid1.1 valid1.2.1 (by omega) (by omega)
      refine ⟨sf,last,?_,?_,validFinal⟩
      · rw [loop_unroll,first]
        simp only [afterWord,pack,Bool.false_eq_true,if_false,add,bind_tc_ok]
        exact tailCall
      · rw [sourceWordsFrom_cons block i.val active,list_cons_owned s _ _ hlen,called]
        simp only [bind_tc_ok,pack,Bool.false_eq_true,if_false]
        simpa only [nv] using tailModel


#print axioms block_loop_source
end AspisS1OwnedQueryBlock.Meaning
