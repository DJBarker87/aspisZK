import S1OwnedQueryBlockBodyV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitScanBody
open AspisV8R19.Q22WordScan

def wordValuesFrom (block : Array U8 32#usize) (i : Nat) : List Nat :=
  (List.ofFn (fun j : Fin 8 => (sampleWord block j.val).val)).drop i

theorem wordValuesFrom_cons (block : Array U8 32#usize) (i : Nat) (hi : i<8) :
    wordValuesFrom block i=(sampleWord block i).val::wordValuesFrom block (i+1) := by
  unfold wordValuesFrom
  rw [List.drop_eq_getElem_cons (by simp;omega)]
  simp only [List.getElem_ofFn]

theorem scan_cons_compose (s : ScanState) (x : Nat) (xs : List Nat) :
    scan s (x::xs)=(let r:=scan s [x];if r.2 then r else scan r.1 xs) := by
  by_cases stop : s.accepted.length=22 ∨ s.draws=64
  · simp only [scan,if_pos stop];rfl
  · simp only [scan,if_neg stop];rfl

private theorem mk (n : Nat) (h : UScalar.inBounds .Usize n) :
    UScalar.tryMk .Usize n=ok (Usize.ofNatCore n h) := by
  simp only [UScalar.tryMk,UScalar.tryMkOpt,
    dif_pos ((UScalar.check_bounds_eq_inBounds .Usize n).mpr h),Result.ofOption]
  rfl

/-- Actual extracted block loop, all its successful/stopped paths and complete
returned buffers, refines the fixed mathematical scan. All word calls and
numeric invariants come from this same execution. -/
theorem block_loop_model (fuel : Nat) (s : CurrentScan) (block : Array U8 32#usize)
    (i : Usize) (hlen : s.accepted_len.val≤22) (hd : s.draws.val≤64)
    (hi : i.val≤8) (hf : 8-i.val=fuel) :
    ∃ (sf : CurrentScan) (stop : Bool),
      owned_block_loop s.accepted s.accepted_len s.draws block i=
        ok (sf.accepted,sf.accepted_len,sf.draws,if stop then some (pack sf true) else none) ∧
      scan (q22StateOf s) (wordValuesFrom block i.val)=(q22StateOf sf,stop) ∧
      Query31ExplicitListLoop.validState sf := by
  induction fuel generalizing s i with
  | zero =>
    have stopped : ¬ i<8#usize := by scalar_tac
    have dropped : wordValuesFrom block i.val=[] := by
      unfold wordValuesFrom
      apply List.drop_eq_nil_of_le
      simp only [List.length_ofFn]
      omega
    refine ⟨s,false,?_,?_,Query31ExplicitListLoop.validState_of_bounds s hlen hd⟩
    · unfold owned_block_loop
      rw [loop.eq_def]
      simp only [owned_block_loop.body,if_neg stopped]
      rfl
    · rw [dropped];rfl
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
      · unfold owned_block_loop
        rw [loop.eq_def,first]
        simp only [afterWord,pack,if_true,bind_tc_ok]
        rfl
      · rw [wordValuesFrom_cons block i.val active,scan_cons_compose,wordModel]
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
      · unfold owned_block_loop
        rw [loop.eq_def,first]
        simp only [afterWord,pack,Bool.false_eq_true,if_false,add,bind_tc_ok]
        exact tailCall
      · rw [wordValuesFrom_cons block i.val active,scan_cons_compose,wordModel]
        simp only [Bool.false_eq_true,if_false]
        simpa only [nv] using tailModel

/-- TOTAL model join for the complete extracted owned block, with no successful
block/word or model-law premise. The actual native loop binding is separate. -/
theorem block_model (s : CurrentScan) (block : Array U8 32#usize)
    (hlen : s.accepted_len.val≤22) (hd : s.draws.val≤64) :
    ∃ (sf : CurrentScan) (stop : Bool),
      owned_block s.accepted s.accepted_len s.draws block=ok (pack sf stop) ∧
      scan (q22StateOf s) (wordValuesFrom block 0)=(q22StateOf sf,stop) ∧
      Query31ExplicitListLoop.validState sf := by
  obtain ⟨sf,stop,call,model,valid⟩ := block_loop_model 8 s block 0#usize hlen hd
    (by scalar_tac) (by scalar_tac)
  refine ⟨sf,stop,?_,?_,valid⟩
  · unfold owned_block
    rw [call]
    cases stop <;> rfl
  · exact model

#print axioms block_loop_model
#print axioms block_model
end AspisS1OwnedQueryBlock.Meaning
