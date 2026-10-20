import CuSavingsS2SourceRowDigit
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceRow
open Aeneas Aeneas.Std Result ControlFlow AspisR1S2Groups
open OccupancyRangeTraversal

def digitNat (j d out : Nat) : Nat :=
  out ||| (((j >>> (2*d)) &&& 3) <<< (2*CuSavingsS2Tables.tau.getD d 0))

def run (j start : Nat) : Nat → Nat → Nat
  | 0, out => out
  | n+1, out => run j (start+1) n (digitNat j start out)

theorem body_step (j out value : Usize) (iter next : Range)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some iter.start,next))
    (hd : CuSavingsS2SourceRowDigit.digit j iter.start out = .ok value) :
    transport.Variant.row_loop.body j iter out = .ok (.cont (next,value)) := by
  simp only [transport.Variant.row_loop.body,hn,bind_tc_ok]
  change (do
    let shift ← 2#usize * iter.start
    let right ← j >>> shift
    let tau ← Array.index_usize transport.TAU iter.start
    let shift1 ← 2#usize*tau
    let left ← (right &&& 3#usize) <<< shift1
    Result.ok (ControlFlow.cont (β:=Usize) (next,out ||| left))) = _
  have factor : (do
      let value ← CuSavingsS2SourceRowDigit.digit j iter.start out
      Result.ok (ControlFlow.cont (β:=Usize) (next,value))) = .ok (.cont (next,value)) := by
    rw [hd];rfl
  simpa only [CuSavingsS2SourceRowDigit.digit,bind_assoc_eq,bind_tc_ok] using factor

theorem loop_success (fuel : Nat) (j : Usize) (iter : Range) (out : Usize)
    (he : iter.end.val=5) (hi : iter.start.val≤5) (hf : 5-iter.start.val=fuel) :
    ∃ value : Usize, transport.Variant.row_loop iter j out = .ok value ∧
      value.val=run j.val iter.start.val fuel out.val := by
  induction fuel generalizing iter out with
  | zero =>
    have hn := next_done iter (by omega)
    refine ⟨out,?_,rfl⟩
    unfold transport.Variant.row_loop
    rw [loop]
    simp only [transport.Variant.row_loop.body,hn,bind_tc_ok]
    rfl
  | succ fuel ih =>
    obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
    obtain ⟨value,hvalue,hval⟩ := CuSavingsS2SourceRowDigit.source_success j iter.start out (by omega)
    obtain ⟨final,hfinal,hv⟩ := ih next value (by rw [hend];exact he) (by omega) (by omega)
    refine ⟨final,?_,?_⟩
    · unfold transport.Variant.row_loop
      rw [loop]
      dsimp only
      rw [body_step j out value iter next hn hvalue]
      exact hfinal
    · rw [hinc,hval] at hv
      exact hv

theorem source_s2 [Shared] (j : Usize) :
    ∃ row : Usize, transport.Variant.row transport.Variant.S2 j = .ok row ∧
      row.val=CuSavingsS2Tables.row j.val := by
  obtain ⟨row,hr,hv⟩ := loop_success 5 j {start:=0#usize,«end»:=5#usize} 0#usize
    (by scalar_tac) (by scalar_tac) (by scalar_tac)
  have hcmp : transport.Variant.Insts.CoreCmpPartialEqVariant.eq
      transport.Variant.S2 transport.Variant.D = .ok false := by
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  refine ⟨row,?_,?_⟩
  · simp only [transport.Variant.row,hcmp,bind_tc_ok,Bool.false_eq_true,if_false]
    exact hr
  · have h0 : (0#usize).val=0 := by scalar_tac
    change row.val = run j.val 0 5 0
    simpa only [h0] using hv

#print axioms body_step
#print axioms loop_success
#print axioms source_s2
end AspisR1.CuSavingsS2SourceRow
