import DotPushSourceResidues
import OccupancyRangeTraversal
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error WP
open AspisR1DotPushLocal

namespace AspisR1DotPushOriginalRaw.Proof

abbrev Iter := core.ops.range.Range Usize

private theorem ix0 (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
private theorem ix1 (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
private theorem ix2 (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
private theorem ix3 (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
private theorem up0 (a b c d x : U64) : Array.update (Array.make 4#usize [a,b,c,d]) 0#usize x = .ok (Array.make 4#usize [x,b,c,d]) := rfl
private theorem up1 (a b c d x : U64) : Array.update (Array.make 4#usize [a,b,c,d]) 1#usize x = .ok (Array.make 4#usize [a,x,c,d]) := rfl
private theorem up2 (a b c d x : U64) : Array.update (Array.make 4#usize [a,b,c,d]) 2#usize x = .ok (Array.make 4#usize [a,b,x,d]) := by rfl
private theorem up3 (a b c d x : U64) : Array.update (Array.make 4#usize [a,b,c,d]) 3#usize x = .ok (Array.make 4#usize [a,b,c,x]) := rfl
private theorem shift31 (r : U64) : r >>> 31#i32 = .ok (AspisR1.EbyKDotPushCanonicalFoldBridgeV1.high r) := rfl

private theorem sourceFold_eq (x : U64) :
    core.num.U64.wrapping_add (x &&& core.convert.num.FromU64U32.from canonical.P)
      (AspisR1.EbyKDotPushCanonicalFoldBridgeV1.high x) =
      AspisR1.EbyKDotPushCanonicalFoldBridgeV1.wrappingFold x := by
  simp only [canonical.P, AspisR1.EbyKDotPushCanonicalFoldBridgeV1.wrappingFold,
    AspisR1.EbyKDotPushCanonicalFoldBridgeV1.high,
    AspisR1.ExtractedCurrentReducer.mask64, AspisR1.ExtractedCurrentReducer.mask32]
  rfl

/-- Exact Aeneas lowering of the retained Rust `Dot::push` loop body, with
only the opaque `Q::raw` call made an explicit argument. -/
def body (raw : Array U64 4#usize) (iter : Iter)
    (self : canonical.Dot) : Result (ControlFlow (Iter × canonical.Dot) canonical.Dot) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done self)
  | some j =>
    let i ← Array.index_usize self.sums j
    let i1 ← Array.index_usize raw j
    let i2 ← lift (core.convert.num.FromU64U32.from canonical.P)
    let i3 ← lift (i1 &&& i2)
    let i4 ← i1 >>> 31#i32
    let i5 ← lift (core.num.U64.wrapping_add i3 i4)
    let i6 ← lift (core.num.U64.wrapping_add i i5)
    let a ← Array.update self.sums j i6
    ok (cont (iter1, { sums := a }))

def loop (iter : Iter) (self : canonical.Dot) (raw : Array U64 4#usize) :
    Result canonical.Dot :=
  Aeneas.Std.loop (fun (s : Iter × canonical.Dot) => body raw s.1 s.2) (iter,self)

def push (rawFn : canonical.Q → canonical.Q → Result (Array U64 4#usize))
    (self : canonical.Dot) (left right : canonical.Q) : Result canonical.Dot := do
  let raw ← rawFn left right
  loop { start := 0#usize, «end» := 4#usize } self raw

def ExpectedSums (a b c d r0 r1 r2 r3 : U64) (n : Nat) : Array U64 4#usize :=
  Array.make 4#usize
    [if 0 < n then AspisR1DotPushLocal.Proof.updateWord a r0 else a,
     if 1 < n then AspisR1DotPushLocal.Proof.updateWord b r1 else b,
     if 2 < n then AspisR1DotPushLocal.Proof.updateWord c r2 else c,
     if 3 < n then AspisR1DotPushLocal.Proof.updateWord d r3 else d]

def LoopInv (a b c d r0 r1 r2 r3 : U64) (s : Iter × canonical.Dot) : Prop :=
  s.1.end.val = 4 ∧ s.1.start.val ≤ 4 ∧
    s.2.sums = ExpectedSums a b c d r0 r1 r2 r3 s.1.start.val

def LoopPost (a b c d r0 r1 r2 r3 : U64) (out : canonical.Dot) : Prop :=
  out.sums = ExpectedSums a b c d r0 r1 r2 r3 4

theorem loop_eq_literal4 (raw : Array U64 4#usize) (a b c d r0 r1 r2 r3 : U64)
    (hraw : raw = Array.make 4#usize [r0,r1,r2,r3]) :
    loop { start := 0#usize, «end» := 4#usize }
      ⟨Array.make 4#usize [a,b,c,d]⟩ raw =
      .ok ⟨Array.make 4#usize
        [AspisR1DotPushLocal.Proof.updateWord a r0,
         AspisR1DotPushLocal.Proof.updateWord b r1,
         AspisR1DotPushLocal.Proof.updateWord c r2,
         AspisR1DotPushLocal.Proof.updateWord d r3]⟩ := by
  subst raw
  let raw0 : Array U64 4#usize := Array.make 4#usize [r0,r1,r2,r3]
  let initial : canonical.Dot := ⟨Array.make 4#usize [a,b,c,d]⟩
  let iter0 : Iter := { start := 0#usize, «end» := 4#usize }
  have hinitial : LoopInv a b c d r0 r1 r2 r3 (iter0, initial) := by
    change iter0.end.val = 4 ∧ iter0.start.val ≤ 4 ∧
      initial.sums = ExpectedSums a b c d r0 r1 r2 r3 iter0.start.val
    constructor
    · decide
    constructor
    · decide
    · simp [ExpectedSums, iter0, initial]
  have hwp : WP.spec (Aeneas.Std.loop (fun s : Iter × canonical.Dot => body raw0 s.1 s.2)
      (iter0, initial)) (LoopPost a b c d r0 r1 r2 r3) := by
    refine Aeneas.Std.loop.spec_decr_nat (fun s : Iter × canonical.Dot => 4 - s.1.start.val)
      (LoopInv a b c d r0 r1 r2 r3) (LoopPost a b c d r0 r1 r2 r3)
      (fun s : Iter × canonical.Dot => body raw0 s.1 s.2) (iter0, initial) ?_ hinitial
    · intro s hs
      rcases s with ⟨iter, dot⟩
      rcases hs with ⟨hend, hstart, hvalues⟩
      change iter.end.val = 4 at hend
      change iter.start.val ≤ 4 at hstart
      change dot.sums = ExpectedSums a b c d r0 r1 r2 r3 iter.start.val at hvalues
      by_cases hlt : iter.start.val < iter.end.val
      · obtain ⟨iterNext, hnext, hstartNext, hendNext, hbound⟩ :=
          AspisR1.OccupancyRangeTraversal.next_step iter hlt
        have hidx : iter.start.val < 4 := by rw [← hend]; exact hlt
        let j := iter.start
        let nextDot : canonical.Dot := ⟨ExpectedSums a b c d r0 r1 r2 r3 (iter.start.val + 1)⟩
        have hbody : body raw0 iter dot = .ok (.cont (iterNext, nextDot)) := by
          have hidx0 : iter.start.val = 0 ∨ iter.start.val = 1 ∨
              iter.start.val = 2 ∨ iter.start.val = 3 := by omega
          rcases hidx0 with h0 | h1 | h2 | h3
          · have hiter : iter.start = 0#usize := UScalar.eq_of_val_eq h0
            have hnext' := hnext
            rw [hiter] at hnext'
            unfold body
            rw [hnext']
            simp only [bind_tc_ok]
            rw [hvalues]
            simp [h0, nextDot, ExpectedSums, AspisR1DotPushLocal.Proof.updateWord,
              AspisR1EbyKDotPushActualFoldV2.actualWrappingFold,
              ix0, ix1, ix2, ix3, up0, up1, up2, up3, raw0, lift, shift31]
            rw [sourceFold_eq]
          · have hiter : iter.start = 1#usize := UScalar.eq_of_val_eq h1
            have hnext' := hnext
            rw [hiter] at hnext'
            unfold body
            rw [hnext']
            simp only [bind_tc_ok]
            rw [hvalues]
            simp [h1, nextDot, ExpectedSums, AspisR1DotPushLocal.Proof.updateWord,
              AspisR1EbyKDotPushActualFoldV2.actualWrappingFold,
              ix0, ix1, ix2, ix3, up0, up1, up2, up3, raw0, lift, shift31]
            rw [sourceFold_eq]
          · have hiter : iter.start = 2#usize := UScalar.eq_of_val_eq h2
            have hnext' := hnext
            rw [hiter] at hnext'
            unfold body
            rw [hnext']
            simp only [bind_tc_ok]
            rw [hvalues]
            simp [h2, nextDot, ExpectedSums, AspisR1DotPushLocal.Proof.updateWord,
              AspisR1EbyKDotPushActualFoldV2.actualWrappingFold,
              ix0, ix1, ix2, ix3, up0, up1, up2, up3, raw0, lift, shift31]
            rw [sourceFold_eq]
          · have hiter : iter.start = 3#usize := UScalar.eq_of_val_eq h3
            have hnext' := hnext
            rw [hiter] at hnext'
            unfold body
            rw [hnext']
            simp only [bind_tc_ok]
            rw [hvalues]
            simp [h3, nextDot, ExpectedSums, AspisR1DotPushLocal.Proof.updateWord,
              AspisR1EbyKDotPushActualFoldV2.actualWrappingFold,
              ix0, ix1, ix2, ix3, up0, up1, up2, up3, raw0, lift, shift31]
            rw [sourceFold_eq]
        have hinv : LoopInv a b c d r0 r1 r2 r3 (iterNext, nextDot) := by
          refine ⟨?_, ?_, ?_⟩
          · rw [hendNext]; exact hend
          · rw [hstartNext]; omega
          · simp [nextDot, ExpectedSums, hstartNext]
        rw [hbody, WP.spec_ok]
        change LoopInv a b c d r0 r1 r2 r3 (iterNext, nextDot) ∧
          4 - iterNext.start.val < 4 - iter.start.val
        exact ⟨hinv, by rw [hstartNext]; omega⟩
      · have hge : iter.start.val ≥ iter.end.val := Nat.le_of_not_gt hlt
        have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hge
        have hdone : body raw0 iter dot = .ok (.done dot) := by
          simp [body, raw0, hnext]
        rw [hdone, WP.spec_ok]
        change LoopPost a b c d r0 r1 r2 r3 dot
        have hstartEq : iter.start.val = 4 := by rw [← hend]; omega
        simpa [LoopPost, ExpectedSums, hstartEq] using hvalues
  obtain ⟨out, hout, houtInv⟩ := WP.spec_imp_exists hwp
  have houtRun : loop { start := 0#usize, «end» := 4#usize }
      ⟨Array.make 4#usize [a,b,c,d]⟩ (Array.make 4#usize [r0,r1,r2,r3]) = .ok out := by
    simpa [loop, iter0, initial, raw0] using hout
  have houtShape : out = ⟨Array.make 4#usize
        [AspisR1DotPushLocal.Proof.updateWord a r0,
         AspisR1DotPushLocal.Proof.updateWord b r1,
         AspisR1DotPushLocal.Proof.updateWord c r2,
         AspisR1DotPushLocal.Proof.updateWord d r3]⟩ := by
    cases out with
    | mk sums =>
      simp [LoopPost, ExpectedSums] at houtInv
      simp [canonical.Dot, houtInv]
  rw [houtRun, houtShape]


theorem loop_eq_updatedSums (a b c d r0 r1 r2 r3 : U64) :
    loop { start := 0#usize, «end» := 4#usize }
      ⟨Array.make 4#usize [a,b,c,d]⟩ (Array.make 4#usize [r0,r1,r2,r3]) =
      .ok ⟨AspisR1DotPushLocal.Proof.updatedSums
        (Array.make 4#usize [a,b,c,d]) (Array.make 4#usize [r0,r1,r2,r3])⟩ := by
  rw [loop_eq_literal4 (Array.make 4#usize [r0,r1,r2,r3]) a b c d r0 r1 r2 r3 rfl]
  rfl

#print axioms loop_eq_literal4
#print axioms loop_eq_updatedSums
end AspisR1DotPushOriginalRaw.Proof
