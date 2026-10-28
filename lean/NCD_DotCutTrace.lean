import NCD_R_NCB_DotNativeStep
set_option autoImplicit false
noncomputable section
namespace NCD_DotCutTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
/-- Ordered scalar/coefficient/eight-cell observations from the SAME range
and arrays. Existence of these native observations remains a native gate. -/
inductive Cuts (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize)
    (slot : Usize) : Nat → core.ops.range.Range Usize →
    Array U64 8#usize → Array U64 8#usize → Prop
  | done (n iter sums) (stop : iter.end.val ≤ iter.start.val) :
      Cuts q g slot n iter sums sums
  | step (n iter next before after final wide coefficient scalar)
      (active : iter.start.val < iter.end.val) (small : n<4)
      (increment : next.start.val=iter.start.val+1) (ending : next.end=iter.end)
      (scalarRead : JFr_TX2_ScalarRead.read q slot iter.start=ok scalar)
      (wideRead : Array.index_usize g iter.start=ok wide)
      (limbRead : FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs wide=ok coefficient)
      (canonical : JFs_TX2_ArrayEight.Canon coefficient) (scalarDomain : scalar.val<2147483647)
      (cells : NBS_NativeEight.Observed coefficient scalar before after)
      (tail : Cuts q g slot (n+1) next after final) :
      Cuts q g slot n iter before final

theorem bound (coefficient : Array U32 8#usize) (scalar : U32)
    (before after : Array U64 8#usize) (n : Nat)
    (hc : JFs_TX2_ArrayEight.Canon coefficient) (hscalar : scalar.val<2147483647)
    (hn : n<4) (hs : JFs_TX2_ArrayEight.Bound before n)
    (cells : NBS_NativeEight.Observed coefficient scalar before after) :
    JFs_TX2_ArrayEight.Bound after (n+1) := by
  obtain ⟨out,run,bounded⟩ := JFs_TX2_ArrayEight.source coefficient scalar before n hc hscalar hn hs
  have observed := NBS_NativeEight.source coefficient scalar before after n hc hscalar hn hs cells
  have same := Result.ok.inj (run.symm.trans observed)
  simpa only [same] using bounded

theorem associated (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize)
    (slot : Usize) (n : Nat) (iter : core.ops.range.Range Usize)
    (before final : Array U64 8#usize)
    (cuts : Cuts q g slot n iter before final) (hs : JFs_TX2_ArrayEight.Bound before n) :
    FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter q g slot before=ok final := by
  induction cuts with
  | done n iter sums stop =>
    have terminal : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=
        ok (done sums) := by
      obtain ⟨⟨o,next⟩,run,none,_⟩ := WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_UScalar_none_spec
          (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
          (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro a b;rfl) iter stop)
      subst o
      rw [JFr_TX2_DotStep.body]
      simp only [JFr_TX2_DotStep.step,run,bind_tc_ok,Aeneas.Std.uncurry]
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,terminal]
  | step n iter next before after final wide coefficient scalar active small increment ending scalarRead wideRead limbRead canonical scalarDomain cells tail ih =>
    have nextBound := bound coefficient scalar before after n canonical scalarDomain small hs cells
    have tailRun := ih nextBound
    obtain ⟨cursor,inc,he,body⟩ := NCB_DotNativeStep.source q g slot iter before after wide
      coefficient scalar n active scalarRead wideRead limbRead canonical scalarDomain small hs cells
    have same : cursor=next := by
      cases cursor with
      | mk a b =>
        cases next with
        | mk c d =>
          dsimp only at inc he increment ending
          have ac : a=c := UScalar.eq_of_val_eq (inc.trans increment.symm)
          have bd : b=d := he.trans ending.symm
          cases ac
          cases bd
          rfl
    rw [same] at body
    unfold FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,body]
    exact tailRun
#print axioms bound
#print axioms associated
end NCD_DotCutTrace
end
