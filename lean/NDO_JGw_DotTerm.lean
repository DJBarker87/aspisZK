import NDO_JGw_DotUpdate
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_DotTerm
open Aeneas Aeneas.Std Result ControlFlow

abbrev cursor := JFr_TX2_DotTerm.cursor

/-- Every retained native term body reaches the actual eight-limb update
with its computed real-byte scalar. The update remains the real checked body;
no successful-update or loop-return assumption is used. -/
theorem source (q : Array U8 608#usize) (slot : Fin 4) (term : Fin 26)
    (scalar : U32) (read : JFr_TX2_ScalarRead.read q
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))
      (cursor term.val (by have:=term.isLt;omega))=ok scalar)
    (stop : Usize) (order : term.val<stop.val)
    (g : Array FIo_Install.NE 29#usize) (sums : Array U64 8#usize) :
    ∃ next : core.ops.range.Range Usize,
      next.start.val=term.val+1 ∧ next.end=stop ∧
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
        q g
        (Usize.ofNat slot.val (by have := slot.isLt;scalar_tac))
        {start:=cursor term.val (by have := term.isLt;omega),«end»:=stop} sums=
      (do let out ← JFr_TX2_DotStep.update g (cursor term.val (by have := term.isLt;omega))
            scalar sums
          ok (cont (next,out))) := by
  let iter : core.ops.range.Range Usize :=
    {start:=cursor term.val (by have := term.isLt;omega),«end»:=stop}
  obtain ⟨⟨o,next⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro a b;rfl)
      iter order)
  subst o
  refine ⟨next,hs,he,?_⟩
  rw [JFr_TX2_DotStep.body]
  unfold JFr_TX2_DotStep.step
  rw [run,bind_tc_ok]
  dsimp only [iter,cursor]
  simp only [Aeneas.Std.uncurry,read,bind_tc_ok]

#print axioms source
end AspisR1.JGw_DotTerm
end
