import RPt_JFr_TX2_Scalars
import RPt_JFr_TX2_DotStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_DotTerm
open Aeneas Aeneas.Std Result ControlFlow

def cursor (n : Nat) (bound : n<27) : Usize := Usize.ofNat n (by scalar_tac)

/-- Every retained native term body reaches the actual eight-limb update
with its computed real-byte scalar. The update remains the real checked body;
no successful-update or loop-return assumption is used. -/
theorem source (i : Fin 12) (slot : Fin 4) (term : Fin 26)
    (stop : Usize) (order : term.val<stop.val)
    (g : Array FIo_Install.NE 29#usize) (sums : Array U64 8#usize) :
    ∃ next : core.ops.range.Range Usize,
      next.start.val=term.val+1 ∧ next.end=stop ∧
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
        (JFr_TX2_Windows.array (JFn_Values.position i)) g
        (Usize.ofNat slot.val (by have := slot.isLt;scalar_tac))
        {start:=cursor term.val (by have := term.isLt;omega),«end»:=stop} sums=
      (do let out ← JFr_TX2_DotStep.update g (cursor term.val (by have := term.isLt;omega))
            ((JFr_TX2_Scalars.values i slot).val[term.val]'(by rw [(JFr_TX2_Scalars.values i slot).property];exact term.isLt)) sums
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
  simp only [Aeneas.Std.uncurry,JFr_TX2_Scalars.source,bind_tc_ok]

#print axioms source
end AspisR1.JFr_TX2_DotTerm
end
