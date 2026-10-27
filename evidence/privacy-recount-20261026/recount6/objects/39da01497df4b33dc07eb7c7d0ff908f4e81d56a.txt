import R1Z.PV_AL_PopUnfold
import R1Z.PV_CBL_ArrayStep
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_AL_PopStep
set_option autoImplicit false

theorem done {T : Type} (v : Slice T) (out : alloc.vec.Vec T) (last i : Usize)
    (h : last.val ≤ i.val) :
    PV_CBL_PopSlices.pop_slices_reference_loop.body v last out i = ok (.done out) := by
  have hn : ¬i<last := by change ¬i.val<last.val; omega
  simp only [PV_CBL_PopSlices.pop_slices_reference_loop.body,hn,if_false]

theorem continuing {T : Type} (v : Slice T) (out : alloc.vec.Vec T) (last i : Usize)
    (h : i.val<last.val) (hv : last.val≤v.val.length)
    (ho : out.val.length<Usize.max) :
    ∃ next, PV_CBL_PopSlices.pop_slices_reference_loop.body v last out i =
      ok (.cont (next,Usize.wrapping_add i 1#usize)) ∧
      next.val=out.val++[v.val[i.val]'(by omega)] := by
  obtain ⟨next,hnext,he⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out
    v.val[i.val] ho)
  refine ⟨next,?_,he⟩
  have hn : i<last := h
  simp only [PV_CBL_PopSlices.pop_slices_reference_loop.body,hn,if_true,
    PV_CBL_ArrayStep.read v i (by omega),hnext,lift,bind_tc_ok]
#print axioms done
#print axioms continuing
end R1Z.PV_AL_PopStep
