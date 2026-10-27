import PV_B3_Forest_134_Funs
import PV_B3_Result
namespace PV_B3_MaskCounter
open Aeneas Aeneas.Std Result ControlFlow
open PV_B3_Forest_134 PV_B3_Result
set_option autoImplicit false

abbrev State := Array U8 1024#usize × Array U8 1024#usize × Array U16 64#usize × Usize
abbrev Final := core.result.Result (Array U16 64#usize)
  aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1

def Progress (i : Usize) : ControlFlow State Final → Prop
  | .done _ => True
  | .cont next => next.2.2.2 = Usize.wrapping_add i 1#usize

theorem done_safe (i : Usize) (value : Final) : Safe (Progress i) (ok (done value)) := by
  intro cf h
  cases h
  trivial

theorem body_counter (producers consumers : Array U8 1024#usize)
    (masks : Array U16 64#usize) (i : Usize) :
    Safe (Progress i)
      (host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
        producers consumers masks i) := by
  unfold host_forest.pool_v1_pair_forest_copy_active_row_masks_v1_loop.body
  split
  · apply bind_any
    rintro ⟨a,b⟩
    apply bind_any
    intro p
    apply bind_any
    intro c
    split
    · exact done_safe i _
    · apply bind_any
      intro oldp
      apply bind_any
      intro bumpedp
      cases bumpedp with
      | none => exact done_safe i _
      | some newp =>
        apply bind_any
        rintro ⟨_,back⟩
        split
        · exact done_safe i _
        · apply bind_any
          intro oldc
          apply bind_any
          intro bumpedc
          cases bumpedc with
          | none => exact done_safe i _
          | some newc =>
            apply bind_any
            intro consumers1
            apply bind_any
            intro bitp
            apply bind_any
            intro shiftp
            apply bind_any
            intro powp
            apply bind_any
            intro blockp
            apply bind_any
            intro oldmaskp
            apply bind_any
            intro newmaskp
            apply bind_any
            intro masks1
            apply bind_any
            intro bitc
            apply bind_any
            intro shiftc
            apply bind_any
            intro powc
            apply bind_any
            intro blockc
            apply bind_any
            intro oldmaskc
            apply bind_any
            intro newmaskc
            apply bind_any
            intro masks2
            intro cf h
            cases h
            rfl
  · exact done_safe i _

#print axioms Progress
#print axioms done_safe
#print axioms body_counter
end PV_B3_MaskCounter
