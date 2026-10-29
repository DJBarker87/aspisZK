import PV_B3P_IndexSteps9227
import PV_B3P_BindBranch12227
import PV_B3P_MatrixModel10227
import PV_B3P_UsizeLoop9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 Result
set_option autoImplicit false

abbrev Channels12 := Array (Array U32 3#usize) 3#usize
def source_channel12 (left right : Channels12) (component : Usize)
    (sums : Matrix3x3) (channel : Usize) : Result Matrix3x3 := do
  let lrow ← Array.index_usize left component
  let l ← Array.index_usize lrow channel
  let rrow ← Array.index_usize right component
  let r ← Array.index_usize rrow channel
  matrix_cell sums component channel l r

theorem source_channel_binding12 (left right : Channels12) (component channel : Usize)
    (hc : component.val<3) (hk : channel.val<3) (sums : Matrix3x3) :
    source_channel12 left right component sums channel =
      matrix_cell sums component channel
        ((left.val[component.val]'(by rw [left.property]; exact hc)).val[channel.val]'(by
          rw [(left.val[component.val]'(by rw [left.property]; exact hc)).property]; exact hk))
        ((right.val[component.val]'(by rw [right.property]; exact hc)).val[channel.val]'(by
          rw [(right.val[component.val]'(by rw [right.property]; exact hc)).property]; exact hk)) := by
  unfold source_channel12
  rw [PV_B3P_SelectIndex227.index_value left component hc]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value (n:=3#usize) _ channel hk]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value right component hc]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value (n:=3#usize) _ channel hk]
  simp only [bind_tc_ok]

theorem three_loop12 {α : Type} (step : α → Usize → Result α) (state : α) :
    loop (usize_body step 3#usize) (state,0#usize) = (do
      let s0 ← step state 0#usize
      let s1 ← step s0 1#usize
      step s1 2#usize) := by
  rw [usize_loop_plan step 3#usize 0#usize 3 state (by scalar_tac)]
  have h01 : Usize.wrapping_add 0#usize 1#usize = 1#usize := next_exact _ _ rfl
  have h12 : Usize.wrapping_add 1#usize 1#usize = 2#usize := next_exact _ _ rfl
  simp only [usize_plan,h01,h12,PV_B3P_Ordered227.bind_assoc,bind_tc_ok,bind_return12]

def source_component12 (left right : Channels12) (component : Usize) (sums : Matrix3x3) : Result Matrix3x3 :=
  loop (usize_body (source_channel12 left right component) 3#usize) (sums,0#usize)

def source_nested12 (left right : Channels12) (sums : Matrix3x3) : Result Matrix3x3 :=
  loop (usize_body (fun sums component => source_component12 left right component sums) 3#usize) (sums,0#usize)

#print axioms source_channel_binding12
#print axioms three_loop12
end PV_B3P_Binding12227
