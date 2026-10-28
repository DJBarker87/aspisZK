import R1Z.PV_RunJoin_MergeLoop35
import R1Z.PV_RunJoin_WideArithmetic44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchRowThread44
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Coefficients := Slice (Array W 1024#usize)

def step (coefficients : Coefficients) (gp : Array W 29#usize)
    (row lane : Usize) (value : W) : Result W := do
  let p ← Array.index_usize gp lane
  let a ← Slice.index_usize coefficients lane
  let q ← Array.index_usize a row
  let product ← aspis_core.field.wide_exact.WideExact.mul p q
  aspis_core.field.wide_exact.WideExact.add value product

def phase (coefficients : Coefficients) (gp : Array W 29#usize) (row : Usize) :
    Nat → Usize → W → Result W
  | 0,_,value => .ok value
  | n+1,lane,value => do
    let next ← step coefficients gp row lane value
    phase coefficients gp row n (Usize.wrapping_add lane 1#usize) next

theorem stop (coefficients : Coefficients) (gp : Array W 29#usize)
    (row lane : Usize) (value : W) (bound : 29 ≤ lane.val) :
    prover.opening_row_loop.body coefficients gp row value lane = .ok (.done value) := by
  simp only [prover.opening_row_loop.body,
    show ¬lane < 29#usize from (by change ¬lane.val < 29;omega),↓reduceIte]

theorem one_step (coefficients : Coefficients) (gp : Array W 29#usize)
    (row lane : Usize) (value : W) (bound : lane.val < 29) :
    prover.opening_row_loop.body coefficients gp row value lane = (do
      let next ← step coefficients gp row lane value
      .ok (.cont (next,Usize.wrapping_add lane 1#usize))) := by
  simp only [prover.opening_row_loop.body,
    show lane < 29#usize from bound,↓reduceIte,step,lift,bind_assoc_eq,bind_tc_ok]

theorem complete (coefficients : Coefficients) (gp : Array W 29#usize)
    (row lane : Usize) (value : W) (n : Nat) (bound : lane.val + n = 29) :
    prover.opening_row_loop coefficients gp row value lane = phase coefficients gp row n lane value := by
  induction n generalizing lane value with
  | zero =>
    unfold prover.opening_row_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop coefficients gp row lane value (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.opening_row_loop
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step coefficients gp row lane value (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step coefficients gp row lane value))
    funext next
    exact ih _ next (by rw [PV_RunJoin_MergeLoop35.increment lane (by omega)];omega)

theorem caller (coefficients : Coefficients) (gp : Array W 29#usize) (row : Usize) :
    prover.opening_row coefficients gp row = (do
      let zero ← aspis_core.field.wide_exact.WideExact.ZERO
      phase coefficients gp row 29 0#usize zero) := by
  unfold prover.opening_row
  apply congrArg (Aeneas.Std.bind _)
  funext zero
  exact complete coefficients gp row 0#usize zero 29 (by rfl)
#print axioms stop
#print axioms one_step
#print axioms complete
#print axioms caller
end R1Z.PV_RunJoin_BatchRowThread44
