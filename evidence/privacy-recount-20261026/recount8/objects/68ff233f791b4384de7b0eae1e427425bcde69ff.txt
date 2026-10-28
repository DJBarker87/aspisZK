import R1Z.PV_RunJoin_BatchRowThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchThread44
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
open PV_RunJoin_BatchRowThread44 (W Coefficients)

def step (coefficients : Coefficients) (gp : Array W 29#usize)
    (q : alloc.vec.Vec W) (row : Usize) : Result (alloc.vec.Vec W) := do
  let value ← prover.opening_row coefficients gp row
  alloc.vec.Vec.push q value

def phase (coefficients : Coefficients) (gp : Array W 29#usize) :
    Nat → alloc.vec.Vec W → Usize → Result (alloc.vec.Vec W)
  | 0,q,_ => .ok q
  | n+1,q,row => do
    let next ← step coefficients gp q row
    phase coefficients gp n next (Usize.wrapping_add row 1#usize)

theorem stop (coefficients : Coefficients) (gp : Array W 29#usize)
    (q : alloc.vec.Vec W) (row : Usize) (bound : 1024 ≤ row.val) :
    prover.opening_batch_loop.body coefficients gp q row = .ok (.done q) := by
  simp only [prover.opening_batch_loop.body,
    show ¬row < 1024#usize from (by change ¬row.val < 1024;omega),↓reduceIte]

theorem one_step (coefficients : Coefficients) (gp : Array W 29#usize)
    (q : alloc.vec.Vec W) (row : Usize) (bound : row.val < 1024) :
    prover.opening_batch_loop.body coefficients gp q row = (do
      let next ← step coefficients gp q row
      .ok (.cont (next,Usize.wrapping_add row 1#usize))) := by
  simp only [prover.opening_batch_loop.body,
    show row < 1024#usize from bound,↓reduceIte,step,lift,bind_assoc_eq,bind_tc_ok]

theorem complete (coefficients : Coefficients) (gp : Array W 29#usize)
    (q : alloc.vec.Vec W) (row : Usize) (n : Nat) (bound : row.val + n = 1024) :
    prover.opening_batch_loop coefficients gp q row = phase coefficients gp n q row := by
  induction n generalizing q row with
  | zero =>
    unfold prover.opening_batch_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop coefficients gp q row (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.opening_batch_loop
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step coefficients gp q row (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step coefficients gp q row))
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment row (by omega)];omega)

theorem caller (coefficients : Coefficients) (gamma : W) :
    prover.opening_batch coefficients gamma = (do
      let gp ← weights.powers 29#usize gamma
      phase coefficients gp 1024 (alloc.vec.Vec.with_capacity W 1024#usize) 0#usize) := by
  unfold prover.opening_batch
  apply congrArg (Aeneas.Std.bind _)
  funext gp
  exact complete coefficients gp _ 0#usize 1024 (by rfl)
#print axioms stop
#print axioms one_step
#print axioms complete
#print axioms caller
end R1Z.PV_RunJoin_BatchThread44
