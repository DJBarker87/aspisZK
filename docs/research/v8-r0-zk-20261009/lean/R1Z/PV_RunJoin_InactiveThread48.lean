import R1Z.PV_RunJoin_MergeLoop35
import R1Z.PV_RunJoin_CoefficientInstalled45
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InactiveThread48
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def step (q : Slice W) (w : weights.Weights) (sum : W) (row : Usize) := do
  let value ← Slice.index_usize q row
  let raw ← weights.Weights.raw w 0#usize row
  let product ← aspis_core.field.wide_exact.WideExact.mul_qm31 value raw
  aspis_core.field.wide_exact.WideExact.add sum product

def phase (q : Slice W) (w : weights.Weights) : Nat → W → Usize → Result (W)
  | 0,out,_ => .ok out
  | n+1,out,lane => do
    let next ← step q w out lane
    phase q w n next (Usize.wrapping_add lane 1#usize)

theorem stop (q : Slice W) (w : weights.Weights) (out : W)
    (lane : Usize) (bound : 1024 ≤ lane.val) :
    prover.opening_inactive_loop.body q w out lane = .ok (.done out) := by
  simp only [prover.opening_inactive_loop.body,
    show ¬lane < 1024#usize from (by change ¬lane.val < 1024;omega),↓reduceIte]

theorem one_step (q : Slice W) (w : weights.Weights) (out : W)
    (lane : Usize) (bound : lane.val < 1024) :
    prover.opening_inactive_loop.body q w out lane = (do
      let next ← step q w out lane
      .ok (.cont (next,Usize.wrapping_add lane 1#usize))) := by
  simp only [prover.opening_inactive_loop.body,
    show lane < 1024#usize from bound,↓reduceIte,step,lift,bind_assoc_eq,bind_tc_ok]

theorem complete (q : Slice W) (w : weights.Weights) (out : W)
    (lane : Usize) (n : Nat) (bound : lane.val + n = 1024) :
    prover.opening_inactive_loop q w out lane = phase q w n out lane := by
  induction n generalizing out lane with
  | zero =>
    unfold prover.opening_inactive_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop q w out lane (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.opening_inactive_loop
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step q w out lane (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step q w out lane))
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment lane (by omega)];omega)
#print axioms stop
#print axioms one_step
#print axioms complete
end R1Z.PV_RunJoin_InactiveThread48
