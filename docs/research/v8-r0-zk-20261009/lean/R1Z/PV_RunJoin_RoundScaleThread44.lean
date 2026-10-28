import R1Z.PV_RunJoin_RoundCellThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundScaleThread44
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def step (c : Array W 7#usize) (i : Usize) : Result (Array W 7#usize) := do
  let value ← Array.index_usize c i
  let scaled ← aspis_core.field.wide_exact.WideExact.mul_m31 value weights.QUARTER
  Array.update c i scaled

def phase : Nat → Array W 7#usize → Usize → Result (Array W 7#usize)
  | 0,c,_ => .ok c
  | n+1,c,i => do
    let next ← step c i
    phase n next (Usize.wrapping_add i 1#usize)

theorem stop (c : Array W 7#usize) (i : Usize) (bound : 7 ≤ i.val) :
    prover.round_loop1.body c i = .ok (.done c) := by
  simp only [prover.round_loop1.body,
    show ¬i < 7#usize from (by change ¬i.val < 7;omega),↓reduceIte]

theorem one_step (c : Array W 7#usize) (i : Usize) (bound : i.val < 7) :
    prover.round_loop1.body c i = (do
      let next ← step c i
      .ok (.cont (next,Usize.wrapping_add i 1#usize))) := by
  simp only [prover.round_loop1.body,
    show i < 7#usize from bound,↓reduceIte,step,lift,bind_assoc_eq,bind_tc_ok]

theorem complete (c : Array W 7#usize) (i : Usize) (n : Nat) (bound : i.val + n = 7) :
    prover.round_loop1 c i = phase n c i := by
  induction n generalizing c i with
  | zero =>
    unfold prover.round_loop1
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop c i (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.round_loop1
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step c i (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step c i))
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment i (by omega)];omega)
#print axioms stop
#print axioms one_step
#print axioms complete
end R1Z.PV_RunJoin_RoundScaleThread44
