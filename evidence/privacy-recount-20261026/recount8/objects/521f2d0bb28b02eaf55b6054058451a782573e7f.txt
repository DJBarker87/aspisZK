import R1Z.PV_RunJoin_RoundCellThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundLaneThread44
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def step (q w : Slice W) (d : Usize) (c : Array W 7#usize) (s : Usize) : Result (Array W 7#usize) :=
  PV_RunJoin_RoundCellThread44.phase q w d s 4 c 0#usize

def phase (q w : Slice W) (d : Usize) : Nat → Array W 7#usize → Usize → Result (Array W 7#usize)
  | 0,c,_ => .ok c
  | n+1,c,s => do
    let next ← step q w d c s
    phase q w d n next (Usize.wrapping_add s 1#usize)

theorem stop (q w : Slice W) (d : Usize) (c : Array W 7#usize) (s : Usize) (bound : 4 ≤ s.val) :
    prover.round_loop0_loop0.body q w d c s = .ok (.done c) := by
  simp only [prover.round_loop0_loop0.body,
    show ¬s < 4#usize from (by change ¬s.val < 4;omega),↓reduceIte]

theorem one_step (q w : Slice W) (d : Usize) (c : Array W 7#usize) (s : Usize) (bound : s.val < 4) :
    prover.round_loop0_loop0.body q w d c s = (do
      let next ← step q w d c s
      .ok (.cont (next,Usize.wrapping_add s 1#usize))) := by
  simp only [prover.round_loop0_loop0.body,
    show s < 4#usize from bound,↓reduceIte,lift,bind_assoc_eq,bind_tc_ok]
  rw [PV_RunJoin_RoundCellThread44.complete q w d s c 0#usize 4 (by rfl)]
  rfl

theorem complete (q w : Slice W) (d : Usize) (c : Array W 7#usize) (s : Usize)
    (n : Nat) (bound : s.val + n = 4) :
    prover.round_loop0_loop0 q w c d s = phase q w d n c s := by
  induction n generalizing c s with
  | zero =>
    unfold prover.round_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop q w d c s (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.round_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step q w d c s (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step q w d c s))
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment s (by omega)];omega)
#print axioms stop
#print axioms one_step
#print axioms complete
end R1Z.PV_RunJoin_RoundLaneThread44
