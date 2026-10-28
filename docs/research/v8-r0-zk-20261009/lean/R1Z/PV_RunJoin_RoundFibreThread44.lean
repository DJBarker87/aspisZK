import R1Z.PV_RunJoin_RoundLaneThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundFibreThread44
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def step (q w : Slice W) (c : Array W 7#usize) (d : Usize) : Result (Array W 7#usize) :=
  PV_RunJoin_RoundLaneThread44.phase q w d 4 c 0#usize

def phase (q w : Slice W) : Nat → Array W 7#usize → Usize → Result (Array W 7#usize)
  | 0,c,_ => .ok c
  | n+1,c,d => do
    let next ← step q w c d
    phase q w n next (Usize.wrapping_add d 1#usize)

theorem stop (q w : Slice W) (c : Array W 7#usize) (d : Usize) (bound : q.length / 4 ≤ d.val) :
    prover.round_loop0.body q w c d = .ok (.done c) := by
  obtain ⟨k,hk,hkv⟩ := PV_RunJoin_FoldThread44.quotient q
  unfold prover.round_loop0.body
  dsimp only
  rw [hk]
  simp only [bind_tc_ok,show ¬d < k from (by change ¬d.val < k.val;omega),↓reduceIte]

theorem one_step (q w : Slice W) (c : Array W 7#usize) (d : Usize) (bound : d.val < q.length / 4) :
    prover.round_loop0.body q w c d = (do
      let next ← step q w c d
      .ok (.cont (next,Usize.wrapping_add d 1#usize))) := by
  obtain ⟨k,hk,hkv⟩ := PV_RunJoin_FoldThread44.quotient q
  unfold prover.round_loop0.body
  dsimp only
  rw [hk]
  simp only [bind_tc_ok,show d < k from (by change d.val < k.val;omega),↓reduceIte,lift]
  rw [PV_RunJoin_RoundLaneThread44.complete q w d c 0#usize 4 (by rfl)]
  rfl

theorem complete (q w : Slice W) (c : Array W 7#usize) (d : Usize)
    (n : Nat) (bound : d.val + n = q.length / 4) (small : q.length / 4 ≤ 256) :
    prover.round_loop0 q w c d = phase q w n c d := by
  induction n generalizing c d with
  | zero =>
    unfold prover.round_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop q w c d (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.round_loop0
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step q w c d (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step q w c d))
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment d (by omega)];omega)
#print axioms stop
#print axioms one_step
#print axioms complete
end R1Z.PV_RunJoin_RoundFibreThread44
