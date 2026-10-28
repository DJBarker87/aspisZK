import R1Z.PV_RunJoin_FoldThread44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundCellThread44
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact

def step (q w : Slice W) (d s : Usize) (c : Array W 7#usize) (t : Usize) : Result (Array W 7#usize) := do
  let p ← Array.index_usize weights.PERM t
  let at1 := Usize.wrapping_add s p
  let old ← Array.index_usize c at1
  let qv ← Slice.index_usize q (Usize.wrapping_add (Usize.wrapping_mul 4#usize d) s)
  let wv ← Slice.index_usize w (Usize.wrapping_add (Usize.wrapping_mul 4#usize d) t)
  let product ← aspis_core.field.wide_exact.WideExact.mul qv wv
  let value ← aspis_core.field.wide_exact.WideExact.add old product
  Array.update c at1 value

def phase (q w : Slice W) (d s : Usize) : Nat → Array W 7#usize → Usize → Result (Array W 7#usize)
  | 0,c,_ => .ok c
  | n+1,c,t => do
    let next ← step q w d s c t
    phase q w d s n next (Usize.wrapping_add t 1#usize)

theorem stop (q w : Slice W) (d s : Usize) (c : Array W 7#usize) (t : Usize) (bound : 4 ≤ t.val) :
    prover.round_loop0_loop0_loop0.body q w d s c t = .ok (.done c) := by
  simp only [prover.round_loop0_loop0_loop0.body,
    show ¬t < 4#usize from (by change ¬t.val < 4;omega),↓reduceIte]

theorem one_step (q w : Slice W) (d s : Usize) (c : Array W 7#usize) (t : Usize) (bound : t.val < 4) :
    prover.round_loop0_loop0_loop0.body q w d s c t = (do
      let next ← step q w d s c t
      .ok (.cont (next,Usize.wrapping_add t 1#usize))) := by
  simp only [prover.round_loop0_loop0_loop0.body,
    show t < 4#usize from bound,↓reduceIte,step,lift,bind_assoc_eq,bind_tc_ok]

theorem complete (q w : Slice W) (d s : Usize) (c : Array W 7#usize) (t : Usize)
    (n : Nat) (bound : t.val + n = 4) :
    prover.round_loop0_loop0_loop0 q w c d s t = phase q w d s n c t := by
  induction n generalizing c t with
  | zero =>
    unfold prover.round_loop0_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [stop q w d s c t (by omega),bind_tc_ok,phase]
  | succ n ih =>
    unfold prover.round_loop0_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step q w d s c t (by omega)]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind (step q w d s c t))
    funext next
    exact ih next _ (by rw [PV_RunJoin_MergeLoop35.increment t (by omega)];omega)
#print axioms stop
#print axioms one_step
#print axioms complete
end R1Z.PV_RunJoin_RoundCellThread44
